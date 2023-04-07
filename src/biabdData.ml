open Tools
open Slsyntax
open Sltosmt   
open Smttoz3
open Smtsyntax
module SatResult = Smttoz3.SatcheckResult

exception NoSolution
;;
(* tag for debugging: -deb "BIABD_debug" *)
let tagDebug = "BIABD_debug"
;;
let tagDebug2 = "BIABD_debug2" (* detailed debugging *)
;;
let tagTime = "BIABD_time"
;;
let (tm1,tm2) = (ref 0.0,ref 0.0)
;;
let getTime1 () = tm1 := Sys.time ()
;;
let getTime2 () = tm2 := Sys.time ()
;;
let showTimeDiff mes = print_endline (mes ^ " (" ^ (string_of_float (!tm2 -. !tm1)) ^ ")")
;;
let isValid_pb p =
  let vv = Strset.elements (P.fv p) in
  let q = allint' vv (mkExp_p p) in
  checkSatExpBool q
;;
let ml = 100000000
;;
(* Extension of Brotherston's gamma *)
(* It is for SH with arrays and lists *)
(* gammaAL pp ss is sat'ble <-> (p,ss) is sat'ble *)
let gammaAL pp ss : P.t =
  let (ssPto,ssArr,ssLs) = SS.splitPtoArrayList ss in
  let iiPto = List.map S.mkInterval ssPto in    
  let iiArr = List.map S.mkInterval ssArr in
  let iiLs = List.map S.mkIntervalLs ssLs in
  let ppBody0 =
    let ttAddr = (List.map fst iiPto) @ (List.map fst iiArr) in
    let ppAddrCond1 = List.map (fun t -> zero <.< t) ttAddr in
    let ppAddrCond2 = List.map (fun (a,b) -> a <.= b) iiArr in
    List.rev_append ppAddrCond1 ppAddrCond2
  in
  let ppBody1 =
    List.map
      (fun (c,d) ->
        let pDisj = P.mkAnd (List.map (fun (t,u) -> (_Disj c c t u)) (iiPto@iiArr)) in
        (c <.> d) =.> pDisj)
      iiLs
  in
  let ppBody2 = applyDiff (fun (c1,d1) (c2,d2) -> ((c1 <.> d1) &.& (c2 <.> d2)) =.> (c1 <.> c2)) iiLs in
  let ppBody3 = applyDiff (fun (c1,d1) (c2,d2) -> (_Disj c1 d1 c2 d2)) (iiPto@iiArr) in
  P.mkAnd (List_tailrec.concat [pp;ppBody0;ppBody1;ppBody2;ppBody3])
;;

module BAquery = struct
  (* Biabduction query *)
  (* (pure_ex,pure,ss1,ss2) *)
  type t = P.t list * P.t * SS.t * SS.t

  let pp fmt (bq : t) =
    let (pp_ex,p,ss1,ss2) = bq in
    let sAnd = match pp_ex with [] -> "" | _ -> "&" in
    Format.fprintf fmt "%a%s%a && %a * X? |- %a * Y?" (pp_list "" " & " P.pp) pp_ex sAnd P.pp p SS.pp ss1 SS.pp ss2

  let print = Format.printf "@[%a@]" pp

  let println = Format.printf "@[%a@." pp
       
end
;;

module BAanswer = struct
  (* Biabduction answer *)
  (* (pureL,ss1,ss2) *)
  type t =
    {
      mutable pp : P.t list;
      mutable ssX : SS.t;
      mutable ssY : SS.t
    }

  let create pp ssX ssY =
    {
      pp = pp;
      ssX = ssX;
      ssY = ssY;
    }

  let clone (ba : t) = create ba.pp ba.ssX ba.ssY

  let pp fmt (ba : t) =
    let disjuncts =
      match ba.pp with
      | [P.Or pp] ->
         let nLst = genLst (List.length pp) in
         zipLst nLst pp
      | _ -> [(0,P.mkAnd ba.pp)]
    in
    let pp_disjuncts fmt disj =
      let pp1 fmt (n,p) = Format.fprintf fmt "P%d: %a" n P.pp p in
      Format.fprintf fmt "%a" (pp_list "" "\n" pp1) disj
    in
    let pp_pure fmt disj =
      let pp1 fmt (n,_) = Format.fprintf fmt "P%d" n in
      Format.fprintf fmt "%a" (pp_list "True" " | " pp1) disj
    in
    Format.fprintf fmt "%a\n" pp_disjuncts disjuncts;
    Format.fprintf fmt "P: %a\n" pp_pure disjuncts;
    Format.fprintf fmt "X: %a\n" SS.pp ba.ssX;
    Format.fprintf fmt "Y: %a" SS.pp ba.ssY

  let println = Format.printf "@[%a@." pp
    
  let printlnln = Format.printf "@[%a\n@." pp

  let println_many baL =
    let num = List.length baL in
    let rec aux n baL =
      match baL with
      | [] -> ()
      | ba::baL1 ->
         ANSITerminal.(printf [Bold] "- Answer (%n/%n)\n" n num);
         Format.printf "@[%a@." pp ba;
         aux (n+1) baL1
    in
    match num with
    | 0 -> ANSITerminal.(printf [Bold] "No Answers\n");
    | _ ->
       ANSITerminal.(printf [Bold] "Number of Answers: %n\n" num);
       aux 1 baL
                           
  let syntactical_simpl (ba: t) =
    ba.pp <- P.syntactical_simplL ba.pp;
    ba.ssX <- SS.syntactical_simpl ba.ssX;
    ba.ssY <- SS.syntactical_simpl ba.ssY;
    ba

  (* addContentsPure *)
(* Input
ss1: [ t->(f:x,g:y); 10->() ] 
ss2: [ t->(g:z+1,f:1) ] 
Result
x=1 & y=z+1
 *)
  let update_ptocontents bq ba =
    let (pp_ex,p,ss1,ss2) = bq in
    let p1 = P.mkAnd (p :: pp_ex @ ba.pp) in
    let ss1' = ss1 @ ba.ssX in
    let h : QFSH.t = (p1,ss1') in
    let _pmodel = ref [] in
    let setPModel () =
      match Satcheck.satcheck_hat true false h with (* ~modelflag:true ~ucflag:false ~bnflag:true *)      
      (*      match Satcheck.satcheck_bn true false true h with (* ~modelflag:true ~ucflag:false ~bnflag:true *) *)
      | SatResult.Model pmod -> _pmodel := pmod
      | _ -> raise Exit
    in
    let mkSortedPto ss = (* t->(f:u1;g:u2) becomes [ (n,[(f:u1);(g:u2)]) ] *)
      let vcc = List.fold_left (fun qq s -> match s with S.Pto(t,cc) -> (SHterm.evalUnderPmodel !_pmodel t,cc)::qq | _ -> qq) [] ss in
      List.sort (fun p1 p2 -> compare (fst p1) (fst p2)) vcc
    in
    let mkPairFromDic f dic1 dic2 = (* dic : a list with sorted indexes, like [ (1,"ABC"); (2,"XYS") ] *)
      let rec aux res d1 d2 =
        match d1,d2 with
        | [],_ | _,[] -> List.rev res
        | (k1,c1)::d1',(k2,c2)::d2' ->
           if k1 = k2 then aux ((f c1 c2)::res) d1' d2'
           else if k1 < k2 then aux res d1' d2
           else aux res d1 d2'
      in
      aux [] dic1 dic2
    in
    try
      setPModel ();
      let ccPairs = mkPairFromDic (fun x y -> (x,y)) (mkSortedPto ss1) (mkSortedPto ss2) in
      let ppContents = List.fold_left (fun qq ccPair -> qq @ (mkPairFromDic ( =.= ) (fst ccPair) (snd ccPair))) [] ccPairs in
      ba.pp <- ba.pp @ ppContents;
    with
      Exit -> ()

  let subst sub ans =
    ans.pp <- List.map (P.subst sub) ans.pp;
    ans.ssX <- SS.subst sub ans.ssX;
    ans.ssY <- SS.subst sub ans.ssY;
    ans
    
  (* merge two solutions (P1,X,Y) and (P2,X,Y) to (P1 or P2,X,Y) *)
  let merge_opt ans1 ans2 =
    let ssX1std = List.sort S.compare ans1.ssX in
    let ssX2std = List.sort S.compare ans2.ssX in
    if compareList S.compare ssX1std ssX2std <> 0
    then None
    else
      let ssY1std = List.sort S.compare ans1.ssY in
      let ssY2std = List.sort S.compare ans2.ssY in
      if compareList S.compare ssY1std ssY2std <> 0
      then None
      else
        (* make disjunction of ans1.pp and ans2.pp *)
        let pp = 
          match ans1.pp,ans2.pp with
          | [],_ -> []  (* ans1.pp is true *)
          | _,[] -> []  (* ans2.pp is true *)
          | [p],[q]-> [P.Or ((P.flattenOr [p]) @ (P.flattenOr [q]))]
          | [p],qq -> [P.Or ((P.flattenOr [p]) @ [P.mkAnd qq])]
          | pp,[q] -> [P.Or ([P.mkAnd pp] @ (P.flattenOr [q]))]
          | pp,qq  -> [P.Or [P.mkAnd pp;P.mkAnd qq]]
        in
        let ans = create pp ssX1std ssY1std in
        Some ans

  let mergeL ansL =
    let rec mergeOne res ansL ans =
      match ansL with
      | [] -> ans::res
      | ans1::ansL1 ->
         match merge_opt ans ans1 with
         | None -> mergeOne (ans1::res) ansL1 ans 
         | Some ansMgd -> List.rev_append res (ansMgd::ansL1)
    in
    List.fold_left (fun ansResL ans -> mergeOne [] ansResL ans) [] ansL

  let check pp_ex pure ss ans =
    let ssAX = List.rev_append ans.ssX ss in
    let ppAX = pure :: (List.rev_append pp_ex ans.pp) in
    (* Note: ssAX and ppAX may NOT be Presburger fmls *)
    let dummy = (Strset.empty,[]) in
    let ppAX = snd @@ List_tailrec.map_state P.extract_nonPb dummy ppAX in
    let ssAX = snd @@ SS.extract_nonPb dummy ssAX in
    let gamma = gammaAL ppAX ssAX in
    Ftools.pf_s tagDebug println_debug1 "Checking solution: gammaAL (simplified)";
    Ftools.pf_s tagDebug println_debug2 "ppAX";
    Ftools.pf_s tagDebug P.println (P.And ppAX);
    Ftools.pf_s tagDebug println_debug2 "ssAX";
    Ftools.pf_s tagDebug SS.println ssAX;
    Ftools.pf_s tagDebug P.println (P.syntactical_simpl gamma);
    match isSatPure gamma with
    | Model _ ->
       Ftools.pf_s tagDebug println_debug1 "OK";
       true
    | _ ->
       Ftools.pf_s tagDebug println_debug1 "REJECTED (unsat)";
       false
    
  (* Answer combining *)
  let combine_opt pp_ex pure ss (baL : t list) : t option =
    let (pp,ssX,ssY) = List.fold_left (fun (pp,ssX,ssY) ba -> (ba.pp@pp, ba.ssX@ssX, ba.ssY@ssY)) ([],[],[]) baL in
    let ba = create pp ssX ssY in
    match check pp_ex pure ss ba with
    | true -> Some ba
    | false -> None
    
  let combineL pp_ex pure ss1 baL1 baL2 =
    let baOptL = List_tailrec.map2 (fun ba1 ba2 -> combine_opt pp_ex pure ss1 [ba1;ba2]) baL1 baL2 in
    List.fold_left (fun baL baOpt -> match baOpt with None -> baL | Some ba -> ba::baL) [] baOptL
    
end
;;

module BAoutput = struct
  (* Biabduction output: (baAnswerL,pp)  *)
  (* baAnswerL = [(id,pureL,ss1,ss2)] *)
  (* pp is the giveup case *)  
  type t = BAanswer.t list * P.t list
         
  let subst sub (ba_out : t) =
    let (baL,pp) = ba_out in
    let baL' = List.map (BAanswer.subst sub) baL in
    let pp' = List.map (P.subst sub) pp in
    (baL',pp')
    
  let println (ba_out : t) =
    let (baL,ppGU) = ba_out in
    match baL,ppGU with
    | [],[] -> Format.printf "@[No Output@."
    | _,_ ->
       BAanswer.println_many baL;
       ANSITerminal.(printf [Bold] "- Unsearched\n");
       match ppGU with
       | [] -> Format.printf "@[Empty@."
       | [P.False] -> Format.printf "@[None@."
       | _ -> Format.printf "@[%a@." P.pp (P.mkOr (P.syntactical_simplL ppGU))

  let syntactical_simpl (ba_out: t) =
    let (baL,pp) = ba_out in
    let baL' = List.map BAanswer.syntactical_simpl baL in
    let pp' = List.map P.syntactical_simpl pp in
    (baL',pp')
    
end
;;
