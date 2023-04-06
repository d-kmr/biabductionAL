open Tools
open Slsyntax
open Sltosmt   
open Smttoz3
open Smtsyntax
module SatResult = Smttoz3.SatcheckResult

open BiabdData
open BiabdArr
open BiabdLs
   
                 
(*
メモ：2021.09.28
biabd_core に繰り返し回数 (balimit) を追加
biabdlimit の分だけ繰り返し実行して複数の解を生成 (2個くらいにしておくのが妥当？)
example_tatsuta/eg6 で解が足りなかったため (eg28.bi)
*)                 
                 

(* Pure extraction from QFSH *)
let extractPureSS ss : P.t list =
  let _pp = ref [] in
  let rec mkPlist ss1 =
    match ss1 with
    | [] -> []
    | S.Pto(t,_)::ss2 -> (t,t)::(mkPlist ss2)
    | S.Arr(t,u)::ss2 -> (t,u)::(mkPlist ss2)
    | S.Str(t,u)::ss2 -> (t,u)::(mkPlist ss2)
    | S.Ind(_,_)::ss2 -> (mkPlist ss2)
  in
  let plist = mkPlist ss in
  for i = 0 to L.length plist - 1 do
    for j = i+1 to L.length plist - 1 do
      let (ti,ui) = L.nth plist i in
      let (tj,uj) = L.nth plist j in
      match ti = ui, tj = uj with
      | true,true ->
         _pp := (ti <.> tj) :: !_pp
      | true,false ->
         _pp := (_Out ti tj uj) :: !_pp
      | false,true ->
         _pp := (_Out tj ti ui) :: !_pp
      | _,_ ->
         _pp := (_Disj ti ui tj uj) :: !_pp
    done;
  done;  
  !_pp
;;

let extractPureSH (k : QFSH.t) =
  let (p,ss) = k in
  let pp = extractPureSS ss in
  p::pp
;;

(* CHECK!!!!!!!!!!!! This procedure can be included in biabd_core *)
(* checking solution *)
(* a produced solution should satisfy the following condition *)
(* ss2 <> [] -> forall s in ss1.(cells(s) not sub seg(Y) *)
let checkSolution bq _Y =
  let (pp_ex,p,ss1,ss2) = bq in
  if ss2 = []
  then true
  else
    let segY = SS.mkSegment _Y in
    let mkCondMemOfSegY t = P.And (L.map (fun (u1,u2) -> P.Atom(P.Out,[t;u1;u2])) segY) in
    let expCondMemOfSegY t = mkExp_p (mkCondMemOfSegY t) in
    try
      for i = 0 to L.length ss1 - 1 do
        match L.nth ss1 i with
        | S.Pto(t,_) ->
           let exp = expCondMemOfSegY t in
           begin
             match Smttoz3.checkSatExpBool exp with
             | true -> ()
             | false -> raise Exit
           end
        | S.Arr(t1,t2) | S.Str(t1,t2) ->
           let exp1 = expCondMemOfSegY t1 in
           let exp2 = expCondMemOfSegY t2 in
           let exp = bigOr' [exp1;exp2] in
           begin
             match Smttoz3.checkSatExpBool exp with
             | true -> ()
             | false -> raise Exit
           end
        | S.Ind(_,_) -> failwith "checkSolution"
      done;
      true
    with
      Exit -> false
;;


(* Avoiding zero_div exception *)
let avoid_zero_div_exception pp_ex pure ss1 ss2 =
  let tttDenoms =
    let tttDenomsPP = Tset.mapUnion P.denominators (pure::pp_ex) in
    let tttDenomsSS = Tset.mapUnion S.denominators (L.rev_append ss1 ss2) in
    Tset.union tttDenomsPP tttDenomsSS
  in
  let ppZeroLtDenoms = L.map (fun t -> zero <.< t) (Tset.elements tttDenoms) in
  let pp_ex1 = L.rev_append ppZeroLtDenoms pp_ex in
  (pp_ex1,pure,ss1,ss2)
;;

(* biabductionAL: this may raise "NoSolution" *)
let biabductionAL balimit pp_ex pure ss1 ss2 : BAoutput.t =
  let biabductionA ssArr1 ssArr2 =
    Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] Start BiabductionARRAY";
    let ((baArrL,ppGuArr) as baOut): BAoutput.t = biabductionArray balimit (pp_ex,pure,ssArr1,ssArr2) in
    match baArrL with
    | [] ->
       Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] BiabductionARRAY result: None";
       raise NoSolution
    | _ ->
       Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] BiabductionARRAY result";
       Ftools.pf_s tagDebug BAoutput.println baOut;
       baOut
  in
  let biabductionL ssLs1 ssLs2 =
    Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] Start BiabductionLIST";
    let ((baLsL,ppGuLs) as baOut): BAoutput.t = biabductionList balimit (pp_ex,pure,ssLs1,ssLs2) in
    match baLsL with
    | [] ->
       Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] BiabductionLS result: None";
       raise NoSolution
    | _ ->
       Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] BiabductionLS result";
       Ftools.pf_s tagDebug BAoutput.println baOut;
       baOut
  in
  Ftools.pf_s tagDebug println_debug1 "Biabd.biabductionAL is called";
  (* Splitting Arrays and Lists *)
  Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] Splitting Array-part and List-part";
  let (ssArr1,ssLs1) = SS.splitArrayList ss1 in
  let (ssArr2,ssLs2) = SS.splitArrayList ss2 in
  Ftools.pf_s tagDebug (Format.printf "@[ArrL: %a@." SS.pp) ssArr1;
  Ftools.pf_s tagDebug (Format.printf "@[ArrR: %a@." SS.pp) ssArr2;
  Ftools.pf_s tagDebug (Format.printf "@[Ls L: %a@." SS.pp) ssLs1;  
  Ftools.pf_s tagDebug (Format.printf "@[Ls R: %a@." SS.pp) ssLs2;
  (* Execute biabuduction procedures for Arrays and Lists *)
  let (baArrL,ppGuArr) = biabductionA ssArr1 ssArr2 in
  let (baLsL,ppGuLs) = biabductionL ssLs1 ssLs2 in    
  (* Combining Solutions *)
  Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] Combining solutions";  
  let baL = BAanswer.combineL pp_ex pure ss1 baArrL baLsL in
  let ppGu =
    let pGuArr = P.mkAnd ppGuArr in
    let pGuLs = P.mkAnd ppGuLs in
    match pGuArr, pGuLs with
    | P.False,pGuLs -> [pGuLs]
    | pGuArr,P.False -> [pGuArr]
    | _,_ -> [P.mkOr [pGuArr;pGuLs]]
  in
  let baOutput = (baL,ppGu) in
  Ftools.pf_s tagDebug println_debug1 "[BiabductionAL] Biabduction Result";
  Ftools.pf_s tagDebug BAoutput.println baOutput;
  baOutput
;;

let pp_idtlist fmt idtlist =
  let pp_triple fmt (u,fld,cc) = Format.fprintf fmt "(%a,%s,%a)" T.pp u fld S.pp_cc cc in
  let pp1 fmt (t,opt) = Format.fprintf fmt "(%a,%a)" T.pp t (pp_opt "None" pp_triple) opt in
  Format.fprintf fmt "[%a]" (pp_list "" "," pp1) idtlist
;;

(* Indirect Preprocessing/Postprocessing *)
let indirect_collection ss =
  (* idtlist = [(zInd,None); (wInd,Some u)] *)
  (* (zInd,None) is ?->zInd is missing (open)   *)
  (* (zInd,Some (t,f)) is t->(f:zInd) exists     (closed) *)
  (* This returns (openlist,closedlist) = ([(zInd,None)], [(wInd,Some (u,f))]) *)
  let isNew v idtlist = not (list_mem_assoc_compare T.compare v idtlist) in
  let addnew (t,opt) idtlist = if isNew t idtlist then (t,opt)::idtlist else idtlist in
  let overwrite (t,opt) idtlist = if isNew t idtlist then (t,opt)::idtlist else (t,opt)::(L.remove_assoc t idtlist) in
  let rec aux idtlist = function
    | [] -> idtlist
    | S.Arr(t,u)::ss1 | S.Str(t,u)::ss1 | S.Ind (_,[t;u])::ss1 when T.isIndirectVar t || T.isIndirectVar u ->
       aux (addnew ((if T.isIndirectVar t then t else u),None) idtlist) ss1
    | S.Pto(t,cc)::ss1 when T.isIndirectVar t ->
       (*
       print_endline "***************************hoge";
       Format.printf "@[hogehogehoge: %a@." pp_idtlist idtlist;
       Format.printf "@[fugafugafuga: %a@." pp_idtlist (addnew (t,None) idtlist);
       print_endline "***************************hoge";  
        *)
       aux (addnew (t,None) idtlist) ss1
    | S.Pto(u,cc)::ss1 ->
       let rec ccHandle idtlist = function
         | [] -> idtlist
         | (fld,t)::cc1 when T.isIndirectVar t ->
            ccHandle (overwrite (t,Some (u,fld,cc)) idtlist) cc1
         | _::cc1 -> ccHandle idtlist cc1
       in
       aux (ccHandle idtlist cc) ss1
    | _::ss1 -> aux idtlist ss1
  in
  L.partition (fun (_,head) -> head = None) (aux [] ss) (* (openlist,closedlist) *)
;;

let diffOpenClosed openlist closedlist =
  let rec aux covered missing = function
    | [] -> (covered,missing)
    | (t,_)::openlist1 ->
       begin
         match list_assoc_compare_opt T.compare t closedlist with
         | Some (Some (u,_,cc)) -> aux (S.Pto(u,cc)::covered) missing openlist1
         | _ -> aux covered (t::missing) openlist1
       end
  in
  aux [] [] openlist
;;
let fold_indirect (ss: SS.t) =
  (* x->(f:z@INDIRECT, f1:u1) * z->( *:a) -transform->  x->(f:#IN(a,z@INDIRECT), f1:u1) *)
  let indirectVars = Tset.mapUnion S.indirectVars ss in
  let indirectVarNames = Strset.mapUnion T.getVarName (Tset.elements indirectVars) in
  let isIdtL = function (S.Pto(t,_)) -> not (Strset.disjoint (T.getVarName t) indirectVarNames) | _ -> false in
  let (ssIdtL,ss1) = List_tailrec.splitLst isIdtL ss in
  let mes = "fold_indirect: indirect variable points an unexpected cell" in  
  let idtpairL = L.map (function S.Pto(vIdt,[(_,u)]) -> (T.getVarName vIdt,u) | _ -> failwith mes) ssIdtL in
  let substC (f,t) = if T.isIndirectVar t then (f,T.Fcall("#IN",[L.assoc (T.getVarName t) idtpairL;t])) else (f,t) in
  let substCC_s = function S.Pto(t,cc) -> S.Pto(t,L.map substC cc) | s -> s in
  L.map substCC_s ss1
;;
let indirect_preprocess ss1 ss2 =
  (* (1) Array transform:  Arr(z@INDIRECT,z@INDIRECT) -transform-> z@INDIRECT->( *:arr@PHANTOM) *)
  (* (2) Separate open/closed indirect variables *)
  (* (3) Find missing pto (say x->( *:z@INDIRECT, f:t)) for each open ind.var z@INDIRECT *)
  (* (4) Fold: x->(f:z@INDIRECT, f1:u1) * z@INDIRECT->( *:t) -transform-> x->(f:#IN(t,z@INDIRECT), f1:u1) *)
  let c = ref 0 in
  let replaceArr1 s =
    match s with 
    | S.Arr(t,u) when T.isIndirectVar t ->
       c:=!c+1;
       let arrvar = var (Format.sprintf "arr%d" !c) (Attrs.singleton Attr.PHANTOM) in
       S.Pto(t,[("*",arrvar)])
    | _ -> s
  in
  let ss1 = L.map replaceArr1 ss1 in
  let ss2 = L.map replaceArr1 ss2 in
  let (openlist1,closedlist1) = indirect_collection ss1 in
  let (openlist2,closedlist2) = indirect_collection ss2 in
  let (cov1,miss1) = diffOpenClosed openlist1 closedlist2 in
  let (cov2,miss2) = diffOpenClosed openlist2 closedlist1 in
  (*
  print_endline "***************************hoge";
  Format.printf "@[open1: %a@." pp_idtlist openlist1;
  Format.printf "@[closed1: %a@." pp_idtlist closedlist1;
  Format.printf "@[open2: %a@." pp_idtlist openlist2;
  Format.printf "@[closed2: %a@." pp_idtlist closedlist2;
  Format.printf "@[cov1: %a@." SS.pp cov1;
  Format.printf "@[miss1: %a@." (pp_list "" " " T.pp) miss1;
  Format.printf "@[cov2 %a@." SS.pp cov2;
  Format.printf "@[miss2: %a@." (pp_list "" " " T.pp) miss2;
  print_endline "***************************hoge";  
   *)
  (*
  if miss1@miss2 <> []
  then (Format.printf "@[Error (experimental): Missing Indirects!: %a@." (pp_list "" " " T.pp) (miss1@miss2); exit 0)
  else ();
   *)
  if cov1 <> [] then (Format.printf "@[Indirect extension-A: [%a] * %a@." SS.pp cov1 SS.pp ss1) else ();
  if cov2 <> [] then (Format.printf "@[Indirect extension-B: [%a] * %a@." SS.pp cov2 SS.pp ss2) else ();
  let ss1 = fold_indirect (cov1@ss1) in
  let ss2 = fold_indirect (cov2@ss2) in
  (ss1,ss2,cov1,cov2)
;;  
let indirect_postprocess cov1 cov2 (baOut: BAoutput.t) =
  (* (1) Unfold-1: x->(f:#IN(t,z@INDIRECT), f1:u1) -transform-> x->(f:z@INDIRECT, f1:u1) * z@INDIRECT->( *:t) *)
  (*     Unfold-2: x->(f:#IN(a@PHANTOM,z@INDIRECT), f1:u1) -transform-> x->(f:z@INDIRECT, f1:u1) * Arr(z@INDIRECT,z@INDIRECT) *)
  (* (3) Add cov1 and cov2 to X and Y, respectively *)
  (* (4) Delete phantom variables from pure part: arr@PHANTOM = t --> delete *)
  (* t->(f:in(u,x<INDIRECT>),f1:t1) => t->(f:x<INDIRECT>,f1:t1) * x->( *:u) *)
  let unfold_indirect_spat_rev ss =
    let rec unfoldCC ccHead ssRes = function
      | [] -> (L.rev ccHead, L.rev ssRes)
      | (f,T.Fcall("#IN",uPTM::zIDT::_))::cc1 when T.isPhantomVar uPTM -> unfoldCC ((f,zIDT)::ccHead) (S.Arr(zIDT,zIDT)::ssRes) cc1
      | (f,T.Fcall("#IN",u::zIDT::_))::cc1 -> unfoldCC ((f,zIDT)::ccHead) (S.Pto(zIDT,[("*",u)])::ssRes) cc1
      | c::cc1 -> unfoldCC (c::ccHead) ssRes cc1
    in
    L.fold_left (fun ssUF -> function
        | S.Pto(t,cc) -> let (ccHead,ssRes) = unfoldCC [] [] cc in ssRes@[S.Pto(t,ccHead)]@ssUF
        | s -> s::ssUF)
      [] ss
  in
  let unfold_indirect_ans ans =
    ans.BAanswer.pp <- L.map (fun p -> P.extinguish_phantoms (P.unfold_indirect p)) ans.BAanswer.pp;
    ans.BAanswer.ssX <- L.rev_append (unfold_indirect_spat_rev ans.BAanswer.ssX) cov1;
    ans.BAanswer.ssY <- L.rev_append (unfold_indirect_spat_rev ans.BAanswer.ssY) cov2;
    ans
  in
  let (baL,pp) = baOut in
  let pp' = L.map (fun p -> P.extinguish_phantoms (P.unfold_indirect p)) pp in  
  let baL' = List.map unfold_indirect_ans baL in
  (baL',pp')
;;

(* biabduction_core *)
let biabduction_core balimit pp_ex pure ss1 ss2 : BAoutput.t =
  Ftools.pf_s tagDebug println_debug1 "Biabd.biabduction_core is called";  
  let p1 = P.syntactical_simpl (P.And (pure::pp_ex)) in
  (* Indirect preprocessing *)
  Ftools.pf_s tagDebug println_debug1 "[Biabduction_core] Preprocessing Indirects";
  (*
  print_endline "***************************hoge";
  Format.printf "@[ss1: %a@." SS.pp ss1;
  Format.printf "@[ss2: %a@." SS.pp ss2;
  print_endline "***************************hoge";  
   *)
  let (ss1,ss2,cov1,cov2) = indirect_preprocess ss1 ss2 in
  Ftools.pf_s tagDebug (fun _ -> Format.printf "@[Indirect preprocessing result@.") ();
  Ftools.pf_s tagDebug (Format.printf "@[P: %a@." P.pp) p1;
  Ftools.pf_s tagDebug (Format.printf "@[A: %a@." SS.pp) ss1;
  Ftools.pf_s tagDebug (Format.printf "@[B: %a@." SS.pp) ss2;
  Ftools.pf_s tagDebug print_newline ();
  (* Avoiding Zero-dividing *)
  Ftools.pf_s tagDebug println_debug1 "[Biabduction_core] Avoid Zero-dividing";  
  let (pp_ex,pure,ss1,ss2) = avoid_zero_div_exception pp_ex pure ss1 ss2 in
  Ftools.pf_s tagDebug (Format.printf "@[P: %a@." P.pp) p1;
  Ftools.pf_s tagDebug (Format.printf "@[A: %a@." SS.pp) ss1;
  Ftools.pf_s tagDebug (Format.printf "@[B: %a@." SS.pp) ss2;
  Ftools.pf_s tagDebug print_newline ();
  (* Separating Non-Presburger terms *)
  let vvv_eqlist = (Strset.empty,[]) in
  let pp_t_v fmt (t,v) = Format.fprintf fmt "(%a,%s)" T.pp t v in
  let (vvv_eqlist,pp_ex') = List_tailrec.map_state P.extract_nonPb vvv_eqlist pp_ex in
  let (vvv_eqlist,pure') = P.extract_nonPb vvv_eqlist pure in
  let (vvv_eqlist,ss1) = SS.extract_nonPb vvv_eqlist ss1 in
  let (vvv_eqlist,ss2) = SS.extract_nonPb vvv_eqlist ss2 in
  Ftools.pf_s tagDebug (ANSITerminal.printf fontDebug1) "[Biabduction_core] Separation of Non-Presburger terms\n";
  Ftools.pf_s tagDebug (Format.printf "@[EqList: %a@." (pp_list "None" "," pp_t_v)) (snd vvv_eqlist);
  Ftools.pf_s tagDebug (Format.printf "@[P1: %a@." P.pp) (P.And pp_ex');
  Ftools.pf_s tagDebug (Format.printf "@[P2: %a@." P.pp) pure';
  Ftools.pf_s tagDebug (Format.printf "@[A: %a@." SS.pp) ss1;
  Ftools.pf_s tagDebug (Format.printf "@[B: %a@." SS.pp) ss2;
  (* biabductionAL *)
  let baOutputPb = biabductionAL balimit pp_ex' pure' ss1 ss2 in (* this may raise NoSolution *)
  (* Restoring Non-Presburger terms *)
  Ftools.pf_s tagDebug println_debug1 "[Biabduction_core] Restoring Non-Presburger terms";
  let sub = L.map (fun (nonPb,v) -> (v,nonPb)) (snd vvv_eqlist) in
  let baOutputNonPb = BAoutput.subst sub baOutputPb in
  Ftools.pf_s tagDebug BAoutput.println baOutputNonPb;
  (* Indirect postprocessing *)
  Ftools.pf_s tagDebug (ANSITerminal.printf fontDebug1) "[Biabduction_core] Postprocessing Indirects\n";
  let baOutput = indirect_postprocess cov1 cov2 baOutputNonPb in
  Ftools.pf_s tagDebug BAoutput.println baOutput;
  Ftools.pf_s tagDebug print_newline ();
  let baOutput' = BAoutput.syntactical_simpl baOutput in
  match baOutput' with
  | ([],_) -> raise NoSolution
  | _ -> baOutput'
;;

let biabduction_core_switch balimit pp_ex pure ss1 ss2 : BAoutput.t =
  (* to support t->(next:u) |- Arr(t,t) *)
  (* 0. Check type of biabduction query (type1 if it includes the next field, type2 otherwise) *)
  (* 1. Execute biabuction_core -> Finish if some solution is returned or type2, Goto 2 otherwise (No solution & type1) *)
  (* 2. Replace all t->(next:u) in ss1 by Arr(t,t), and then execute biabuction_core *)
  let isType1 = ref false in
  let repl s = match S.getListPtoHead s with [] -> s | t::_ -> isType1 := true; S.Arr(t,t) in
  let ss1' = L.map repl ss1 in
  try
    biabduction_core balimit pp_ex pure ss1 ss2
  with
  | NoSolution when !isType1 = true -> (* No solution + type1 *)
     Ftools.pf_s tagDebug println_debug1 "[Biabduction_switch] NoSolution --> switch to approx mode";
     biabduction_core balimit pp_ex pure ss1' ss2
;;  

let biabduction balimit pp_ex pure ss1 ss2 : BAoutput.t =
  Ftools.pf_s tagDebug println_debug1 "Biabd.biabduction is called";  
  (* simplify the input *)
  let pp_ex' = L.map P.syntactical_simpl pp_ex in
  let pure' = P.syntactical_simpl pure in
  let ss1' = SS.syntactical_simpl ss1 in
  let ss2' = SS.syntactical_simpl ss2 in
  Ftools.pf_s tagDebug (ANSITerminal.printf fontDebug1) "[Biabduction] Simplified Input\n";
  Ftools.pf_s tagDebug (Format.printf "@[P: %a@." P.pp) (P.And (pp_ex'@[pure']));
  Ftools.pf_s tagDebug (Format.printf "@[A: %a@." SS.pp) ss1';
  Ftools.pf_s tagDebug (Format.printf "@[B: %a@." SS.pp) ss2';
  Ftools.pf_s tagDebug print_newline ();
  try
    match ss1',ss2' with
    | [],_ -> (* special case: ss1=Emp *)
       Ftools.pf_s tagDebug println_debug1 "[Biabduction] Trivial case: (pure,Emp,ss2)";
       let ba = BAanswer.create [] ss2' [] in
       if BAanswer.check pp_ex' pure' ss1' ba
       then ([ba],[])
       else raise NoSolution
    | _,[] ->  (* special case: ss2=Emp *)
       Ftools.pf_s tagDebug println_debug1 "[Biabduction] Trivial case: (pure,ss1,Emp)";
       let ba = BAanswer.create [] [] ss1' in
       if BAanswer.check pp_ex' pure' ss1' ba
       then ([ba],[])
       else raise NoSolution
    | _,_ -> (* normal case *)
       Ftools.pf_s tagDebug println_debug1 "[Biabduction] Entering Biabduction_core";
       biabduction_core_switch balimit pp_ex' pure' ss1' ss2' (* this may raise NoSolution *)
  with
  | NoSolution ->
     Ftools.pf_s tagDebug println_debug1 "[Biabduction] NO ANSWER";
     ([],[])
;;
