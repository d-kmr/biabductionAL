open Tools
open Slsyntax
open Sltosmt   
open Smttoz3
open Smtsyntax
module SatResult = Smttoz3.SatcheckResult

open BiabdData

(*-----------------------
biabduction list

Main function: biabductionL
INPUT: (pureL,pure,ss1,ss2): BAquery
OUTPUT: (solutionList,pureL): BAoutput.t
-----------------------*)

(* approximation under a model *)
let approxSpat pmodel (ss : SS.t) =
  let rec aux res ss = 
    match ss with
    | [] -> List.rev res
    | ((S.Pto _) as s)::ss1 -> aux (s::res) ss1
    | (Ind (ls,[t1;t2]))::ss1 when ls = "Ls" ->
       let n1 = SHterm.evalUnderPmodel pmodel t1 in
       let n2 = SHterm.evalUnderPmodel pmodel t2 in
       if n1 = n2
       then
         aux res ss1
       else
         let s' = S.Pto(t1,[("next",t2)]) in
         aux (s'::res) ss1
    | _ ->
       Ftools.pf_s tagDebug2 println_debug2 "Debug Info ********************";
       Ftools.pf_s tagDebug2 (Format.printf "@model: %a@." SatResult.pp_model) pmodel;
       Ftools.pf_s tagDebug2 println_debug2 "*******";
       Format.printf "%a\n" SS.pp ss;
       Ftools.pf_s tagDebug2 println_debug2 "Debug Info ********************";
       Ftools.raiseStError "BiabdLs.approxSpatExp: unexpected input";

  in
  aux [] ss
;;

(* beta_L in the PPL2022 paper *)
let mkBeta pp ss1 ss2 : P.t list =
  let (ssPto1,ssArr1,ssStr1,ssInd1) = SS.split ss1 in
  let (ssPto2,_,ssStr2,ssInd2) = SS.split ss2 in
  let ppGamma1 = P.flattenAnd [gammaAL pp ss1] in
  let ppGamma2 = P.flattenAnd [gammaAL [] ss2] in
  (* make equalities for pto contents *)
  let tttPto1Cont = Tset.mapUnion S.getPtoContentTms_s ssPto1 in
  let tttPto2Cont = Tset.mapUnion S.getPtoContentTms_s ssPto2 in
  let tttPtoCont = Tset.union tttPto1Cont tttPto2Cont in
  let ppTriv = Tset.fold (fun t pp -> (t=.=t)::pp) tttPtoCont [] in
  (* condPto: t1->u1 |- t2->u2 satisfies "t1 = t2 implies u1 = u2" *)
  let mkCondPtoOne pto1 pto2 =
    let t1 = List.hd (S.addrs pto1) in
    let t2 = List.hd (S.addrs pto2) in
    let cc1 = S.getPtoContent pto1 in
    let cc2 = S.getPtoContent pto2 in
    let pairs = S.mkContentPairs cc1 cc2 in 
    let cond2 = P.mkAnd (List.map (fun (u1,u2) -> (u1 =.= u2)) pairs) in
    (t1 =.= t2) =.> cond2
  in
  let condPto = List_tailrec.map2 mkCondPtoOne ssPto1 ssPto2 in
  let mkCondLsOne ls =
    match S.getLsEndpoints ls with
    | t1::t2::_ -> [(t1 =.= zero) =.> (t2 =.= zero); zero <.= t1; zero <.= t2]
    | _ -> []
  in
  let condLs = List.fold_left (fun pp s -> List.rev_append (mkCondLsOne s) pp) [] (ssInd1@ssInd2) in
  let condHat = mkHatCond pp ss1 ss2 in
  List_tailrec.concat [pp; ppTriv; ppGamma1; ppGamma2; condHat; condPto; condLs]
;;                          

(* Check s |= tt0 disj tt1 *)
let checkDisj pmodel tt0 tt1 =
  let evalP t = Intset.singleton (SHterm.evalUnderPmodel pmodel t) in
  Intset.disjoint (Intset.mapUnion evalP tt0) (Intset.mapUnion evalP tt1)
;;

(* biabdL in PPL2022 paper *)
let biabdL_ppl pmodel ttU ppA ssA ss =
  Ftools.pf_s tagDebug println_debug1 "BiabdLs.biabdL is called";
  let evalP p = P.evalUnderPmodel pmodel p in
  let getNext cc = try List.assoc "next" cc with _ -> Ftools.raiseStError "biabdL: no NEXT field" in
  let rec biabdL_rec ttU ssA ssY ssBtmp ssB =
    Ftools.pf_s tagDebug2 println_debug2 "BiabdLs.biabdL.biabdL_rec is called";
    Ftools.pf_s tagDebug2 (Format.printf "@[model : %a@." SatResult.pp_model) pmodel;
    Ftools.pf_s tagDebug2 (Format.printf "@[ttU   : %a@." (pp_list "None" "," T.pp)) ttU;
    Ftools.pf_s tagDebug2 (Format.printf "@[ppA   : %a@." (pp_list "True" " & " P.pp)) ppA;
    Ftools.pf_s tagDebug2 (Format.printf "@[ssA   : %a@." SS.pp) ssA;
    Ftools.pf_s tagDebug2 (Format.printf "@[ssY   : %a@." SS.pp) ssY;
    Ftools.pf_s tagDebug2 (Format.printf "@[ssBtmp: %a@." SS.pp) ssBtmp;
    Ftools.pf_s tagDebug2 (Format.printf "@[ssB   : %a@." SS.pp) ssB;    
    match ssA,ssB with
    | [],_ ->
       let ssX = List.rev_append ssBtmp ssB in
       if (checkDisj pmodel ttU (SS.addrs ssX)) && (evalP (gammaAL ppA ssX))
       then
         (Ftools.pf_s tagDebug2 println_debug2 "(Emp,_)-case: Consistent solution -> Finish";
         [(ttU,ssX,ssY)])
       else
         (Ftools.pf_s tagDebug2 println_debug2 "(Emp,_)-case: Inconsistent solution -> Fail";
          [])
    | _,[] when ssBtmp = [] ->
       if evalP (gammaAL ppA ssA)
       then
         (Ftools.pf_s tagDebug2 println_debug2 "(_,Emp)-Case: Consistent solution --> Finish";
         [(ttU,[],ssA)])
       else
         (Ftools.pf_s tagDebug2 println_debug2 "(_,Emp)-Case: Inconsistent solution --> Fail";
          [])
    | (S.Pto(t,_) as s)::ssA1,[] ->
       Ftools.pf_s tagDebug2 println_debug2 "(Pto,Emp)-case: all mismatch --> Add Pto to ssY";
       biabdL_rec (t::ttU) ssA1 (s::ssY) [] (List.rev ssBtmp)
    | (S.Pto(t,_))::ssA1,(S.Pto(t',_) as s')::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Pto,Pto)-case: ";
       begin
         match evalP (t =.= t') with
         | true ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match";
            biabdL_rec (t::ttU) ssA1 ssY [] (List.rev_append ssBtmp ssB1)
         | false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssA ssY (s'::ssBtmp) ssB1
       end
    | S.Pto(t,cc)::ssA1,(S.Ind("Ls",[a';b']) as s')::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Pto,Ls)-case: ";
       let u = getNext cc in
       begin
         match evalP (t =.= a'), evalP (a' =.= b'), evalP (b' =.= u) with
         | false,_,_ ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssA ssY (s'::ssBtmp) ssB1
         | true,true,_ ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|=0 --> Remove LsR";
            biabdL_rec ttU ssA ssY ssBtmp ssB1
         | true,false,true ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|=1 --> Remove Pto+LsR";
            biabdL_rec (t::ttU) ssA1 ssY [] (List.rev_append ssBtmp ssB1)
         | true,false,false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|>1 --> Remove Pto & take tail of LsR)";
            biabdL_rec (t::ttU) ssA1 ssY [] (S.Ind("Ls",[u;b'])::(List.rev_append ssBtmp ssB1))
       end
    | S.Ind("Ls",[a;b])::ssA1,_ when evalP (a =.= b) ->
       Ftools.pf_s tagDebug2 println_debug2 "(Ls,Emp)-case: |LsL|=0 --> Remove LsL";
       biabdL_rec ttU ssA1 ssY [] (List.rev_append ssBtmp ssB)
    | (S.Ind("Ls",[a;b]) as s)::ssA1,[] ->
       Ftools.pf_s tagDebug2 println_debug2 "(Ls,Emp)-case: |LsL|>0 --> Add LsL to ssY";
       biabdL_rec (a::ttU) ssA1 (s::ssY) [] (List.rev ssBtmp)
    | S.Ind("Ls",[a;b])::ssA1,(S.Pto(t',cc') as s')::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Ls,Pto)-case: ";
       begin
         match evalP (a =.= t') with
         | true -> (Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsL|>0 --> Fail (non-empty LsL cannot match with PtoR)";
                    [])
         | false -> (Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
                     biabdL_rec ttU ssA ssY (s'::ssBtmp) ssB1)
       end
    | S.Ind("Ls",[a;b])::ssA1,(S.Ind("Ls",[a';b']) as s')::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Ls,Ls)-case: ";
       begin
         match evalP (a =.= a'), evalP (a' =.= b') with
         | false,_ ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssA ssY (s'::ssBtmp) ssB1
         | true,true ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|=0 --> Remove LsR";
            biabdL_rec ttU ssA ssY ssBtmp ssB1
         | true,false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|>0 + ";
            begin
              match evalP (P.mkAnd (mkBeta ppA ssA1 (S.Ind("Ls",[b;b'])::ssB1))), evalP (b =.= b') with
              | false,_ ->
                 Ftools.pf_s tagDebug2 println_debug2 "Inconsistent --> Fail";
                 []
              | true,true ->
                 Ftools.pf_s tagDebug2 println_debug2 "Consisitent + exact-match --> Remove LsL+LsR";
                 biabdL_rec (a::ttU) ssA1 ssY [] (List.rev_append ssBtmp ssB1)
              | true,false ->
                 Ftools.pf_s tagDebug2 println_debug2 "Consistent + not exact-match --> Cut LsL (by LsL<LsR)";
                 biabdL_rec (a::ttU) ssA1 ssY [] (S.Ind("Ls",[b;b'])::(List.rev_append ssBtmp ssB1)) 
            end
           
       end                                             
    | _,_ -> Ftools.raiseStError "BiabdLs.biabdL: unexpected case"           
  in
  let aa = biabdL_rec ttU ssA [] [] ss in
  Ftools.pf_s "BIABD" print_endline "BiabdLs.biabdL is finished";
  aa
;;

(* biabdL of compsoft version *)
let biabdL_compsoft pmodel ttU ppA ssA ss =
  Ftools.pf_s tagDebug println_debug1 "BiabdLs.biabdL is called";
  let tagDebug2 = tagDebug in (* delete later *)
  let println_debug2 = print_endline in
  let print_debug2 = print_endline in
  let evalP p = P.evalUnderPmodel pmodel p in
  let evalT t = T.evalUnderPmodel pmodel t in
  let checkMem t tt = List.mem (evalT t) (List.map evalT tt) in
  let getNext cc = try List.assoc "next" cc with _ -> Ftools.raiseStError "biabdL: no NEXT field" in
  Ftools.pf_s tagDebug2 println_debug2 "-----------------------------------";    
  Ftools.pf_s tagDebug2 println_debug2 "BiabdLs.biabdL.biabdL_compsoft";
  Ftools.pf_s tagDebug2 (Format.printf "@[model : %a@." SatResult.pp_model) pmodel;
  Ftools.pf_s tagDebug2 (Format.printf "@[ppA   : %a@." (pp_list "True" " & " P.pp)) ppA;
  let rec biabdL_rec ttU ssX ssA ssAtmp ssB =
    Ftools.pf_s tagDebug2 (fun _ -> 
        Format.printf "@[({%a} ;; %a ;; [%a] * %a ;; %a)@."
          (pp_list "" "," T.pp) ttU
          SS.pp ssX
          SS.pp ssAtmp
          SS.pp ssA          
          SS.pp ssB) ();
    match ssA,ssB with
    (* (Emp) *)
    | _,[] ->
       Ftools.pf_s tagDebug2 print_debug2 "(Emp)-case";
       let ssY = List.rev_append ssAtmp ssA in
       [(ttU,ssX,ssY)]
    (* (Ls0L) *)
    | S.Ind("Ls",[a;b])::ssA1,_ when evalP (a =.= b) ->
       Ftools.pf_s tagDebug2 print_debug2 "(Ls0L)-case";
       biabdL_rec ttU ssX ssA1 ssAtmp ssB
    (* Pto-Pto *)
    | (S.Pto(t,_) as s)::ssA1,S.Pto(t',_)::ssB1 ->
       begin
         match evalP (t =.= t') with
         | true ->
            Ftools.pf_s tagDebug2 print_debug2 "(PtoPto)-case: ";
            biabdL_rec (t::ttU) ssX (List.rev_append ssAtmp ssA1) [] ssB1
         | false ->
            biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
       end
    (* Ls-Pto *)
    | (S.Ind("Ls",[a;_]) as s)::ssA1,S.Pto(t',_)::_ ->
       Ftools.pf_s tagDebug2 print_debug2 "(LsPto)-case: ";
       begin
         match evalP (a =.= t') with
         | true ->
            Ftools.pf_s tagDebug2 println_debug2 "Ls-Pto match --> Fail";
            []
         | false ->
            biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
       end
    (* (NonePto) *)
    | [],(S.Pto(t',_) as s')::ssB1 ->
       Ftools.pf_s tagDebug2 println_debug2 "(NonePto)-case";
       begin
         match checkMem t' ttU with
         | true ->
            Ftools.pf_s tagDebug2 println_debug2 "NonePto (t in U) --> Fail";
            []
         | false ->
            biabdL_rec (t'::ttU) (s'::ssX) (List.rev ssAtmp) [] ssB1            
       end
    (* (Ls0R) *)      
    | _,S.Ind("Ls",[a';b'])::ssB1 when evalP (a' =.= b') ->
       Ftools.pf_s tagDebug2 println_debug2 "(Ls0R)-case --> Remove LsR";
       biabdL_rec ttU ssX (List.rev_append ssAtmp ssA) [] ssB1
    (* Pto-Ls *)
    | (S.Pto(t,cc) as s)::ssA1,S.Ind("Ls",[a';b'])::ssB1 ->
       let u = getNext cc in
       begin
         match evalP (t =.= a') with
         | false -> biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
         | true ->
            begin
              match evalP (P.mkAnd (mkBeta ppA (List.rev_append ssAtmp ssA1) (S.Ind("Ls",[u;b'])::ssB1))) with
              | true -> 
                 Ftools.pf_s tagDebug2 print_debug2 "(PtoLs)-case";
                 biabdL_rec (t::ttU) ssX (List.rev_append ssAtmp ssA1) [] (S.Ind("Ls",[u;b'])::ssB1)
              | false ->
                 Ftools.pf_s tagDebug2 println_debug2 "(PtoLs')-case: beta-check false --> Fail";
                 []
            end
       end
    (* Ls-Ls *)
    | (S.Ind("Ls",[a;b]) as s)::ssA1,S.Ind("Ls",[a';b'])::ssB1 ->
       begin
         match evalP (a =.= a') with
         | false -> biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
         | true ->          
            begin
              match evalP (P.mkAnd (mkBeta ppA (List.rev_append ssAtmp ssA1) (S.Ind("Ls",[b;b'])::ssB1))) with
              | true ->
                 Ftools.pf_s tagDebug2 println_debug2 "(LsLs)-case --> Cut LsL (by LsL<LsR)";
                 biabdL_rec (a::ttU) ssX (List.rev_append ssAtmp ssA1) [] (S.Ind("Ls",[b;b'])::ssB1)
              | false ->
                 Ftools.pf_s tagDebug2 println_debug2 "(LsLs')-case: beta-check false --> Fail";
                 []
            end
       end
    (* (NoneLs) *)
    | [],(S.Ind("Ls",[a';_]) as s')::ssB1 ->
       begin
         match checkMem a' ttU with
         | true ->
            Ftools.pf_s tagDebug2 println_debug2 "(NoneLs)-case: a' in U --> Fail";
            []
         | false ->
            Ftools.pf_s tagDebug2 println_debug2 "(NoneLs)-case";
            biabdL_rec (a'::ttU) (s'::ssX) (List.rev ssAtmp) [] ssB1            
       end
    | _,_ -> Ftools.raiseStError "BiabdLs.biabdL: unexpected case"
  in
  let aa = biabdL_rec ttU [] ssA [] ss in
  Ftools.pf_s "BIABD" print_endline "BiabdLs.biabdL is finished";
  aa
;;

(* biabdL of modified version *)
let biabd_mod pmodel ttU ppA ssA ss =
  Ftools.pf_s tagDebug println_debug1 "BiabdLs.biabdL is called";
  let evalP p = P.evalUnderPmodel pmodel p in
  let getNext cc = try List.assoc "next" cc with _ -> Ftools.raiseStError "biabdL: no NEXT field" in
  let rec biabdL_rec ttU ssX ssA ssAtmp ssB =
    Ftools.pf_s tagDebug2 println_debug2 "-----------------------------------";
    Ftools.pf_s tagDebug2 println_debug2 "BiabdLs.biabdL.biabdL_rec is called";
    Ftools.pf_s tagDebug2 (Format.printf "@[model : %a@." SatResult.pp_model) pmodel;
    Ftools.pf_s tagDebug2 (Format.printf "@[model : %a@." SatResult.pp_model) pmodel;
    Ftools.pf_s tagDebug2 (Format.printf "@[ttU   : %a@." (pp_list "None" "," T.pp)) ttU;
    Ftools.pf_s tagDebug2 (Format.printf "@[ppA   : %a@." (pp_list "True" " & " P.pp)) ppA;
    Ftools.pf_s tagDebug2 (Format.printf "@[ssX   : %a@." SS.pp) ssX;        
    Ftools.pf_s tagDebug2 (Format.printf "@[ssA   : %a@." SS.pp) ssA;
    Ftools.pf_s tagDebug2 (Format.printf "@[ssAtmp: %a@." SS.pp) ssAtmp;    
    Ftools.pf_s tagDebug2 (Format.printf "@[ssB   : %a@." SS.pp) ssB;    
    match ssA,ssB with
    | _,[] ->
       let ssY = List.rev_append ssAtmp ssA in
       if (checkDisj pmodel ttU (SS.addrs ssX)) && (evalP (gammaAL ppA ssX))
       then
         (Ftools.pf_s tagDebug2 println_debug2 "(_,Emp)-case: Consistent solution -> Finish";
         [(ttU,ssX,ssY)])
       else
         (Ftools.pf_s tagDebug2 println_debug2 "(_,Emp)-case: Inconsistent solution -> Fail";
          [])
    | [],_ when ssAtmp = [] ->
       let ssX = List.rev_append ssX ssB in
       if (checkDisj pmodel ttU (SS.addrs ssX)) && (evalP (gammaAL ppA ssX))
       then
         (Ftools.pf_s tagDebug2 println_debug2 "(Emp,_)-case: Consistent solution -> Finish";
         [(ttU,ssX,[])])
       else
         (Ftools.pf_s tagDebug2 println_debug2 "(Emp,_)-case: Inconsistent solution -> Fail";
          [])
    (* RightHead is Pto *)       
    | [],(S.Pto(t',_) as s')::ssB1 ->
       Ftools.pf_s tagDebug2 println_debug2 "(Emp,Pto)-case: all mismatch --> Add Pto to ssX";
       biabdL_rec (t'::ttU) (s'::ssX) (List.rev ssAtmp) [] ssB1
    | (S.Pto(t,_) as s)::ssA1,S.Pto(t',_)::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Pto,Pto)-case: ";
       begin
         match evalP (t =.= t') with
         | true ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match";
            biabdL_rec (t::ttU) ssX (List.rev_append ssAtmp ssA1) [] ssB1
         | false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
       end
    | (S.Ind("Ls",[a;b]) as s)::ssA1,S.Pto(t',cc')::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Ls,Pto)-case: ";
       begin
         match evalP (a =.= b), evalP (a =.= t') with
         | true,_ ->
            Ftools.pf_s tagDebug2 println_debug2 "|LsL|=0 --> Remove LsL";
            biabdL_rec ttU ssX ssA1 ssAtmp ssB
         | _,true ->
            Ftools.pf_s tagDebug2 println_debug2 "|LsL|>0 + head-match --> Fail";
            []
         | _,false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
       end
    (* RightHead is Ls *)
    | _,S.Ind("Ls",[a';b'])::ssB1 when evalP (a' =.= b') ->
       Ftools.pf_s tagDebug2 println_debug2 "(_,Ls)-case: |LsR|=0 --> Remove LsR";
       biabdL_rec ttU ssX (List.rev_append ssAtmp ssA) [] ssB1
    | [],(S.Ind("Ls",[a';b']) as s')::ssB1 ->
       Ftools.pf_s tagDebug2 println_debug2 "(Emp,Ls)-case: |LsR|>0 --> Add LsR to ssX";
       biabdL_rec (a'::ttU) (s'::ssX) (List.rev ssAtmp) [] ssB1
    | (S.Pto(t,cc) as s)::ssA1,S.Ind("Ls",[a';b'])::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Pto,Ls)-case: ";
       let u = getNext cc in
       begin
         match evalP (t =.= a'), evalP (b' =.= u) with
         | true,true ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|=1 --> Remove Pto+LsR";
            biabdL_rec (t::ttU) ssX (List.rev_append ssAtmp ssA1) [] ssB1
         | true,false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-match + |LsR|>1 --> Remove Pto & take tail of LsR)";
            biabdL_rec (t::ttU) ssX (List.rev_append ssAtmp ssA1) [] (S.Ind("Ls",[u;b'])::ssB1)
         | false,_ ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
       end
    | (S.Ind("Ls",[a;b]) as s)::ssA1,S.Ind("Ls",[a';b'])::ssB1 ->
       Ftools.pf_s tagDebug2 print_debug2 "(Ls,Ls)-case: ";
       begin
         match evalP (a =.= b),evalP (a =.= a') with
         | true,_ ->
            Ftools.pf_s tagDebug2 println_debug2 "|LsL|=0 --> Remove LsL";
            biabdL_rec ttU ssX ssA1 ssAtmp ssB
         | false,true ->
            Ftools.pf_s tagDebug2 println_debug2 "|LsR|>0 + head-match + ";
            begin
              match evalP (P.mkAnd (mkBeta ppA ssA1 (S.Ind("Ls",[b;b'])::ssB1))), evalP (b =.= b') with
              | false,_ ->
                 Ftools.pf_s tagDebug2 println_debug2 "Inconsistent --> Fail";
                 []
              | true,true ->
                 Ftools.pf_s tagDebug2 println_debug2 "Consisitent + exact-match --> Remove LsL+LsR";
                 biabdL_rec (a::ttU) ssX (List.rev_append ssAtmp ssA1) [] ssB1
              | true,false ->
                 Ftools.pf_s tagDebug2 println_debug2 "Consistent + not exact-match --> Cut LsL (by LsL<LsR)";
                 biabdL_rec (a::ttU) ssX (List.rev_append ssAtmp ssA1) [] (S.Ind("Ls",[b;b'])::ssB1)
            end
         | false,false ->
            Ftools.pf_s tagDebug2 println_debug2 "head-mismatch";
            biabdL_rec ttU ssX ssA1 (s::ssAtmp) ssB
       end                                             
    | _,_ -> Ftools.raiseStError "BiabdLs.biabdL: unexpected case"           
  in
  let aa = biabdL_rec ttU [] ssA [] ss in
  Ftools.pf_s "BIABD" print_endline "BiabdLs.biabdL is finished";
  aa
;;

let biabdL = biabdL_compsoft
;;

let mkSolutionSeed pmodel ss1 ss2 =
  let (ssPto1,_,_,ssInd1) = SS.split ss1 in
  let (ssPto2,_,_,ssInd2) = SS.split ss2 in  
  let tttPto1Addr = Tset.mapUnion S.addrs_ls ssPto1 in
  let tttPto2Addr = Tset.mapUnion S.addrs_ls ssPto2 in
  let tttPtoAddr = Tset.union tttPto1Addr tttPto2Addr in
  let tttLs1Ep = Tset.mapUnion S.getLsEndpoints_s ssInd1 in
  let tttLs2Ep = Tset.mapUnion S.getLsEndpoints_s ssInd2 in
  let tttLsEp = Tset.union tttLs1Ep tttLs2Ep in
  let ttt = Tset.union tttPtoAddr tttLsEp in
  let tvL = List.map (fun t -> (t, SHterm.evalUnderPmodel pmodel t)) (Tset.elements ttt) in
  applyDiff (fun (t1,v1) (t2,v2) -> if v1 = v2 then (t1 =.= t2) else (t1 <.> t2)) tvL
;;  

let rec lsZero pp res ss = (* special handling for Ls(0,u) *)
  match ss with
  | [] -> (pp,res)
  | S.Ind("Ls",[t;u]) :: ss1 when t = zero && u = zero -> lsZero pp res ss
  | S.Ind("Ls",[t;u]) :: ss1 when t = zero -> lsZero ((u =.= zero)::pp) res ss1
  | s::ss1 -> lsZero pp (s::res) ss1
;;

(* This works correctly iff pmodel satisfies beta(pure&ss1,ss2) *)
let biabdListOne pmodel (bq : BAquery.t) : BAanswer.t list =
  Ftools.pf_s tagDebug println_debug1 "BiabdLs.biabdListOne is called";        
  let header = "[BiabductionListOne] " in
  Ftools.pf_s tagDebug println_debug1 (header ^ "Start");
  Ftools.pf_s tagDebug println_debug1 (header ^ "Biabduction query & pmodel:");
  Ftools.pf_s tagDebug BAquery.println bq;
  Ftools.pf_s tagDebug2 (Format.printf "@[model: %a@." SatResult.pp_model) pmodel;
  let (_pp_ex,pA,ssA,ss) = bq in (* pp_ex is accumurated pure (it is unnecessary for final results) *)
  let ppSeed = mkSolutionSeed pmodel ssA ss in
  let outputL = biabdL pmodel [] (P.flattenAnd [pA]) ssA ss in
  let baL =  List.map (fun (_,ssX,ssY) ->
                 let (pp',ssX') = lsZero [] [] ssX in
                 let ppSol = List_tailrec.concat_rev [pp';ppSeed] in 
                 let ppSol' = if !simplFlag then P.syntactical_simplL ppSol else ppSol in                 
                 BAanswer.create ppSol' ssX' ssY) outputL
  in
  Ftools.pf_s tagDebug println_debug1 (header ^ "Produced solutions");
  Ftools.pf_s tagDebug (List.iter BAanswer.println) baL;
  Ftools.pf_s tagDebug println_debug1 (header ^ "Finish");
  baL
;;  

(* biabductionList finds several solutions *)
(* balimit = maxLoop means no limit *)
let biabductionList balimit (bq: BAquery.t) : BAoutput.t =
  Ftools.pf_s tagDebug println_debug1 "BiabdLs.biabdList is called";          
  let headerBL = "[BiabductionLIST] " in
  Ftools.pf_s tagDebug println_debug1 (headerBL ^ "Biabduction query");
  Ftools.pf_s tagDebug BAquery.println bq;
  let (pp_ex,pure,ss1,ss2) = bq in
  let maxS = if balimit = maxLoop then "oo" else string_of_int balimit in
  let rec biabdL_iter n solL ppAcc =
    let header = Format.sprintf "[BiabdL_iter (%d/%s)] " (balimit-n) maxS in
    Ftools.pf_s tagDebug2 println_debug2 (header ^ "Accumulated Pure");
    Ftools.pf_s tagDebug2 P.println (P.mkAnd ppAcc);
    Ftools.pf_s tagDebug println_debug1 (header ^ "Accumulated Pure (simplified)");
    Ftools.pf_s tagDebug (fun _ -> P.println (P.mkAnd (P.syntactical_simplL ppAcc))) ();
    if n = 0
    then
      (solL,ppAcc)
    else
      let ppBeta = mkBeta (pure::ppAcc) ss1 ss2 in      
      Ftools.pf_s tagDebug2 println_debug2 (header ^ "Beta");
      Ftools.pf_s tagDebug2 P.println (P.mkAnd ppBeta);
      Ftools.pf_s tagDebug println_debug1 (header ^ "Beta (simplified)");
      Ftools.pf_s tagDebug (fun _ -> P.println (P.mkAnd (P.syntactical_simplL ppBeta))) ();
      match getModelPureL ppBeta with
      | Some pmodel ->
         let solL' = List.rev_append (biabdListOne pmodel (ppAcc,pure,ss1,ss2)) solL in
         let pSeed = P.mkAnd (mkSolutionSeed pmodel ss1 ss2) in
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Produced Solution Seed");
         Ftools.pf_s tagDebug2 P.println pSeed;
         Ftools.pf_s tagDebug println_debug1 (header ^ "Produced Solution Seed (simplified)");
         Ftools.pf_s tagDebug P.println (P.syntactical_simpl pSeed);
         let ppAcc' = (P.dual pSeed) :: ppAcc in
         biabdL_iter (n-1) solL' ppAcc'
      | None ->
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Beta is unsat (unsat core is produced)");
         Ftools.pf_s tagDebug2 showUnsatCorePureL ppBeta;
         (solL,[P.False])
  in
  match ss1,ss2 with
  | [],[] -> (* special case: (ss1,ss2)=(Emp,Emp) *)
     Ftools.pf_s tagDebug println_debug1 (headerBL ^ "Trivial case: (pure,Emp,Emp)");
     let ans = BAanswer.create [] [] [] in
     ([ans],[P.False])
  | _,_ -> (* normal case *)
     Ftools.pf_s tagDebug println_debug1 (headerBL ^ "Start BiabdL_iter");
     let (solL,ppGU) = biabdL_iter balimit [] pp_ex in
     Ftools.pf_s tagDebug println_debug1 (headerBL ^ "Finish BiabdL_iter");
     (* simplification of ppGU (it is in CNF) *)
     (* remove trivially true/false literal using the fact that terms are addresses *)
     let ppGU' = if !simplFlag then P.syntactical_simplL_CNF P.evalAddr ppGU else ppGU in
     let solL' = BAanswer.mergeL solL in
     let baOutput = (solL',ppGU') in
     Ftools.pf_s tagDebug println_debug1 (headerBL ^ "Finish");
     baOutput
;;

