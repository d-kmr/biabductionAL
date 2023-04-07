open Tools
open Slsyntax
open Sltosmt   
open Smttoz3
open Smtsyntax
module SatResult = Smttoz3.SatcheckResult

open BiabdData

(*-----------------------
biabduction array     
(Brotherston's method + it's iteration)

Main function: biabductionA
INPUT: (pureL,pure,ss1,ss2): BAquery
OUTPUT: (solutionList,pureL): BAoutput.t
-----------------------*)

(* Brotherston's beta *)
(* "beta p ss1 ss2" returns a pure-formula *)
(* that is equivalent to the biabduction-problem (p,ss1,ss2) has a solution  *)
let beta p ss1 ss2 : P.t list =
  let (ssPto1,ssArr1,ssStr1,ssInd1) = SS.split ss1 in
  let (ssPto2,_,ssStr2,ssInd2) = SS.split ss2 in
  let ttPtoAddr2 = mapAppend S.addrs ssPto2 in
  let segArr1 = mapAppend_rev S.getArraySeg ssArr1 in
  let segStr1 = mapAppend_rev S.getStringSeg ssStr1 in
  let segStr2 = mapAppend_rev S.getStringSeg ssStr2 in
  
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
  (* condPtoArr: Arr(a,b) |- t->_ cannot match "t out [a,b]" *)
  (* condPtoStr: Str(a,b) |- t->_ cannot match "t out [a,b]" *)  
  let mkCondPtoSegOne seg t = List.map (fun (a,b) -> (_Out t a b)) seg in
  let mkCondPtoSeg seg = mapAppend_rev (mkCondPtoSegOne seg) ttPtoAddr2 in
  let condPtoArr = mkCondPtoSeg segArr1 in
  let condPtoStr = mkCondPtoSeg segStr1 in
  
  (* gamma1: ss1 has a model *)
  (* gamma2: ss2 has a model *)  
  let gamma1 = Satcheck.gamma ss1 in
  let gamma2 = Satcheck.gamma ss2 in
  
  (* condPtoStr: t->[0] |- Str(c',d') cannot match "t out [c',d']" *)
  let mkCondNullCharStrOne pto seg =
    let t = List.hd (S.addrs pto) in
    let cc = S.getPtoContent pto in
    match cc with
    | (_,u)::[] when u = T.Int 0 -> List.map (fun (a,b) -> (_Out t a b)) seg
    | _ -> []
  in
  let condNullCharStr = mapAppend_rev (fun pto -> mkCondNullCharStrOne pto segStr2) ssPto1 in
  (* condArrStr: Arr(a,b) |- Str(c',d') cannot match "[a,b] disj [c',d']" *)
  let condArrStr = List_tailrec.map2 (fun (a,b) (c',d') -> _Disj a b c' d') segArr1 segStr2 in
  List_tailrec.concat [P.flattenAnd [p]; gamma1; gamma2; condPtoArr; condPtoStr; condPto; condNullCharStr; condArrStr]
;;

(*
let rho p ss1 ss2 =
  let ss = List.rev_append ss1 ss2 in
  let vvvFV = Strset.union (P.fv p) (SS.fv ss) in
  let tttFV = Tset.union (P.fv_t p) (SS.fv_t ss) in
  let tttHV = Tset.filter T.isHatVar' tttFV in
  let ttHV = Tset.elements tttHV in  
  match Tset.is_empty tttHV with
  | true -> []
  | false ->
     let _pp = ref [] in
     let tttAddr = Tset.union (SS.fv_t ss) (Tset.of_list (SS.addrs ss)) in
     let mkHvGroup tHV = Tset.filter (fun t -> Tset.mem tHV (Tset.fv_t t)) tttAddr in
     let blkGroups = List.map mkHvGroup ttHV in (* block-groups [ [a@hat;a@hat+3;a@hat+10]; [b@hat;b@hat+10] ] *)
     let blkNumber = List.length blkGroups in
     let ttLowerBounds = Strset.fold (fun v l -> (T.Var (v,Attrs.empty))::l) (Strset.genFreshMany "#lb" vvvFV blkNumber) [] in
     let lb_0 = List.nth ttLowerBounds 0 in
     (* Lower-bounds' ordering condition *)
     let pp0 = [lb_0 =.= zero] in
     let pp1 = List_tailrec.fold_int
                 (fun pp i ->
                   let lb_i = List.nth ttLowerBounds i in
                   let lb_i1 = List.nth ttLowerBounds (i+1) in
                   (lb_i <.< lb_i1) :: pp)
                 pp0
                 (blkNumber - 2)
     in
     (* Block-Group range condition except the last group *)
     let pp2 = List_tailrec.fold_int
                 (fun pp i ->
                   let blkGroup_i = Tset.elements (List.nth blkGroups i) in
                   let lb_i = List.nth ttLowerBounds i in
                   let lb_i1 = List.nth ttLowerBounds (i+1) in
                   List_tailrec.fold_int
                     (fun qq j ->
                       let t = List.nth blkGroup_i j in
                       (t <.< lb_i1) :: (lb_i <.< t) :: qq)
                     pp
                     (List.length blkGroup_i - 1)
                 )
                 pp1
                 (blkNumber - 2)
     in
     (* Block-Group range condition of the last group *)
     let last = blkNumber - 1 in
     let blkGroup_last = Tset.elements (List.nth blkGroups last) in
     let lb_last = List.nth ttLowerBounds last in
     let pp3 = List_tailrec.fold_int
                 (fun pp j ->
                   let t = List.nth blkGroup_last j in
                   (lb_last <.< t) :: pp)
                 pp2
                 (List.length blkGroup_last - 1)
     in
     pp3
;;
 *)
  
(* mkBetaRho p ss1 ss2 *)
(* A model of this formula is a model of a biabduction solution of (p,ss1,ss2) *)
let mkBetaRho p ss1 ss2 =
  let ttt_p = P.fv_t p in
  let ttt_ss = SS.fv_t (List.rev_append ss1 ss2) in
  let ppVarcond = Tset.fold (fun t l -> (zero <.= t)::l) (Tset.union ttt_p ttt_ss) [] in  
  let ppBeta = beta p ss1 ss2 in  
  let ppRho = mkHatCond [p] ss1 ss2 in
  let ppCond = List_tailrec.concat [ppVarcond;ppBeta;ppRho] in
  p::ppCond
;;

(* mkSolutionSeed pmodel ss1 ss2 *)
(* This produces the pure condition for the biabduction solution of (p,ss1,ss2) specified by 'pmodel' *)
let mkSolutionSeed pmodel ss1 ss2 : P.t list =
  (* Format.printf "@[%a@." SatResult.pp_model pmodel; *)
  let (ssPto1,ssArr1,ssStr1,_) = SS.split ss1 in
  let (ssPto2,ssArr2,ssStr2,_) = SS.split ss2 in
  let ssPto = List.rev_append ssPto1 ssPto2 in
  let ssArr = List.rev_append ssArr1 ssArr2 in
  let ssStr = List.rev_append ssStr1 ssStr2 in
  let tvAddrs_sorted = 
    let tttPtoAddr = Tset.mapUnion S.addrs_s ssPto in
    let segArr = mapAppend_rev S.getArraySeg ssArr in
    let segStr = mapAppend S.getStringSeg ssStr in
    let seg = List.rev_append segArr segStr in
    let tttSegPts = Tset.mapUnion (fun (tL,tR) -> Tset.of_list [tL;tR;tR +.+ one]) seg in
    let tttPoints = Tset.union tttPtoAddr tttSegPts in
    let ttPoints = Tset.elements tttPoints in
    let tvL = List.map (fun t -> (t, SHterm.evalUnderPmodel pmodel t)) ttPoints in
    List.sort (fun pv1 pv2 -> compare (snd pv1) (snd pv2)) tvL
  in
  let tvPtoContents_sorted = 
    let tttPtoContents = Tset.mapUnion S.getPtoContentTms_s ssPto in
    let ttPtoContents = Tset.elements tttPtoContents in    
    let tvL = List.map (fun t -> (t, SHterm.evalUnderPmodel pmodel t)) ttPtoContents in
    List.sort (fun pv1 pv2 -> compare (snd pv1) (snd pv2)) tvL
  in
  let rec mkPure opt pp tvL = (* opt=true for addrs, false for contents *)
    match tvL with
    | [] -> pp
    | _::[] -> pp
    | (t1,v1)::(t2,v2)::tvL1 ->
       let hVar = Tset.union (Tset.hatVars t1) (Tset.hatVars t2) in
       begin
         match Tset.cardinal hVar < 2, v1 = v2 with
         | true,true -> mkPure opt ((t1 =.= t2)::pp) ((t2,v2)::tvL1)
         | true,false when opt=true -> mkPure opt ((t1 <.< t2)::pp) ((t2,v2)::tvL1)
         | _,_ -> mkPure opt pp ((t2,v2)::tvL1)
       end
  in
  (mkPure true [] tvAddrs_sorted) @ (mkPure false [] tvPtoContents_sorted)
;;

(* ptocover *)
(* This returns the missing part 't->gg' if it is not covered by 'seg' *)
(* It is Brotherston's ptocov *)
let mkPtoCover pmodel t gg seg =
  let eval t = SHterm.evalUnderPmodel pmodel t in
  let rec aux seg0 = 
    match seg0 with
    | [] -> [S.Pto(t,gg)]
    | (tL,tR)::_ when (eval tL) <= (eval t) && (eval t) <= (eval tR) -> []
    | _ :: seg1 -> aux seg1
  in
  aux seg
;;       

(* blkcover blk tL tR seg *)
(* blk is "arr" or "str" *)
(* This returns the missing (part of) block between tL and tR (Arr if blk="arr", Str if blk="str") *)
(* if it is not covered by 'seg' *)
let mkBlkCover pmodel blk tL tR seg =
  let eval t = SHterm.evalUnderPmodel pmodel t in  
  let blkflag = if blk = "arr" then true else if blk = "str" then false else failwith "blkcover" in
  let rec aux tL0 tR0 seg0 = 
    match blkflag,seg0 with
    | _,_ when (eval tL0) > (eval tR0) -> []
    | true, []          -> [S.Arr(tL0,tR0)]
    | false, []         -> [S.Str(tL0,tR0)]
    | _,(tL1,tR1)::seg1
         when ((eval tL0) <= (eval tR1) && (eval tL1) <= (eval tR0))
              || ((eval tL1) <= (eval tR0) && (eval tL0) <= (eval tR1)) (* i.e. [tL0,tR0] comm [tL1,tR1] *)
      ->
       let ans1 = aux tL0 (T.minusOne tL1) seg1 in (* 1,0 *)
       let ans2 = aux (T.plusOne tR1) tR0 seg1 in (* 2,1 *)
       ans1 @ ans2
    | _,_::seg1 -> aux tL0 tR0 seg1
  in
  aux tL tR seg
;;       

let mkCover pmodel s ss =
  let combineSeg (seg: Seg.t): Seg.t = (* [(t1,u1);(t2,u2)] *)
    let eval t = SHterm.evalUnderPmodel pmodel t in
    let segVal = List.map (fun (t,u) -> (t,u,eval t,eval u)) seg in (* [(t1,u1,6,8);(t2,u2,3,5)]*)
    let sortSegVal = List.sort (fun (_,_,n1,_) (_,_,n2,_) -> compare n1 n2) segVal in (* [(t2,u2,3,5);(t1,u1,6,8)]*)
    let rec combineSegVal sv =
      match sv with
      | [] -> []
      | [a] -> [a]
      | (t1,u1,m1,n1)::(t2,u2,m2,n2)::res when n1+1=m2 -> combineSegVal ((t1,u2,m1,n2)::res)
      | (t,u,m,n)::res -> (t,u,m,n)::(combineSegVal res)
    in
    let combSegVal = combineSegVal sortSegVal in
    List.map (fun (t,u,_,_) -> (t,u)) combSegVal
  in
  let seg = SS.mkSegment ss in  
  let seg_comb = combineSeg seg in
  let ssRes =
    match s with
    | S.Pto(t,gg) -> mkPtoCover pmodel t gg seg_comb
    | S.Arr(tL,tR) -> mkBlkCover pmodel "arr" tL tR seg_comb
    | S.Str(tL,tR) -> mkBlkCover pmodel "str" tL tR seg_comb
    | S.Ind(p,tt) -> failwith "mkCover: inductive predicate"
  in
  ssRes
;;

(* Brotherston's function *)
(* This works correctly iff pmodel satisfies beta(pure&ss1,ss2) *)
let biabdArrayOne pmodel (bq : BAquery.t) : BAanswer.t =
  let (pp_ex,pure,ss1,ss2) = bq in
  let ppSeed = mkSolutionSeed pmodel ss1 ss2 in
  let ssX = List.fold_left (fun ss s -> List.rev_append (mkCover pmodel s ss1) ss) [] ss2 in
  let ssY = List.fold_left (fun ss s -> List.rev_append (mkCover pmodel s ss2) ss) [] ss1 in  
  let ssX' = SS.syntactical_simpl ssX in
  let ssY' = SS.syntactical_simpl ssY in
  let pp_ex1 = List.rev_append pp_ex ppSeed in
  let pp_ex2 = if !simplFlag then P.syntactical_simplL pp_ex1 else pp_ex1 in
  let biAns = BAanswer.create pp_ex2 ssX' ssY' in
  biAns
;;  

(* biabductionArray finds several solutions *)
let biabductionArray balimit (bq: BAquery.t) : BAoutput.t =
  let headerAL = "[BiabductionARRAY] " in
  Ftools.pf_s tagDebug println_debug1 (headerAL ^ "Biabduction query:");
  Ftools.pf_s tagDebug BAquery.println bq;
  Ftools.pf_s tagDebug println_debug1 "";
  let (pp_ex,pure,ss1,ss2) = bq in
  let maxS = if balimit = ml then "oo" else string_of_int balimit in
  let rec biabdA_iter n solL ppAcc =
    (*
    Format.printf "@[************************************@.";
    Format.printf "@[%a@." (pp_list "" "\n" P.pp) ppAcc;
     *)
    let header = Format.sprintf "[BiabdA_iter (%d/%s)] " n maxS in
    Ftools.pf_s tagDebug2 println_debug2 (header ^ "biabductionArray.biabdA_iter is called");
    Ftools.pf_s tagDebug2 println_debug2 (header ^ "Accumulated Pure");
    Ftools.pf_s tagDebug2 P.println (P.mkAnd ppAcc);
    if n = balimit
    then
      (solL,ppAcc)
    else
      let ppBetaRho = mkBetaRho (P.mkAnd (pure::ppAcc)) ss1 ss2 in
      Ftools.pf_s tagDebug2 println_debug2 (header ^ "Beta Rho (simplified)");
      Ftools.pf_s tagDebug2 P.println (P.syntactical_simpl (P.mkAnd ppBetaRho));
      match getModelPureL ppBetaRho with
      | Some pmodel ->
         let pSeed = P.mkAnd (mkSolutionSeed pmodel ss1 ss2) in
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Produced Solution Seed (original)");
         Ftools.pf_s tagDebug2 P.println pSeed;
         Ftools.pf_s tagDebug println_debug1 (header ^ "Produced Solution Seed (simplified)");
         Ftools.pf_s tagDebug P.println (P.syntactical_simpl pSeed);
         let pBetaRho = P.mkAnd ppBetaRho in
         let solL' = 
           if not(P.evalUnderPmodel pmodel pBetaRho)
           then (* pSeed is not a correct seed -> skip *)
             solL
           else (* pSeed is a correct seed *)
             let bq' = (ppAcc,pure,ss1,ss2) in
             let sol = biabdArrayOne pmodel bq' in
             Ftools.pf_s tagDebug println_debug1 (header ^ "Found solution");
             Ftools.pf_s tagDebug BAanswer.println sol;
             sol :: solL
         in
         let ppAcc' = P.syntactical_simplL ((P.dual pSeed) :: ppAcc) in
         biabdA_iter (n+1) solL' ppAcc'
      | None ->
         let pBetaRho = P.mkAnd ppBetaRho in
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Beta is UNSAT");
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Beta (original)");         
         Ftools.pf_s tagDebug2 P.println pBetaRho;
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Beta (simplified)");
         Ftools.pf_s tagDebug2 P.println (P.syntactical_simpl pBetaRho);
         Ftools.pf_s tagDebug2 println_debug2 (header ^ "Unsat core");
         Ftools.pf_s tagDebug2 showUnsatCorePureL [P.syntactical_simpl pBetaRho];
         (solL,[P.False])
  in
  match ss1,ss2 with
  | [],_ -> (* special case: ss1=Emp *)
     Ftools.pf_s tagDebug println_debug1 (headerAL ^ "Trivial case: (pure,Emp,ss2)");
     let ans = BAanswer.create [] ss2 [] in
     ([ans],[P.False])
  | _,[] ->  (* special case: ss2=Emp *)
     Ftools.pf_s tagDebug println_debug1 (headerAL ^ "Trivial case: (pure,ss1,Emp)");
     let ans = BAanswer.create [] [] ss1 in
     ([ans],[P.False])
  | _,_ -> (* normal case *)
     Ftools.pf_s tagDebug println_debug1 (headerAL ^ "Start BiabdA_iter");
     let (solL,ppGU) = biabdA_iter 1 [] pp_ex in
     Ftools.pf_s tagDebug println_debug1 (headerAL ^ "Finish BiabdA_iter");
     (* simplification of ppGU (it is in CNF) *)
     (* remove trivially true/false literal using the fact that terms are addresses *)
     let ppGU' = if !simplFlag then P.syntactical_simplL_CNF P.evalAddr ppGU else ppGU in
     let solL' = BAanswer.mergeL solL in
     let baOutput = (solL',ppGU') in
     Ftools.pf_s tagDebug println_debug1 (headerAL ^ "Finish");
     baOutput
;;

