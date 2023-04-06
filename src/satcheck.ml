(*
  Satchecker of symbolic heaps
*)

open Tools
open Slsyntax
open Sltosmt
open Smtsyntax
open Smttoz3
module SatResult = Smttoz3.SatcheckResult

(* brotherston's gamma *)
(* gamma (t->_ * Arr(a,b) * Str(c,d)) is (a <= b & c <= d & t disj [a,b] & t disj [c,d] *)
let gamma ss : P.t list =
  let seg = List.map S.mkInterval ss in
  let condSeg = List.flatten @@ List.map (fun (t,u) -> [zero <.< t; t <.= u]) seg in
  let condDisj = applyDiff (fun (ti,ui) (tj,uj) -> _Disj ti ui tj uj) seg in
  List.rev_append condDisj condSeg
;;

let gammaExp_sh sh : Exp.t list =
  let rec split_and p =
    match p with
    | P.And pp -> List.flatten (List.map split_and pp)
    | _ -> [p]
  in  
  let (p,ss) = sh in
  try
    let pp = (split_and p) @ (gamma ss) in
    let ee = List.map mkExp_p pp in
    ee
  with
  | e ->
     print_endline "Exception from gammaExp_sh";
     raise e
;;

(* Satchecker with hat vars *)
(* Assume that sh contains a@hat,a@hat+x,b@hat,b@hat+10 *)
(* 1. make an order of hat variables occuring in sh (e.g. a@hat < b@hat) *)
(* 2. sh --> a@hat < b@hat & a@hat+x < b@hat & sh *)
let pp_q fmt (t,u) = Format.printf "(%a,%a)" T.pp t T.pp u
;;  
let mkSH_hat (sh : QFSH.t) =
  let (p,ss) = sh in
  let tttTerms = Tset.union (P.terms p) (SS.terms ss) in
  let qqTermHvL =
    Tset.fold
      (fun t qq -> try (t, Tset.choose (Tset.hatVars' t))::qq with Not_found -> qq)
      tttTerms
      []
  in
  let rec aux pp upperHV curHV qq =
    match qq with
    | [] -> pp
    | (_,tHV)::qq' when T.compare tHV upperHV = 0 -> aux pp upperHV curHV qq'
    | (t,tHV)::qq' when T.compare tHV curHV = 0  -> aux ((t <.< upperHV)::pp) upperHV curHV qq'
    | (t,tHV)::qq' when T.compare tHV curHV != 0 -> aux ((t <.< curHV)::pp) curHV tHV qq'
    | (t,tHV)::qq' -> failwith "mkSH_hat: something wrong\n"
  in
  let qqTermHvSortedL = List.sort (fun (_,tHV1) (_,tHV2) -> T.compare_rev tHV1 tHV2) qqTermHvL in
  match qqTermHvSortedL with
  | [] -> (p,ss)
  | (_,tHVmax)::qqRest ->
     let pp = aux [] tHVmax tHVmax qqRest in
     (P.And (pp@[p]),ss)
;;

(* satchecker for Array with hat *)
let satcheckArr_hat modelflag ucflag (sh : QFSH.t) =
  let sh1 = mkSH_hat sh in
  try
    checkSatExpL modelflag ucflag (gammaExp_sh sh1)
  with
  | e -> print_endline "Exception from satcheckArr_hat"; raise e
;;

(***************************)
(* Satchecker for Ls + Arr *)
(***************************)
let lsElim (k : QFSH.t) : QFSH.t list =
  let (p,ss) = k in
  let _res = ref [([p],[])] in
  let extend pp1 ss1 (pp2,ss2) = (pp1 @ pp2, ss1 @ ss2) in
  for i = 0 to List.length ss - 1 do
    match List.nth ss i with
    | S.Ind(ls,t::u::_) when ls = "Ls" ->
       let res1 = List.map (extend [t =.= u] []) !_res in
       let res2 = List.map (extend [t <.> u] [t -.> [("*",u)]]) !_res in
       _res := res1 @ res2
    | s ->
       _res := List.map (extend [] [s]) !_res
  done;
  List.map (fun (pp,ss) -> (P.And (List.rev pp), List.rev ss)) !_res
;;  
(* satchecker for Array+Ls with hat vars *)
let satcheck_hat modelflag ucflag (sh :QFSH.t) : SatResult.t =
  let _ucL = ref [] in
  let _result = ref SatResult.Unknown in
  let _shL = ref (lsElim sh) in
  begin
    try
      while !_shL <> [] do
        let sh1 = List.hd !_shL in
        _shL := List.tl !_shL;
        match satcheckArr_hat modelflag ucflag sh1 with
        | SatResult.Model _ as q -> _result := q; raise Exit (* sat *)
        | SatResult.UnsatCore uc -> _ucL := uc @ !_ucL
        | SatResult.Unknown as q -> _result := q; raise Exit
      done;
      _result := SatResult.UnsatCore !_ucL
    with
    | Exit -> ()
    | e -> print_endline "Exception from satcheck_hat"; raise e
  end;
  !_result
;;
