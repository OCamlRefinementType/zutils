(** Axiom system *)

open Syntax
open Zdatatype
open Sugar

let _log = Myconfig._log "axiom"

let add_laxiom asys (name, tasks, prop, z3_prop) =
  let tasks = StrSet.of_list tasks in
  let preds = StrSet.of_list @@ get_fv_preds_from_prop prop in
  if StrMap.mem name asys then _die [%here]
  else StrMap.add name { tasks; preds; prop; z3_prop } asys

let add_laxioms asys l = List.fold_left add_laxiom asys l

let find_axioms_by_task asys task =
  let m = StrMap.filter (fun _ { tasks; _ } -> StrSet.mem task tasks) asys in
  StrMap.to_key_list m

let find_axioms_by_preds asys query_preds =
  let m =
    StrMap.filter (fun _ { preds; _ } -> StrSet.subset preds query_preds) asys
  in
  StrMap.to_key_list m

let pred_extension (_, ps) = ps

let find_axioms asys (task, qeury) =
  let query_preds = StrSet.of_list @@ get_fv_preds_from_prop qeury in
  let query_preds = pred_extension (task, query_preds) in
  let axiom1 =
    match task with None -> [] | Some task -> find_axioms_by_task asys task
  in
  let axiom2 = find_axioms_by_preds asys query_preds in
  let axioms = List.slow_rm_dup String.equal (axiom1 @ axiom2) in
  let () =
    _log @@ fun () ->
    Pp.printf "@{<bold>Axioms: @} %s\n" @@ StrList.to_string axioms
  in
  let props =
    StrMap.filter (fun name _ -> List.exists (String.equal name) axioms) asys
  in
  List.map (fun x -> x.z3_prop) @@ StrMap.to_value_list props

let emp = StrMap.empty
