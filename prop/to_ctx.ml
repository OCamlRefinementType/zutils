open OcamlParser
open Oparse
open Parsetree
open Zdatatype
open Sugar
open Common

(* NOTE: The top level normal type need to be closed by Nt.close_poly_nt *)
let get_normal_ctx filename =
  let parse_nt pval_type =
    Nt.close_poly_nt [%here] (Nt.core_type_to_t pval_type)
  in
  let f structure =
    match structure.pstr_desc with
    | Pstr_primitive { pval_name; pval_type; _ } ->
        Some pval_name.txt#:(parse_nt pval_type)
    | Pstr_type _ -> None
    | Pstr_attribute _ -> None
    | _ ->
        let () = Printf.printf "%s\n" (string_of_structure [ structure ]) in
        _failatwith [%here] "not a normal type definition"
  in
  let l = List.filter_map f (parse_imp_from_file ~sourcefile:filename) in
  let l =
    [
      "None"#:(parse_nt @@ parse_core_type "'a option");
      "Some"#:(parse_nt @@ parse_core_type "'a -> 'a option");
    ]
    @ l
  in
  Typectx.(add_to_rights emp l)

let get_axiom_ctx filename =
  let f structure =
    match structure.pstr_desc with
    | Pstr_value (_, [ value_binding ]) ->
        Some
          (let name = To_id.typed_id_of_pattern value_binding.pvb_pat in
           let name = name.x in
           match value_binding.pvb_attributes with
           | [ x ] -> (
               match x.attr_name.txt with
               | "axiom" ->
                   let tasks =
                     match x.attr_payload with
                     | PStr [] -> []
                     | PPat (pat, None) -> To_id.tuple_id_of_pattern pat
                     | _ -> _die [%here]
                   in
                   (name, tasks, To_prop.prop_of_expr value_binding.pvb_expr)
               | _ ->
                   _failatwith [%here]
                     "syntax error: non known rty kind, not axiom | assert | \
                      library")
           | _ -> _failatwith [%here] "wrong syntax")
    | Pstr_attribute _ -> None
    | _ ->
        let () = Printf.printf "%s\n" (string_of_structure [ structure ]) in
        _failatwith [%here] "translate not a func_decl"
  in
  List.filter_map f (parse_imp_from_file ~sourcefile:filename)
