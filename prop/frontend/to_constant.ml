open Ast
open OcamlParser
open Parsetree
open Zdatatype
open To_id
open To_op
open Sugar
open Mutils

let string_to_constant = function
  | "true" -> B true
  | "false" -> B false
  | "()" -> U
  | x -> failwith (spf "do not support literal: %s" x)

let rec expr_to_constant e =
  let mk_exn () =
    failwith
      (spf "do not support complicate literal: %s"
         (Pprintast.string_of_expression e))
  in
  match e.pexp_desc with
  | Pexp_tuple es -> Tu (List.map expr_to_constant es)
  | Pexp_construct (id, e) -> (
      let name = longid_to_id id in
      match e with
      | None -> string_to_constant name
      | Some e -> (
          match (string_to_op name, expr_to_constant e) with
          | DtConstructor op, Tu es -> Dt (op, es)
          | _, _ -> mk_exn ()))
  | Pexp_constant (Pconst_integer (istr, None)) -> I (int_of_string istr)
  | Pexp_constant (Pconst_string (elem, _, _)) ->
      Enum { enum_name = ""; elem; enum_elems = [] }
  | Pexp_array l -> SetLiteral (List.map expr_to_constant l)
  | _ -> mk_exn ()

let constant_to_expr v =
  let rec aux v =
    match v with
    | U -> mk_construct ("()", [])
    | B true -> mk_construct ("true", [])
    | B false -> mk_construct ("false", [])
    | I i ->
        desc_to_ocamlexpr
          (Pexp_constant (Pconst_integer (string_of_int i, None)))
    | Dt (op, vs) -> mk_construct (op, List.map aux vs)
    | Tu l -> desc_to_ocamlexpr (Pexp_tuple (List.map aux l))
    | SetLiteral l -> desc_to_ocamlexpr (Pexp_array (List.map aux l))
    | Enum { enum_name; elem; enum_elems } ->
        let enum_ty = Normalty.Ty_enum { enum_name; enum_elems } in
        desc_to_ocamlexpr
        @@ Pexp_constraint
             ( desc_to_ocamlexpr
               @@ Pexp_constant (Pconst_string (elem, Location.none, None)),
               Normalty.t_to_core_type enum_ty )
  in
  aux v

let layout_constant v = Pprintast.string_of_expression @@ constant_to_expr v
let layout_constants ts = List.split_by_comma layout_constant ts
