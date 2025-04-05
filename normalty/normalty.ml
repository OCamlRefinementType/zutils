include Ast
include Subst

(* module SMTtyped = Typed.SMTtyped *)
(* module Notatedtyped = Typed.Notatedtyped *)
(* module Ntyped = Typed.Ntyped *)
(* module NOpttyped = Typed.NOpttyped *)
(* module Frontend = Frontend *)
(* module Connective = Connective *)
include Frontend
include Syntax
include Unification
open Sugar

let is_unkown = function Ty_unknown -> true | _ -> false
let known_opt = function Ty_unknown -> None | ty -> Some ty

let __force_known loc ty =
  if is_unkown ty then _die_with loc "unkonwn type" else ty

let __force_typed loc x = x#=>(__force_known loc)

(* let __type_unify = Unification.__type_unify layout_nt *)
(* let _type_unify = __type_unify *)
let mk_arr a b = Ty_arrow (a, b)
let layout = layout_nt
let layout_nt = layout_nt
let nt_of_string = nt_of_string
let string_of_nts = string_of_nts
let untyped x = { x; ty = Ty_unknown }
let nt_name nt = String.concat "_" @@ String.split_on_char ' ' @@ layout_nt nt

let to_smtty t =
  let rec aux = function
    | Ty_constructor ("bool", _) -> Smt_Bool
    | Ty_constructor ("int", _) -> Smt_Int
    | Ty_constructor ("nat", _) -> Smt_Int
    | Ty_constructor ("unit", _) -> Smt_Unit
    | Ty_constructor ("option", [ nt ]) -> Smt_option (aux nt)
    | Ty_constructor (name, []) -> Smt_Uninterp name
    | Ty_constructor (_, _) -> Smt_Uninterp (nt_name t)
    | Ty_tuple l -> Smt_tuple (List.map aux l)
    | Ty_var name -> Smt_Uninterp name
    | Ty_record l -> Smt_record (List.map (fun x -> x#=>aux) (sort_record l))
    | _ -> _die_with [%here] (spf "%s not a basic type" (show_nt t))
  in
  aux t

open Zdatatype

let rec layout_smtty = function
  | Smt_Bool -> "B"
  | Smt_Int -> "I"
  | Smt_Unit -> "U"
  | Smt_Uninterp x -> x
  | Smt_option smtty -> spf "%s_O" (layout_smtty smtty)
  | Smt_tuple ts -> spf "T_%s_T" (List.split_by "!" layout_smtty ts)
  | Smt_record ts -> spf "R_%s_R" (List.split_by "!" _get_x ts)

let has_poly_tp tp =
  let rec aux tp =
    match tp with
    | Ty_var _ | Ty_unknown | Ty_uninter _ -> false
    | Ty_constructor (_, tps) -> List.exists aux tps
    | Ty_record xs -> List.exists (fun x -> aux x.ty) xs
    | Ty_arrow (nt1, nt2) -> List.exists aux [ nt1; nt2 ]
    | Ty_tuple nts -> List.exists aux nts
    | Ty_poly _ -> true
  in
  aux tp

let lift_poly_tp tp =
  _assert [%here]
    (spf "not a well-formed poly type: %s" (Frontend.layout_nt tp))
    (wf_nt tp);
  let rec aux tp =
    match tp with
    | Ty_poly (p, nt) ->
        let ps, nt = aux nt in
        (p :: ps, nt)
    | _ -> ([], tp)
  in
  let ps, tp = aux tp in
  _assert [%here] "not a well-formed poly type" (not (has_poly_tp tp));
  _assert [%here] "same poly type var"
    (List.length ps == List.length (Zdatatype.List.slow_rm_dup String.equal ps));
  (ps, tp)
