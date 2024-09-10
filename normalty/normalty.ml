include Ast
include Subst

(* module SMTtyped = Typed.SMTtyped *)
(* module Notatedtyped = Typed.Notatedtyped *)
(* module Ntyped = Typed.Ntyped *)
(* module NOpttyped = Typed.NOpttyped *)
(* module Frontend = Frontend *)
(* module Connective = Connective *)
include Frontend
open Sugar

let __force_known loc = function
  | Ty_unknown -> _die_with loc "unkonwn type"
  | _ as ty -> ty

let __force_typed loc x = (__force_known loc) #=> x
let __type_unify = Unification.__type_unify layout_nt
let _type_unify = __type_unify
let mk_arr a b = Ty_arrow (a, b)
let layout = layout_nt
let layout_nt = layout_nt
let nt_of_string = nt_of_string
let string_of_nts = string_of_nts
let untyped x = { x; ty = Ty_unknown }
let nt_name nt = String.concat "_" @@ String.split_on_char ' ' @@ layout_nt nt

let to_smtty t =
  let aux = function
    | Ty_bool -> Smt_Bool
    | Ty_int -> Smt_Int
    | Ty_nat -> Smt_Int
    | Ty_constructor (name, []) -> Smt_Uninterp name
    | Ty_constructor (_, _) -> Smt_Uninterp (nt_name t)
    | _ -> _die_with [%here] (spf "%s not a basic type" (show_nt t))
  in
  aux t
