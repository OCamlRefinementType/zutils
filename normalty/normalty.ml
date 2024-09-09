include Ast
include Subst

let __type_unify = Unification.__type_unify

(* module SMTtyped = Typed.SMTtyped *)
(* module Notatedtyped = Typed.Notatedtyped *)
(* module Ntyped = Typed.Ntyped *)
(* module NOpttyped = Typed.NOpttyped *)
(* module Frontend = Frontend *)
(* module Connective = Connective *)
include Frontend

let mk_arr a b = Ty_arrow (a, b)
let layout = layout_nt
let layout_nt = layout_nt
let nt_of_string = nt_of_string
let string_of_nts = string_of_nts
