open Sexplib.Std
open Sugar
module Nt = Normalty

type op = PrimOp of string | DtConstructor of string
[@@deriving sexp, show, eq, ord]

(* a string:
   1. is in builtin_primop, then is a builtin operator.
   2. is in not builtin_primop, and with a non-lowercase alphabeta first char, then is a data constructor (include [])
   3. else, invalid
*)

let builtin_primop =
  [ "+"; "-"; "*"; "/"; ">"; ">="; "<"; "<="; "=="; "!="; "&&"; "||" ]

let eq_op = "=="
let is_builtin_op str = List.exists (String.equal str) builtin_primop

type constant =
  | U
  | B of bool
  | I of int
  | Tu of constant list
  | Dt of string * constant list
  | SetLiteral of constant list
  | Enum of { enum_name : string; enum_elems : string list; elem : string }
[@@deriving sexp, show, eq, ord]

type 't lit =
  | AC of constant
  | AVar of (('t, string) typed[@free])
  | ATu of ('t, 't lit) typed list
  | AProj of ('t, 't lit) typed * int
  | AAppOp of ('t, string) typed * ('t, 't lit) typed list
[@@deriving sexp, show, eq, ord]

type 't prop =
  | Lit of ('t, 't lit) typed
  | Implies of 't prop * 't prop
  | Ite of 't prop * 't prop * 't prop
  | Not of 't prop
  | And of 't prop list
  | Or of 't prop list
  | Iff of 't prop * 't prop
  | Forall of { qv : (('t, string) typed[@bound]); body : 't prop }
  | Exists of { qv : (('t, string) typed[@bound]); body : 't prop }
[@@deriving sexp, show, eq, ord]

(* type 't sevent = *)
(*   | GuardEvent of { vs : ('t, string) typed list; phi : 't prop } *)
(*   | EffEvent of { op : string; vs : ('t, string) typed list; phi : 't prop } *)
(* [@@deriving sexp, show, eq, ord] *)

let eq_lit p1 p2 = equal_lit (fun _ _ -> true) p1 p2
let eq_prop p1 p2 = equal_prop (fun _ _ -> true) p1 p2

(** Ast builder *)

let uAVar x = AVar (Nt.untyped x)
