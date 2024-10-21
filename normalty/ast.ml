open Sugar
open Sexplib.Std

(** Quantifiers *)

type qt = Fa | Ex [@@deriving sexp, show, eq, ord]
type binary = Implies | Iff [@@deriving sexp, show, eq, ord]
type multi = And | Or [@@deriving sexp, show, eq, ord]

let is_forall = function Fa -> true | Ex -> false
let is_exists x = not @@ is_forall x

let qt_of_string = function
  | "forall" -> Fa
  | "exists" -> Ex
  | _ -> failwith "not a quantifier"

let qt_to_string = function Fa -> "forall" | Ex -> "exists"
let qt_pretty_layout = function Fa -> "∀ " | Ex -> "∃ "

(** Type used for smt query. *)

type smtty = Smt_Bool | Smt_Int | Smt_Uninterp of string
[@@deriving sexp, show, eq, ord]

(** Normal Type. *)

type nt =
  | Ty_unknown (* parsing only, equal to none *)
  | Ty_any
  | Ty_var of string
  | Ty_unit
  | Ty_int
  | Ty_nat
  | Ty_bool
  | Ty_arrow of nt * nt
  | Ty_tuple of nt list
  | Ty_uninter of string
  | Ty_constructor of (string * nt list)
  | Ty_record of (nt, string) typed list
  | Ty_enum of { enum_name : string; enum_elems : string list }
[@@deriving sexp, eq, show, ord]

type t = nt

open Sugar

let is_uninterp = function Smt_Uninterp _ -> true | _ -> false

let is_base_tp = function
  | Ty_unit | Ty_int | Ty_nat | Ty_bool | Ty_uninter _ | Ty_constructor _
  | Ty_enum _ ->
      true
  | _ -> false

let is_basic_tp = function
  | Ty_unit | Ty_int | Ty_nat | Ty_bool | Ty_uninter _ | Ty_enum _ -> true
  | _ -> false

let is_dt = function Ty_constructor _ -> true | _ -> false
let fst_ty = function Ty_tuple [ a; _ ] -> a | _ -> _die [%here]
let snd_ty = function Ty_tuple [ _; a ] -> a | _ -> _die [%here]
let para_ty = function Ty_arrow (t, _) -> t | _ -> _die [%here]
let ret_ty = function Ty_arrow (_, t) -> t | _ -> _die [%here]
let get_record_types = function Ty_record l -> l | _ -> _die [%here]

let get_enum_name = function
  | Ty_enum { enum_name; _ } -> enum_name
  | _ -> _die [%here]

let get_enum_elems = function
  | Ty_enum { enum_elems; _ } -> enum_elems
  | _ -> _die [%here]

let destruct_arr_tp tp =
  let rec aux = function
    | Ty_arrow (t1, t2) ->
        let argsty, bodyty = aux t2 in
        (t1 :: argsty, bodyty)
    | ty -> ([], ty)
  in
  aux tp

let rec construct_arr_tp = function
  | [], retty -> retty
  | h :: t, retty -> Ty_arrow (h, construct_arr_tp (t, retty))
