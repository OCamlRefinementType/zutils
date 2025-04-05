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

type smtty =
  | Smt_Unit
  | Smt_Bool
  | Smt_Int
  | Smt_option of smtty
  | Smt_tuple of smtty list
  | Smt_record of (smtty, string) typed list
  | Smt_Uninterp of string
[@@deriving sexp, show, eq, ord]

(** Normal Type. *)

type nt =
  | Ty_unknown (* parsing only, equal to none *)
  | Ty_var of string
  | Ty_arrow of nt * nt
  | Ty_tuple of nt list
  | Ty_uninter of string
  | Ty_constructor of (string * nt list)
  | Ty_record of (nt, string) typed list
  | Ty_poly of string * nt
    (* We only allow poly type appear at 1. top level 2. return type of arrow *)
[@@deriving sexp, eq, show, ord]

type t = nt

open Sugar

let is_uninterp = function Smt_Uninterp _ -> true | _ -> false

let rec is_base_tp = function
  | Ty_poly (_, _) | Ty_arrow _ -> false
  | Ty_uninter _ | Ty_constructor _ | Ty_var _ -> true
  | Ty_record l -> List.for_all (fun x -> is_base_tp x.ty) l
  | Ty_tuple l -> List.for_all is_base_tp l
  | _ -> false

(* let is_basic_tp = function Ty_enum _ -> true | _ -> false *)
let _constructor_ty_0 name = Ty_constructor (name, [])
let unit_ty = _constructor_ty_0 "unit"
let bool_ty = _constructor_ty_0 "bool"
let int_ty = _constructor_ty_0 "int"
let nat_ty = _constructor_ty_0 "nat"
let is_dt = function Ty_constructor _ -> true | _ -> false
let fst_ty = function Ty_tuple [ a; _ ] -> a | _ -> _die [%here]
let snd_ty = function Ty_tuple [ _; a ] -> a | _ -> _die [%here]
let para_ty = function Ty_arrow (t, _) -> t | _ -> _die [%here]
let ret_ty = function Ty_arrow (_, t) -> t | _ -> _die [%here]
let get_record_types = function Ty_record l -> l | _ -> _die [%here]

let get_nth_ty loc ty n =
  match ty with
  | Ty_tuple l -> (
      match List.nth_opt l n with
      | None ->
          _die_with loc
          @@ spf "cannot find %i th element of tuple type %s" n (show_nt ty)
      | Some ty -> ty)
  | _ -> _die_with loc "not a tuple type"

(* let get_record_name = function *)
(*   | Ty_record { record_name; _ } -> record_name *)
(*   | _ -> _die [%here] *)

(* let get_record_feilds = function *)
(*   | Ty_enum { enum_elems; _ } -> enum_elems *)
(*   | _ -> _die [%here] *)

let get_arr_lhs = function Ty_arrow (t1, _) -> t1 | _ -> _die [%here]
let get_arr_rhs = function Ty_arrow (_, t2) -> t2 | _ -> _die [%here]

let _lift_poly_tp tp =
  let rec aux tp =
    match tp with
    | Ty_poly (p, nt) ->
        let ps, nt = aux nt in
        (p :: ps, nt)
    | _ -> ([], tp)
  in
  let ps, tp = aux tp in
  (ps, tp)

let gather_type_vars t =
  let open Zdatatype in
  let rec aux m = function
    | Ty_var x -> StrMap.add x () m
    | Ty_unknown | Ty_uninter _ -> m
    | Ty_constructor (_, tps) -> List.fold_left aux m tps
    | Ty_record xs -> List.fold_left (fun m x -> aux m x.ty) m xs
    | Ty_arrow (nt1, nt2) -> List.fold_left aux m [ nt1; nt2 ]
    | Ty_tuple nts -> List.fold_left aux m nts
    | Ty_poly (x, t) -> StrMap.remove x (aux m t)
  in
  StrMap.to_key_list @@ aux StrMap.empty t

(** Record type *)

(* NOTE: the Z3 encoding use list instead of map, thus we need to make sure the input list has the same order *)

let sort_record args = List.sort (fun a b -> String.compare a.x b.x) args
let mk_record args = Ty_record (sort_record args)

let as_record loc = function
  | Ty_record args -> sort_record args
  | _ -> _die loc

let get_feild loc t name =
  let args = as_record loc t in
  match List.find_opt (fun y -> String.equal name y.x) args with
  | None -> _die [%here]
  | Some n -> n.ty

let get_feild_idx loc t name =
  let args = as_record loc t in
  match List.find_index (fun y -> String.equal name y.x) args with
  | None -> _die [%here]
  | Some n -> n
