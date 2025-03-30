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
  | Smt_Bool
  | Smt_Int
  | Smt_tuple of smtty list
  | Smt_enum of { enum_name : string; enum_elems : string list }
  | Smt_Uninterp of string
[@@deriving sexp, show, eq, ord]

(** Normal Type. *)

type nt =
  | Ty_unknown (* parsing only, equal to none *)
  | Ty_any
  | Ty_var of string
  | Ty_arrow of nt * nt
  | Ty_tuple of nt list
  | Ty_uninter of string
  | Ty_constructor of (string * nt list)
  | Ty_record of (nt, string) typed list
  | Ty_enum of { enum_name : string; enum_elems : string list }
  | Ty_poly of string * nt
    (* We only allow poly type appear at 1. top level 2. return type of arrow *)
[@@deriving sexp, eq, show, ord]

type t = nt

open Sugar

let is_uninterp = function Smt_Uninterp _ -> true | _ -> false

let is_base_tp = function
  | Ty_uninter _ | Ty_constructor _ | Ty_enum _ -> true
  | _ -> false

let is_basic_tp = function Ty_enum _ -> true | _ -> false
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

let get_enum_name = function
  | Ty_enum { enum_name; _ } -> enum_name
  | _ -> _die [%here]

let get_enum_elems = function
  | Ty_enum { enum_elems; _ } -> enum_elems
  | _ -> _die [%here]

let get_arr_lhs = function Ty_arrow (t1, _) -> t1 | _ -> _die [%here]
let get_arr_rhs = function Ty_arrow (_, t2) -> t2 | _ -> _die [%here]

open Zdatatype

let wf_nt t =
  let rec aux tvars = function
    | Ty_var x -> List.exists (String.equal x) tvars
    | Ty_any | Ty_unknown | Ty_uninter _ | Ty_enum _ -> true
    | Ty_constructor (_, tps) -> List.for_all (aux tvars) tps
    | Ty_record xs -> List.for_all (fun x -> aux tvars x.ty) xs
    | Ty_arrow (nt1, nt2) -> List.for_all (aux tvars) [ nt1; nt2 ]
    | Ty_tuple nts -> List.for_all (aux tvars) nts
    | Ty_poly _ -> false
  in
  let rec aux_top tvars = function
    | Ty_poly (x, ty) -> aux_top (x :: tvars) ty
    | _ as ty -> aux tvars ty
  in
  aux_top [] t

let gather_type_vars t =
  let rec aux m = function
    | Ty_var x -> StrMap.add x () m
    | Ty_any | Ty_unknown | Ty_uninter _ | Ty_enum _ -> m
    | Ty_constructor (_, tps) -> List.fold_left aux m tps
    | Ty_record xs -> List.fold_left (fun m x -> aux m x.ty) m xs
    | Ty_arrow (nt1, nt2) -> List.fold_left aux m [ nt1; nt2 ]
    | Ty_tuple nts -> List.fold_left aux m nts
    | Ty_poly (x, t) -> StrMap.remove x (aux m t)
  in
  StrMap.to_key_list @@ aux StrMap.empty t

let has_poly_tp tp =
  let rec aux tp =
    match tp with
    | Ty_any | Ty_var _ | Ty_unknown | Ty_uninter _ | Ty_enum _ -> false
    | Ty_constructor (_, tps) -> List.exists aux tps
    | Ty_record xs -> List.exists (fun x -> aux x.ty) xs
    | Ty_arrow (nt1, nt2) -> List.exists aux [ nt1; nt2 ]
    | Ty_tuple nts -> List.exists aux nts
    | Ty_poly _ -> true
  in
  aux tp

let lift_poly_tp tp =
  _assert [%here]
    (spf "not a well-formed poly type: %s" (show_nt tp))
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

let rec construct_poly_nt = function
  | [], ty -> ty
  | x :: xs, ty -> Ty_poly (x, construct_poly_nt (xs, ty))

let close_poly_nt loc t =
  let t = construct_poly_nt (gather_type_vars t, t) in
  _assert loc (spf "not a well-formed poly type: %s" (show_nt t)) (wf_nt t);
  t

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
