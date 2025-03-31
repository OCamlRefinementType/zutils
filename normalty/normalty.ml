include Ast
include Subst

(* module SMTtyped = Typed.SMTtyped *)
(* module Notatedtyped = Typed.Notatedtyped *)
(* module Ntyped = Typed.Ntyped *)
(* module NOpttyped = Typed.NOpttyped *)
(* module Frontend = Frontend *)
(* module Connective = Connective *)
include Frontend
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
    | Ty_constructor ("unit", _) ->
        Smt_enum { enum_name = "unit"; enum_elems = [ "tt" ] }
    | Ty_constructor (name, []) -> Smt_Uninterp name
    | Ty_constructor (_, _) -> Smt_Uninterp (nt_name t)
    | Ty_tuple l -> Smt_tuple (List.map aux l)
    | Ty_enum { enum_name; enum_elems } -> Smt_enum { enum_name; enum_elems }
    | Ty_var name -> Smt_Uninterp name
    | _ -> _die_with [%here] (spf "%s not a basic type" (show_nt t))
  in
  aux t

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

let rec construct_poly_nt = function
  | [], ty -> ty
  | x :: xs, ty -> Ty_poly (x, construct_poly_nt (xs, ty))

let close_poly_nt loc t =
  let t = construct_poly_nt (gather_type_vars t, t) in
  _assert loc
    (spf "not a well-formed poly type: %s" (Frontend.layout_nt t))
    (wf_nt t);
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
