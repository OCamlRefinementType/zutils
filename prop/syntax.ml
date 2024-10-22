include Ast
open Sugar

(** constant *)

let rec constant_to_nt c =
  let open Nt in
  match c with
  | U -> Ty_unit
  | B _ -> Ty_bool
  | I _ -> Ty_int
  | Tu l -> Nt.Ty_tuple (List.map constant_to_nt l)
  | Enum { enum_name; enum_elems; _ } -> Ty_enum { enum_name; enum_elems }
  | Dt _ | SetLiteral _ -> failwith "Not implemented"

(** op *)

(* NOTE: there are several constructors cannot be parsed directly from the external files *)
let dt_name_for_typectx = function
  | "()" -> "TT"
  | "::" -> "Cons"
  | "[]" -> "Nil"
  | _ as s -> s

let op_name_for_typectx = function
  | PrimOp name -> name
  | DtConstructor name -> dt_name_for_typectx name

let is_dt_op str =
  let fst_char = String.get str 0 in
  Char.uppercase_ascii fst_char == fst_char

let id_eq_op = function PrimOp "==" -> true | _ -> false
let id_is_dt name = String.(equal name @@ capitalize_ascii name)
let mk_eq_op = PrimOp eq_op
let typed_eq_op_string ty = eq_op #: Nt.(mk_arr ty (mk_arr ty Ty_bool))

(** lit *)

let rec fv_lit (lit_e : 't lit) =
  match lit_e with
  | AC _ -> []
  | AVar _t_stringtyped0 -> [] @ [ _t_stringtyped0 ]
  | ATu _t__tlittypedlist0 ->
      [] @ List.concat (List.map typed_fv_lit _t__tlittypedlist0)
  | AProj (_t__tlittyped0, _) -> [] @ typed_fv_lit _t__tlittyped0
  | AAppOp (_, _t__tlittypedlist1) ->
      [] @ List.concat (List.map typed_fv_lit _t__tlittypedlist1)

and typed_fv_lit (lit_e : ('t, 't lit) typed) = fv_lit lit_e.x

let rec subst_lit (string_x : string) f (lit_e : 't lit) =
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 ->
      if String.equal _t_stringtyped0.x string_x then f _t_stringtyped0
      else AVar _t_stringtyped0
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (typed_subst_lit string_x f) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) ->
      AProj (typed_subst_lit string_x f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        ( _t_stringtyped0,
          List.map (typed_subst_lit string_x f) _t__tlittypedlist1 )

and typed_subst_lit (string_x : string) f (lit_e : ('t, 't lit) typed) =
  (subst_lit string_x f) #-> lit_e

let rec map_lit : 't 's. ('t -> 's) -> 't lit -> 's lit =
 fun f lit_e ->
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 -> AVar f #=> _t_stringtyped0
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (fun e -> typed_map_lit f e) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) -> AProj (typed_map_lit f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        (f #=> _t_stringtyped0, List.map (typed_map_lit f) _t__tlittypedlist1)

and typed_map_lit :
      't 's. ('t -> 's) -> ('t, 't lit) typed -> ('s, 's lit) typed =
 fun f lit_e -> f #=> ((map_lit f) #-> lit_e)

let fv_lit_id e = fv_typed_id_to_id fv_lit e
let typed_fv_lit_id e = fv_typed_id_to_id typed_fv_lit e
let subst_lit_instance x instance e = subst_f_to_instance subst_lit x instance e

let typed_subst_lit_instance x instance e =
  subst_f_to_instance typed_subst_lit x instance e
(* Generated from _lit.ml *)

(* force *)
let typed_lit_force_aappop_opt (lit, op) =
  match lit.x with
  | AAppOp ({ x; _ }, args) when String.equal x op -> Some args
  | _ -> None

let typed_lit_force_avar_opt lit =
  match lit.x with AVar id -> Some id | _ -> None

let typed_lit_force_ac_opt lit = match lit.x with AC c -> Some c | _ -> None
let mk_lit_true = AC (B true)
let mk_lit_false = AC (B true)

(** For Nt.t typed *)

let mk_lit_eq_lit ty lx ly =
  AAppOp (typed_eq_op_string ty, [ lx #: ty; ly #: ty ])

let mk_var_eq_var ty x y =
  let lx = AVar x in
  let ly = AVar y in
  AAppOp (typed_eq_op_string ty, [ lx #: ty; ly #: ty ])

let mk_int_l1_eq_l2 l1 l2 =
  AAppOp (typed_eq_op_string Nt.Ty_int, [ l1 #: Nt.Ty_int; l2 #: Nt.Ty_int ])

let get_var_opt = function AVar x -> Some x | _ -> None

let get_subst_pair a b =
  match get_var_opt a with Some a -> [ (a, b) ] | None -> []

let get_eqlits lit =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      get_subst_pair a.x b.x @ get_subst_pair b.x a.x
  | _ -> []

let find_assignment_of_intvar lit x =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x -> (
      match (a.x, b.x) with
      | AVar y, _ when String.equal x y.x -> Some b.x
      | _, AVar y when String.equal x y.x -> Some a.x
      | _, _ -> None)
  | _ -> None

let rec get_non_unit_lit lit =
  (* let () = *)
  (*   Env.show_log "gather" @@ fun _ -> *)
  (*   Printf.printf ">>>>> get_non_unit_lit: %s\n" *)
  (*     (Sexplib.Sexp.to_string (sexp_of_lit lit.x)) *)
  (* in *)
  if Nt.equal_nt Nt.Ty_unit lit.ty then None
  else
    match lit.x with
    | AAppOp (_, args) -> (
        (* let () = *)
        (*   Env.show_log "gather" @@ fun _ -> *)
        (*   Printf.printf ">>>>> %s: %s\n" (Op.to_string op.x) *)
        (*     (List.split_by_comma (fun x -> layout x.ty) args) *)
        (* in *)
        let res = List.filter_map get_non_unit_lit args in
        match res with [] -> None | _ -> Some lit.x)
    | _ -> Some lit.x

let get_op_args lit = match lit with AAppOp (_, args) -> args | _ -> []

(** prop *)

open Ast

let show_lit regex = show_lit (fun _ _ -> ()) regex
let show_prop regex = show_prop (fun _ _ -> ()) regex

let rec fv_prop (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> [] @ typed_fv_lit _t__tlittyped0
  | Implies (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Ite (_tprop0, _tprop1, _tprop2) ->
      (([] @ fv_prop _tprop2) @ fv_prop _tprop1) @ fv_prop _tprop0
  | Not _tprop0 -> [] @ fv_prop _tprop0
  | And _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Or _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Iff (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Forall { qv; body } ->
      Zdatatype.List.substract (eq_typed String.equal)
        ([] @ fv_prop body)
        [ qv ]
  | Exists { qv; body } ->
      Zdatatype.List.substract (eq_typed String.equal)
        ([] @ fv_prop body)
        [ qv ]

and typed_fv_prop (prop_e : ('t, 't prop) typed) = fv_prop prop_e.x

let rec subst_prop (string_x : string) f (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_subst_lit string_x f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite
        ( subst_prop string_x f _tprop0,
          subst_prop string_x f _tprop1,
          subst_prop string_x f _tprop2 )
  | Not _tprop0 -> Not (subst_prop string_x f _tprop0)
  | And _tproplist0 -> And (List.map (subst_prop string_x f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (subst_prop string_x f) _tproplist0)
  | Iff (_tprop0, _tprop1) ->
      Iff (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Forall { qv; body } ->
      if String.equal qv.x string_x then Forall { qv; body }
      else Forall { qv; body = subst_prop string_x f body }
  | Exists { qv; body } ->
      if String.equal qv.x string_x then Exists { qv; body }
      else Exists { qv; body = subst_prop string_x f body }

and typed_subst_prop (string_x : string) f (prop_e : ('t, 't prop) typed) =
  (subst_prop string_x f) #-> prop_e

let rec map_prop (f : 't -> 's) (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_map_lit f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (map_prop f _tprop0, map_prop f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite (map_prop f _tprop0, map_prop f _tprop1, map_prop f _tprop2)
  | Not _tprop0 -> Not (map_prop f _tprop0)
  | And _tproplist0 -> And (List.map (map_prop f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (map_prop f) _tproplist0)
  | Iff (_tprop0, _tprop1) -> Iff (map_prop f _tprop0, map_prop f _tprop1)
  | Forall { qv; body } -> Forall { qv = f #=> qv; body = map_prop f body }
  | Exists { qv; body } -> Exists { qv = f #=> qv; body = map_prop f body }

and typed_map_prop (f : 't -> 's) (prop_e : ('t, 't prop) typed) =
  (map_prop f) #-> (f #=> prop_e)

let fv_prop_id e = fv_typed_id_to_id fv_prop e
let typed_fv_prop_id e = fv_typed_id_to_id typed_fv_prop e

let subst_prop_instance x instance e =
  subst_f_to_instance subst_prop x instance e

let typed_subst_prop_instance x instance e =
  subst_f_to_instance typed_subst_prop x instance e
(* Generated from _prop.ml *)

(* force *)
let prop_force_typed_lit_opt prop =
  match prop with Lit lit -> Some lit | _ -> None

let rec get_cbool prop =
  match prop with
  | Lit { x = AC (B b); _ } -> Some b
  | Not p ->
      let* p = get_cbool p in
      Some p
  | _ -> None

let smart_not prop =
  match get_cbool prop with
  | Some p -> Lit (AC (B (not p))) #: Nt.Ty_bool
  | None -> ( match prop with Not p -> p | _ -> Not prop)

let mk_true = Lit (AC (B true)) #: Nt.Ty_bool
let mk_false = Lit (AC (B false)) #: Nt.Ty_bool
let is_true p = match get_cbool p with Some true -> true | _ -> false
let is_false p = match get_cbool p with Some false -> true | _ -> false

open Zdatatype

let unfold_and prop =
  let rec aux = function
    | [] -> []
    | And l :: l' -> aux (l @ l')
    | prop :: l' -> prop :: aux l'
  in
  let l = aux prop in
  List.slow_rm_dup eq_prop l

let smart_and l =
  let l = unfold_and l in
  if List.exists is_false l then mk_false
  else
    match List.filter (fun p -> not (is_true p)) l with
    | [] -> mk_true
    | [ x ] -> x
    | l -> And l

let unfold_or prop =
  let rec aux = function
    | [] -> []
    | Or l :: l' -> aux (l @ l')
    | prop :: l' -> prop :: aux l'
  in
  let l = aux prop in
  List.slow_rm_dup eq_prop l

let smart_or l =
  let l = unfold_or l in
  if List.exists is_true l then mk_true
  else
    match List.filter (fun p -> not (is_false p)) l with
    | [] -> mk_false
    | [ x ] -> x
    | l -> Or l

let smart_add_to (a : 't prop) (prop : 't prop) =
  match get_cbool a with
  | Some true -> prop
  | Some false -> mk_false
  | None -> (
      match prop with
      | And props -> smart_and (a :: props)
      | _ -> smart_and [ a; prop ])

let smart_implies a prop =
  match get_cbool a with
  | Some true -> prop
  | Some false -> mk_true
  | None -> Implies (a, prop)

let smart_forall qvs prop =
  List.fold_right (fun qv body -> Forall { qv; body }) qvs prop

let smart_exists qvs prop =
  List.fold_right (fun qv body -> Exists { qv; body }) qvs prop

let get_lits prop =
  let rec aux e res =
    match e with
    | Lit { x = AC _; _ } -> res
    | Lit lit -> (
        let litopt = get_non_unit_lit lit in
        match litopt with None -> res | Some lit -> lit :: res)
    | Implies (e1, e2) -> aux e1 @@ aux e2 res
    | Ite (e1, e2, e3) -> aux e1 @@ aux e2 @@ aux e3 res
    | Not e -> aux e res
    | And es -> List.fold_right aux es res
    | Or es -> List.fold_right aux es res
    | Iff (e1, e2) -> aux e1 @@ aux e2 res
    | Forall _ -> _die [%here]
    | Exists _ -> _die [%here]
  in
  let (lits : Nt.t lit list) = aux prop [] in
  (* let () = *)
  (*   Printf.printf ">>>>> get_lits: %s\n" *)
  (*     (List.split_by_comma layout_sexp_lit lits) *)
  (* in *)
  Zdatatype.List.slow_rm_dup eq_lit lits

let build_euf vars =
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux ty vars =
    let pairs = List.combination_l vars 2 in
    let eqlits =
      List.map
        (fun l ->
          match l with [ x; y ] -> mk_lit_eq_lit ty x y | _ -> _die [%here])
        pairs
    in
    eqlits
  in
  let res =
    Hashtbl.fold
      (fun ty vars res ->
        if
          List.length vars > 1 && not (Nt.equal_nt ty (Nt.Ty_uninter "Bytes.t"))
        then aux ty vars @ res
        else res)
      space []
  in
  res

(** sevent *)

(* subst *)

(* normalize name *)

(* let normalize_name = function *)
(*   | GuardEvent { vs; phi } -> *)
(*       let vs' = vs_names (List.length vs) in *)
(*       let tmp = _safe_combine [%here] vs vs' in *)
(*       let phi = *)
(*         List.fold_left *)
(*           (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi) *)
(*           phi tmp *)
(*       in *)
(*       let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in *)
(*       GuardEvent { vs; phi } *)
(*   | EffEvent { op; vs; phi } -> *)
(*       let vs' = vs_names (List.length vs) in *)
(*       let tmp = _safe_combine [%here] vs vs' in *)
(*       let phi = *)
(*         List.fold_left *)
(*           (fun phi (x', x) -> subst_prop_instance x'.x (AVar x #: x'.ty) phi) *)
(*           phi tmp *)
(*       in *)
(*       let vs = List.map (fun (x', x) -> x #: x'.ty) tmp in *)
(*       EffEvent { op; vs; phi } *)

(* gather lits *)
(** For Nt.t typed*)

open Zdatatype

type gathered_lits = {
  global_lits : Nt.t lit list;
  local_lits : ((Nt.t, string) typed list * Nt.t lit list) StrMap.t;
}

let gathered_lits_init () = { global_lits = []; local_lits = StrMap.empty }

let gathered_rm_dup { global_lits; local_lits } =
  let global_lits = List.slow_rm_dup eq_lit global_lits in
  let local_lits =
    StrMap.map (fun (vs, lits) -> (vs, List.slow_rm_dup eq_lit lits)) local_lits
  in
  { global_lits; local_lits }

let rec get_consts_from_lit = function
  | AAppOp (_, args) -> List.concat_map get_consts_from_typed_lit args
  | AC c -> [ c ]
  | _ -> []

and get_consts_from_typed_lit lit = get_consts_from_lit lit.x

let get_consts prop =
  let lits = get_lits prop in
  let cs = List.concat_map get_consts_from_lit lits in
  List.slow_rm_dup equal_constant cs

let lit_to_nt = function
  | AC c -> constant_to_nt c
  | AAppOp (op, _) -> snd @@ Nt.destruct_arr_tp op.ty
  | AVar x -> x.ty
  | _ -> _die [%here]

let lit_to_prop lit = Lit lit #: (lit_to_nt lit)
let msubst f = List.fold_right (fun (x, lit) -> f x lit)
let subst_name_qv x z y = if y.x == x then z else y

let to_conjs prop =
  let rec aux = function And l -> List.concat_map aux l | _ as r -> [ r ] in
  aux prop

let to_lit_opt = function Lit lit -> Some lit.x | _ -> None
let is_var_c = function AVar _ | AC _ -> true | _ -> false

let simp_eq_lit lit =
  match lit with
  | AAppOp (op, [ a; b ]) when String.equal eq_op op.x ->
      if equal_lit Nt.equal_nt a.x b.x then AC (B true) else lit
  | _ -> lit

let simpl_eq_in_prop =
  let rec aux = function
    | Lit lit -> Lit (simp_eq_lit lit.x) #: lit.ty
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not p ->
        let p = aux p in
        if is_true p then mk_false else if is_false p then mk_true else Not p
    | And es -> smart_and (List.map aux es)
    | Or es -> smart_or (List.map aux es)
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Forall { qv; body } -> Forall { qv; body = aux body }
    | Exists { qv; body } -> Exists { qv; body = aux body }
  in
  aux

let tv_mem vs qv = List.exists (fun x -> String.equal x.x qv.x) vs
let tv_not_mem vs qv = not (tv_mem vs qv)
let tv_to_lit x = (AVar x) #: x.ty
let c_to_lit c = (AC c) #: (constant_to_nt c)
