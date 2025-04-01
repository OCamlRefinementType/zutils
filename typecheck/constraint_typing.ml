open Prop
open Sugar
open Typectx
open Zdatatype

type t = Nt.t

module BC = Normalty.BoundConstraints

let mk_constraint ty (bc, x') =
  if Nt.is_unkown ty then (bc, x')
  else
    let bc, (ty, _) = BC.add bc (ty, x'.ty) in
    (bc, x'.x#:ty)

let constraint_id_type_infer (ctx : t ctx) (bc : BC.bc) (x : string) =
  match get_opt ctx x with
  | None -> _die_with [%here] (spf "variable %s is free" x)
  | Some ty ->
      let bc, ty = BC.add_type bc ty in
      (bc, x#:ty)

let constraint_id_type_check (ctx : t ctx) (bc : BC.bc) (x : (t, string) typed)
    =
  let bc, x' = constraint_id_type_infer ctx bc x.x in
  mk_constraint x.ty (bc, x')

let constraint_op_type_infer (ctx : t ctx) (bc : BC.bc) (op : op) =
  let res =
    match op with
    | PrimOp id ->
        let id =
          match get_opt ctx id with
          | None -> _die_with [%here] (spf "variable %s is free" id)
          | Some ty -> id#:ty
        in
        (PrimOp id.x)#:id.ty
    | DtConstructor id ->
        (* let _ = Printf.printf "op: %s\n" id in *)
        let name = dt_name_for_typectx id in
        let name =
          match get_opt ctx name with
          | None -> _die_with [%here] (spf "variable %s is free" name)
          | Some ty -> name#:ty
        in
        (DtConstructor id)#:name.ty
  in
  let bc, ty = BC.add_type bc res.ty in
  (bc, res.x#:ty)

let constraint_op_type_check (ctx : t ctx) (bc : BC.bc) (op : (t, op) typed) =
  let bc, op' = constraint_op_type_infer ctx bc op.x in
  mk_constraint op.ty (bc, op')

let rec constraint_lit_type_infer (ctx : t ctx) (bc : BC.bc) (lit : t lit) =
  match lit with
  | AVar id ->
      let bc, id' = constraint_id_type_check ctx bc id in
      (bc, (AVar id')#:id'.ty)
  | AC c -> (bc, (AC c)#:(Normal_constant_typing.infer_constant c))
  | ATu l ->
      let bc, l = constraint_lits_type_check ctx bc l in
      (bc, (ATu l)#:(Nt.Ty_tuple (List.map _get_ty l)))
  | AProj (y, n) -> (
      let cs, y = constraint_lit_type_check ctx bc y in
      match y.ty with
      | Nt.Ty_tuple l -> (cs, (AProj (y, n))#:(List.nth l n))
      | _ ->
          _die_with [%here]
          @@ spf "%s has type %s which is not a tuple type" (layout_lit y.x)
               (Nt.show_nt y.ty))
  | AAppOp (mp, args) ->
      let bc, mp = constraint_id_type_check ctx bc mp in
      let bc, args = constraint_lits_type_check ctx bc args in
      let bc, retty = BC.fresh bc in
      let mp_ty = Nt.construct_arr_tp (List.map _get_ty args, retty) in
      let bc, _ = BC.add bc (mp_ty, mp.ty) in
      (bc, (AAppOp (mp.x#:mp_ty, args))#:retty)

and constraint_lits_type_check (ctx : t ctx) (bc : BC.bc)
    (lits : (t, t lit) typed list) =
  match lits with
  | [] -> (bc, [])
  | lit :: lits ->
      let bc, lits = constraint_lits_type_check ctx bc lits in
      let bc, lit = constraint_lit_type_check ctx bc lit in
      (bc, lit :: lits)

and constraint_lit_type_check (ctx : t ctx) (bc : BC.bc)
    (lit : (t, t lit) typed) =
  (* (\* HACK: we don't do type check when a literal is typed *\) *)
  (* if Nt.is_unkown lit.ty then *)
  mk_constraint lit.ty (constraint_lit_type_infer ctx bc lit.x)
(* else (bc, lit) *)

let lit_type_check (ctx : t ctx) (poly_vars : string list)
    (lit : (t, t lit) typed) =
  let bc, lit = constraint_lit_type_check ctx (BC.empty poly_vars) lit in
  let solution = Normalty.type_unification StrMap.empty bc.cs in
  match solution with
  | None ->
      Printf.printf "bc\n%s\nlit:%s" (BC.layout bc) (layout_lit lit.x);
      _die_with [%here] "lit normal type errpr"
  | Some sol -> typed_map_lit (Normalty.msubst_nt sol) lit

let prop_type_check (ctx : t ctx) (poly_vars : string list) (prop : t prop) =
  let rec aux ctx prop =
    match prop with
    | Lit lit -> Lit (lit_type_check ctx poly_vars lit.x#:Nt.bool_ty)
    | Implies (e1, e2) -> Implies (aux ctx e1, aux ctx e2)
    | Ite (e1, e2, e3) -> Ite (aux ctx e1, aux ctx e2, aux ctx e3)
    | Not e -> Not (aux ctx e)
    | And es -> And (List.map (aux ctx) es)
    | Or es -> Or (List.map (aux ctx) es)
    | Iff (e1, e2) -> Iff (aux ctx e1, aux ctx e2)
    | Forall { qv; body } ->
        let qv = Nt.__force_typed [%here] qv in
        Forall { qv; body = aux (add_to_right ctx qv) body }
    | Exists { qv; body } ->
        let qv = Nt.__force_typed [%here] qv in
        Exists { qv; body = aux (add_to_right ctx qv) body }
  in
  aux ctx prop
