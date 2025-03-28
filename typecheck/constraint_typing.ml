open Prop
open Sugar
open Typectx
open Zdatatype

type t = Nt.t

let fresh_type_var () = Nt.Ty_var (Rename.unique "__tvar")

let mk_constraint ty (cs, x') =
  if Nt.is_unkown ty then (cs, x') else ((ty, x'.ty) :: cs, x'.x#:ty)

let constraint_id_type_infer (ctx : t ctx) (x : string) =
  match get_opt ctx x with
  | None -> _die_with [%here] (spf "variable %s is free" x)
  | Some ty -> x#:ty

let constraint_id_type_check (ctx : t ctx) (x : (t, string) typed) =
  let x' = constraint_id_type_infer ctx x.x in
  mk_constraint x.ty ([], x')

let constraint_op_type_infer (ctx : t ctx) (op : op) =
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

let constraint_op_type_check (ctx : t ctx) (op : (t, op) typed) =
  let op' = constraint_op_type_infer ctx op.x in
  mk_constraint op.ty ([], op')

let rec constraint_lit_type_infer (ctx : t ctx) (lit : t lit) =
  match lit with
  | AVar id ->
      let cs, id' = constraint_id_type_check ctx id in
      (cs, (AVar id')#:id'.ty)
  | AC c -> ([], (AC c)#:(Normal_constant_typing.infer_constant c))
  | ATu l ->
      let css, l = List.split @@ List.map (constraint_lit_type_check ctx) l in
      let lit' = (ATu l)#:(Nt.Ty_tuple (List.map _get_ty l)) in
      (List.concat css, lit')
  | AProj (y, n) -> (
      let cs, y = constraint_lit_type_check ctx y in
      match y.ty with
      | Nt.Ty_tuple l -> (cs, (AProj (y, n))#:(List.nth l n))
      | _ ->
          _die_with [%here]
          @@ spf "%s has type %s which is not a tuple type" (layout_lit y.x)
               (Nt.show_nt y.ty))
  | AAppOp (mp, args) ->
      let cs, mp = constraint_id_type_check ctx mp in
      let css, args =
        List.split @@ List.map (constraint_lit_type_check ctx) args
      in
      let retty = fresh_type_var () in
      let cs =
        (mp.ty, Nt.construct_arr_tp (List.map _get_ty args, retty))
        :: List.concat (cs :: css)
      in
      (cs, (AAppOp (mp, args))#:retty)

and constraint_lit_type_check (ctx : t ctx) (lit : (t, t lit) typed) =
  (* HACK: we don't do type check when a literal is typed *)
  if Nt.is_unkown lit.ty then
    mk_constraint lit.ty (constraint_lit_type_infer ctx lit.x)
  else ([], lit)

let lit_type_check (ctx : t ctx) (lit : (t, t lit) typed) =
  let cs, lit = constraint_lit_type_check ctx lit in
  let cs = (Nt.bool_ty, lit.ty) :: cs in
  let solution = Normalty.type_unification StrMap.empty cs in
  match solution with
  | None -> _die_with [%here] "lit normal type errpr"
  | Some sol -> typed_map_lit (Normalty.msubst_nt sol) lit

let prop_type_check (ctx : t ctx) (prop : t prop) =
  let rec aux ctx prop =
    match prop with
    | Lit lit -> Lit (lit_type_check ctx lit)
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
