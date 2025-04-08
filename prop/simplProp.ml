open Syntax
open Sugar
open Zdatatype

(** Simplify Query *)

let lit_is_var_by_name x lit =
  match lit.x with AVar a when String.equal a.x x -> true | _ -> false

let find_eq_lit_in_prop (x : string) (query : Nt.t prop) =
  let rec aux prop =
    match prop with
    | Lit lit -> (
        if lit_is_var_by_name x lit then Some mk_lit_true#:lit.ty
        else
          match lit.x with
          | AAppOp (op, [ a; b ]) when String.equal op.x eq_op ->
              if lit_is_var_by_name x a then Some b
              else if lit_is_var_by_name x b then Some a
              else None
          | _ -> None)
    | Not (Lit lit) ->
        if lit_is_var_by_name x lit then Some mk_lit_false#:lit.ty else None
    | Iff (Lit a, Lit b) ->
        if lit_is_var_by_name x a then Some b
        else if lit_is_var_by_name x b then Some a
        else None
    | Iff _ -> None
    | And l -> (
        match List.filter_map aux l with
        | [] -> None
        | x :: _ ->
            Some x
            (* | _ as l -> *)
            (*     let () = *)
            (*       Printf.printf "Find eq %s: %s\n" x *)
            (*         (List.split_by_comma Front.layout_typed_lit l) *)
            (*     in *)
            (*     _die [%here] *))
    | Exists { body; _ } -> aux body
    | Implies (_, e2) -> aux e2
    | Ite _ | Not _ | Or _ | Forall _ -> None
  in
  aux query

let simpl_no_used_quantifiers =
  let rec aux prop =
    match prop with
    | Exists { body; qv } ->
        let body = aux body in
        let fv = fv_prop body in
        if List.exists (fun y -> String.equal qv.x y.x) fv then
          Exists { body; qv }
        else body
    | Forall { body; qv } ->
        let body = aux body in
        let fv = fv_prop body in
        if List.exists (fun y -> String.equal qv.x y.x) fv then
          Forall { body; qv }
        else body
    | And l -> smart_and (List.map aux l)
    | Or l -> smart_or (List.map aux l)
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Lit _ -> prop
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
  in
  aux

let instantiate_quantified_bool =
  let rec aux prop =
    match prop with
    | Exists { body; qv } ->
        let body = aux body in
        if Nt.equal_nt qv.ty Nt.bool_ty then
          let body_true = subst_prop_instance qv.x mk_lit_true body in
          let body_false = subst_prop_instance qv.x mk_lit_false body in
          (* let () = Printf.printf "body_true: %s\n" @@ Front.layout body_true in *)
          (* let () = *)
          (*   Printf.printf "body_false: %s\n" @@ Front.layout body_false *)
          (* in *)
          (* let () = *)
          (*   Printf.printf "or: %s\n" *)
          (*   @@ Front.layout (smart_or [ body_true; body_false ]) *)
          (* in *)
          simpl_eq_in_prop (smart_or [ body_true; body_false ])
        else Exists { body; qv }
    | Forall { body; qv } ->
        let body = aux body in
        if Nt.equal_nt qv.ty Nt.bool_ty then
          let body_true = subst_prop_instance qv.x mk_lit_true body in
          let body_false = subst_prop_instance qv.x mk_lit_false body in
          simpl_eq_in_prop (smart_and [ body_true; body_false ])
        else Forall { body; qv }
    | And l -> smart_and (List.map aux l)
    | Or l -> smart_or (List.map aux l)
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Lit _ -> prop
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
  in
  aux

(* let instantiate_quantified_tuple_by_elems = *)
(*   let destruct_qv qv = *)
(*     match qv.ty with *)
(*     | Nt.Ty_tuple l -> *)
(*         let qvs = List.mapi (fun i ty -> (i, (spf "%s!%i" qv.x)#:ty)) l in *)
(*         Some qvs *)
(*     | _ -> None *)
(*   in *)
(*   let inline_proj_in_lit (qv, lits) lit = *)
(*     let rec aux lit = *)
(*       let res = *)
(*         match lit.x with *)
(*         | AC _ -> lit *)
(*         | AVar _ when lit_is_var_by_name qv.x lit -> _die [%here] *)
(*         | AVar _ -> lit *)
(*         | ATu l -> ATu (List.map aux l) *)
(*         | AProj (lit, i) when lit_is_var_by_name qv.x lit -> List.nth lits i *)
(*         | ARecord l -> ARecord (List.map (fun (x, lit) -> (x, aux lit)) l) *)
(*         | AField (lit, x) -> AField (aux lit, x) *)
(*         | AAppOp (f, args) -> AAppOp (f, List.map aux args) *)
(*       in *)
(*       res#:lit.ty *)
(*     in *)
(*     aux lit *)
(*   in *)
(*   let rec aux prop = *)
(*     match prop with *)
(*     | Exists { body; qv } -> *)
(*         let body = aux body in *)
(*         let fv = fv_prop body in *)
(*         if List.exists (fun y -> String.equal qv.x y.x) fv then *)
(*           Exists { body; qv } *)
(*         else body *)
(*     | Forall { body; qv } -> *)
(*         let body = aux body in *)
(*         let fv = fv_prop body in *)
(*         if List.exists (fun y -> String.equal qv.x y.x) fv then *)
(*           Exists { body; qv } *)
(*         else body *)
(*     | And l -> smart_and (List.map aux l) *)
(*     | Or l -> smart_or (List.map aux l) *)
(*     | Implies (e1, e2) -> Implies (aux e1, aux e2) *)
(*     | Lit _ -> prop *)
(*     | Iff (e1, e2) -> Iff (aux e1, aux e2) *)
(*     | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3) *)
(*     | Not e -> Not (aux e) *)
(*   in *)
(*   aux *)

(* let instantiate_quantified_tuple_by_elems = *)
(*   let destruct_qv qv = *)
(*     match qv.ty with *)
(*     | Nt.Ty_tuple l -> *)
(*         let qvs = List.mapi (fun i ty -> (i, (spf "%s!%i" qv.x)#:ty)) l in *)
(*         Some qvs *)
(*     | Nt.Ty_record l -> *)
(*         let qvs = List.map (fun x -> (x.x, (spf "%s!%i" x.x)#:x.ty)) l in *)
(*         Some qvs *)
(*     | _ -> None *)
(*   in *)
(*   (\* let inline_proj (qv, l)  *\) *)
(*   let rec aux prop = *)
(*     match prop with *)
(*     | Exists { body; qv } -> *)
(*         let body = aux body in *)
(*         let fv = fv_prop body in *)
(*         if List.exists (fun y -> String.equal qv.x y.x) fv then *)
(*           Exists { body; qv } *)
(*         else body *)
(*     | Forall { body; qv } -> *)
(*         let body = aux body in *)
(*         let fv = fv_prop body in *)
(*         if List.exists (fun y -> String.equal qv.x y.x) fv then *)
(*           Exists { body; qv } *)
(*         else body *)
(*     | And l -> smart_and (List.map aux l) *)
(*     | Or l -> smart_or (List.map aux l) *)
(*     | Implies (e1, e2) -> Implies (aux e1, aux e2) *)
(*     | Lit _ -> prop *)
(*     | Iff (e1, e2) -> Iff (aux e1, aux e2) *)
(*     | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3) *)
(*     | Not e -> Not (aux e) *)
(*   in *)
(*   aux *)

let simpl_query_by_eq (query : Nt.t prop) =
  let rec aux prop =
    match prop with
    | Exists { body; qv } -> (
        let body = aux body in
        match find_eq_lit_in_prop qv.x body with
        | None -> Exists { body; qv }
        | Some lit ->
            let body = subst_prop_instance qv.x lit.x body in
            let body = simpl_eq_in_prop body in
            let body = simpl_no_used_quantifiers body in
            body)
    | Forall { body; qv } -> Forall { body = aux body; qv }
    | And l -> smart_and (List.map aux l)
    | Or l -> smart_or (List.map aux l)
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Lit _ -> prop
    | Iff (e1, e2) -> Iff (aux e1, aux e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
  in
  let query = simpl_no_used_quantifiers @@ simpl_eq_in_prop query in
  aux query

let eval_arithmetic_in_lit =
  let rec aux lit =
    match lit.x with
    | AC _ | AVar _ | ATu _ | AProj _ | ARecord _ | AField _ -> lit
    | AAppOp (f, args) ->
        let const_to_lit c = (AC c)#:(constant_to_nt c) in
        let bool_to_lit c = const_to_lit (B c) in
        let int_to_lit c = const_to_lit (I c) in
        let args = List.map aux args in
        let res =
          match (f.x, List.map _get_x args) with
          | "==", [ AC a; AC b ] -> bool_to_lit (equal_constant a b)
          | "!=", [ AC a; AC b ] -> bool_to_lit (not (equal_constant a b))
          | "<=", [ AC (I a); AC (I b) ] -> bool_to_lit (a <= b)
          | ">=", [ AC (I a); AC (I b) ] -> bool_to_lit (a >= b)
          | "<", [ AC (I a); AC (I b) ] -> bool_to_lit (a < b)
          | ">", [ AC (I a); AC (I b) ] -> bool_to_lit (a > b)
          | "+", [ AC (I a); AC (I b) ] -> int_to_lit (a + b)
          | "+", [ AC (I 0); lit ] -> lit_to_tlit lit
          | "+", [ lit; AC (I 0) ] -> lit_to_tlit lit
          | "-", [ AC (I a); AC (I b) ] -> int_to_lit (a - b)
          | "-", [ lit; AC (I 0) ] -> lit_to_tlit lit
          | "mod", [ AC (I a); AC (I b) ] -> int_to_lit (a mod b)
          | "*", [ AC (I a); AC (I b) ] -> int_to_lit (a * b)
          | "/", [ AC (I a); AC (I b) ] -> int_to_lit (a / b)
          | _ -> (AAppOp (f, args))#:lit.ty
        in
        res
  in
  aux

let eval_arithmetic_in_lit prop =
  let rec aux prop =
    match prop with
    | Exists { body; qv } ->
        let body = aux body in
        Exists { body; qv }
    | Forall { body; qv } ->
        let body = aux body in
        Forall { body; qv }
    | And l -> smart_and (List.map aux l)
    | Or l -> smart_or (List.map aux l)
    | Implies (e1, e2) -> Implies (aux e1, aux e2)
    | Lit lit -> Lit (eval_arithmetic_in_lit lit)
    | Iff (e1, e2) ->
        let e1, e2 = map2 aux (e1, e2) in
        if equal_prop (fun _ _ -> true) e1 e2 then mk_true else Iff (e1, e2)
    | Ite (e1, e2, e3) -> Ite (aux e1, aux e2, aux e3)
    | Not e -> Not (aux e)
  in
  let res = aux prop in
  simpl_eq_in_prop res

let simpl_query q =
  let q = eval_arithmetic_in_lit q in
  let q = simpl_query_by_eq q in
  let q = instantiate_quantified_bool q in
  let q = eval_arithmetic_in_lit q in
  q
