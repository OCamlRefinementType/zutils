open Sugar
open Ast
open Zdatatype
open Subst

(* let _fresh_type_var () = Ty_var (Rename.unique "__tvar") *)

module BoundConstraints = struct
  type bc = { type_vars : unit StrMap.t; cs : (t * t) list }

  let exists vars p = StrMap.exists (fun y () -> String.equal p y) vars

  let uniquelize (vars, t) =
    let ps, t = _lift_poly_tp t in
    let rec aux vars (ps, t) =
      match ps with
      | [] -> (vars, t)
      | p :: ps ->
          if exists vars p then (
            let p' = Rename.unique p in
            _assert [%here]
              (spf "rename success: %s in [%s]" p'
                 (StrList.to_string (StrMap.to_key_list vars)))
              (not (exists vars p'));
            aux (StrMap.add p' () vars) (ps, subst_nt (p, Ty_var p') t))
          else aux (StrMap.add p () vars) (ps, t)
    in
    aux vars (ps, t)

  let add_type { type_vars; cs } t =
    let type_vars, t = uniquelize (type_vars, t) in
    ({ type_vars; cs }, t)

  let add bc (t1, t2) =
    let type_vars, t1 = uniquelize (bc.type_vars, t1) in
    let type_vars, t2 = uniquelize (type_vars, t2) in
    _assert [%here] "new poly type var"
      (StrMap.cardinal bc.type_vars == StrMap.cardinal type_vars);
    ({ bc with cs = (t1, t2) :: bc.cs }, (t1, t2))

  let fresh { type_vars; cs } =
    let x = Rename.unique "t" in
    (* let () = Printf.printf "fresh: %s\n" x in *)
    _assert [%here] "fresh var create success" (not (exists type_vars x));
    ({ type_vars = StrMap.add x () type_vars; cs }, Ty_var x)

  let empty vars =
    {
      type_vars = StrMap.from_kv_list (List.map (fun x -> (x, ())) vars);
      cs = [];
    }

  let layout bc =
    spf "type vars: %s;\n constraints: %s;\n"
      (StrList.to_string (StrMap.to_key_list bc.type_vars))
      (List.split_by ", "
         (fun (a, b) ->
           spf "%s = %s" (Frontend.layout_nt a) (Frontend.layout_nt b))
         bc.cs)
end

let type_unification m (cs : (t * t) list) =
  let rec aux m cs =
    match cs with
    | [] -> Some m
    | (t1, t2) :: cs -> (
        let err () =
          Printf.printf "cannot solve %s = %s\n" (Frontend.layout_nt t1)
            (Frontend.layout_nt t2);
          None
        in
        match (t1, t2) with
        | Ty_unknown, _ | _, Ty_unknown -> aux m cs
        | Ty_var n, Ty_var k ->
            if String.compare n k == 0 then aux m cs
            else if String.compare n k > 0 then
              let m = subst_on_sol (n, t2) m in
              let cs = subst_on_cs (n, t2) cs in
              aux (StrMap.add n t2 m) cs
            else aux m ((Ty_var k, Ty_var n) :: cs)
        | Ty_var n, _ ->
            if List.exists (String.equal n) @@ gather_type_vars t2 then err ()
            else
              let m = subst_on_sol (n, t2) m in
              let cs = subst_on_cs (n, t2) cs in
              aux (StrMap.add n t2 m) cs
        | _, Ty_var n ->
            if List.exists (String.equal n) @@ gather_type_vars t1 then err ()
            else
              let m = subst_on_sol (n, t1) m in
              let cs = subst_on_cs (n, t1) cs in
              aux (StrMap.add n t1 m) cs
        | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
            if String.equal id1 id2 && List.length ts1 == List.length ts2 then
              aux m (List.combine ts1 ts2 @ cs)
            else err ()
        | Ty_arrow (t11, t12), Ty_arrow (t21, t22) ->
            aux m ((t11, t21) :: (t12, t22) :: cs)
        (* unfold singleton tuple *)
        | Ty_tuple [ t1 ], _ -> aux m ((t1, t2) :: cs)
        | _, Ty_tuple [ t2 ] -> aux m ((t1, t2) :: cs)
        | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 ->
            aux m (List.combine ts1 ts2 @ cs)
        | Ty_record l1, Ty_record l2 ->
            let tab = Hashtbl.create (List.length l1) in
            let () = List.iter (fun x -> Hashtbl.add tab x.x x.ty) l1 in
            let cs =
              List.fold_left
                (fun res x ->
                  match Hashtbl.find_opt tab x.x with
                  | None -> _die_with [%here] (spf "cannot find feild %s" x.x)
                  | Some t' -> (t', x.ty) :: res)
                cs l2
            in
            aux m cs
        | _, _ -> if equal_nt t1 t2 then aux m cs else err ())
  in
  aux m cs

let unify_two_types_opt (poly_vars : string list) (t1, t2) =
  let bc, (t1, _) = BoundConstraints.(add (empty poly_vars) (t1, t2)) in
  let solution = type_unification StrMap.empty bc.cs in
  match solution with None -> None | Some sol -> Some (msubst_nt sol t1)

let unify_two_types loc (poly_vars : string list) (t1, t2) =
  match unify_two_types_opt poly_vars (t1, t2) with
  | None -> _die_with loc __FUNCTION__
  | Some t -> t

(* open Zdatatype *)

(* let __type_unify_ (pprint : t -> string) loc m t1 t2 = *)
(*   (\* let () = Printf.printf "unify %s --> %s\n" (layout t1) (layout t2) in *\) *)
(*   let rec unify m (t1, t2) = *)
(*     let t1, t2 = map2 (msubst_nt m) (t1, t2) in *)
(*     (\* let () = Printf.printf "one %s --> %s\n" (layout t1) (layout t2) in *\) *)
(*     match (t1, t2) with *)
(*     | Ty_unknown, Ty_unknown -> _die_with loc "unknown type" *)
(*     | Ty_any, _ -> (m, t2) *)
(*     | Ty_unknown, _ -> (m, t2) *)
(*     | Ty_var n, t2 -> ( *)
(*         match StrMap.find_opt m n with *)
(*         | Some _ -> _die [%here] *)
(*         | None -> (StrMap.add n t2 m, t2)) *)
(*     | Ty_enum { enum_elems = []; _ }, Ty_enum { enum_elems = []; _ } -> *)
(*         _die [%here] *)
(*     | _, Ty_enum { enum_elems = []; _ } -> (m, t1) *)
(*     | Ty_enum { enum_elems = []; _ }, _ -> (m, t2) *)
(*     (\* | Ty_enum _, Ty_enum _ -> *\) *)
(*     | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) -> *)
(*         let id = _check_equality loc String.equal id1 id2 in *)
(*         let m, ts = *)
(*           List.fold_left *)
(*             (fun (m, ts) (t1, t2) -> *)
(*               let m, t = unify m (t1, t2) in *)
(*               (m, ts @ [ t ])) *)
(*             (m, []) (List.combine ts1 ts2) *)
(*         in *)
(*         (m, Ty_constructor (id, ts)) *)
(*     | Ty_arrow (t11, t12), Ty_arrow (t21, t22) -> *)
(*         let m, t1 = unify m (t11, t21) in *)
(*         let m, t2 = unify m (t12, t22) in *)
(*         (m, Ty_arrow (t1, t2)) *)
(*     (\* unfold singleton tuple *\) *)
(*     | Ty_tuple [ t1 ], _ -> unify m (t1, t2) *)
(*     | _, Ty_tuple [ t2 ] -> unify m (t1, t2) *)
(*     | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 -> *)
(*         let m, ts = *)
(*           List.fold_left *)
(*             (fun (m, ts) (t1, t2) -> *)
(*               let m, t = unify m (t1, t2) in *)
(*               (m, ts @ [ t ])) *)
(*             (m, []) (List.combine ts1 ts2) *)
(*         in *)
(*         (m, Ty_tuple ts) *)
(*     | Ty_record l1, Ty_record l2 when List.length l1 == List.length l2 -> *)
(*         let tab = Hashtbl.create (List.length l1) in *)
(*         let () = List.iter (fun x -> Hashtbl.add tab x.x x.ty) l1 in *)
(*         let m, l = *)
(*           List.fold_left *)
(*             (fun (m, l) x -> *)
(*               match Hashtbl.find_opt tab x.x with *)
(*               | None -> _die_with [%here] (spf "connot find feild %s" x.x) *)
(*               | Some t' -> *)
(*                   let m, t = unify m (t', x.ty) in *)
(*                   (m, (x#+t) :: l)) *)
(*             (m, []) l2 *)
(*         in *)
(*         (m, Ty_record l) *)
(*     | _, Ty_any -> (m, t1) *)
(*     | _, Ty_unknown -> (m, t1) *)
(*     | _, Ty_var _ -> *)
(*         (\* (m, t1) *\) *)
(*         _die_with loc "argment should not contain type var" *)
(*     | _, _ -> *)
(*         ( m, *)
(*           try _check_equality loc equal_nt t1 t2 *)
(*           with e -> *)
(*             Printf.printf "%s != %s\n" (show_nt t1) (show_nt t2); *)
(*             raise e ) *)
(*   in *)
(*   try unify m (t1, t2) *)
(*   with e -> *)
(*     Printf.printf "Type unify error: %s ==> %s\n" (pprint t1) (pprint t2); *)
(*     Printf.printf "Precisely: %s ==> %s\n" (show_nt t1) (show_nt t2); *)
(*     raise e *)

(* let __type_unify_v1 pprint loc t1 t2 = *)
(*   match snd @@ __type_unify_ pprint loc StrMap.empty t1 t2 with *)
(*   | Ty_unknown -> _die_with loc "still unknown type" *)
(*   | _ as ty -> ty *)

(* let __type_unify_v2 (pprint : t -> string) loc t1 t2 = *)
(*   let m = type_unification_v2 StrMap.empty [ (t1, t2) ] in *)
(*   let error_print () = *)
(*     Printf.printf "Type unify error: %s ==> %s\n" (pprint t1) (pprint t2); *)
(*     _die_with loc "normal type check error" *)
(*   in *)
(*   match m with *)
(*   | Some m -> *)
(*       let t1, t2 = map2 (msubst_nt m) (t1, t2) in *)
(*       if equal_nt t1 t2 then t1 else error_print () *)
(*   | None -> error_print () *)

(* let __type_unify = __type_unify_v2 *)
