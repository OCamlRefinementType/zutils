open Sugar
open Ast
open Zdatatype
open Subst

let type_unification_v2 m (cs : (t * t) list) =
  let rec aux m cs =
    match cs with
    | [] -> Some m
    | (t1, t2) :: cs -> (
        match (t1, t2) with
        | Ty_any, _ | _, Ty_any | Ty_unknown, _ | _, Ty_unknown -> aux m cs
        | Ty_enum _, Ty_enum _ -> aux m cs
        | Ty_var n, _ ->
            let m = subst_on_sol (n, t2) m in
            let cs = subst_on_cs (n, t2) cs in
            aux (StrMap.add n t2 m) cs
        | _, Ty_var n ->
            let m = subst_on_sol (n, t1) m in
            let cs = subst_on_cs (n, t1) cs in
            aux (StrMap.add n t1 m) cs
        | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
            if String.equal id1 id2 && List.length ts1 == List.length ts2 then
              aux m (List.combine ts1 ts2 @ cs)
            else None
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
                  | None -> _die_with [%here] (spf "connot find feild %s" x.x)
                  | Some t' -> (t', x.ty) :: res)
                cs l2
            in
            aux m cs
        | _, _ -> if equal_nt t1 t2 then aux m cs else None)
  in
  aux m cs

open Zdatatype

let __type_unify_ (pprint : t -> string) loc m t1 t2 =
  (* let () = Printf.printf "unify %s --> %s\n" (layout t1) (layout t2) in *)
  let rec unify m (t1, t2) =
    let t1, t2 = map2 (msubst_nt m) (t1, t2) in
    (* let () = Printf.printf "one %s --> %s\n" (layout t1) (layout t2) in *)
    match (t1, t2) with
    | Ty_unknown, Ty_unknown -> _die_with loc "unknown type"
    | Ty_any, _ -> (m, t2)
    | Ty_unknown, _ -> (m, t2)
    | Ty_var n, t2 -> (
        match StrMap.find_opt m n with
        | Some _ -> _die [%here]
        | None -> (StrMap.add n t2 m, t2))
    | Ty_enum { enum_elems = []; _ }, Ty_enum { enum_elems = []; _ } ->
        _die [%here]
    | _, Ty_enum { enum_elems = []; _ } -> (m, t1)
    | Ty_enum { enum_elems = []; _ }, _ -> (m, t2)
    (* | Ty_enum _, Ty_enum _ -> *)
    | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
        let id = _check_equality loc String.equal id1 id2 in
        let m, ts =
          List.fold_left
            (fun (m, ts) (t1, t2) ->
              let m, t = unify m (t1, t2) in
              (m, ts @ [ t ]))
            (m, []) (List.combine ts1 ts2)
        in
        (m, Ty_constructor (id, ts))
    | Ty_arrow (t11, t12), Ty_arrow (t21, t22) ->
        let m, t1 = unify m (t11, t21) in
        let m, t2 = unify m (t12, t22) in
        (m, Ty_arrow (t1, t2))
    (* unfold singleton tuple *)
    | Ty_tuple [ t1 ], _ -> unify m (t1, t2)
    | _, Ty_tuple [ t2 ] -> unify m (t1, t2)
    | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 ->
        let m, ts =
          List.fold_left
            (fun (m, ts) (t1, t2) ->
              let m, t = unify m (t1, t2) in
              (m, ts @ [ t ]))
            (m, []) (List.combine ts1 ts2)
        in
        (m, Ty_tuple ts)
    | Ty_record l1, Ty_record l2 when List.length l1 == List.length l2 ->
        let tab = Hashtbl.create (List.length l1) in
        let () = List.iter (fun x -> Hashtbl.add tab x.x x.ty) l1 in
        let m, l =
          List.fold_left
            (fun (m, l) x ->
              match Hashtbl.find_opt tab x.x with
              | None -> _die_with [%here] (spf "connot find feild %s" x.x)
              | Some t' ->
                  let m, t = unify m (t', x.ty) in
                  (m, (x #+ t) :: l))
            (m, []) l2
        in
        (m, Ty_record l)
    | _, Ty_any -> (m, t1)
    | _, Ty_unknown -> (m, t1)
    | _, Ty_var _ ->
        (* (m, t1) *)
        _die_with loc "argment should not contain type var"
    | _, _ ->
        ( m,
          try _check_equality loc equal_nt t1 t2
          with e ->
            Printf.printf "%s != %s\n" (show_nt t1) (show_nt t2);
            raise e )
  in
  try unify m (t1, t2)
  with e ->
    Printf.printf "Type unify error: %s ==> %s\n" (pprint t1) (pprint t2);
    Printf.printf "Precisely: %s ==> %s\n" (show_nt t1) (show_nt t2);
    raise e

let __type_unify_v1 pprint loc t1 t2 =
  match snd @@ __type_unify_ pprint loc StrMap.empty t1 t2 with
  | Ty_unknown -> _die_with loc "still unknown type"
  | _ as ty -> ty

let __type_unify_v2 (pprint : t -> string) loc t1 t2 =
  let m = type_unification_v2 StrMap.empty [ (t1, t2) ] in
  let error_print () =
    Printf.printf "Type unify error: %s ==> %s\n" (pprint t1) (pprint t2);
    _die_with loc "normal type check error"
  in
  match m with
  | Some m ->
      let t1, t2 = map2 (msubst_nt m) (t1, t2) in
      __type_unify_v1 pprint loc t1 t2
  (* if not (eq t1 t2) then ( *)
  (*   Printf.printf "Precisely: %s ==> %s\n" (layout t1) (layout t2); *)
  (*   error_print ()) *)
  (* else t2 *)
  | None -> error_print ()

let __type_unify = __type_unify_v2
