open Prop
open Sugar
open Typectx
open Zdatatype

let _unify_opt loc t1 t2 =
  match t1 with None -> t2 | Some t1 -> Nt._type_unify loc t1 t2

type t = Nt.t

let bi_typed_id_infer (ctx : t ctx) (x : (t, string) typed) : (t, string) typed
    =
  let ty = match get_opt ctx x.x with None -> Nt.Ty_unknown | Some ty -> ty in
  try { ty = Nt._type_unify [%here] ty x.ty; x = x.x }
  with e ->
    let _ =
      Printf.printf "typectx: %s\n"
        (List.split_by_comma (fun x -> spf "%s:%s" x.x (Nt.layout x.ty))
        @@ ctx_to_list ctx)
    in
    let _ = Printf.printf "type error at %s\n" x.x in
    raise e

let bi_typed_id_check (ctx : t ctx) (x : (t, string) typed) (ty : t) :
    (t, string) typed =
  let x = bi_typed_id_infer ctx x in
  let ty = Nt._type_unify [%here] x.ty ty in
  { ty; x = x.x }
