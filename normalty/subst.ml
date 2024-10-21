open Sugar
open Ast

let subst_nt (id, t') t =
  let rec aux t =
    match t with
    | Ty_unknown | Ty_any | Ty_unit | Ty_int | Ty_nat | Ty_bool | Ty_uninter _
    | Ty_enum _ ->
        t
    | Ty_var x -> if streq x id then t' else t
    | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
    | Ty_tuple xs -> Ty_tuple (List.map aux xs)
    | Ty_constructor (id, args) -> Ty_constructor (id, List.map aux args)
    | Ty_record l -> Ty_record (List.map (( #=> ) aux) l)
  in

  aux t

open Zdatatype

let msubst_nt (m : t StrMap.t) = StrMap.fold (fun x ty -> subst_nt (x, ty)) m
let subst_on_sol (i, t) m = StrMap.map (subst_nt (i, t)) m
let subst_on_cs (i, t) cs = List.map (map2 (subst_nt (i, t))) cs
