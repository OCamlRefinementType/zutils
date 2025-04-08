open Sugar
open Ast

let subst_nt (id, t') t =
  let rec aux t =
    match t with
    | Ty_unknown -> t
    | Ty_var x -> if streq x id then t' else t
    | Ty_poly (y, nt) ->
        if String.equal id y then Ty_poly (y, nt) else Ty_poly (y, aux nt)
    | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
    | Ty_tuple xs -> Ty_tuple (List.map aux xs)
    | Ty_constructor (id, args) -> Ty_constructor (id, List.map aux args)
    | Ty_record { alias; fds } ->
        Ty_record { alias; fds = List.map (fun x -> x#=>aux) fds }
  in
  aux t

let subst_constructor_nt (name, f) t =
  let rec aux t =
    match t with
    | Ty_unknown | Ty_var _ -> t
    | Ty_poly (y, nt) -> Ty_poly (y, aux nt)
    | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
    | Ty_tuple xs -> Ty_tuple (List.map aux xs)
    | Ty_constructor (id, args) ->
        let args = List.map aux args in
        if String.equal id name then f args else Ty_constructor (id, args)
    | Ty_record { alias; fds } ->
        Ty_record { alias; fds = List.map (fun x -> x#=>aux) fds }
  in
  aux t

open Zdatatype

let msubst_nt (m : t StrMap.t) = StrMap.fold (fun x ty -> subst_nt (x, ty)) m
let subst_on_sol (i, t) m = StrMap.map (subst_nt (i, t)) m
let subst_on_cs (i, t) cs = List.map (map2 (subst_nt (i, t))) cs
