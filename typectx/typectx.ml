open Sugar
open Sexplib.Std

type 't ctx = Typectx of ('t, string) typed list
[@@deriving sexp, show, eq, ord]

let emp = Typectx []

let get_opt (type a) (ctx : a ctx) name =
  match ctx with
  | Typectx l ->
      let* x = List.find_opt (fun x -> String.equal name x.x) l in
      Some x.ty

let _get_force loc ctx name =
  match get_opt ctx name with
  | None -> _die_with loc (spf "cannot find %s in the ctx" name)
  | Some x -> x

let add_to_right (type a) (ctx : a ctx) ({ x; ty } : (a, string) typed) =
  match get_opt ctx x with
  | Some _ -> _die_with [%here] (spf "duplicate adding (%s) to ctx" x)
  | None -> ( match ctx with Typectx l -> Typectx (l @ [ { x; ty } ]))

open Zdatatype

let add_to_rights ctx l = List.fold_left add_to_right ctx l
let ctx_to_list ctx = match ctx with Typectx l -> l
let ctx_from_list l = add_to_rights emp l

let ctx_from_map m =
  add_to_rights emp (List.map typed_from_pair @@ StrMap.to_kv_list m)

let ctx_to_map ctx =
  StrMap.from_kv_list @@ List.map typed_to_pair @@ ctx_to_list ctx

let map_ctx_typed (f : ('t, string) typed -> ('b, string) typed)
    (ctx_e : 't ctx) =
  match ctx_e with
  | Typectx _t_stringtypedlist0 -> Typectx (List.map f _t_stringtypedlist0)

let map_ctx (f : 't -> 's) (ctx_e : 't ctx) =
  match ctx_e with
  | Typectx _t_stringtypedlist0 ->
      Typectx (List.map (( #=> ) f) _t_stringtypedlist0)

let filter_ctx_typed (f : ('t, string) typed -> bool) (ctx_e : 't ctx) =
  match ctx_e with
  | Typectx _t_stringtypedlist0 -> Typectx (List.filter f _t_stringtypedlist0)

let filter_ctx_name (f : string -> bool) (ctx_e : 't ctx) =
  match ctx_e with
  | Typectx _t_stringtypedlist0 ->
      Typectx (List.filter (fun x -> f x.x) _t_stringtypedlist0)

let filter_ctx (f : 't -> bool) (ctx_e : 't ctx) =
  match ctx_e with
  | Typectx _t_stringtypedlist0 ->
      Typectx (List.filter (fun x -> f x.ty) _t_stringtypedlist0)

let layout_ctx f ctx =
  match ctx with
  | Typectx l -> List.split_by "" (fun x -> spf "%s: %s\n" x.x (f x.ty)) l
