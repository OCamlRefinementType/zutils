open Ast
open OcamlParser
open Parsetree
open Oparse
open Sugar
open Ast_helper

let get_str t =
  match t.ptyp_desc with
  | Ptyp_constr (name, []) -> List.nth (Longident.flatten name.txt) 0
  | _ -> _die [%here]

let rec core_type_to_t ct =
  (* enum type *)
  match ct.ptyp_attributes with
  | [ attr ] ->
      let enum_name = attr.attr_name.txt in
      let enum_elems =
        match ct.ptyp_desc with
        | Ptyp_tuple cts -> List.map get_str cts
        | _ -> _die [%here]
      in
      let enum_elems = List.map String.capitalize_ascii enum_elems in
      Ty_enum { enum_name; enum_elems }
  | _ ->
      let nt = core_type_desc_to_t ct.ptyp_desc in
      nt

and object_to_labeled_type feild =
  match feild.pof_desc with
  | Otag (label, ct) -> label.txt #: (core_type_to_t ct)
  | _ -> _die_with [%here] "wrong record type"

and core_type_desc_to_t t =
  match t with
  | Ptyp_any -> Ty_any
  | Ptyp_object (l, _) ->
      let l = List.map object_to_labeled_type l in
      Ty_record l
  | Ptyp_class (_, _)
  | Ptyp_alias (_, _)
  | Ptyp_variant (_, _, _)
  | Ptyp_package _ | Ptyp_extension _ ->
      _die [%here]
  | Ptyp_poly ([ lc ], ct) ->
      _die_with [%here]
        (spf "unimp: poly: lc: %s; ct: %s" lc.txt (string_of_core_type ct))
  | Ptyp_poly ([], ct) -> core_type_to_t ct
  | Ptyp_poly (_, _) ->
      _die_with [%here]
        (spf "unimp: poly: %s" @@ string_of_core_type @@ desc_to_ct t)
  | Ptyp_var name -> Ty_var name
  | Ptyp_arrow (_, t1, t2) -> Ty_arrow (core_type_to_t t1, core_type_to_t t2)
  | Ptyp_tuple ts -> Ty_tuple (List.map core_type_to_t ts)
  | Ptyp_constr (lc, ts) -> (
      (* let () = *)
      (*   Printf.printf "%s\n" *)
      (*     (Zzdatatype.Datatype.StrList.to_string (Longident.flatten lc.txt)) *)
      (* in *)
      match (Longident.flatten lc.txt, ts) with
      | [ "unit" ], [] -> Ty_unit
      | [ "bool" ], [] -> Ty_bool
      | [ "int" ], [] -> Ty_int
      | [ "nat" ], [] -> Ty_nat
      (* | [ "list" ], [ t ] -> Ty_constructor ("list", [ core_type_to_t t ]) *)
      | [ c ], args -> Ty_constructor (c, List.map core_type_to_t args)
      | cs, [] -> Ty_uninter (Zdatatype.List.split_by "." (fun x -> x) cs)
      | _, _ ->
          failwith
          @@ Printf.sprintf "--un-imp??: %s"
               (string_of_core_type @@ desc_to_ct t))

let rec t_to_core_type t = Typ.mk (t_to_core_type_desc t)

and t_to_core_type_desc t =
  let open Longident in
  let open Location in
  let mk0 name = Ptyp_constr (mknoloc @@ Lident name, []) in
  (* let mk1 name t = Ptyp_constr (mknoloc @@ Lident name, [ t ]) in *)
  let aux = function
    | Ty_any -> Ptyp_any
    | Ty_unknown -> mk0 "unknown"
    | Ty_var name ->
        let res = Ptyp_var name in
        (* let () = *)
        (*   Printf.printf "output res: %s\n" @@ string_of_core_type @@ desc_to_ct res *)
        (* in *)
        res
    | Ty_unit -> mk0 "unit"
    | Ty_bool -> mk0 "bool"
    | Ty_int -> mk0 "int"
    | Ty_nat -> mk0 "nat"
    | Ty_enum { enum_name; _ } -> mk0 enum_name
    | Ty_uninter name -> mk0 name
    (* | Ty_list t -> mk1 "list" (t_to_core_type t) *)
    | Ty_tuple t -> Ptyp_tuple (List.map t_to_core_type t)
    | Ty_arrow (t1, t2) ->
        Ptyp_arrow (Asttypes.Nolabel, t_to_core_type t1, t_to_core_type t2)
    | Ty_constructor (id, args) ->
        Ptyp_constr
          ( (Location.mknoloc
            @@
            match Longident.unflatten [ id ] with
            | None -> _die [%here]
            | Some x -> x),
            List.map t_to_core_type args )
    | Ty_record l -> Ptyp_object (List.map labeled_t_to_feild l, Asttypes.Closed)
  in
  aux t

and labeled_t_to_feild { x; ty = t } =
  Of.tag (Location.mknoloc x) (t_to_core_type t)

let core_type_to_notated_t ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> (Some name.txt, core_type_to_t ty)
  | _ -> (None, core_type_to_t ct)

let notated_t_to_core_type (name, t) =
  let ct = t_to_core_type t in
  match name with
  | None -> ct
  | Some name -> desc_to_ct (Ptyp_extension (Location.mknoloc name, PTyp ct))

let layout_nt t = string_of_core_type (t_to_core_type t)

let nt_of_string str =
  core_type_to_t @@ Parse.core_type @@ Lexing.from_string str

let string_of_nts ts = Zdatatype.List.split_by_comma layout_nt ts

(* let%test "rev" = List.equal Int.equal (List.rev [ 3; 2; 1 ]) [ 1; 2 ] *)
(* let%test "parse1" = equal_nt int_ty (of_string "int") *)
(* let%test "parse2" = equal_nt bool_ty (of_string "bool") *)
(* let%test "parse3" = equal_nt (mk_arr bool_ty int_ty) (of_string "bool -> int") *)
(* let%test "parse4" = equal_nt (mk_arr bool_ty int_ty) (of_string "bool -> int") *)
(* let%test "parse5" = equal_nt (uninter_ty "path") (of_string "path") *)
(* let%test "parse6" = equal_nt (uninter_ty "Path.t") (of_string "Path.t") *)

(* let%test "parse7" = *)
(*   equal_nt *)
(*     (Ty_record [ ("z", Ty_bool); ("x", Ty_int) ]) *)
(*     (of_string "<x:int; z:bool>") *)
