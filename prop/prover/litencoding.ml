open Z3
open Z3aux
open Syntax
open Sugar
open Myconfig

let get_idx_in_list x l =
  let rec aux i = function
    | [] -> _die [%here]
    | h :: l -> if String.equal x h then i else aux (i + 1) l
  in
  aux 0 l

let constant_to_z3 ctx c =
  match c with
  | U | Tu _ | Dt _ | SetLiteral _ ->
      _die_with [%here] "unimp complex constant encoding"
  | B b -> bool_to_z3 ctx b
  | I i -> int_to_z3 ctx i
  | Enum { elem; enum_elems; _ } ->
      let ty = constant_to_nt c in
      let idx = get_idx_in_list elem enum_elems in
      Enumeration.get_const (tp_to_sort ctx ty) idx

let rec typed_lit_to_z3 ctx lit =
  match lit.x with
  | ATu _ | AProj _ -> _die [%here]
  | AC c -> constant_to_z3 ctx c
  | AVar x -> tpedvar_to_z3 ctx (x.ty, x.x)
  | AAppOp (op, args) -> (
      let () =
        _log "z3encode" @@ fun () ->
        Pp.printf "app (%s:%s) on %s\n" op.x (Nt.layout op.ty)
          (Zdatatype.List.split_by_comma
             (fun l -> spf "%s:%s" (Front.layout_lit l.x) (Nt.layout l.ty))
             args)
      in
      let args = List.map (typed_lit_to_z3 ctx) args in
      let () =
        _log "z3encode" @@ fun () ->
        Pp.printf "app (%s:%s) on %s\n" op.x (Nt.layout op.ty)
          (Zdatatype.List.split_by_comma Expr.to_string args)
      in
      match (op.x, args) with
      (* NOTE: we don't encode force *)
      | "forc", [ a ] -> a
      | "==", [ a; b ] -> Boolean.mk_eq ctx a b
      | "!=", [ a; b ] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx a b
      | "<=", [ a; b ] -> Arithmetic.mk_le ctx a b
      | ">=", [ a; b ] -> Arithmetic.mk_ge ctx a b
      | "<", [ a; b ] -> Arithmetic.mk_lt ctx a b
      | ">", [ a; b ] -> Arithmetic.mk_gt ctx a b
      | "+", [ a; b ] -> Arithmetic.mk_add ctx [ a; b ]
      | "-", [ a; b ] -> Arithmetic.mk_sub ctx [ a; b ]
      | "mod", [ a; b ] -> Arithmetic.Integer.mk_mod ctx a b
      | "*", [ a; b ] -> Arithmetic.mk_mul ctx [ a; b ]
      | "/", [ a; b ] -> Arithmetic.mk_div ctx a b
      | opname, args ->
          let argsty, retty = Nt.destruct_arr_tp op.ty in
          let func = z3func ctx opname argsty retty in
          Z3.FuncDecl.apply func args)
