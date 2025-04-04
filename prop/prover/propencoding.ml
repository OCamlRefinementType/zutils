open Z3
open Z3aux
open Syntax
open Sugar
open Myconfig
open Zdatatype

let to_nnf prop =
  let rec aux is_negate prop =
    match prop with
    | Lit _ -> if is_negate then Not prop else prop
    | Implies (e1, e2) ->
        if is_negate then smart_and [ e1; aux true e2 ]
        else Implies (aux false e1, aux false e2)
    | Ite _ | Iff _ -> if is_negate then smart_not prop else prop
    | Not p -> aux (not is_negate) p
    | And es ->
        if is_negate then smart_or (List.map (aux true) es)
        else smart_and (List.map (aux false) es)
    | Or es ->
        if is_negate then smart_and (List.map (aux true) es)
        else smart_or (List.map (aux false) es)
    | Forall { qv; body } ->
        if is_negate then Exists { qv; body = aux true body }
        else Forall { qv; body = aux false body }
    | Exists { qv; body } ->
        if is_negate then Forall { qv; body = aux true body }
        else Exists { qv; body = aux false body }
  in
  let res = aux false prop in
  res

let to_snf prop =
  let rec aux = function Exists { body; _ } -> aux body | _ as prop -> prop in
  aux prop

let to_z3 ctx prop =
  let rec aux prop =
    match prop with
    | Implies (p1, p2) ->
        let () =
          _log "z3encode" @@ fun () ->
          Pp.printf "implies %s %s\n" (Front.layout p1) (Front.layout p2)
        in
        let e1 = aux p1 in
        let e2 = aux p2 in
        let () =
          _log "z3encode" @@ fun () ->
          Pp.printf "implies %s %s\n" (Expr.to_string e1) (Expr.to_string e2)
        in
        Boolean.mk_implies ctx e1 e2
    | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
    | Not p -> Boolean.mk_not ctx (aux p)
    | And ps -> Boolean.mk_and ctx (List.map aux ps)
    | Or ps -> Boolean.mk_or ctx (List.map aux ps)
    | Iff (p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2)
    | Forall { qv; body } ->
        make_forall ctx [ tpedvar_to_z3 ctx (qv.ty, qv.x) ] (aux body)
    | Exists { qv; body } ->
        make_exists ctx [ tpedvar_to_z3 ctx (qv.ty, qv.x) ] (aux body)
    | Lit lit -> Litencoding.typed_lit_to_z3 ctx lit
  in
  let () =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>Origin:@} %s\n" (Front.layout_prop prop)
  in
  let p1 = to_nnf prop in
  let () =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>To NNF:@} %s\n" (Front.layout_prop p1)
  in
  let p2 = to_snf p1 in
  let () =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>To SNF:@} %s\n" (Front.layout_prop p2)
  in
  aux p2
