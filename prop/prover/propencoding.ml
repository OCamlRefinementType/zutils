open Z3
open Z3aux
open Syntax
open Sugar
open Myconfig

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
  aux prop
