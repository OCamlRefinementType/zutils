open Z3
open Solver
open Goal
open Sugar
open Syntax
open Myconfig
module Propencoding = Propencoding

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

let layout_smt_result = function
  | SmtSat _ -> "sat"
  | SmtUnsat -> "unsat"
  | Timeout -> "timeout"

type prover = {
  axioms : Expr.expr list;
  ctx : context;
  solver : solver;
  goal : goal;
}

let _mk_prover timeout_bound =
  let ctx =
    mk_context
      [
        ("model", "true");
        ("proof", "false");
        ("timeout", string_of_int timeout_bound);
      ]
  in
  let solver = mk_solver ctx None in
  let goal = mk_goal ctx true false false in
  (* TODO: choose axioms *)
  let axioms = [] in
  { ctx; axioms; solver; goal }

let mk_prover () = _mk_prover (get_prover_timeout_bound ())
let _prover : prover option ref = ref None

let get_prover () =
  match !_prover with
  | Some p -> p
  | None ->
      let p = mk_prover () in
      let () = _prover := Some p in
      p

let get_ctx () = (get_prover ()).ctx

let update_axioms axioms =
  let ctx = get_ctx () in
  let axioms = List.map (Propencoding.to_z3 ctx) axioms in
  match !_prover with
  | Some p -> _prover := Some { p with axioms }
  | None ->
      let p = mk_prover () in
      _prover := Some { p with axioms }

let handle_sat_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> SmtUnsat
  | UNKNOWN ->
      (* raise (InterExn "time out!") *)
      (* Printf.printf "\ttimeout\n"; *)
      Timeout
  | SATISFIABLE -> (
      match Solver.get_model solver with
      | None -> failwith "never happen"
      | Some m -> SmtSat m)

let check_sat prop =
  let { goal; solver; axioms; ctx } = get_prover () in
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string prop)
  in
  Goal.reset goal;
  Goal.add goal [ prop ];
  let tac_result = Tactic.apply (Tactic.mk_tactic ctx "nnf") goal None in
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>nnf result:@} %s\n"
      (Tactic.ApplyResult.to_string tac_result)
  in
  let tac_result = Tactic.apply (Tactic.mk_tactic ctx "simplify") goal None in
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>simplify result:@} %s\n"
      (Tactic.ApplyResult.to_string tac_result)
  in
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>Goal:@}\n%s\n" (Goal.to_string goal)
  in
  Goal.add goal axioms;
  Solver.reset solver;
  Solver.add solver (get_formulas goal);
  let time_t, res = Sugar.clock (fun () -> handle_sat_result solver) in
  let () =
    _log_stat @@ fun _ -> Pp.printf "@{<bold>Z3 Solving time: %.2f@}\n" time_t
  in
  res

let check_sat_bool prop =
  let ctx = get_ctx () in
  let assertion = Propencoding.to_z3 ctx prop in
  let res = check_sat assertion in
  let () =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>SAT(%s): @} %s\n" (layout_smt_result res)
      (Front.layout_prop prop)
  in
  let res =
    match res with
    | SmtUnsat -> false
    | SmtSat model ->
        ( _log "model" @@ fun _ ->
          Printf.printf "model:\n%s\n"
          @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
        true
    | Timeout ->
        (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
        true
  in
  res

(** Unsat means true; otherwise means false *)
let check_valid prop =
  let ctx = get_ctx () in
  let () =
    Printf.printf "input:\n%s\n"
      (Sexplib.Sexp.to_string @@ sexp_of_prop Nt.sexp_of_nt (Not prop))
  in
  let assertion = Propencoding.to_z3 ctx (Not prop) in
  match check_sat assertion with
  | SmtUnsat -> true
  | SmtSat model ->
      ( _log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
      false
  | Timeout ->
      (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
      false

let _prop_under_test_1 =
  prop_of_sexp Nt.nt_of_sexp
  @@ Sexplib.Sexp.of_string
       "(Not(Forall(qv((ty(Ty_var a1))(x \
        v)))(body(Exists(qv((ty(Ty_constructor(unit())))(x \
        dummy_0)))(body(Exists(qv((ty(Ty_var a1))(x \
        x_0)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
        a1)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var \
        a1))(x(AVar((ty(Ty_var a1))(x \
        v))))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(unit()))(Ty_arrow(Ty_constructor(unit()))(Ty_constructor(bool())))))(x \
        ==))(((ty(Ty_constructor(unit())))(x(AVar((ty(Ty_constructor(unit())))(x \
        dummy_0)))))((ty(Ty_constructor(unit())))(x(AC \
        U))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
        a1)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var \
        a1))(x(AVar((ty(Ty_var a1))(x \
        x_0))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
        a1)(Ty_arrow(Ty_var a1)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
        a1))(x(AVar((ty(Ty_var a1))(x v)))))((ty(Ty_var a1))(x(AVar((ty(Ty_var \
        a1))(x x_0))))))))))))))))))))))"

let%test _ =
  let () =
    meta_config_path := "/Users/zhezzhou/workspace/zutils/meta-config.json"
  in
  let ctx = get_ctx () in
  let expr = Propencoding.to_z3 ctx _prop_under_test_1 in
  let () = Printf.printf "Prop: %s:\n" @@ Front.layout _prop_under_test_1 in
  let () = Printf.printf "Z3: %s:\n" @@ Expr.to_string expr in
  let res = check_sat expr in
  let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in
  false

(* let get_int m i = *)
(*   match Model.eval m i true with *)
(*   | None -> failwith "get_int" *)
(*   | Some v -> *)
(*       (\* printf "get_int(%s)\n" (Expr.to_string i); *\) *)
(*       int_of_string @@ Arithmetic.Integer.numeral_to_string v *)

(* let get_bool_str m i = *)
(*   match Model.eval m i true with None -> "none" | Some v -> Expr.to_string v *)

(* let get_int_name ctx m name = *)
(*   get_int m @@ Arithmetic.Integer.mk_const_s ctx name *)

(* let get_pred m predexpr = *)
(*   match Model.eval m predexpr true with *)
(*   | None -> failwith "get pred" *)
(*   | Some v -> Z3aux.z3expr_to_bool v *)

(* let get_unknown_fv ctx m unknown_fv = *)
(*   List.map (fun (_, b) -> get_pred m (Boolean.mk_const_s ctx b)) unknown_fv *)
