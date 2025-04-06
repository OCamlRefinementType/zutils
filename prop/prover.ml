open Z3
open Solver
open Goal
open Sugar
open Syntax
open Myconfig
module Propencoding = Propencoding

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

let layout_smt_result = function
  | SmtSat model ->
      ( _log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
      "sat"
  | SmtUnsat -> "unsat"
  | Timeout -> "timeout"

type prover = {
  ax_sys : laxiom_system;
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
  let ax_sys = Axiom.emp in
  { ctx; ax_sys; solver; goal }

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
  let axioms =
    List.map
      (fun (name, tasks, prop) ->
        let z3_prop = Propencoding.to_z3 ctx prop in
        (name, tasks, prop, z3_prop))
      axioms
  in
  match !_prover with
  | Some p ->
      _prover := Some { p with ax_sys = Axiom.add_laxioms p.ax_sys axioms }
  | None ->
      let p = mk_prover () in
      _prover := Some { p with ax_sys = Axiom.add_laxioms p.ax_sys axioms }

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

let check_sat (task, prop) =
  let { goal; solver; ax_sys; ctx } = get_prover () in
  let axioms = Axiom.find_axioms ax_sys (task, prop) in
  let query = Propencoding.to_z3 ctx prop in
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>QUERY:@}\n%s\n" (Expr.to_string query)
  in
  Goal.reset goal;
  Goal.add goal (axioms @ [ query ]);
  let _ =
    _log_queries @@ fun _ ->
    Pp.printf "@{<bold>Goal:@}\n%s\n" (Goal.to_string goal)
  in
  (* let goal = Goal.simplify goal None in *)
  (* let _ = *)
  (*   _log_queries @@ fun _ -> *)
  (*   Pp.printf "@{<bold>Simplifid Goal:@}\n%s\n" (Goal.to_string goal) *)
  (* in *)
  Goal.add goal axioms;
  Solver.reset solver;
  Solver.add solver (get_formulas goal);
  let time_t, res = Sugar.clock (fun () -> handle_sat_result solver) in
  let () =
    _log_stat @@ fun _ -> Pp.printf "@{<bold>Z3 Solving time: %.2f@}\n" time_t
  in
  res

let check_sat_bool (task, prop) =
  let res = check_sat (task, prop) in
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
let check_valid (task, prop) =
  let () =
    Printf.printf "input:\n%s\n"
      (Sexplib.Sexp.to_string @@ sexp_of_prop Nt.sexp_of_nt (Not prop))
  in
  match check_sat (task, Not prop) with
  | SmtUnsat -> true
  | SmtSat model ->
      ( _log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
      false
  | Timeout ->
      (_log_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
      false

let _p1 =
  "(Not(Forall(qv((ty(Ty_var a1))(x \
   v)))(body(Exists(qv((ty(Ty_constructor(unit())))(x \
   dummy_0)))(body(Exists(qv((ty(Ty_var a1))(x \
   x_0)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a1)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a1))(x(AVar((ty(Ty_var \
   a1))(x \
   v))))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(unit()))(Ty_arrow(Ty_constructor(unit()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(unit())))(x(AVar((ty(Ty_constructor(unit())))(x \
   dummy_0)))))((ty(Ty_constructor(unit())))(x(AC \
   U))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a1)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a1))(x(AVar((ty(Ty_var \
   a1))(x \
   x_0))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a1)(Ty_arrow(Ty_var a1)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
   a1))(x(AVar((ty(Ty_var a1))(x v)))))((ty(Ty_var a1))(x(AVar((ty(Ty_var \
   a1))(x x_0))))))))))))))))))))))"

let _p2 =
  "(Not(Forall(qv((ty(Ty_var a))(x \
   v)))(body(Implies(Or((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p2))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))))(Exists(qv((ty(Ty_constructor(bool())))(x \
   x)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AC(B \
   true)))))(Or((And((Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))))(And((Not(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x)))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p2))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))))))))))))))"

let _p3 =
  "(Not(Forall(qv((ty(Ty_constructor(option((Ty_var a)))))(x \
   v)))(body(Implies(Exists(qv((ty(Ty_var a))(x \
   y)))(body(Or((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a_10))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a_10))))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(option((Ty_var \
   a_10)))))(x(AVar((ty(Ty_constructor(option((Ty_var a_10)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a_10)))))(x(AAppOp((ty(Ty_constructor(option((Ty_var a_10)))))(x \
   None))()))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a_11))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a_11))))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(option((Ty_var \
   a_11)))))(x(AVar((ty(Ty_constructor(option((Ty_var a_11)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a_11)))))(x(AAppOp((ty(Ty_arrow(Ty_var a_11)(Ty_constructor(option((Ty_var \
   a_11))))))(x Some))(((ty(Ty_var a_11))(x(AVar((ty(Ty_var a_11))(x \
   y))))))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   y))))))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x)))(body(And((And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AC(I \
   10)))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))((ty(Ty_constructor(int())))(x(AC(I \
   10)))))))))))(Exists(qv((ty(Ty_constructor(bool())))(x \
   x_27)))(body(And((Iff(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_27))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))((ty(Ty_constructor(int())))(x(AC(I \
   2))))))))))(Or((And((Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_27))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_constructor(bool())))))(x ==))(((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(option((Ty_var a)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AAppOp((ty(Ty_constructor(option((Ty_var a)))))(x \
   None))()))))))))))(And((Not(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_27)))))))(Exists(qv((ty(Ty_var a))(x \
   x_28)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_28))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_constructor(bool())))))(x ==))(((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(option((Ty_var a)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AAppOp((ty(Ty_arrow(Ty_var a)(Ty_constructor(option((Ty_var \
   a))))))(x Some))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_28))))))))))))))))))))))))))))))))))"

let _p4 =
  "(Not(Forall(qv((ty(Ty_constructor(list((Ty_var a)))))(x \
   l)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_constructor(bool()))))(x p1))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l))))))))))(Forall(qv((ty(Ty_var a))(x \
   v)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_arrow(Ty_var a)(Ty_constructor(bool())))))(x \
   list_mem))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x l)))))((ty(Ty_var \
   a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_33)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_33)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_constructor(int()))))(x \
   list_len))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l))))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_34)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_34)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(int())))))(x \
   -))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_33)))))((ty(Ty_constructor(int())))(x(AC(I \
   1)))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_36)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_34))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_34))))))))))(Exists(qv((ty(Ty_var a))(x \
   x_37)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_constructor(int()))))(x \
   list_len))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l))))))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))))(x \
   list_nth_pred))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36)))))((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_37))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_arrow(Ty_var a)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
   a))(x(AVar((ty(Ty_var a))(x v)))))((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_37)))))))))))))))))))))))))))))))))"

let _p5 =
  "(Not(Forall(qv((ty(Ty_constructor(int())))(x \
   a)))(body(Forall(qv((ty(Ty_constructor(int())))(x \
   b)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b))))))))))(Forall(qv((ty(Ty_constructor(int())))(x \
   v)))(body(Implies(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   v))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   v)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b))))))))))))(Exists(qv((ty(Ty_constructor(bool())))(x \
   x_11)))(body(And((Iff(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_11))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))))))))(Not(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_11)))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_14)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_14)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(int())))))(x \
   -))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a))))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x)))(body(And((And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_14))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_14))))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   v)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(int())))))(x \
   +))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))))))))))))))))))))))))))))))))"

open OcamlParser.Oparse

let basic_type_ctx =
  let l =
    [
      "=="#:"'a -> 'a -> bool";
      "<="#:"'a -> 'a -> bool";
      "<"#:"'a -> 'a -> bool";
      "None"#:"'a option";
      "Some"#:"'a -> 'a option";
      "list_mem"#:"'a list -> 'a -> bool";
      "list_nth_pred"#:"'a list -> int -> 'a -> bool";
      "list_nth"#:"'a list -> int -> 'a";
      "list_len"#:"'a list -> int";
      "list_length"#:"'a list -> int";
    ]
  in
  let l =
    List.map
      (fun x ->
        x.x#:(Nt.close_poly_nt [%here]
             @@ Nt.core_type_to_t @@ parse_core_type x.ty))
      l
  in
  Typectx.ctx_from_list l

let handle_prop str =
  let prop = Front.of_expr @@ parse_expression str in
  let prop = Typecheck.prop_type_check basic_type_ctx [] prop in
  prop

let ax_list_mem_has_nth =
  "fun (l : 'c list) (v : 'c) ->\n\
  \  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->\n\
  \  0 <= idx && idx < list_len l && list_nth_pred l idx v)"

let%test "test" =
  let () =
    meta_config_path := "/Users/zhezzhou/workspace/zutils/meta-config.json"
  in
  let prop =
    handle_prop
      "fun ((x [@ex]) : int * bool) ((y [@ex]) : bool * int) -> Some (fst x) \
       == Some (snd y) && Some (snd x) == None"
  in
  let () = Printf.printf "Prop: %s:\n" @@ Front.layout prop in
  let () = Printf.printf "Prop: %s:\n" @@ show_prop prop in
  let res = check_sat (None, prop) in
  let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in
  false

let%test "query" =
  let () =
    meta_config_path := "/Users/zhezzhou/workspace/zutils/meta-config.json"
  in
  let prop = prop_of_sexp Nt.nt_of_sexp @@ Sexplib.Sexp.of_string _p4 in
  let () = Printf.printf "Prop: %s:\n" @@ Front.layout prop in
  let ax = handle_prop ax_list_mem_has_nth in
  let () = Printf.printf "Ax: %s:\n" @@ Front.layout ax in
  let () = update_axioms [ ("ax", [], ax) ] in
  let res = check_sat (None, prop) in
  let () = Pp.printf "@{<bold>SAT(%s): @}\n" (layout_smt_result res) in
  false
