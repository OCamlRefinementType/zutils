open Assertion
open SugarAux

type name = string * int option

let split_char = '_'

let name_of_string name =
  match String.split_on_char split_char name with
  | [ x ] -> (x, None)
  | [ x; i ] -> (x, Some (int_of_string i))
  | _ -> _die_with [%here] (Printf.sprintf "not a well-formed name: %s" name)

let name_to_string (sname, id) =
  match id with None -> sname | Some i -> spf "%s%c%i" sname split_char i

let _unique tab sname =
  match Hashtbl.find_opt tab sname with
  | Some n ->
      Hashtbl.replace tab sname (n + 1);
      (sname, Some n)
  | None ->
      Hashtbl.add tab sname 0;
      (sname, None)

let mk_unique tab name =
  let sname, id = name_of_string name in
  match id with
  | Some _ ->
      _die_with [%here]
        (Printf.sprintf "the bound name (%s) cannot contain char %c" name
           split_char)
  | None -> name_to_string @@ _unique tab sname

(* NOTE: store the next available name lazily *)
let universal_type_var : (string, int) Hashtbl.t = Hashtbl.create 100
let universal_var : (string, int) Hashtbl.t = Hashtbl.create 1000
let _unique_type_var sname = _unique universal_type_var sname
let _unique_var sname = _unique universal_var sname
let unique_type_var name = mk_unique universal_type_var name
let unique_var name = mk_unique universal_var name
let dummy_var () = unique_var "dummyVar"
let dummy_type_var () = unique_var "dummyTypeVar"
let fresh_type_var () = unique_var "tv"
let fresh_var () = unique_var "tmp"
