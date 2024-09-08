open Sexplib.Std

type t = Bool | Int | Uninterp of string [@@deriving sexp, show, eq, ord]

let is_uninterp = function Uninterp _ -> true | _ -> false
