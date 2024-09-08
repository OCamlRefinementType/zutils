type ('a, 'b) typed = { x : 'a; ty : 'b } [@@deriving sexp, show, eq, ord]

let ( #> ) f { x; ty } = { x = f x; ty }
let ( #-> ) f { x; ty } = { x; ty = f ty }
let ( #: ) x ty = { x; ty }
let ( #+ ) x ty = { x = x.x; ty }
let typed_from_pair (x, ty) = x #: ty
let typed_to_pair { x; ty } = (x, ty)

(** override show *)
let show_typed (f : 'a -> string) (g : 'b -> string) { x; ty } =
  Printf.sprintf "(%s: %s)" (f x) (g ty)
