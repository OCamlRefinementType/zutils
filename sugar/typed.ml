type ('a, 'b) typed = { ty : 'a; x : 'b } [@@deriving sexp, show, eq, ord]

let _get_ty x = x.ty
let _get_x x = x.x
let ( #: ) x ty = { x; ty }

let ( #-> ) : 't 'a 'b. ('a -> 'b) -> ('t, 'a) typed -> ('t, 'b) typed =
 fun f { x; ty } -> (f x) #: ty

let ( #=> ) : 't 's 'a. ('t -> 's) -> ('t, 'a) typed -> ('s, 'a) typed =
 fun f { x; ty } -> x #: (f ty)

let ( #: ) x ty = { x; ty }
let ( #+ ) x ty = { x = x.x; ty }
let typed_from_pair (x, ty) = x #: ty
let typed_to_pair { x; ty } = (x, ty)
let fv_typed_id_to_id f e = List.map (fun x -> x.x) @@ f e
let subst_f_to_instance subst x lit e = subst x (fun _ -> lit) e
let find_in_args name l = List.find_opt (fun x -> String.equal name x.x) l

(** override show *)
let show_typed (f : 'a -> string) (g : 'b -> string) { x; ty } =
  Printf.sprintf "(%s: %s)" (f x) (g ty)

let eq_typed f p1 p2 = equal_typed (fun _ _ -> true) f p1 p2
let typed_eq = eq_typed
