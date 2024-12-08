type var = string

(**
In the linear case, we only consider I, B, and C such that :
 - IX = X
 - BXYZ = X(YZ)
 - CXYZ = XZY
*)
type comb = I | B | C

(** Combinatory logic terms *)
type cl = Var of var | Comb of comb | App of cl * cl

(** Pseudo CL terms : may be abstractions *)
type pcl = PVar of var | PComb of comb | PApp of pcl * pcl | Abs of var * pcl

(** Naive string repr of a CL term, there might be useless parentheses *)
let rec cl_to_string_naive t =
  match t with
  | Var x -> x
  | Comb c -> ( match c with I -> "I" | B -> "B" | C -> "C")
  | App (u, v) -> "(" ^ cl_to_string_naive u ^ cl_to_string_naive v ^ ")"

(** String repr of a CL term without meaningless parentheses *)
let cl_to_string t =
  let rec aux t =
    match t with
    | Var x -> (x, true)
    | Comb c ->
        let s = match c with I -> "I" | B -> "B" | C -> "C" in
        (s, true)
    | App (u, v) ->
        let su, _ = aux u in
        let sv, rv = aux v in
        let fsv = if rv then sv else "(" ^ sv ^ ")" in
        (su ^ fsv, false)
  in
  fst (aux t)

let rec pcl_to_string t =
  match t with
  | PVar x -> x
  | PComb c -> ( match c with I -> "I" | B -> "B" | C -> "C")
  | PApp (u, v) -> "(" ^ pcl_to_string u ^ pcl_to_string v ^ ")"
  | Abs (x, u) -> "[" ^ x ^ "].(" ^ pcl_to_string u ^ ")"

let latexify s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | 'I' -> Buffer.add_string buf "\\mathbf{I}"
      | 'B' -> Buffer.add_string buf "\\mathbf{B}"
      | 'C' -> Buffer.add_string buf "\\mathbf{C}"
      | _ -> Buffer.add_char buf c)
    s;
  Buffer.contents buf

let print_to_latex t = print_endline (latexify (cl_to_string t))

exception EmptyApps

(**
Returns CL term associated to the given list
If l = [U; V; W; Z], returns UVWZ = ((UV)W)Z
*)
let papps l =
  let rec aux l =
    match l with [] -> raise EmptyApps | [ t ] -> t | x :: q -> PApp (aux q, x)
  in
  aux (List.rev l)

exception AbstractionError

let rec pfree x t =
  match t with
  | PVar y -> x = y
  | PComb _ -> false
  | PApp (u, v) -> pfree x u || pfree x v
  | Abs (y, u) when y = x -> false
  | Abs (y, u) -> pfree x u

let rec abs x t =
  match t with
  | PVar y when x = y -> PComb I
  | PVar y -> PVar y
  | PComb c -> PComb c
  | PApp (u, v) when pfree x u && not (pfree x v) ->
      papps [ PComb C; abs x u; v ]
  | PApp (u, v) when (not (pfree x u)) && pfree x v ->
      papps [ PComb B; u; abs x v ]
  | PApp (u, v) -> raise AbstractionError
  | Abs (y, u) when x = y -> Abs (y, u)
  | Abs (y, u) -> Abs (y, abs x u)

let rec pcl_to_cl t =
  match t with
  | PVar x -> Var x
  | PComb c -> Comb c
  | PApp (u, v) -> App (pcl_to_cl u, pcl_to_cl v)
  | Abs (x, u) ->
      let v = abs x u in
      pcl_to_cl v

let baxiom11 =
  Abs
    ( "x",
      PApp
        ( PApp
            ( PComb C,
              PApp
                (PApp (PComb C, papps [ PComb B; PComb B; PVar "x" ]), PVar "V")
            ),
          PVar "Z" ) )

let baxiom12 = Abs ("x", papps [ PComb C; PVar "x"; PVar "V"; PVar "Z" ])
let () = print_to_latex (pcl_to_cl baxiom11)
let () = print_to_latex (pcl_to_cl baxiom12)

let baxiom31 =
  Abs
    ("x", PApp (PApp (PComb B, papps [ PComb B; PVar "U"; PVar "V" ]), PVar "x"))

let baxiom32 =
  Abs
    ( "x",
      PApp (PApp (PComb B, PVar "U"), PApp (PApp (PComb B, PVar "V"), PVar "x"))
    )

let () = print_to_latex (pcl_to_cl baxiom31)
let () = print_to_latex (pcl_to_cl baxiom32)