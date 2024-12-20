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

exception ParsingError

let surronding_parentheses s =
  let n = String.length s in
  let rec aux i ic =
    if i = n - 1 then ic = 1 && s.[i] = ')'
    else if i = 0 then if s.[i] <> '(' then false else aux 1 1
    else
      match s.[i] with
      | '(' -> aux (i + 1) (ic + 1)
      | ')' -> if ic > 0 then aux (i + 1) (ic - 1) else raise ParsingError
      | _ -> aux (i + 1) ic
  in
  aux 0 0

let last_token_idx s =
  let n = String.length s in
  let rec aux i ic =
    if i < 0 then raise ParsingError
    else if i = n - 1 && s.[i] <> ')' then i
    else if s.[i] = ')' then aux (i - 1) (ic + 1)
    else if s.[i] = '(' then if ic = 1 then i else aux (i - 1) (ic - 1)
    else aux (i - 1) ic
  in
  aux (n - 1) 0

(** Utility to parse a PCL term from a string *)
let rec pcl_of_string s =
  let n = String.length s in
  if n = 0 then raise ParsingError (* Empty string : error *)
  else if n = 1 then
    (* One character : combinator or variable *)
    match s.[0] with
    | 'I' -> PComb I
    | 'B' -> PComb B
    | 'C' -> PComb C
    | c -> PVar (String.make 1 c)
  else if surronding_parentheses s then
    (* Useless parentheses around the whole string *)
    pcl_of_string (String.sub s 1 (n - 2))
  else if n >= 4 && s.[0] = '[' && s.[2] = ']' && s.[3] = '.' then
    (* Abstraction *)
    let x = String.make 1 s.[1] in
    Abs (x, pcl_of_string (String.sub s 4 (n - 4)))
  else
    (* Application, let's retrieve the right token *)
    let idx = last_token_idx s in
    let left = String.sub s 0 idx in
    let right = String.sub s idx (n - idx) in
    PApp (pcl_of_string left, pcl_of_string right)

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
  if not (pfree x t) then raise AbstractionError
  else
    match t with
    | PVar y when x = y -> PComb I
    | PVar y -> PVar y
    | PComb c -> PComb c
    | PApp (u, v) when pfree x u && not (pfree x v) ->
        papps [ PComb C; abs x u; v ]
    | PApp (u, v) when (not (pfree x u)) && pfree x v ->
        papps [ PComb B; u; abs x v ]
    | PApp (u, v) -> raise AbstractionError
    | Abs (y, u) ->
        (* First expand the nested abstraction *)
        let p = abs y u in
        abs x p

let rec pcl_to_cl t =
  match t with
  | PVar x -> Var x
  | PComb c -> Comb c
  | PApp (u, v) -> App (pcl_to_cl u, pcl_to_cl v)
  | Abs (x, u) ->
      let v = abs x u in
      pcl_to_cl v

(***********)
(* I-AXIOM *)
(***********)
let iaxiom11 = pcl_of_string "[x].BIx"
let iaxiom12 = pcl_of_string "[x].x"

(* Printing time *)
let () = print_endline "I-axiom"
let () = print_endline (cl_to_string (pcl_to_cl iaxiom11))
let () = print_endline (cl_to_string (pcl_to_cl iaxiom12))

(************)
(* B-AXIOMS *)
(************)
let baxiom11 = pcl_of_string "[x].[v].[z].C(C(BBx)v)z"
let baxiom12 = pcl_of_string "[x].[v].[z].Cx(vz)"
let baxiom21 = pcl_of_string "[x].[u].[z].C(B(Bu)x)z"
let baxiom22 = pcl_of_string "[x].[u].[z].Bu(Cxz)"
let baxiom31 = pcl_of_string "[x].[u].[v].B(Buv)x"
let baxiom32 = pcl_of_string "[x].[u].[v].Bu(Bvx)"

(* Now let's print them *)
(* We can also use print_to_latex to copy-paste LaTeX formula *)
let () = print_endline "B-axioms"
let () = print_to_latex (pcl_to_cl baxiom11)
let () = print_to_latex (pcl_to_cl baxiom12)
let () = print_to_latex (pcl_to_cl baxiom21)
let () = print_to_latex (pcl_to_cl baxiom22)
let () = print_to_latex (pcl_to_cl baxiom31)
let () = print_to_latex (pcl_to_cl baxiom32)

(************)
(* C-AXIOMS *)
(************)
let caxiom11 = pcl_of_string "[x].[v].[z].C(C(BCx)v)z"
let caxiom12 = pcl_of_string "[x].[v].[z].C(Cxz)v"
let caxiom21 = pcl_of_string "[x].[u].[z].C(B(Cu)x)z"
let caxiom22 = pcl_of_string "[x].[u].[z].B(uz)x"
let caxiom31 = pcl_of_string "[x].[u].[v].B(Cuv)x"
let caxiom32 = pcl_of_string "[x].[u].[v].C(Bux)v"

(* Printing time *)
let () = print_endline "C-axioms"
let () = print_to_latex (pcl_to_cl caxiom11)
let () = print_to_latex (pcl_to_cl caxiom12)
let () = print_to_latex (pcl_to_cl caxiom21)
let () = print_to_latex (pcl_to_cl caxiom22)
let () = print_to_latex (pcl_to_cl caxiom31)
let () = print_to_latex (pcl_to_cl caxiom32)

(*************)
(* ETA-AXIOM *)
(*************)
let etaaxiom1 = pcl_of_string "[u].[x].ux"
let etaaxiom2 = pcl_of_string "I"

(* Printing time *)
let () = print_endline "Eta-axiom"
let () = print_to_latex (pcl_to_cl etaaxiom1)
let () = print_to_latex (pcl_to_cl etaaxiom2)
