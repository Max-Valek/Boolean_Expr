(* Max Valek : x500 = valek016 *)
(* reads a file and returns a list of strings, one for each line in the file *)
(* read std input to eof, return list of lines *)
let read_lines () : string list =
  let rec read_help acc =
    try read_help ((read_line ())::acc) with End_of_file -> List.rev acc
  in read_help []

(* split a string at word boundaries and parens *)
let wordlist s : string list =
  let splitlist = Str.full_split (Str.regexp "\\b\\|(\\|)\\|\\$") s in
  let rec filter_splist lst = match lst with
    | [] -> []
    | (Str.Delim "(")::t -> "(" :: (filter_splist t)
    | (Str.Delim ")")::t -> ")" :: (filter_splist t)
    | (Str.Delim "$")::(Str.Text s)::t -> ("$"^s)::(filter_splist t)
    | (Str.Delim "$")::t -> "$"::(filter_splist t)
    | (Str.Delim _) :: t -> filter_splist t
    | (Str.Text s) :: t -> let s' = String.trim s in
			   let t' = (filter_splist t) in
			   if not (s' = "") then s' :: t' else t'
  in filter_splist splitlist

(* is s a legal variable name? (starts with '$' followed by alphanumeric chars or _) *)
let is_varname s =
  let rec checker i = match (i,s.[i]) with
  | (0,'$') -> true
  | (0,_) -> false
  | (_,('a'..'z'|'0'..'9'|'_')) -> checker (i-1)
  | _ -> false
  in checker ((String.length s) - 1)

(* tokens - you need to add some here *)
type bexp_token = OP | CP | AND | OR | XOR | NOT | EQ | NAND | CONST of bool | VAR of string

(* convert a string into a token *)
let token_of_string = function
  | "(" -> OP
  | ")" -> CP
  | "and" -> AND
  | "or" -> OR
  | "xor" -> XOR
  | "not" -> NOT
  | "=" -> EQ
  | "nand" -> NAND
  | "T" -> CONST true
  | "F" -> CONST false
  | s -> if (is_varname s) then (VAR (Str.string_after s 1))
         else (invalid_arg ("Unknown Token: "^s))

(* convert a list of strings into a a list of tokens *)
let tokens wl : bexp_token list = List.map token_of_string wl

(* type representing a boolean expression, you need to add variants here *)
type boolExpr = Const of bool
| Id of string
| Nand of boolExpr * boolExpr
| Not of boolExpr
| And of boolExpr * boolExpr
| Or of boolExpr * boolExpr
| Xor of boolExpr * boolExpr
| Eq of boolExpr * boolExpr

(* attempt to turn a list of tokens into a boolean expression tree.
A token list representing a boolean expression is either
 + a CONST token :: <more tokens> or
 + a VAR token :: <more tokens> or
 + an OPEN PAREN token :: a NAND token :: <a token list representing a boolean expression> @
                                          <a token list representing a boolen expression> @ a CLOSE PAREN token :: <more tokens>
 any other list is syntactically incorrect. *)

(* function to parse the list of tokens *)
let parse_bool_exp tok_list =
(* when possibly parsing a sub-expression, return the first legal expression read
   and the list of remaining tokens  *)
  let rec parser tlist = match tlist with
    | (CONST b)::t -> (Const b, t)
    | (VAR s)::t -> (Id s, t)
    | OP::NAND::t -> let (a1, t1) = parser t in
                    let (a2, t2) = parser t1 in
                    (match t2 with
                     | CP::t' -> ((Nand (a1,a2)), t')
		                 | _ -> invalid_arg "sexp: missing )")
    | OP::AND::t -> let (a1, t1) = parser t in
                    let (a2, t2) = parser t1 in
                    (match t2 with
                     | CP::t' -> ((And (a1,a2)), t')
		                 | _ -> invalid_arg "sexp: missing )")
    | OP::OR::t -> let (a1, t1) = parser t in
                   let (a2, t2) = parser t1 in
                   (match t2 with
                     | CP::t' -> ((Or (a1,a2)), t')
		                 | _ -> invalid_arg "sexp: missing )")
    | OP::XOR::t -> let (a1, t1) = parser t in
                    let (a2, t2) = parser t1 in
                    (match t2 with
                     | CP::t' -> ((Xor (a1,a2)), t')
		                 | _ -> invalid_arg "sexp: missing )")
    | OP::EQ::t -> let (a1, t1) = parser t in
                    let (a2, t2) = parser t1 in
                    (match t2 with
                     | CP::t' -> ((Eq (a1,a2)), t')
		                 | _ -> invalid_arg "sexp: missing )")
    | OP::NOT::t -> let (a1, t1) = parser t in
                    (match t1 with
                     | CP::t' -> ((Not (a1)), t')
 		                 | _ -> invalid_arg "sexp: missing )")
    | _ -> invalid_arg "parse failed."
  in let bx, t = parser tok_list in
     match t with
     | [] -> bx
     | _ -> invalid_arg "parse failed: extra tokens in input."

(* pipeline from s-expression string to boolExpr *)
let bool_exp_of_s_exp s = s |> wordlist |> tokens |> parse_bool_exp

(* evaluate the boolean expression bexp, assuming the variable names
   in the list tru are true, and variables not in the list are false *)
let rec eval_bool_exp bexp tru =
  match bexp with
  | Const b -> b
  | Id s -> List.mem s tru
  | Nand (x1, x2) -> not ((eval_bool_exp x1 tru) && (eval_bool_exp x2 tru)) (* NAND = not(and) *)
  | And (x1, x2) -> ((eval_bool_exp x1 tru) && (eval_bool_exp x2 tru)) (* both true *)
  | Or (x1, x2) -> ((eval_bool_exp x1 tru) || (eval_bool_exp x2 tru)) (* one or both true *)
  | Xor (x1, x2) -> not ((eval_bool_exp x1 tru) = (eval_bool_exp x2 tru)) (* only one true, not both true or both false, one has to be true and one has to be false *)
  | Eq (x1, x2) -> ((eval_bool_exp x1 tru) = (eval_bool_exp x2 tru)) (* check if they are equal *)
  | Not (x1) -> not (eval_bool_exp x1 tru) (* opposite of the argument *)

(* You need to add some new stuff in here: *)


(* helper function to sort the list given by subsets *)
let rec list_sort lst =
  let sort_help = function
  | h1::h2::t when h1 > h2 -> if List.length h2 > List.length h1 then h1::list_sort(h2::t) else h2::list_sort(h1::t) (* compares values and size of sublists and sorts accordingly *)
  | (h1::t) -> let t' = list_sort t in if t' = t then lst else h1::t'
  | t -> t
in sort_help lst

(* list all the subsets of the list s, sorted by size then lexicographically *)
(* subsets: 'a list -> 'a list list *)
let rec subsets s = match s with
| [] -> [[]]
| h::t ->
  let ls = subsets t in
  list_sort (ls @ List.map (fun l -> h::l) ls) (* calls list_sort to sort the list of sublists *)

(* function to remove an element from a list, helper function for remove_duplicates *)
let remove x ls =
  let rec help ls acc = match ls with
  | [] -> List.rev acc
  | h::t -> if (x = h) then help t acc else help t (h::acc)
  in help ls [] (* initialize arguments of help to the inputted list and [] for the accumulator *)

(* a function that removes duplicates from a list, helper for var_list, calls remove *)
let remove_duplicates ls =
  let rec help ls acc = match ls with
    | [] -> List.rev acc
    | h::t -> help (remove h t) (h::acc)
    in help ls [] (* initialize arguments of help to the inputted list and [] for the accumulator *)

(* find all the variable names in a boolExpr, sorted and without duplicates, uses function remove_duplicates to ensure there are not any duplicates *)
(* var_list: boolExpr -> string list *)
let var_list bexp =
  let rec help bexp = match bexp with
  | Const b -> []
  | Id s -> [s]
  | Nand (x1,x2) -> remove_duplicates ((help x1)@(help x2))
  | And (x1,x2) -> remove_duplicates ((help x1)@(help x2))
  | Or (x1,x2) -> remove_duplicates ((help x1)@(help x2))
  | Not (x1) -> remove_duplicates ((help x1))
  | Xor (x1,x2) -> remove_duplicates ((help x1)@(help x2))
  | Eq (x1,x2) -> remove_duplicates ((help x1)@(help x2))
  in help bexp


(* find the list of all lists of variables that when set to true make the expression true *)
(* find_sat_sets: boolExpr -> string list list *)
let find_sat_sets bexp =
  let rec fss_help exp ls acc = match ls with
  | [] -> []
  | h::t -> if (eval_bool_exp exp h) then (h::acc) else (fss_help bexp t acc) (* if eval_bool_exp returns true with the head and the expression then append the head to the accumulator otherwise call the recursive helper on the tail *)
  in fss_help bexp (List.rev (subsets (var_list bexp))) []


let main count =
  let sExpr = String.concat " " (read_lines ()) in
  let bExpr = bool_exp_of_s_exp sExpr in
  let satslist = find_sat_sets bExpr in
  print_endline (match (count,satslist) with
    (true,sl) -> "Number of satisfying assignments = "^(string_of_int (List.length sl))
    | (false,[]) -> "No satisfying assignment"
    | (false,tv::t) -> "First satisfying assignment: {"^(String.concat ", " tv)^"}")
