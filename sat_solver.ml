(*SUMMARY OF PROJECT: A DPLL SAT solver that takes inputs in DIMACS format*)

(*TYPES/PRINT FUNCTIONS*)

(*These are the current assignments of the variables*)
type assignment = 
  True | False | Neutral

(*This is the current state of the problem*)
type state =
  | Unsat
  | Sat of assignment array
  | Tbd of int list list * assignment array 
  (*int list list is the cnfs, assignment array are the variable values (var number is the location)*)

(*This is what the parser returns- all the information that needs to be gathered from the file*)
type sat_problem = {comments: string list ; number_of_vars: int ; cnfs : int list list}

let string_of_assignment_array arr =
  let string_of_assignment a =
    match a with
    | True -> "True"
    | False -> "False"
    | Neutral -> "Neutral"
  in
  "[" ^ String.concat "; " (Array.to_list (Array.map string_of_assignment arr)) ^ "]"

let string_of_state state =
  match state with Unsat -> "Unsat"
  | Sat _ -> "Sat" 
  | Tbd _ -> "Tbd"

let rec string_of_int_list_list lst =
  match lst with
  | [] -> "[]"
  | hd :: tl ->
    let string_of_int_list lst =
      "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]"
    in
    "[" ^ string_of_int_list hd ^ "; " ^ string_of_int_list_list tl ^ "]"


(*PARSER: string --> sat_problem*)
let parser dimacs_string = 
  let lines = String.split_on_char '\n' dimacs_string in

  let white_space c = 
    c = " " || c = "\t" || c = "\n" || c = "\r"|| c = "" in

  (* Step 1: Extract comments *)
   let rec extract_comments acc rest_lines =
    match rest_lines with
    | [] -> List.rev acc, []
    | a :: rest ->
      if String.length a > 0 && a.[0] = 'c' then
        extract_comments (a :: acc) rest
      else
        List.rev acc, rest_lines
  in
  let comments, rest_lines = extract_comments [] lines in


  (* Step 2: Find the p line and extract number_of_vars *)
  match rest_lines with 
  [] -> failwith "There is no p problem to solve"
  | l::rest -> (
    if (l.[0]) != 'p' then failwith "Incorrect format of problem 1"
    else (
      let p_values = String.split_on_char ' ' l in
      let p_no_white = List.fold_left (fun acc a -> if white_space a then acc else (acc@[a])) [] p_values in 
      let number_of_vars = int_of_string (List.nth p_no_white 2) in

  (* Step 3: Extract CNFs *)
  let cnf_strings = rest in

  let convert_strings_to_ints strings =
    List.fold_left (fun acc str -> if white_space str then acc else acc @ [int_of_string str]) [] strings in
  

  let rec read_cnfs cnfs = 
    match cnfs with 
    [] -> []
    |a::rest ->  
      let a = String.split_on_char ' ' a in
      let length = List.length a in 
      if (length = 0) then  failwith "Incorrect format of problem 2"
      else let cnf = List.rev (List.tl (List.rev a)) in 
      convert_strings_to_ints cnf :: read_cnfs rest in 
  
  let cnfs = List.rev (read_cnfs cnf_strings) in 

  { comments = comments; number_of_vars = number_of_vars; cnfs = cnfs }
))

(*FUNCTIONS NEEDED FOR DPLL*)

(*check if the unsat or sat cases are met*)
let check_if_sat tbd=

  match tbd with Unsat -> Unsat
  | Sat assignment -> Sat assignment
  | Tbd (formulas, assignments) ->  
    if formulas = [] then Sat assignments else (*if there are no more formulas let to satify then it is Sat*)
    let rec help formulas =  
      match formulas with [] -> tbd
      | []::rest -> Unsat (*each formulas needs one thing to be true, and we remove the false ones. So if there are no left, then it is all false*)
      | a::rest -> help rest in 
      help formulas
  
  
(*when the new_assignment is assigned to true
   go over all cnfs and delete the ones with a true statment in them (+ new_assignment)
   and delete the ones with a variable false in them (- new_assignment)
   *)
let rec update_to_true partial_assign var updated_assign  =
    match partial_assign with 
      l::rest -> 
        let has_pos = if List.mem var l then true else false in 
        let has_neg = if List.mem (-var) l then true else false in 
        
        if (has_pos && has_neg) then [[]]
        else if (has_pos) then update_to_true rest var updated_assign
        else if (has_neg) then update_to_true rest var ((List.filter (fun x -> x != (-var)) l)::updated_assign)
        else update_to_true rest var (l::updated_assign) 
      | [] -> updated_assign


(*when the new_assignment is assigned to false
      inverse of above *)
let rec update_to_false partial_assign var updated_assign =
   match partial_assign with 
     l::rest -> (
       let has_pos = if List.mem var l then true else false in 
       let has_neg = if List.mem (-var) l then true else false in 
       
       if (has_pos && has_neg) then [[]]
       else if (has_neg) then update_to_false rest var updated_assign
       else if (has_pos) then update_to_false rest var ((List.filter (fun x -> x != (var)) l)::updated_assign)
       else update_to_false rest var (l::updated_assign))
     | [] -> updated_assign


  let rec check_for_singletons formulas assignment = 
    let rec help formulas_to_check updated_formulas updated_assignment = 
      match formulas_to_check with 
      [] -> Tbd (updated_formulas, updated_assignment) 
      | [a]::rest -> (*if a singleton is found, then we have to check everything again. Note: can make more efficent*) (*TODO: check if already full? NOTE: can make more efficent by dealing with TBD and set value cases seperatly*)
        if a > 0 then 
          if updated_assignment.(a-1) = False then  Unsat 
          else if updated_assignment.(a-1) = True then failwith "This should not be here"
          else ((updated_assignment.(a-1) <- True); check_for_singletons (update_to_true updated_formulas a []) updated_assignment)

        else if a < 0 then 
          if updated_assignment.(-a-1) = True then Unsat 
          else if updated_assignment.(-a-1) = False then failwith "This should not be here"
          else ((updated_assignment.(-a-1) <- False); check_for_singletons (update_to_false updated_formulas (-a) []) updated_assignment)

        else failwith "0 is not a variable"
      | []::rest -> Unsat
      | a::rest -> help rest updated_formulas updated_assignment in 
    help formulas formulas assignment

type literal_forms = 
    | Neg |Pos |Both |None
let pure_literal_checking cnfs variable_numbers =
  (*make an array of size of the number of variables. initalize with all None*)
  (*help: this looks through the cnfs. for each varibel you encounter, 
     it looks and sees if there is a neg or pos and updates location accordingly *)
  
  let varible_occurence_list = List.flatten cnfs in 

  let array = Array.make variable_numbers None in 

  let rec help varible_occurence_list array= 
    match varible_occurence_list with a::rest -> 
      if a = 0 then failwith "0 is not a var"
      else if a > 0 then (
        match array.(a-1) with 
        Neg -> array.(a-1) <- Both; help rest array
        | Pos -> help rest array
        | Both -> help rest array
        | None -> array.(a-1) <- Pos; help rest array )
      else  (
        match array.(-a-1) with 
        Neg ->  help rest array
        | Pos -> array.(-a-1) <- Both; help rest array
        | Both -> help rest array
        | None -> array.(-a-1) <- Neg; help rest array ) 
      | [] -> array in 

    let rec modify_cnfs cnfs array i = (*starts at 0*)
      if i >= variable_numbers then cnfs
      else 
        match array.(i) with 
        Neg ->  modify_cnfs ([(-(i+1))]::cnfs) array (i+1)
        | Pos -> modify_cnfs ([(i+1)]::cnfs) array (i+1)
        | Both -> modify_cnfs cnfs array (i+1)
        | None -> modify_cnfs cnfs array (i+1) in 

      let new_array = help varible_occurence_list array in 
      modify_cnfs cnfs new_array 0 

    
  (*for each cnf, we make note in a new array/list what form we see it in
     Neg
     Pos
     Both
     None
     It starts as all "none"*)


(*DPLL algorthm: 
zero: check for failer/sucsess cases
+ if there is a stray [] -> Unsat 
+ if there is no formulas left -> Sat

0.5: UPDATE
+ we check for each variable if it apears in one state or two. 
+ if it only apears in one state, we add it as a singleton 
   
one: check for the singletons
+ update the partial assignment to include the values of singletons 
+ if there is a contridiction, then you return false
+ if there is not a contridicton, then you 
  1) update the partial assignment
  2) update the update_for_sat_true or update_for_sat_false
if false -> return Unsat. if true -> coninue 

two: find the position of the new variable, assign_pos that you will be assigning (the new nuteral)
+ assign_pos = the space in the array, partial_assign
+ assign_var = the variable number = assign_pos + 1

three: 
try true:
+ update_for_sat_true
  + if false -> Unsat
  + if true -> if recursive call = Sat then Sat else ... 

try false: 
+ update_for_sat_false
  + if false -> Unsat
  + if true -> if recursive call = Sat then Sat else ... 
*)

let run cnf_formulas_og partial_assign_og var_num = 
let rec dpll cnf_formulas_1 partial_assign_1 = 

match check_if_sat (Tbd (cnf_formulas_1, partial_assign_1)) with 
  Unsat -> Unsat
  | Sat assignments -> Sat assignments
  | Tbd (cnf_formulas, partial_assign) ->   

let cnf_formulas = pure_literal_checking cnf_formulas var_num in 

(*unit propagation: check for the singletons, and then edit array accordingly*)
match check_for_singletons cnf_formulas partial_assign with 
    Unsat ->  Unsat
    | Sat assignments -> Sat assignments
    | Tbd (cnf_formulas, partial_assign) -> 


match check_if_sat (Tbd (cnf_formulas, partial_assign)) with 
  Unsat -> Unsat
  | Sat assignments ->  Sat assignments
  | Tbd (cnf_formulas, partial_assign) ->   

 (*choose the first variable that is Neutral to assign *)
 let too_assign =  (Array.find_index (fun a ->  a = Neutral) partial_assign) in 
 match too_assign with None -> failwith "This should not happen. When all vars area assigned, program should end."
| Some new_assignment_pos -> 
    let new_assignment_var = new_assignment_pos + 1 in (*this is bc the 0th index equate to "1"-- this is becuse there is no 0 variable*)


let old_assign= Array.copy partial_assign in 
(*try true*)
Array.set partial_assign new_assignment_pos True ;
let updated_formulas = (update_to_true cnf_formulas new_assignment_var []) in
match (dpll updated_formulas partial_assign) with
   Sat a -> Sat a 
   | Tbd (a, b) -> failwith "dpll should not terminate on Tbd"
   | Unsat -> 

(*try false*)
Array.set old_assign new_assignment_pos False ;
let updated_formulas = (update_to_false cnf_formulas new_assignment_var []) in
match (dpll updated_formulas old_assign) with
   Sat a -> Sat a 
   | Tbd (a, b) -> failwith "dpll should not terminate on Tbd"
   | Unsat -> Unsat in 

   dpll cnf_formulas_og partial_assign_og
  


(*read answer*)
let read_answer state sat_problem =  

  (*comments*) 
  let comment_string = String.trim (List.fold_left (fun string line -> string ^ "\n" ^ line) ""  sat_problem.comments )(*reverse?*) in 

  (*s and v lines*)
  let s_and_v_lines = 
  match state with 
  | Unsat -> "\n" ^ "s Unsatisfiable"
  | Tbd _ -> failwith "Tbd should not be here"
  | Sat variables -> (
    let variables_array_numbers = Array.mapi (fun i v -> if v = True then (i + 1) else if v = False then (-i - 1) else (i + 1) ) variables in
    "\n" ^ "s Satisfiable \n" ^ "v "  ^ String.trim (Array.fold_left (fun acc number -> acc ^ " " ^ string_of_int number) "" variables_array_numbers)) in 

    (comment_string ^ s_and_v_lines ) 


(*RUNNING ON A FILE*)
(*read file*)
let read_file filename =
  let channel = open_in_bin filename in
  let string = really_input_string channel (in_channel_length channel) in
  close_in channel; string

let () = 
let file_name = Sys.argv.(1) in 
let string = String.trim (read_file file_name) in 
let problem = parser string in 
let answer = run problem.cnfs (Array.make problem.number_of_vars Neutral) problem.number_of_vars in 
print_string (read_answer answer problem);


  







  


  

