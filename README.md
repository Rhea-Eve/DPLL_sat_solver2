# DPLL SAT Solver

## Summary of Project
This project implements a DPLL (Davis–Putnam–Logemann–Loveland) SAT solver that takes inputs in DIMACS format. The DIMACS format is a standard text-based format for representing SAT instances.

## Types/Print Functions

### Assignment Type
- `True`: Represents a variable assigned to True.
- `False`: Represents a variable assigned to False.
- `Neutral`: Represents an unassigned variable.

### State Type
- `Unsat`: Represents an unsatisfiable state.
- `Sat of assignment array`: Represents a satisfiable state with assigned variable values.
- `Tbd of int list list * assignment array`: Represents a "To be determined" state with remaining CNFs and partial variable assignments.

### Parser Types
- `sat_problem`: Structure containing comments, the number of variables, and CNFs extracted from the DIMACS file.

### Functions
- `string_of_assignment_array`: Converts an array of assignments to a string.
- `string_of_state`: Converts a state to a string.
- `string_of_int_list_list`: Converts a list of lists of integers to a string.
- `parser dimacs_string`: Parses a DIMACS-formatted string into a `sat_problem` structure.

## DPLL Algorithm Functions

### Check if SAT
- `check_if_sat`: Checks if the SAT problem is satisfiable, unsatisfiable, or to be determined.

### Update Assignments
- `update_to_true`: Updates assignments when a new variable is assigned to True.
- `update_to_false`: Updates assignments when a new variable is assigned to False.

### Singletons and Unit Propagation
- `check_for_singletons`: Checks for singletons (variables that appear alone in CNFs) and updates assignments accordingly.
- `pure_literal_checking`: Checks for pure literals and modifies CNFs accordingly.

## DPLL Algorithm

1. **Check for Failure/Success Cases:**
   - If there is a stray `[]` in CNFs, return `Unsat`.
   - If there are no formulas left, return `Sat`.

2. **Update:**
   - Check for each variable if it appears in one state or two.
   - If it only appears in one state, add it as a singleton.

3. **Check for Singletons:**
   - Update the partial assignment to include the values of singletons.
   - If a contradiction occurs, return `Unsat`.
   - If no contradiction, continue.

4. **Choose the Next Variable to Assign:**
   - Assign the first variable with a `Neutral` state.

5. **Try Assigning True:**
   - Update assignments and CNFs when the new variable is assigned to `True`.
   - Recursively call the DPLL algorithm.
   - If `Sat` is returned, return `Sat`.

6. **Try Assigning False:**
   - Update assignments and CNFs when the new variable is assigned to `False`.
   - Recursively call the DPLL algorithm.
   - If `Sat` is returned, return `Sat`.

7. **Recursive Calls:**
   - Continue recursively calling DPLL until a conclusive result is reached.

## Running on a File
- Read the DIMACS-formatted file.
- Parse the input into a `sat_problem`.
- Run the DPLL algorithm on the parsed problem.
- Print the result.

## Usage
```bash
$ ocaml sat_solver.ml your_dimacs_file.cnf
```

**Note:** Ensure you have OCaml installed to run the program.
