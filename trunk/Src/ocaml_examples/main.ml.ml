
let (nvars, target) = BoolFormula.from_dimacs stdin

let is_member assignments =
  match Oracle.is_satisfiable_with_assumption nvars target assignments with
    | None -> Query.NO
    | Some _ -> Query.YES

let is_comember assignments =
  let not_target = BoolFormula.Not target in
    match Oracle.is_satisfiable_with_assumption nvars not_target assignments 
    with
      | None -> Query.NO
      | Some _ -> Query.YES

let is_equivalent n conj =
  let conjecture = BoolFormula.from_boolformula_t conj in
  match Oracle.is_equivalent nvars target conjecture with
    | None -> Query.EQ
    | Some assignment -> 
        let counterexample = Array.sub assignment 0 (succ n) in
          Query.CE counterexample

let init_nvars = ref nvars
let _ = Arg.parse [] (fun str -> init_nvars := int_of_string str)
  "Usage: learnBoolean <init num of vars>"

let learnt = Cdnfp.go (!init_nvars) is_member is_comember is_equivalent 

let _ = 
  (BoolFormula.print (BoolFormula.from_boolformula_t learnt);
   print_newline ())
