Require Export little.
Require Export denot.
Require Export axiom.
Require Export abstract_i.
Require Extraction.

Extract Constant Tarski_fix => "let rec fix f = f (fun y -> fix f y) in fix".

(*Since the code will be used inside a call-by-value engine, if-then-else construct
  should not be represented by plain functions, which provoke full computation in
  both branches, when only the branch corresponding to the boolean argument should
  be expanded. *)
Extraction Inline ifthenelse.

Extract Constant excluded_middle_informative => "Left".

Extract Constant constructive_indefinite_description =>
   "fun a -> failwith ""constructive_indefinite_description not provided""".

(* Zopp is used in the parser. *)

Extraction "interp.ml" Z.opp denot.denot ax ab.
