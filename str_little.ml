module Str = struct 
  type dummy = string
  type string = dummy

  let string_dec (a:string) (b:string) =
    if a = b then Interp.Left else Interp.Right

  let false_cst = "False"
  let true_cst = "True"
  let between_cst = "between"
  let ge_cst = "ge"
  let le_cst = "le"

  type aexpr = string Interp.aexpr0
  
  type bexpr = string Interp.bexpr0
  
  type instr = string Interp.instr0
  
  type rocq_assert = string Interp.assert0

  type condition = string Interp.condition0
  
  type a_instr = string Interp.a_instr0
  
  let false_assert = Interp.Pred(false_cst, Interp.Nil)

  let rec mark = function
     Interp.Sequence(i1, i2) -> Interp.A_sequence (mark i1, mark i2)
   | Interp.While(b, i) -> Interp.A_while(b, false_assert, mark i)
   | Interp.Skip -> Interp.A_skip
   | Interp.Assign(x, e) -> Interp.A_assign(x, e)

   let rec un_annot = function
     Interp.A_sequence(i1, i2) -> Interp.Sequence(un_annot i1, un_annot i2)
   | Interp.A_while(b, a, i) -> Interp.While(b, un_annot i)
   | Interp.A_skip -> Interp.Skip
   | Interp.A_assign(x, e) -> Interp.Assign(x, e)
   | Interp.Prec(_, i) -> un_annot i
end
