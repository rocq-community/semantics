module Str = struct 
  type dummy = string
  type string = dummy

  let string_dec (a:string) (b:string) =
    if a = b then Patched_interp.Left else Patched_interp.Right

  let false_cst = "False"
  let true_cst = "True"
  let between_cst = "between"
  let ge_cst = "ge"
  let le_cst = "le"

  type aexpr = string Patched_interp.aexpr0
  
  type bexpr = string Patched_interp.bexpr0
  
  type instr = string Patched_interp.instr0
  
  type rocq_assert = string Patched_interp.assert0

  type condition = string Patched_interp.condition0
  
  type a_instr = string Patched_interp.a_instr0
  
  let false_assert = Patched_interp.Pred(false_cst, Patched_interp.Nil)

  let rec mark = function
     Patched_interp.Sequence(i1, i2) -> Patched_interp.A_sequence (mark i1, mark i2)
   | Patched_interp.While(b, i) -> Patched_interp.A_while(b, false_assert, mark i)
   | Patched_interp.Skip -> Patched_interp.A_skip
   | Patched_interp.Assign(x, e) -> Patched_interp.A_assign(x, e)

   let rec un_annot = function
     Patched_interp.A_sequence(i1, i2) -> Patched_interp.Sequence(un_annot i1, un_annot i2)
   | Patched_interp.A_while(b, a, i) -> Patched_interp.While(b, un_annot i)
   | Patched_interp.A_skip -> Patched_interp.Skip
   | Patched_interp.A_assign(x, e) -> Patched_interp.Assign(x, e)
   | Patched_interp.Prec(_, i) -> un_annot i
end
