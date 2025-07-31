Require Import little_w_string parser.
From Stdlib Require Import List BinIntDef.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope string_scope.
Import String str intervals syntax AB A D L B.

Definition state1 :=  (("n",(cZ 0,cZ 500))::("x",(cZ 0,cZ 0))::("y",(cZ 0,cZ 0))::nil).

Definition sum_i_to_n :=
  Eval vm_compute in un_annot (parse_instr' 
   "while x < n do [le(x,n)/\pp(y,x)] x:=x+1; y:=x+y done").

Check and.

Eval vm_compute in
  let (i',e) := B.abstract_i sum_i_to_n state1 in
  string_of_a_instr i'.


