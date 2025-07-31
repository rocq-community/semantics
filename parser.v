From Stdlib Require Import String Ascii List ZArith.
Require Import little_w_string.

Import syntax str AB A D L.

Inductive lex_state : Type :=
  Start | In_num | In_id | In_spec.

Inductive token : Type :=
  T_id (_ : string) | T_num (_ : Z) | T_variables | T_in | T_end
| T_semicolon | T_assign | T_lt | T_plus | T_skip | T_while
| T_do | T_done | T_open | T_close | T_open_B | T_close_B
| T_minus | T_comma | T_bang | T_conj | T_open_S | T_close_S.

Open Scope Z_scope.
Open Scope char_scope.
Open Scope string_scope.

Inductive char_category : Type :=
 Digit | Alpha | Space | Other.

Fixpoint Z_of_rev_string (s:string) : Z :=
 match s with
   "" => 0
 | String a tl => (Z_of_nat (nat_of_ascii a) -
                   Z_of_nat (nat_of_ascii "0"%char))+10*Z_of_rev_string tl
 end.

Definition T_num_of_rev_string (s:string) : token :=
  T_num (Z_of_rev_string s).

Fixpoint rev_string_aux (s acc:string) {struct s}: string :=
 match s with "" => acc | String a s' => rev_string_aux s' (String a acc) end.

Definition rev_string (s:string) := rev_string_aux s "".

Definition string_token (rev_buf :string) : token :=
  let buf := rev_string rev_buf in
  if string_dec buf "variables" then
     T_variables
  else if string_dec buf "in" then
     T_in
  else if string_dec buf "end" then
     T_end
  else if string_dec buf "while" then
     T_while
  else if string_dec buf "do" then
     T_do
  else if string_dec buf "done" then
     T_done
  else if string_dec buf "skip" then
     T_skip
  else T_id buf.

Fixpoint special_tokens (rev_buf:string) (acc:list token) {struct rev_buf}:
  option (list token) :=
  match rev_buf with
    "" => Some acc
  | String ";" tl => special_tokens tl (T_semicolon::acc)
  | String "=" (String ":" tl) => special_tokens tl (T_assign::acc)
  | String "<" tl => special_tokens tl (T_lt::acc)
  | String "+" tl => special_tokens tl (T_plus::acc)
  | String "(" tl => special_tokens tl (T_open::acc)
  | String ")" tl => special_tokens tl (T_close::acc)
  | String "{" tl => special_tokens tl (T_open_B::acc)
  | String "}" tl => special_tokens tl (T_close_B::acc)
  | String "[" tl => special_tokens tl (T_open_S::acc)
  | String "]" tl => special_tokens tl (T_close_S::acc)
  | String "-" tl => special_tokens tl (T_minus::acc)
  | String "," tl => special_tokens tl (T_comma::acc)
  | String "\" (String "/" tl) => special_tokens tl (T_conj::acc)
  | String "!" tl => special_tokens tl (T_bang::acc)
  | _ => None
  end.

Definition Z_of_ascii (a:ascii) := Z_of_nat(nat_of_ascii a).

Definition is_digit (a:ascii) : bool :=
  match Z.compare (Z_of_ascii a) (Z_of_ascii "0"%char) with
    Lt => false
  | Eq => true
  | Gt => match Z.compare (Z_of_ascii a) (Z_of_ascii "9"%char) with
      Gt => false
    | _ =>  true
    end
  end.

Fact example_is_digit : is_digit "8" = true.
Proof refl_equal true.

Definition is_alpha (a:ascii) : bool :=
  match Z.compare (Z_of_ascii a) (Z_of_ascii "A"%char) with
    Lt => false
  | Eq => true
  | Gt => match Z.compare (Z_of_ascii a) (Z_of_ascii "Z"%char) with
      Gt => match Z.compare (Z_of_ascii a) (Z_of_ascii "_"%char) with
        Eq => true
      | _ => match Z.compare (Z_of_ascii a) (Z_of_ascii "a"%char) with
          Lt => false
        | Eq => true
        | Gt => match Z.compare (Z_of_ascii a) (Z_of_ascii "z"%char) with
            Gt => false
          | _ => true
          end
        end
      end
    | _ => true
    end
  end.

Definition is_space (a:ascii) : bool :=
  if ascii_dec a " " then true
  else if ascii_dec a "010" then true
  else if ascii_dec a "013" then true
  else if ascii_dec a "009" then true
  else false.

Definition cat_of_char (a:ascii) : char_category :=
  if is_digit a then
     Digit
  else if is_alpha a then
     Alpha
  else if is_space a then
     Space
  else Other.

Fixpoint tokenize (s:string)(st:lex_state)(rev_buf:string) {struct s}
    :list token :=
  match s with
    "" =>
      match st with
        Start => nil
      | In_num => T_num_of_rev_string rev_buf::nil
      | In_id => string_token rev_buf::nil
      | In_spec => match special_tokens rev_buf nil with
                     Some ts => ts | None => nil
                   end
      end
  | String a s' =>
      match st with
        Start =>
          match cat_of_char a with
            Digit =>
            tokenize s' In_num (String a "")
          | Alpha =>
             tokenize s' In_id (String a "")
          | Space =>
             tokenize s' Start rev_buf
          | Other =>
            tokenize s' In_spec (String a "")
          end
      | In_num =>
          match cat_of_char a with
            Digit =>
            tokenize s' In_num (String a rev_buf)
          | Alpha =>
            T_num (Z_of_rev_string rev_buf)::
            tokenize s' In_id (String a "")
          | Space =>
            T_num (Z_of_rev_string rev_buf)::tokenize s' Start ""
          | Other =>
            T_num (Z_of_rev_string rev_buf)::tokenize s' In_spec (String a "")
          end
      | In_id =>
          match cat_of_char a with
            Digit =>
            tokenize s' In_id (String a rev_buf)
          | Alpha =>
             tokenize s' In_id (String a rev_buf)
          | Space =>
             string_token rev_buf::tokenize s' Start rev_buf
          | Other =>
             string_token rev_buf::tokenize s' In_spec (String a "")
          end
      | In_spec =>
          match cat_of_char a with
            Digit =>
            match special_tokens rev_buf nil with
              Some ts => (ts++tokenize s' In_num (String a ""))%list
            | None => nil
            end
          | Alpha =>
            match special_tokens rev_buf nil with
              Some ts => (ts++tokenize s' In_id (String a ""))%list
            | None => nil
            end
          | Space =>
            match special_tokens rev_buf nil with
              Some ts => (ts++tokenize s' Start "")%list
            | None => nil
            end
          | Other =>
            tokenize s' In_spec (String a rev_buf)
          end
      end
  end.

Fixpoint parse_variables (l:list token) :
  option ((list (string*Z))*list token) :=
  match l with
    T_id s::T_minus::T_num n::T_in::tl => Some((s,-n)::nil, tl)
  | T_id s::T_num n::T_in::tl => Some((s,n)::nil, tl)
  | T_id s::T_minus::T_num n::T_semicolon::tl =>
    match parse_variables tl with
      Some(l,r) => Some((s,-n)::l,r)
    | None => None
    end
  | T_id s::T_num n::T_semicolon::tl =>
    match parse_variables tl with
      Some(l,r) => Some((s,n)::l,r)
    | None => None
    end
  | _ => None

  end.

Definition parse_right_expr (f:list token -> nat -> option(aexpr*list token)):
  list token -> nat -> aexpr -> option (aexpr*list token) :=
  fix p_r_e (l:list token) (n:nat)(acc: aexpr) {struct n} :
      option (aexpr*list token) :=
    match n with
      0%nat => None
    | S p =>
      match l with
        T_plus::T_minus::T_num n::tl => p_r_e tl p (aplus acc (anum (-n)))
      | T_plus::t_atom::tl =>
        match t_atom with
          T_num n => p_r_e tl p (aplus acc (anum n))
        | T_id s => p_r_e tl p (aplus acc (avar s))
        | T_open => match f tl p with
                      Some(e,T_close::tl') => p_r_e tl' p (aplus acc e)
                    | _ => None
                    end
        | _ => None
        end
      | _ => Some(acc, l)
      end
    end.

Fixpoint parse_expr (l:list token)(n:nat){struct n}
   : option(aexpr*list token) :=
  match n with
    0%nat => None
  | S p =>
    match l with
      T_num n::tl => parse_right_expr parse_expr tl p (anum n)
    | T_minus::T_num n::tl => parse_right_expr parse_expr tl p (anum (-n))
    | T_id s::tl => parse_right_expr parse_expr tl p (avar s)
    | T_open::tl => match parse_expr tl p with
                      Some(e,T_close::tl') =>
                      parse_right_expr parse_expr tl' p e
                    | _ => None
                    end
    | _ => None
    end
  end.


Fixpoint parse_expr_list(l:list token)(n:nat) {struct n}:
  (list aexpr)*list token :=
  match n with
    0%nat => (nil,l)
  | S p =>
    match parse_expr l n with
      Some(e,tl) =>
      match tl with
        T_comma::tl =>
        let (l,tl) := parse_expr_list tl p in (e::l,tl)
      | _ => (e::nil, tl)
      end
    | None => (nil, l)
    end
  end.

Definition parse_bexpr (l:list token) (n:nat) : option(bexpr * list token) :=
  match parse_expr l n with
    Some(e1, T_lt::l') =>
    match parse_expr l' n with
      Some (e2, l'') => Some (blt e1 e2, l'')
    | _ => None
    end
  | _ => None
  end.

Fixpoint parse_elem_assert (l:list token) (n:nat) {struct n}:
  option(assert*list token) :=
match parse_bexpr l n with
  Some(e, tl) => Some(a_b e, tl)
| None =>
  match n with
    0%nat => None
  | S p =>
    match l with
      T_id s::T_open::tl =>
      let (l, tl) := parse_expr_list tl n in
      match tl with
        T_close::tl => Some(pred s l, tl)
      | _ => None
      end
    | T_bang::l =>
      match parse_elem_assert l p with
        Some(a, l) => Some(a_not a, l)
      | _ => None
      end
    | _ => None
    end
  end
end.

Fixpoint parse_assert (l:list token)(n:nat) {struct n}:
  option(assert*list token) :=
match n with
  0%nat => None
| S p =>
  match parse_elem_assert l p with
    Some(a1, T_conj::tl) =>
    match parse_assert tl p with
      Some(a2, tl) => Some(a_conj a1 a2, tl)
    | None => None
    end
  | Some(a, tl) => Some(a, tl)
  | None => None
  end
end.

Definition parse_elem_instr
   (parse_instr:list token -> nat -> option(instr*list token))
   (l:list token)(n:nat) :option(instr*list token) :=
 match l with
   T_skip::tl => Some(skip, tl)
 | T_id var::T_assign::tl =>
   match parse_expr tl n with
     Some(e,tl) => Some(assign var e, tl)
   | None => None
   end
 | T_while::tl =>
   match parse_bexpr tl n with
     Some(b,T_do::tl) =>
     match parse_instr tl n with
       Some(i,T_done::tl) =>
       Some(while b i, tl)
     | _ => None
     end
   | _ => None
   end
 | T_open_B::tl =>
   match parse_instr tl n with
     Some(i,T_close_B::tl) => Some(i,tl)
   | _ => None
   end
 | _ => None
 end.

Definition parse_elem_a_instr
   (parse_instr:list token -> nat -> option(a_instr*list token)) :=
fix peai (l:list token)(n:nat){struct n} : option(a_instr*list token):=
 match n with
   O%nat => None
 | S p =>
   match l with
     T_skip::tl => Some(a_skip, tl)
   | T_open_S::tl =>
     match parse_assert tl n with
       Some(a,T_close_S::tl) =>
       match peai tl p with
         Some(i, tl) => Some(prec a i, tl)
       | None => None
       end
     | _ => None
     end
   | T_id var::T_assign::tl =>
     match parse_expr tl n with
       Some(e,tl) => Some(a_assign var e, tl)
     | None => None
     end
   | T_while::tl =>
     match parse_bexpr tl n with
       Some(b,T_do::T_open_S::tl) =>
       match parse_assert tl n with
         Some(a,T_close_S::tl) =>
         match parse_instr tl n with
           Some(i,T_done::tl) =>
           Some(a_while b a i, tl)
         | _ => None
         end
       | _ =>  None
       end
     | _ => None
     end
   | T_open_B::tl =>
     match parse_instr tl n with
       Some(i,T_close_B::tl) => Some(i,tl)
     | _ => None
     end
   | _ => None
   end
 end.

Fixpoint parse_a_instr (l:list token)(n:nat){struct n} :
  option(a_instr*list token) :=
  match n with
    0%nat => None
  | S p =>
    match parse_elem_a_instr parse_a_instr l p with
      Some(i,tl) as it =>
      match tl with
        T_semicolon::tl =>
        match parse_a_instr tl p with
          Some(i', tl) =>
          Some(a_sequence i i', tl)
        | None => None
        end
      | _ => it
      end
    | _ => None
    end
  end.

Fixpoint parse_instr (l:list token) (n:nat) {struct n} :
  option(instr*list token) :=
  match n with
    0%nat => None
  | S p =>
    match parse_elem_instr parse_instr l p with
      Some(i,tl) as it =>
      match tl with
        T_semicolon::tl =>
        match parse_instr tl p with
          Some(i', tl) =>
          Some(sequence i i', tl)
        | None => None
        end
      | _ => it
      end
    | _ => None
    end
  end.

Definition parse_program (l:list token) :
   option((list(string*Z))*instr) :=
   match l with
     T_variables::tl =>
     match parse_variables tl with
       Some(l,r) =>
        match parse_instr r (List.length r) with
          Some (i, T_end::nil) => Some(l,i)
        | _ => None
        end
     | None => None
     end
   | _ => None
   end.

Definition parse_a (s:string) :=
   match tokenize s Start "" with
     T_variables::tl =>
     match parse_variables tl with
       Some(l,r) =>
        match parse_a_instr r (List.length r) with
          Some (i, T_end::nil) => Some(l,i)
        | _ => None
        end
     | None => None
     end
   | _ => None
   end.

Definition parse (s : string) : option((list(string*Z))*instr) :=
  parse_program (tokenize s Start "").

Definition parse_instr' (s:string) :=
   let l := tokenize s Start "" in
   match parse_a_instr l (List.length l) with
     Some (i, nil) => i
   | _ => a_skip
   end.

Definition parse_instr'' (s:string) := un_annot (parse_instr' s).

Definition string_of_Z_aux (f:positive -> Z -> string -> string) :=
  fun (p:positive)(x:Z)(acc:string) =>
    match x with
      0 => if string_dec acc "" then "0" else acc
  | _ => let (q,r) := Z.div_eucl x 10 in
          f p q (String (ascii_of_nat (nat_of_ascii "0"%char + Z.abs_nat r))
                   acc)
  end.

Fixpoint string_of_Z_aux2 (p:positive)(x:Z)(acc:string){struct p} : string :=
  match p with
    xH => "Bad arguments for string_of_Z"
  | xO p => string_of_Z_aux string_of_Z_aux2 p x acc
  | xI p => string_of_Z_aux string_of_Z_aux2 p x acc
  end.

Definition string_of_Z (x:Z) : string :=
  match x with
    0 => "0"
  | Zpos p => string_of_Z_aux2 (xI (xI p)) x ""
  | Zneg p => String "-" (string_of_Z_aux2 (xI (xI p)) (Zpos p) "")
  end.

Definition eol := String "010" "".

Fixpoint string_of_env (l:list(string*Z)) : string :=
  match l with
  | (s,n)::nil => s ++ " " ++ string_of_Z n
  | (s,n)::tl =>
    s ++ " " ++ string_of_Z n ++ ";" ++ eol ++ string_of_env tl
  | nil => ""
  end.

Fixpoint string_of_aexpr (e:aexpr) : string :=
  match e with
    anum x => string_of_Z x
  | avar a => a
  | aplus e1 ((aplus _ _) as e2) => string_of_aexpr e1 ++ "+(" ++
                                     string_of_aexpr e2 ++ ")"
  | aplus e1 e2 => string_of_aexpr e1 ++ "+" ++ string_of_aexpr e2
  end.

Definition string_of_bexpr (e:bexpr) :string :=
  match e with
    blt e1 e2 => string_of_aexpr e1 ++ "<" ++ string_of_aexpr e2
  end.

Fixpoint string_of_instr (i:instr) :string :=
  match i with
    skip => "skip"
  | sequence ((sequence _ _) as i1) i2 =>
     "{" ++ string_of_instr i1 ++ "};" ++ eol ++ string_of_instr i2
  | sequence i1 i2 =>
    string_of_instr i1 ++ ";" ++ eol ++ string_of_instr i2
  | assign x e => x ++ ":=" ++ string_of_aexpr e
  | while b i => "while " ++ string_of_bexpr b ++ " do" ++ eol ++
                  string_of_instr i ++ eol ++ "done" ++ eol
  end.

Fixpoint string_of_list (l:list aexpr) : string :=
  match l with
    nil => ""
  | e::nil => string_of_aexpr e
  | e::tl => string_of_aexpr e ++ "," ++ string_of_list tl
  end.

Fixpoint string_of_assert (a:assert) :string :=
  match a with
    a_b b => string_of_bexpr b
  | a_not a => "not " ++ string_of_assert a
  | a_conj a1 a2 => string_of_assert a1 ++ "&" ++ string_of_assert a2
  | pred s l => s ++ "(" ++ string_of_list l ++ ")"
  end.

Fixpoint string_of_a_instr (i:a_instr) :string :=
match i with
  a_skip => "skip"
  | a_sequence ((a_sequence _ _) as i1) i2 =>
     "{" ++ string_of_a_instr i1 ++ "};" ++ eol ++ string_of_a_instr i2
  | a_sequence i1 i2 =>
    string_of_a_instr i1 ++ ";" ++ eol ++ string_of_a_instr i2
  | a_assign x e => x ++ ":=" ++ string_of_aexpr e
  | a_while b a i => "while " ++ string_of_bexpr b ++ " do" ++ eol ++
      "[" ++ string_of_assert a ++ "]" ++ eol ++
                  string_of_a_instr i ++ eol ++ "done" ++ eol
  | prec a i => "[" ++ string_of_assert a ++ "]" ++ eol ++ string_of_a_instr i
  end.


Definition interp (n:nat) (s:string) : string :=
   match parse s with
     Some(r,i) =>
     match f_star n r i with
       Some (l,skip) => "Complete computation" ++ eol ++
                        string_of_env l
     | Some (l,i) => "Incomplete computation" ++ eol ++
                      "variables " ++ string_of_env l ++ " in" ++
                      eol ++ string_of_instr i ++ "end"
     | None => "An error occurred while executing"
     end
   | None => "An error occurred while parsing"
   end.

Definition PP (s:string) := True.

Ltac pretty_hyp_curses id id1 :=
  match type of id with
    exec ?r ?i ?r' => idtac "ok";
    let res := eval vm_compute in
         ("execution in state " ++ eol ++ string_of_env r ++ eol ++
                "of instruction" ++ eol ++ String "027" "[0;31;48m" ++
                string_of_instr i ++ String "027" "[0;30;48m" ++ eol ++
                "terminates and yields" ++ eol ++ string_of_env r') in
    (assert (id1 : PP res ); [unfold PP; trivial| idtac])
  end.

Ltac pretty_hyp id :=
  match type of id with
    exec ?r ?i ?r' => idtac "ok";
    let res := eval vm_compute in
         ("execution in state " ++ eol ++ string_of_env r ++ eol ++
                "of instruction" ++ eol ++ string_of_instr i ++ eol ++
                "terminates and yields" ++ eol ++ string_of_env r') in
    (assert (PP res ); [unfold PP; trivial| idtac])
  end.

Definition parse_assert' (s:string) :=
  let l := tokenize s Start "" in
  match parse_assert l (List.length l) with
    Some(a,tl) => a
  | None => pred "true" nil
  end.

Ltac parse_it :=
  match goal with
    |- context[parse_assert' ?x]=>
    let v := eval vm_compute in (parse_assert' x) in
       change (parse_assert' x) with v; parse_it
  | |- context[parse_instr' ?x] =>
    let v := eval vm_compute in (parse_instr' x) in
      change (parse_instr' x) with v; parse_it
  | |- _ => idtac "parse_done"
  end.

Ltac expand_semantics :=
  cbv beta iota zeta delta [str.string_dec string_dec string_rec
  string_rect sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
  Ascii.ascii_dec Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect
  sym_eq].
