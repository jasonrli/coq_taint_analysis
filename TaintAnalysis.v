Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From PLF Require Import Maps.

(* The aexp, bexp, and com from IMP, with an added command to taint a variable *)

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp)
| ADiv (a1 a2 : aexp).

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BNeq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BGt (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com)
| CTaintSource (x : string). (* taint variable x *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "x / y" := (ADiv x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'taint' x" :=
         (CTaintSource x)
           (in custom com at level 0, x constr at level 0) : com_scope.
    

Open Scope com_scope.

Definition state := total_map nat.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x 
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{a1 / a2}> => (aeval st a1) / (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition empty_st := (_ !-> 0).
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

(* taint is just a list of variables, not their values *)
Definition taint := list string.

(* returns whether or not an ID is tainted *)
Fixpoint is_id_tainted (id: string) (t: taint) : bool :=
  match t with
  | h::t' => if (eqb h id) then true else (is_id_tainted id t')
  | _ => false
  end.

(* determines if an aexp does any operations on a tainted variable *)
Fixpoint is_aexp_tainted  (a: aexp) (t: taint) : bool :=
  match a with
  | ANum n => false
  | AId x => if (is_id_tainted x t) then true else false
  | <{a1 + a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))
  | <{a1 - a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))
  | <{a1 * a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))
  | <{a1 / a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))           
  end.

(* determines if a bexp does any operations on a tainted variable *)
Fixpoint is_bexp_tainted (b: bexp) (t: taint) : bool :=
  match b with
  | <{true}> => false
  | <{false}> => false
  | <{a1 = a2}> => (orb (is_aexp_tainted  a1 t) (is_aexp_tainted a2 t))
  | <{a1 <> a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))
  | <{a1 <= a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))
  | <{a1 > a2}> => (orb (is_aexp_tainted a1 t) (is_aexp_tainted a2 t))
  | <{~ b1}> => (is_bexp_tainted b1 t)
  | <{b1 && b2}> => (orb (is_bexp_tainted b1 t) (is_bexp_tainted b2 t))
  end.

(* "this is super cursed" - Leo *)
Reserved Notation
  "it '(^-^)' st '<(._.<)' t '<(._.)>' c '<(._.)>' st' '(>._.)>' t'"
  (at level 40, c custom com at level 99,
   it constr, st constr, st' constr, t constr, t' constr at next level).

(* starts with a state and a taint, evaluates the command into a new state and
   new taint list, the bool is to keep track of if the current taint_eval is within
   a block of code in a tainted guard, and thus will need to be tainted *)
Inductive taint_eval : bool -> state -> taint -> com -> state -> taint ->  Prop :=
| T_Skip : forall it st t,
    taint_eval it st t <{skip}> st t
| T_Asgn_Tainted : forall it st t a n x,
    is_aexp_tainted a t = true ->
    aeval st a = n ->
    taint_eval it st t <{x:=a}> (x !-> n; st) (x::t)
| T_Asgn_Implicit_Tainted : forall it st t a n x,
    is_aexp_tainted a t = false ->
    aeval st a = n ->
    it = true ->
    taint_eval it st t <{x:=a}> (x !-> n; st) (x::t)
| T_Asgn_Untainted : forall it st t a n x,
    is_aexp_tainted a t = false ->
    aeval st a = n ->
    it = false ->
    taint_eval it st t <{x:=a}> (x !-> n; st) ((remove string_dec) x t)
| T_Seq : forall it c1 c2 st t st' t' st'' t'',
    taint_eval it st t c1 st' t' ->
    taint_eval it st' t' c2 st'' t'' ->
    taint_eval it st t <{c1;c2}> st'' t''
| T_IfTrue_Implicit : forall it st t st' t' st'' t''  b c1 c2,
    beval st b = true ->
    is_bexp_tainted b t = true ->
    taint_eval true st t c1 st'' t'' ->
    taint_eval true st t c2 st' t' ->
    taint_eval it st t <{if b then c1 else c2 end}> st'' (t'++t'')
| T_IfTrue : forall it st t st' t' b c1 c2,
    beval st b = true ->
    is_bexp_tainted b t = false ->
    taint_eval it st t c1 st' t' ->
    taint_eval it st t <{if b then c1 else c2 end}> st' t'
| T_IfFalse_Implicit : forall it st t st' t' st'' t'' b c1 c2,
    beval st b = false ->
    is_bexp_tainted b t = true ->
    taint_eval true st t c2 st'' t'' ->
    taint_eval true st t c1 st' t' ->
    taint_eval it st t <{if b then c1 else c2 end}> st'' (t'++t'')
| T_IfFalse : forall it st t st' t' b c1 c2,
    beval st b = false ->
    is_bexp_tainted b t = false ->
    taint_eval it st t c2 st' t' ->
    taint_eval it st t <{if b then c1 else c2 end}> st' t'
| T_WhileFalse : forall it b st t c,
    beval st b = false ->
    taint_eval it st t <{while b do c end}> st t
| T_WhileTrue_Implicit : forall it st t st' t' st'' t'' b c,
    beval st b = true ->
    is_bexp_tainted b t = true ->
    taint_eval true st t c st' t' ->
    taint_eval it st' t' <{while b do c end}> st'' t'' ->
    taint_eval it st t <{while b do c end}> st'' t''
| T_WhileTrue : forall it st t st' t' st'' t'' b c,
    beval st b = true ->
    taint_eval it st t c st' t' ->
    is_bexp_tainted b t = false ->
    taint_eval it st' t' <{while b do c end}> st'' t'' ->
    taint_eval it st t <{while b do c end}> st'' t''
| T_TaintSource : forall it st t x,
    taint_eval it st t <{taint x}> st (x::t)    
                                   
  where "it (^-^) st <(._.<) t <(._.)> c <(._.)> st' (>._.)> t'" := (taint_eval it st t c st' t').

(* some examples of basic tainting *)

Example tainting_x_and_y :
  false (^-^) empty_st <(._.<) [] <(._.)>
    X := 42;
    taint X;
    Y := X / 2
  <(._.)> (Y !-> 21; X !-> 42) (>._.)> [Y;X].
Proof.
  apply T_Seq with (X !-> 42) [].
  - apply T_Asgn_Untainted; reflexivity.
  - apply T_Seq with (X !-> 42) ([X]++[]).
    + apply T_TaintSource.
    + apply T_Asgn_Tainted; reflexivity.
Qed.

Example untainting_y :
  false (^-^) (Y !-> 21; X !-> 42) <(._.<) [Y;X] <(._.)>
    Y := 5
  <(._.)> (Y !-> 5; Y !-> 21; X !-> 42) (>._.)> [X].
Proof.
  apply T_Asgn_Untainted; reflexivity.
Qed.

Example taint_list_dup :
  false (^-^) (X !-> 4) <(._.<) [X] <(._.)>
    while (X > 0) do
        X := X - 1
    end
  <(._.)> (X !-> 0; X !-> 1; X !-> 2; X !-> 3; X !-> 4) (>._.)> [X;X;X;X;X].
Proof.
  apply T_WhileTrue_Implicit with (X !-> 3; X !-> 4) [X;X].
  - reflexivity.
  - reflexivity.
  - apply T_Asgn_Tainted; reflexivity.
  - apply T_WhileTrue_Implicit with (X !-> 2; X !-> 3; X !-> 4) [X;X;X].
    -- reflexivity.
    -- reflexivity.
    -- apply T_Asgn_Tainted; reflexivity.
    -- apply T_WhileTrue_Implicit with (X !-> 1; X !-> 2; X !-> 3; X !-> 4) [X;X;X;X].
       --- reflexivity.
       --- reflexivity.
       --- apply T_Asgn_Tainted; reflexivity.
       --- apply T_WhileTrue_Implicit with (X !-> 0; X !-> 1; X !-> 2; X !-> 3; X !-> 4) [X;X;X;X;X].
           ---- reflexivity.
           ---- reflexivity.
           ---- apply T_Asgn_Tainted; reflexivity.
           ---- apply T_WhileFalse. reflexivity.
Qed.

Example taint_list_dedup :
  false (^-^) (X !-> 0; X !-> 1; X !-> 2; X !-> 3; X !-> 4) <(._.<) [X;X;X;X;X] <(._.)>
    X := 42
  <(._.)> (X !-> 42; X !-> 0; X !-> 1; X !-> 2; X !-> 3; X !-> 4) (>._.)> [].
Proof.
  apply T_Asgn_Untainted; reflexivity.
Qed.            

Example if_statement :
  false (^-^) empty_st <(._.<) [] <(._.)>
    if 1 = 2 then
      Y := 1
    else
      Y := 2
    end
  <(._.)> (Y !-> 2) (>._.)> [].
Proof.
  apply T_IfFalse.          
  - reflexivity.
  - reflexivity.
  - apply T_Asgn_Untainted.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
Qed.
  
Example implicit_taint_if_y :
  false (^-^) (X !-> 4) <(._.<) [X] <(._.)>
    if X <= 0 then
      Y := 1
    else
      Z := 2
    end
  <(._.)> (Z !-> 2; X !-> 4) (>._.)> ([Y;X]++[Z;X]).
Proof.
  eapply T_IfFalse_Implicit.
  - reflexivity.
  - simpl. reflexivity.
  - apply T_Asgn_Implicit_Tainted.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
  - apply T_Asgn_Implicit_Tainted.
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
Qed.

Example implicit_taint_while_y :
  false (^-^) (X !-> 1) <(._.<) [X] <(._.)>
    while X > 0 do
      Y := 1;
      X := X - 1                    
    end
  <(._.)> (X !-> 0; Y !-> 1; X !-> 1) (>._.)> [X;Y;X].
Proof.
  apply T_WhileTrue_Implicit with (X !-> 0; Y !-> 1; X !-> 1) [X;Y;X].
  - reflexivity.
  - reflexivity.
  - apply T_Seq with (Y !-> 1; X !-> 1) [Y;X].
    -- apply T_Asgn_Implicit_Tainted.
       --- reflexivity.
       --- reflexivity.
       --- reflexivity.
    -- apply T_Asgn_Tainted.
       --- reflexivity.
       --- reflexivity.
  - apply T_WhileFalse. reflexivity.
Qed.

(* got as far on this as I could, given other exams and projects to study for I couldn't
   make more progress on this *)
Theorem taint_correctness :
  forall st1 st2 t st1' st2' t1 t2 c,
    taint_eval false st1 t c st1' t1 ->
    taint_eval false st2 t c st2' t2 ->
    t1 = t2.
Proof.
  intros st1 st2 t st1' st2' t1 t2 c E1 E2. generalize dependent st2. generalize dependent st2'. generalize dependent t2. induction E1; intros t2 st2 st2' E2; inversion E2; subst; try reflexivity.
  - rewrite H in H3. discriminate.
  - discriminate.
  - rewrite H in H7. discriminate.
  - discriminate.
  - rewrite (IHE1_1 t'0 st'0 st2' H4) in *. apply IHE1_2 with st2 st'0. assumption.
  - replace t' with t'0. replace t'' with t''0. reflexivity.
Admitted.
    
       
  
  
  




















                           


           

        
