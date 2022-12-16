# Taint Analysis in IMP

## Deliverables

Everything was done inside of ```TaintAnalysis.v```, running with Proof Assistant in EMACS.

## Changes to the language

This is Jason's final project for CMSC631, implementing taint analysis in IMP in Coq. This feature allows us to keep track of variable data flow by defining sources of taint and keeping track of the list of variables that are "tainted" by the taint sources. The following `aexp` and `bexp` remain unchanged from IMP:

```
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
```

There is one additional command to define a source of taint, in the form of a variable:

```
Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com)
| CTaintSource (x : string). (* taint variable x *)
```

With this, we can run `taint_eval` on any IMP program and find data flow. For termination purposes, `taint_eval` is defined as a relation (similar to how `ceval` was a relation): `taint_eval b st t c st' t'`, or better yet, the notation `b (^-^) st <(._.<) t <(._.)> c <(._.)> st' (>._.)> t'`

## Examples and Rationale 

Let's start easy with a program like this:
```
x = 42;
taint x;
y = x / 2;
```
In `taint_eval`, as expected we would expect y to also be tainted: 
```
taint_eval false empty_st []
  x = 42;
  taint x;
  y = x / 2;
[y !-> 21; x !-> 42] [y; x]
```

As you can expect, any aritrary long chain of assignments will all be tainted. But how do we handle the two more interesting commands -- `if`'s and `while`'s? For an if, I opted to taint both paths (this may prove to be overtaining, but in the "security through PL" scope, it atleast guarantees implicit tainting). Here's an example:
```
taint_eval false empty_st []
  x = 42;
  taint x;
  if x > 0:
    y = 1
  else:
    y = 2
    z = 2
[y !-> 1; x !-> 42] [y; z; x]
```
Obviously, y's value depends on x, therefore it is tainted. However, the existence of z also depends on x, thus z is also tainted. 
`while`'s are easier to take care of, tainting everything in the `while` if `b = true` and b somehow depends on a tainted variable:
```
taint_eval false empty_st []
  x = 42;
  taint x;
  while x > 0:
    x = x - 1;
    y = 2
  end
[y !-> 2; x !-> 0; x !-> 1 ... x !-> 42] [y; x; x... x]
```
Those are all the "interesting" commands to look at in terms of taint analysis. There are more examples in the `TaintAnalysis.v` file itself.

## Da Rules

Written these in IMP style for readability:
```
---------------------------------------                   (T_Skip)
st, t =[ skip ]=> st, t
```
```
aexp a is tainted in t = true
aeval a in st = n
---------------------------------------                   (T_Asgn_Tainted)
st, t =[ x := a ]=> (x !-> n; st), x::t
```
```
aexp a is tainted in t = false
aeval a in st = n
b is true ( we are in the body of a tainted guard)
---------------------------------------                   (T_Asgn_Implicit_Tainted)
st, t =[ x := a ]=> (x !-> n; st) x::t
```
```
aexp a is tainted in t = false
aeval a in st = n
b is false
---------------------------------------                   (T_Asgn_Untainted)
st, t =[ x:= a ]=> (x !-> n; st) (remove string_dec x t)
```
```
st, t =[ c1 ]=> st', t'
st', t' =[ c2 ]=> st'', t''
---------------------------------------                   (T_Seq)
st, t =[ c1; c2 ]=> st'', t''
```
```
beval b in st = true
bexp b is tainted in t = false
st, t =[ c1 ]=> st', t' | b as false
---------------------------------------                   (T_IfTrue)
st, t =[ if b then c1 else c2 ]=> st', t'
```
```
beval b in st = true
bexp b is tainted in t = true
st, t =[ c1 ]=> st', t' | b as true
st, t =[ c2 ]=> st'', t'' | b as true
---------------------------------------                   (T_IfTrue_Implicit)
st, t =[ if b then c1 else c2 ]=> st', t'++t''
```
```
beval b in st = false
bexp b is tainted in t = false
st, t =[ c2 ]=> st', t' | b as false
---------------------------------------                   (T_IfFalse)
st, t =[ if b then c1 else c2 ]=> st', t'
```
```
beval b in st = false
bexp b is tainted in t = false
st, t =[ c1 ]=> st', t' | b as true
st, t =[ c2 ]=> st'', t'' | b as true
---------------------------------------                   (T_IfFalse_Implicit)
st, t =[ if b then c1 else c2 ]=> st'', t'++t''
```
```
beval b in st = false
---------------------------------------                   (T_WhileFalse)
st, t =[ while b do c end ]=> st, t
```
```
beval b in st = true
bexp b is tainted in t = true
st, t =[ c ]=> st', t' | b as true
st', t' =[ while b do c end ]=> st'', t''
---------------------------------------                   (T_WhileTrue_Implicit)
st, t =[ while b do c end ]=> st'', t'' 
```
```
beval b in st = true
bexp b is tainted in t = false
st, t =[ c ]=> st', t' | b as false
st', t' =[ while b do c end ]=> st'', t''
---------------------------------------                   (T_WhileTrue)
st, t =[ while b do c end ]=> st'', t'' 
```
Unless otherwise specified, b is `false` in the context of `_, _ =[...]=> _, _`

## Correctness

This part is half complete because other exams and projects exist. See the `TaintAnalysis.v` file's bottom to see how far I got lol. I think I'm on the right track, following in the footsteps of proving `ceval_determinism`. The theorem saying "the state of variables should not affect the taint given the same program" :
```
forall st1 st2 t st1' st2' t1 t2 c,
    taint_eval false st1 t c st1' t1 ->
    taint_eval false st2 t c st2' t2 ->
    t1 = t2.
```

## Crab
```
                            e$$$      .c.                 
                          4$$$$     ^$$$$$.
                          $$$$        $$$$$.
                         .$$$$         $$$$$
                      z$$$$$$$$       $$$$$$b
                     $$$$$$""          *$$$$$$.
                     $$$$$                $$$$$r
            \        $$$*     dc    ..    '$$$$b
            4       $$$F      $F    $%     $$$$$       4
            'r     4$$$L  .e$$$$$$$$$$bc    $$$$r      $
             $.    '$$$$z$$$$$$$$$$$$$$$$$..$$$$$     z$
             $$$c   $$$$$$$$$$$$$$$$$$$$$$$$$$$$F  .d$$*
               "$$$. $$$$$$$$$$$$$$$$$$$$$$$$$$P z$$$"
                  "$$b$$$$$$$$$$$$$$$$$$$$$$$$$d$$*
                     "$$$$$$$$$$$$$$$$$$$$$$$$$P"
         ^         .d$$$$$$$$$$$$$$$$$$$$$$$$"
          "e   .e$$$$*"$$$$$$$$$$$$$$$$$$$$$$$$$$e..  e"
           *$$$$P"     ^$$$$$$$$$$$$$$$$$$$$P ""**$$$$
            *"          $$$$$$$$$$$$$$$$$$$P
                      .$$"*$$$$$$$$$$$$P**$$e
                     z$P   J$$$$$$$$$$$e.  "$$c     .
                    d$" .$$$$$$*""""*$$$$$F  "$$. .P
             ^%e.  $$   4$$$"          ^$$     "$$"
                "*$*     "$b           $$"       ^
                           $r          $
                            ".        $    
                             ^
```

Thanks for a great semester!
