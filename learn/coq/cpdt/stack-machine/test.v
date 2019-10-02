(* importing the required libraries.*)
Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.


(*
defining the operator for the sake of simplicity let's consider only addition and multiplication
*)
Inductive binop : Set := Plus | Times.


(*
  Similarly define meaning for an expression.
*)
Inductive exp: Set :=
|Const : nat -> exp
|Binop:binop -> exp -> exp -> exp.


Check (Const 2).
Check (Binop Plus (Const 2) (Const 3)).
Check (Binop Plus (Const 2) (Binop Times (Const 3) (Const 5))).

(* even though we have operators they dont have mathematical meaning yet so to add those we will use the following Function
  this takes an element of type binop and returns a coq function that have type nat -> nat -> nat
  this function will be usefull when we have to process the expression and gets its value*)
Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(* once we have and expression we need to process it and find it's value. for that we will use this function. 
   now from the Definition of expression we know that it is either a const n or a Recursivly defined expression
   the answet of expdenote will be a natural number , so for const n we can directly return n which is a natural 
   number and for exp we use the function that we have defined above which will be expecting two natural numbers 
   which is what expDenote returns exactly*)
Fixpoint expDenote (e:exp):nat :=
  match e with
    | Const n => n
    |Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(* checking out the working of the above defined functions*)
Eval simpl in expDenote (Const 42).

Eval simpl in expDenote (Binop Plus (Const 3) (Const 7)).

(* the expression will be compiled into a stack machine which has
    1. a stack of natural numbers 
    2. a list of instructions to be executed.
  and it is stated that upon executing the instructions the answer yeiled will be same as the answer when the 
  expression is evaluated.
 *)

(* the machine's syntax would be *)
Inductive instr: Set :=
|iConst : nat -> instr
|iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(* an instruction either pushes an element onto the stack or pops two elements and applies a binary operation on it *)
Print option.
Definition instrDentoe (i:instr) (s:stack): option stack :=
  match i with
    | iConst n => Some (n::s)
    | iBinop b =>
      match s with
        | arg1::arg2::sd => Some ( (binopDenote b) arg1 arg2 :: sd)
        | _ => None
      end
  end.

                                        
Fixpoint progDenote (p:prog) (s:stack) : option stack :=
  match p with
    | nil => Some s (* if the program is empty that means we have the required result in the top of the stack*)
    | i::pd =>
      match instrDentoe i s with
        | None => None (* instrcution denote has failed *)
        |Some sd => progDenote pd sd (* do the rest of the program in the rest of the stack *)
      end
  end.

(* lets define the compile function it takes the expression and generates a program for it *)
Fixpoint compile (e:exp) :prog :=
  match e with
    |Const n => iConst n::nil
    |Binop b e1 e2 =>(compile e1) ++ (compile e2) ++ (iBinop b) :: nil
  end.

(* lets test our compiler *)
Eval simpl in compile (Const 42).
Eval simpl in compile ( Binop Times (Binop Plus (Const 4) (Const 3)) (Const 5)). (* 5*(3+4) *)

(* what about running the programes *)

(* 4*(1+2) = 12 *) 
Eval simpl in progDenote (compile
                            ( Binop Times (Const 4) (Binop Plus (Const 1) (Const 2)))
                         ).

(* and it can be seen that the program is working correctly for the given input *)

(* time to prove this compiles correctly *)
Theorem compile_correct : (forall e:exp ,progDenote (compile e) nil = Some (expDenote e::nil)).
Proof.
  intros e.
Abort.

About "++".

Lemma first_element_lemma : forall A (a : A) (p1 p2 : list A), (a :: p1) ++ p2 = a :: (p1 ++ p2) .
  intros. trivial.
Qed.

Lemma foo1 : forall a p1 p2,  progDenote ((a :: p1) ++ p2) = progDenote (a :: (p1 ++ p2)).
  intros. rewrite first_element_lemma. trivial.
Qed.


Lemma programDenoteOVerAppend : forall p1 p2,  forall s, progDenote (p1 ++ p2) s
                                                       = match progDenote p1 s with
                                                           | None => None
                                                           | Some s1 => progDenote p2 s1
                                                         end.
  intro p1.
  induction p1. simpl;trivial.
  intro p2.
  rewrite first_element_lemma.
  unfold progDenote. fold progDenote.
  destruct a; unfold instrDentoe. intro s; eauto. trivial.
  unfold app; unfold progDenote; fold progDenote. fold app.
Theorem compiler_is_better : (forall (e: exp) (s : stack), progDenote (compile e) s = Some (expDenote e :: s)).
  intro e.
  induction e. simpl. trivial. simpl.