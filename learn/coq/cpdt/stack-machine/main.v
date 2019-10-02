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
    |Binop b e1 e2 =>(compile e2) ++ (compile e1) ++ (iBinop b) :: nil
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

(* lets proove this for any expression e and any program p and any stack s
   the rest of the theorem is self explanatory *)
Lemma compile_correct' : (forall (e:exp)  (p:prog)  (s:stack) ,
                            progDenote (compile e ++ p) s = progDenote p (expDenote e::s) ).
Proof.
  (* doing an induction on e would split it into (Const n) and (Binop e1 e2) *)
  induction e.
  (* the first subgoal is for the (Const n) now we will do intros to quantify the forall expressions *)
  intros.
  (* unfolding the two function applications (ie, compile and expDenote) will simplify the current goal 
     and then we can unfold the progDenote in the begining which will turn the goal into a anonymous recursive definition
     and here we will have the constructor (iConst n) which is know and hence we can use the simpl. to simplify it.
     after which folding back the progDenote will leave us with a trivial goal which can be done using trivial. or reflexivity. 
     or this can also be done with a simple simplify statement followed by a trivial. I dont know why the book did other way around*)
  unfold compile.
  unfold expDenote.
  simpl.
  trivial.
 (* this is what the book did but it can also be done with (simpl. trivial.) which I've done above 
  unfold progDenote at 1.
  simpl.
  fold progDenote.
  trivial.
  *)
  (* now onto the second subgoal
     we will unfold and fold to get some of the simplifications done*)
  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.
  (* the progDenote at LHS has an argument that needs to be written in the other way (associativity )
    and we will use app_assoc_reverse to get it done then we will rewrite it using the inductive hypothesis IHe1 *)
  rewrite app_assoc_reverse.
  rewrite IHe2.
  rewrite app_assoc_reverse.
  rewrite IHe1.
  simpl.
  trivial.
Qed.

(* error found := the older version of compile was (compile e1) :: (complie e2):: binop which was left associative but the 
   function expDenote by nature was right associative and hence while proving it will run into an error. Now I've changed 
   the Definition of compile to (compile e2)::(complie e1)::binop and the proof turned out correct. chnage it back to the 
   older compile to see the errors (then you will also have to change the order in which the inductive hypothesis are being used.
*)