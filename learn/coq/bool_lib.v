Require Import Bool.
(*
  this has functions that are defined as
  Definition eqb (b1 b2 : bool) :bool :=
    match b1,b2 with 
    | true , true => true
    | true , false => false
    | false , true => false
    | false , false => true
    end.

  Definition Is_true (b : bool) : bool :=
    match b with
    | true => true
    | false => false
    end.

 *)

Theorem true_is_True: Is_true true.
Proof.
  (*
    simpl. stands for simplify here what it does is that it takes the function and applies the argument to
    it. before the vernicaular call simpl. the subgoal is "Is_true true" which is a function call.
    and once simpl. is called that subgoal becomes "True" which can be exacted with I.
   *)
  simpl.
  exact I.
Qed.

Theorem true_is_not_false : ~Is_true (eqb true false).
Proof.
  simpl.
  (* now we have the subgoal false and we need a proof that false cannot be proven 
   we'll use one from the last examples*)
  unfold not.
  intros proof_of_false.
  exact proof_of_false.
  (* case proof_of_false also works here *)
Qed.

(* same stuff but using a previous theorem *)
Theorem false_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_false.
  case proof_of_false.
Qed.

Theorem t_not_f : ~ Is_true (eqb true false).
Proof.
  simpl.
  exact false_cannot_be_proven.
Qed.

(* forall over bools (using case) *)
Theorem eqb_a_a :(forall a:bool , Is_true (eqb a a)).
Proof.
  intros a.
  (* a will have two cases one being true and the other one being false 
   here we can see more that one subgoal*)
  case a.
  (* when a is true*)
  simpl.
  exact I.
  (* when a is false*)
  simpl.
  exact I.
Qed.

Theorem eqb_a_t : (forall a:bool, ( Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
  simpl.
  intros proof_of_true.
  exact I. (* exact proof_of_true also works *)
  simpl.
  intros proof_of_false.
  exact proof_of_false. (* case proof_of_false also works *)
Qed.
