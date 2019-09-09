Theorem true_can_be_proven : True.
Proof.
  (* I stands for the type that is true . 
   before the last command the subgoals is "True"
   and we need something of type true which is given by I.*)
  exact I.
Qed.

(* false can never be proven hence we proove it's negation *)
Theorem false_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_false.
  exact proof_of_false.
Qed.

Theorem true_impl_true : True -> True.
Proof.
  intros proof_of_true.
  exact I.
  (* exact proof_of_true also works . *)
Qed.

(* true imp false cannot be proven hence we prove the negation *)
Theorem true_impl_false : ~(True -> False).
Proof.
  intros true_imp_false.
  pose (false := true_imp_false I).
  exact false.
Qed.

(* can also be written as *)
Theorem true_imp_false_2 : ~(True -> False ).
Proof.
  intros true_impl_false.
  refine (true_impl_false _).
  exact I.
Qed.

Theorem absurd2 : (forall A C:Prop , A-> ~A -> C).
Proof.
  intros A C.
  intros proof_of_A.
  intros proof_of_nA.
  unfold not in proof_of_nA.
  pose (proof_of_false := proof_of_nA proof_of_A).
  case proof_of_false.
Qed.

Theorem false_no_proof_case : ~False.
Proof.
  intros proof_of_false.
  (* 
     case creates subgoals for every possible construction of its argument 
     if any hypothesis has type false then we can use case <hype>
   *)  
  case proof_of_false.
Qed.

