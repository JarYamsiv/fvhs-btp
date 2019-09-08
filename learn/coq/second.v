Theorem true_can_be_proven : True.
Proof.
  (* I stands for the type that is true . *)
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
