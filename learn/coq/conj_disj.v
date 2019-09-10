Theorem left_or : (forall A B:Prop , A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  (* or_introl because we already have the left side of the or statement . *)
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
  exact proof_of_A_or_B.
Qed.

Theorem right_or : (forall A B:Prop , B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  (* refine understands the type from the subgoal
     and hence shortenes the proof *)
  refine (or_intror _).
  exact proof_of_B.
Qed.

(* this also works*)

Theorem left_or_quick : (forall A B:Prop , A -> A \/ B).
Proof.
  intros A B proof_of_A.
  exact (or_introl proof_of_A).
Qed.

Theorem or_commutes : (forall A B:Prop , A \/ B -> B \/ A).
Proof.
  intros A B.
  intros proof_of_A_or_B.
  (* the case splits the A or B -> B or A into
     A -> B or A
     B -> B or A*)
  case proof_of_A_or_B.
  (* now for the implication statement A -> A or B first captures A using intros and the use or_intror*)
  intros proof_of_A.
  exact (or_intror proof_of_A).
  (* similarly for the second subgoal *)
  intros proof_of_B.
  exact (or_introl proof_of_B).
Qed.

Theorem both_and : (forall A B:Prop , A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  (* think this as a function that has type 'a -> 'b -> 'a and 'b*)
  exact (conj proof_of_A proof_of_B).
Qed.

(* written in a better way with refine which creates two subgoals*)
Theorem both_and_new : (forall A B:Prop , A -> B -> A /\ B).
Proof.
  intros A B proof_of_A proof_of_B.
  refine (conj _ _).
  (* now we have two subgoals A and B whos proof we already have *)
  exact proof_of_A.
  exact proof_of_B.
  (*
    can also be done using
    pose (A_and_B := conj proof_of_A proof_of_B).
    exact A_and_B.
    pose is like having val x = f y in SML
   *)
Qed.

Theorem and_commutes : (forall A B :Prop , A /\ B -> B /\ A ).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
  exact proof_of_B.
  exact proof_of_A.
Qed.

(*
  the case tactic considers all the ways and / or are constructed.
  like the last time we had a definition for bool.
  and when we used case over there. it considers all the ways in which the bool was defined
 *)

Theorem and_commutes_d : (forall A B:Prop , A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  (* same as case but captures the subgoals in the Arguments*)
  destruct A_and_B as [proof_of_A proof_of_B].
  exact (conj proof_of_B proof_of_A).
Qed.

(*
  Double implications (iff)
  orb a b - is defined like eqb a b , except it checks if either one of a,b is true
 *)

Require Import Bool.

Theorem or_a_b_is_a_or_b : (forall a b : bool , Is_true (orb a b) <-> (Is_true a) \/ (Is_true b)).
Proof.
  intros a b.
  (* unfold a <-> b to  a->b and b->a*)
  unfold iff.
  (* now we have and statement refine them using conj to make two subgoals*)
  refine (conj _ _).

  (* the first subgoal is Is_true(orb a b) -> Is_true a /\ Is_true b*)
  intros aorb.
  (* list all four possible outcomes*)
  case a,b.

  (* first one is a true and b true*)
  simpl.
  refine (or_introl _).
  exact I.

  (* a true b false*)
  simpl.
  refine (or_introl _).
  exact I.

  (* a false b true *)
  simpl.
  refine (or_intror _).
  exact I.

  (* both a and b are false*)
  simpl.
  (* simplify aorb , we'll see that it's false and can be used in the next step*)
  simpl in aorb.
  refine (or_introl _).
  exact aorb.

  (* now for prooving the other way around*)
  (* taking out the LHS of the implication
     which is Is_true a /\ Is_true b *)
  intros ta_or_ab.

  (* splitting the rest into cases*)
  case a,b.
  (* Is_true (true || true )*)
  simpl.
  exact I.
  (* true and flase*)
  simpl.
  exact I.
  (* false and true *)
  simpl.
  exact I.
  (* false and false *)
  simpl in ta_or_ab.
  simpl.
  (* ta_or_ab is false \/ false we divide it into cases to yeild two implications*)
  case ta_or_ab.
  intros f.
  exact f.
  intros f.
  exact f.
Qed.

(* now let's try with and*)

Theorem and_a_b_is_a_and_b : (forall a b:bool , Is_true(andb a b) <-> (Is_true a) /\ (Is_true b)).
Proof.
  intros a b.
  (* unfolding to get two implication statements*)
  unfold iff.
  refine (conj _ _). (* splitting them into subgoals *)
  (* LHS of impl *)
  intros a_and_b.

  (* case on RHS *)
  case a,b.

  (* both are true simply refine and exact*)
  simpl.
  refine (conj I I).

  (* true and false the first one can be exacted with I *)
  simpl.
  refine (conj I _).
  (* but for the second case we simplify a_and_b to get False and exacts it *)
  simpl in a_and_b.
  exact a_and_b.

  (* false and true *)
  refine(conj _ I).
  simpl.
  simpl in a_and_b.
  exact a_and_b.

  (* false and false *)
  simpl.
  simpl in a_and_b.
  case a_and_b.

  (* prooving the other way around *)
  (* taking lhs *)
  intros ta_and_tb.

  case a,b.
  (* cases of rhs *)

  (*true true*)
  simpl.
  exact I.

  (*true false*)
  simpl.
  simpl in ta_and_tb.
  destruct ta_and_tb as [ta fb].
  exact fb.

  (* false true *)
  simpl.
  simpl in ta_and_tb.
  destruct ta_and_tb as [fa tb].
  exact fa.

  (* false false *)
  simpl.
  simpl in ta_and_tb.
  destruct ta_and_tb as [fa fb].
  exact fa.
Qed.

(* negb a returns the negation but in bool *)
Theorem negb_is_not : (forall a:bool, Is_true(negb a) <-> ~(Is_true a)).
Proof.
  intros a.
  unfold iff.
  refine (conj _ _).
  (* forward impl t(n a) -> ~t a*)
  case a.
  simpl.
  intros f.
  unfold not.
  intros t.
  exact f.

  simpl.
  intros t.
  unfold not.
  intros f.
  case f.

  (* backward impl *)
  case a.

  simpl.
  unfold not.
  intros tf.
  pose (f := tf I).
  exact f.

  simpl.
  unfold not.
  intros ff.
  exact I.
Qed.
