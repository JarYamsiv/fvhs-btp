Require Import Bool.

Theorem orb_is_or : (forall a b:bool , Is_true(orb a b) <-> (Is_true a) \/ (Is_true b)).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).

  (* fwd *)
  case a,b.
  simpl.
  intros t.
  refine (or_introl t).

  simpl.
  intros t.
  refine (or_introl t).

  simpl.
  intros t.
  refine (or_intror t).

  simpl.
  intros f.
  refine (or_introl f).

  (* bkd *)
  case a,b.

  simpl.
  intros tt.
  exact I.

  simpl.
  intros tf.
  exact I.

  simpl.
  intros ft.
  exact I.

  simpl.
  intros ff.
  case ff.
  intros f.
  exact f.
  intro f.
  exact f.
Qed.
