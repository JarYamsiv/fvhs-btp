Definition first : forall A:Prop, A-> A.
Proof.
  intros A a.
  exact a.
  Show Proof.
Defined.

Definition same_proof (A : Prop) : A -> A := fun a : A => a.


Section AandB.
  Variable A B : Prop.
  Variable aAb : A /\ B.

  Lemma aNbImpliesA : A. 
    destruct aAb. trivial.
    Show Proof.
  Qed.

  Definition anotherProof : A := match aAb with
                                 | conj aproof _ => aproof
                                 end.
  Print conj.
  
  Lemma aNbImpliesB : B. 
    destruct aAb. trivial.
  Qed.
  
End AandB.

Require Vector.

Search ( forall n : nat,  _ -> Vector.t _ n).

Definition eqsomething : forall A : Type, A -> A.
  
Definition compose (A : Type)(B : A -> Type)
           (C : forall a, B a -> Type)
           ( f : forall a : A, B a) (g : forall a, forall b : B a, C a b) : forall a, C a (f a):= fun a => g a (f a).

Check aNbImpliesA.
Print first.
Print same_proof.
Check I.
Print True.
Compute same_proof True I.
Compute first True I.