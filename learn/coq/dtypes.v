(*
here foo takes an argument of type int and returns a new type based on the value of the argument
ie, if the argument was 0 then what it returns will be a type that is nat
and when the argument is anything else it returns the type nat*nat
*)
Definition foo (n : nat) :=
  match n with
    | 0 => nat
    | _ => (nat * nat)%type
  end.

(* as expected the type of the function will be form nat to type
  that is what the function returns will be a type and not some value
  in Dependent types even types are treated as values.*)
Check foo.

(*
  now lets look at this function . it takes a nat and returns a value that has type (foo n)
  and from definition of foo we know that returns different types based on its argument
  and hence the function bar also has to follow the same. it returns a simple integer when the
  argument is 0 and when the argument is anything else it returns an element of the type nat*nat
*)
Definition bar (n:nat) : foo n :=
  match n with
    | 0 => 42
    | _ => (42,42)
  end.

(*
  this is another way to write the same function. the refine is used when we know the structure of 
  the proof but dont exactly know where each thing needs to be. and these places are given by _ 
  coq inferes what they need to be based on the dictionary that is available.
*)
Definition bar_a (n : nat) : foo n.
  refine(match n with
           | 0 => _
           | _ => _
         end
        ).
  simpl.
  exact n.
  simpl.
  exact (n,n).
Qed.

(* the same definition can be written without refine . but this time we know what the match needs to be
   and hence we first unfold the function foo. which yealds a match subgoal on which when a case statement
   is applied it derives into two subgoals and then we can continue with the proof.
*)
Definition barbar (n:nat):foo n.
Proof.
  unfold foo.
  case n.
  exact n.
  intros a.
  exact (n,a).
Qed.
(*in the above examples one thing that worth noticing is that the definition of the function is lost when it is
  made using proofs , it gets the type correct which states that the function is valid. but conside the first case
  when the function returned 42 for 0 and (42,42) for anything else, when we write the same function using proofs
  the fact that what the fucntions returns is lost. it only talks about the type of what the fucntion returns *)



  (* defining a new type note how and element of this type still has a type inside it
   here we can see that for Dependent types there is no distinguition between types and values . 
   types are nothing but values of higer order types.
   and hence the phrase "type is a type that has type type"
*)
Definition foobar := (Set * Prop)%type.
Check foobar.
Definition example_of_foobar : foobar := (nat,False).

Definition myabsurd : forall P: Prop,  False -> P
  :=
  fun P x => match x with
             end.

Lemma my1absurd : forall P, False -> P.
  intros. destruct H. Show Proof.
Qed.