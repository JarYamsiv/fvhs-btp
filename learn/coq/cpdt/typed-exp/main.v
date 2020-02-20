Require Import Bool Arith List.
Set Implicit Arguments.

(* this can be considered as the type of input this machine will take
   nat and bool are the types that are already defined in coq , the following
   are our own types.*)
Inductive type : Set := Nat | Bool.

(* unlike last time the typed binop takes arguments
   tbinop is defined as an indexed type family an intuitive explanation would be tbinop t1 t2 t is a binary operator whose
   operands have types t1 and t2 and the result has type t consider Tlt it's type is tbinop Nat Nat Bool takes two Nat and
   produces a Bool value. here the new constructor helps in embedding the information about the input and output types of 
   each of the operators . *)
Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

(*
 Here we will make use of the Definition of tbinop even though we have TBinop as forall t t1 t2 the restrictions that we introduced in
 tbinop will carry over to this definition too. and hence giving us a well typed expression*)
Inductive texp:type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t t1 t2,  tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

(* matching from our types to the actual coq equivalent types.*)
Definition typeDenote  (t:type) :Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(* this function will be later usefull while defining expression denote. this can be seen as a function that maps 
   the values in Type 'type' to the actual coq values.*)
Definition tbinopDenote arg1 arg2 res (b :  tbinop arg1 arg2 res) :
  typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => leb
  end.

(* if implicit Arguments are not set the function will fail to infer the type at 'TNConst n => n'*)
Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) ( texpDenote e2)
  end.

(* a simple expression *)
Eval simpl in texpDenote ( TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 5)).

(* this time the stack can get into 'underflow' or 'stuck' state depending on the number and type of Arguments respectivly*)

Definition tstack := list type.

(* any stack classified by tstack must have exactly as many elements , and each stack element must have the type found at the 
   corresponding position of the stack type. *)
Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s,nat -> tinstr s (Nat::s)
| TiBConst : forall s,bool -> tinstr s (Bool::s)
| TiBinop : forall arg1 arg2 res s,
              tbinop arg1 arg2 res -> tinstr (arg1::arg2::s) (res::s).

(**)
Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s,tprog s s
| TCons : forall s1 s2 s3,
                 tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.
                                                      