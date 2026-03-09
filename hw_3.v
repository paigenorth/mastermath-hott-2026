Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* For the following exercises you can use the following results from previous exercise sessions without proofs. *)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
  Admitted.

(*You can/should also use `isweq_iso` and `funextsec` from the library. You should look up their types, but here is some explanation. In Unimath, a contractible map is called a weak equivalence (`weq`) this is their preferred definition for equivalence (because it's often the easiest to use). In Unimath, quasi-equivalences are called isomorphisms. `isweq_iso` turns a proof that a map is a quasi-equivalence/isomorphism and returns the proof that it is contractible/weak equivalence. `funextsec` takes a pointwise equality between to maps f,g to an equality f,g. We will talk about funextsec explicitly in lecture 6, but you don't need that explanation to start using it.*)

(* Exercise 1 *)

(* In the last homework you showed the two definitions of isaprop were *logically equivalent*. Now show that the definitions are *equivalent*. *)

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  Admitted.

(* Exercise 2 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  Admitted.

(* Exercise 3 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  Admitted.

(* Exercise 4 *)

(* An equivalence between propositions is (equivalent to) a logical equivalence. *)

(* In the last homework you showed that an equivalence between propositions is *logically equivalent* to a logical equivalence. Now show that an equivalence between propositions is *equivalent* to a logical equivalence.*)

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  Admitted.