Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* For the following exercises you can use the following results from previous exercise sessions without proofs. *)
(* You can also use results from the previous homework. *)

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

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  Admitted.

(* Exercise 2 *)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  Admitted.

(* Exercise 3 *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  Admitted.

(* Exercise 4 *)

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  Admitted.
