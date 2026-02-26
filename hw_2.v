Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Formulate the following statements from Rijke in type theory (you do not have to prove them). The answer to the first one (a) is given as an example. *)

(* 1a. Theorem 9.3.4 *)

Definition Eq_Σ {A : UU} {B : A → UU}: (∑ x : A, B x) → (∑ x : A, B x) → UU.
Proof.
  Admitted.

Definition pair_eq {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : (s = t) → Eq_Σ s t.
Proof.
  Admitted.

Theorem Thm_9_3_4 {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : isweq (pair_eq s t).
Proof.
  Admitted.

(* 1b. Exercise 9.2a *)

(* 1c. Exercise 9.4a *)

(* 1d. Exercise 9.9a *)

(**************************************************************)

(* From here on, all `Admitted.`s should be filled in. *)

(* Exercise 2 *)

(* Here we give a solution to Exercise 3 from the last homework, so that you can prove something about it in this Exercise.*)
Theorem exp : nat → nat → nat.
Proof.
  intros n m.
  induction m.
  - exact 1.
  - exact (IHm * n).
Defined.

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).

(* This command searches the library for functions of this kind. You should see in the output that ~maponpaths~ is of this kind. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
(* `exp l` takes addition to multiplication.*)
Proof.
  Admitted.

(* Exercise 3 *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
(* Another way to combine paths. *)
Proof.
  Admitted.

(* Exercise 4 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
(* Check that the above way of combining paths does the `right thing'. *)
Proof.
  Admitted.

(* Exercise 5 *)

(* isaprop is defined differently in UniMath than we in class in lecture 5. (It will become clear later why.) We haven't learned yet what isofhlevel means, but we do know what iscontr means. *)

Check isaprop.
Print isaprop.
Lemma trivial_prop_lem (P : UU) : isaprop P = ∏ x y : P, iscontr (x = y).
Proof.
  unfold isaprop.
  unfold isofhlevel.
  apply idpath.
Defined.

Theorem prop_thm {P : UU} : isaprop P <-> (∏ x y : P, x = y).
(* The different definitions of isaprop are logically equivalent. *)
Proof.
  Admitted.

(* Exercise 6 *)

(* NB: The prefered defintion of equivalence in the UniMath library is `isweq`: it says the fibers are contractible.
You are allowed to use isweq_iso from the library in this proof: it says if f is a quasiequivalence, then f is an equivalence in that sense.*)

Theorem prop_equiv_to_log_equiv (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
(* An equivalence between propositions is (logically equivalent to) a logical equivalence. *)
Proof.
  Admitted.