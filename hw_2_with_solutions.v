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

Definition const (b : bool) : bool → bool.
Proof.
  Admitted.

Theorem Ex_9_5a (b : bool) (h : isweq (const b)) : ∅.
Proof.
  Admitted.

(* 1c. Exercise 9.4a *)

Definition sections {A B : UU} (f : A → B) : UU :=
  ∑ s : B → A, f ∘ s ~ idfun B.

Theorem Ex_9_4a {A B X: UU} {h : A → B} {f: A → X} {g : B → X} (H : f ~ g ∘ h) (s : sections f) : (f ∘ (pr1 s) ~ (idfun X)) × ((sections f) <-> (sections g)).
Proof.
  Admitted.

(* 1d. Exercise 9.9a *)

Definition is_finitely_cyclic {X : UU} (f : X → X) : UU.
Proof.
  Admitted.

Theorem Ex_9_9a {X : UU} (f : X → X) : is_finitely_cyclic f → isweq f.
Proof.
  Admitted.

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
  Admitted.

(**************************************************************)

(* For the following exercises you can use the following results from previous exercise sessions without proofs. *)

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

(* From here on, all `Admitted.`s should be filled in. *)

(* Exercise 2 *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
(* Another way to combine paths. *)
Proof.
    induction p.
    induction q.
    apply idpath.
Defined.

(* Exercise 3 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
(* Check that the above way of combining paths does the `right thing'. *)
Proof.
    induction p.
    simpl.
    apply idpath.
Defined.

(* Exercise 4 *)

(* isaprop is defined differently in UniMath than we in class in lecture 5. (It will become clear later why.) We haven't learned yet what isofhlevel means, but we do know what iscontr means. *)

Lemma trivial_prop_lem (P : UU) : isaprop P = ∏ x y : P, iscontr (x = y).
Proof.
  unfold isaprop.
  unfold isofhlevel.
  apply idpath.
Defined.

Theorem prop_thm_a {P : UU} : (isaprop P) → (∏ x y : P, x = y).
Proof.
  intro PProp.
  intros p q.
  set (c := PProp p q).
  simpl in c.
  induction c as [cntr _].
  exact cntr.
Defined.

Lemma path_comp_lem {A : UU} {a b : A} (p : a = b) : idpath a = p @ !p.
Proof.
  induction p.
  simpl.
  apply idpath.
Defined.

Theorem prop_thm_b {P : UU} : (∏ x y : P, x = y) → 
(isaprop P).
Proof.
  intro paths.
  unfold isaprop.
  unfold isofhlevel.
  intros p q.
  set (newpaths := λ x y : P, (paths x p) @ !(paths y p)).
  use tpair.
  - exact (newpaths p q).
  - simpl.
    intro e.
    induction e.
    unfold newpaths.
    use path_comp_lem.
Defined.

Theorem prop_thm {P : UU} : isaprop P <-> (∏ x y : P, x = y).
(* The different definitions of isaprop are logically equivalent. *)
Proof.
  split.
  - apply prop_thm_a.
  - apply prop_thm_b.
Defined. 

(* Exercise 5 *)

(* NB: The prefered defintion of equivalence in the UniMath library is `isweq`: it says the fibers are contractible.
You are allowed to use isweq_iso from the library in this proof: it says if f is a quasiequivalence, then f is an equivalence in that sense.*)

Theorem prop_equiv_to_log_equiv (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
(* An equivalence between propositions is (logically equivalent to) a logical equivalence. *)
Proof.
  split.
  - intro e.
    induction e as [f c].
    split.
    + exact f.
    + intro q.
      unfold isweq in c.
      set (cq := c q).
      induction cq as [h _].
      induction h as [p _].
      exact p.
  - intro b.
    induction b as [f g].
    induction P as [P PProp].
    induction Q as [Q QProp].
    simpl in *.
    use tpair.
    + exact f.
    + use isweq_iso.
      * exact g.
      * intro p.
        set (PProp2 := prop_thm_a PProp).
        exact (PProp2 (g (f p)) p).
      * intro q.
        set (QProp2 := prop_thm_a QProp).
        exact (QProp2 (f (g q)) q).
Defined.
