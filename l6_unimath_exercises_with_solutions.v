Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Example 12.1.2 (second half) from Rijke: The empty type is a proposition. *)

Theorem empty_is_prop : isaprop (∅).
    Proof.
        unfold isaprop.
        simpl.
        intros x y.
        induction x.
Defined.

(* Exercise 2 *)

(* Example 12.1.2 (first half) from Rijke: Every contractible type is a proposition. *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
Proof.
    induction p.
    induction q.
    apply idpath.
Defined.

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
Proof.
    induction p.
    simpl.
    apply idpath.
Defined.

Theorem contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
Proof.
    unfold isaprop.
    simpl.
    intros x y.
    unfold iscontr.
    use tpair.
    induction h as [cntr p].
    + exact (path_combination (p x) (p y)).
    + simpl.
      intro t.
      induction t.
      exact (path_combination_fact (pr2 h x)).
Defined.

(* Exercise 3 *)

(* (i ⇒ iii) in Proposition 12.1.3 of Rijke: If a proposition is inhabited, then it is contractible.*)

Theorem inhab_prop_is_contr {P : UU} (p : P) (h : isaprop P) : iscontr P.
Proof.
    use tpair.
    - exact p. 
    - simpl.
      intro q.
      unfold isaprop in h.
      simpl isofhlevel in h.
      set (e := h q p).
      exact (pr1 e).
Defined.

(* Exercise 4 *)

(* Proposition 12.4.3 of Rijke: If a type has h-level n, then it has h-level n+1.*)

Lemma hlevel_cumulativ_ind  (n : nat) : ∏ (T : UU) (h : isofhlevel n T), isofhlevel (S n) T.
Proof.
    induction n.
    - intros T c.
      exact (contr_is_prop c).
    - intros T h.
      simpl isofhlevel.
      intros x y.
      simpl isofhlevel in h.
      exact (IHn (x = y) (h x y)).
Defined.

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
    apply hlevel_cumulativ_ind.
    exact h.
Defined.

(* Exercise 5 *)

(* Every statement of the form ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)

Lemma iscontr_prop {A : UU} : isaprop (iscontr A).
Proof.
    unfold isaprop.
    simpl isofhlevel.
    intros [cntr1 c1] [cntr2 c2].
    set (A_is_contr := (cntr1,,c1)).
    assert (h1 : ∏ x : A, (iscontr (∏ t : A, t = x))).
    {
        intro.
        apply impred_iscontr.
        intro.
        use contr_is_prop.
        exact A_is_contr.
    }
    assert (h2 : iscontr (∑ cntr : A, ∏ t : A, t = cntr)).
    {
        use (isofhleveltotal2 0).
        - exact A_is_contr.
        - intro a.
          simpl.
          exact (h1 a). 
    }
    apply contr_is_prop.
    exact h2.
Defined.

Lemma hlevelprop_ind (n : nat) : ∏ A : UU, isaprop (isofhlevel n A).
Proof.
    induction n.
    - intro A.
      use iscontr_prop.
    - intro A.
      intros x y.
      simpl in x, y.
      set (h1 := λ a b : A, IHn (a = b)).
      assert (isaprop (∏ a b : A, isofhlevel n (a = b))).
      {
       use impred_isaprop.
       simpl.
       intro a. 
       use impred_isaprop.
        About impred_isaprop.
       intro b.
       simpl.
       apply h1.
      }
      apply X.
Defined.

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
    apply hlevelprop_ind.
Defined.

