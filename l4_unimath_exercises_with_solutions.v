
Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Define neg_neg_bool from Example 9.1.3 in R. (Note that we need to replace the hyphen with an underscore because Coq does not accept hyphens. *)

(* Remember that you can write e.g. ~Locate "~".~ to find information about notation and ~Print negb.~ or ~About negb.~ to find information about a predefined term. *)

Theorem neg_neg_bool: negb ∘ negb ~ idfun bool.
Proof.
    unfold homot.
    intro b.
    induction b.
    - simpl.
      apply idpath.
    - simpl.
      apply idpath.
Defined.

(* Exercise 2 *)

(* Define concat_htpy from Def 9.1.5 in R.*)

Theorem concat_htpy {A : UU} {B : A → UU} {f g h : ∏ (x : A) , B x} : (f ~ g) → (g ~ h) → (f ~ h).
Proof.
    intros H1 H2.
    intro a.
    set (H1a := H1 a).
    set (H2a := H2 a).
    set (H3a := H1a @ H2a).
    exact H3a.
Defined.

Infix "~@~" := concat_htpy (at level 70, no associativity).

(* This defines infix notation for concatenation. The stuff in parentheses is not important, but tells Coq the order of operations when it is used in combination with other infix notation.*)

(* Exercise 3 *)

(* Define assoc_htpy from Prop 9.1.6 in R. *)

(* Hint: use path_assoc. *)

Theorem assoc_htpy {A : UU} {B : A → UU} {f g h i : ∏ (x : A) , B x} (H : f ~ g) (K : g ~ h) (L : h ~ i) : ((H ~@~ K) ~@~ L) ~ (H ~@~ (K ~@~ L)).
Proof.
    intro a.
    simpl.
    unfold concat_htpy.
    apply pathsinv0.
    apply path_assoc.
Defined.

(* Exercise 4 *)

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
    unfold iscontr.
    use tpair.
    - exact tt.
    - simpl.
      intro t.
      induction t.
      apply idpath.
Defined.

(* Exercise 5 *)

Lemma unit_is_prop (x y : unit) : iscontr (x = y).
Proof.
    unfold iscontr.
    use tpair.
    - induction x.
      induction y.
      apply idpath.
    - cbn.
      intro p.
      induction p.
      induction x.
      cbn.
      apply idpath.
Defined.


(* Exercise 6 *)

(* ~weq A B~ is the type of contractible maps from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    unfold weq in e.
    induction e as [f w].
    intro b.
    unfold isweq in w.
    unfold iscontr in w.
    induction (w b) as [cntr _].
    unfold hfiber in cntr.
    induction cntr as [x _].
    exact x.
Defined.

(* Exericse 7 *)

(* Show Theorem 9.3.4 from R. Use ~weq~ for the notion of equivalence. You can prove this directly or use ~isweq_iso~. Solutions to both approaches are provided, so try both if you are looking for extra exercises.*)

(* Hints: - use ~transportf~.
          - cbn (similar to simpl) was necessary in my proof where sometimes simpl didn't work. 
*)

Definition sigma_paths_1 {A : UU} {B : A → UU} {s t : ∑ x : A, B x} : (s = t) → ∑ (p : pr1 s = pr1 t) , transportf B p (pr2 s) = (pr2 t).
Proof.
    intro p.
    induction p.
    use tpair.
    - apply idpath.
    - simpl.
      cbn.
      apply idpath.
Defined.

Definition sigma_paths_2 {A : UU} {B : A → UU} {s t : ∑ x : A, B x} : (∑ (p : pr1 s = pr1 t) , transportf B p (pr2 s) = (pr2 t)) → (s = t).
Proof.
    induction s as [a1 b1].
    induction t as [a2 b2].
    intro s.
    induction s as [pa pb].
    simpl in *.
    induction pa.
    induction pb.
    cbn.
    apply idpath.
Defined.

Lemma sigma_paths_3 {A : UU} {B : A → UU} {s t : ∑ x : A, B x} : (sigma_paths_2 ∘ sigma_paths_1) ~ (idfun (s = t)).
Proof.
    unfold homot.
    intro p.
    induction p.
    simpl.
    induction s.
    apply idpath.
Defined.

Lemma sigma_paths_4 {A : UU} {B : A → UU} {s t : ∑ x : A, B x} : (sigma_paths_1 ∘ sigma_paths_2) ~ (idfun (∑ (p : pr1 s = pr1 t) , transportf B p (pr2 s) = (pr2 t))).
Proof.
    unfold homot.
    intro x.
    induction x as [p q].
    induction s as [a1 b1].
    induction t as [a2 b2].
    simpl in p.
    simpl in q.
    unfold idfun.
    induction p.
    induction q.
    simpl.
    cbn.
    apply idpath.
Defined.

Theorem thm_v1 {A : UU} {B : A → UU} {s t : ∑ x : A, B x} : isweq (@sigma_paths_1 A B s t).
Proof.
    exact (isweq_iso sigma_paths_1 sigma_paths_2 sigma_paths_3 sigma_paths_4).
Defined.

Theorem thm_v2 {A : UU} {B : A → UU} {s t : ∑ x : A, B x} : isweq (@sigma_paths_1 A B s t).
Proof.
    unfold isweq.
    intro y.
    unfold iscontr.
    use tpair.
    - unfold hfiber.
      induction s as [a1 b1].
      induction t as [a2 b2].
      induction y as [p q].
      simpl in *.
      induction p.
      induction q.
      cbn.
      use tpair.
      + apply idpath.
      + simpl. 
        apply idpath.
    - cbn.
      intro h.
      induction h as [a b].
      induction a.
      simpl in *.
      induction b.
      cbn.
      induction s as [a b].
      cbn.
      apply idpath.
Defined.

(* Exercise 8 *)

(* Every contractible type is equivalent to the unit.*)

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
    induction h as [h1 h2].
    exact ((h2 x) @ !(h2 y)).
Defined.

Lemma paths_in_unit (p : tt = tt) : p = idpath tt.
Proof.
    exact (contr_to_path (unit_is_prop tt tt) p (idpath tt)).
Defined. 

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
    unfold weq.
    use tpair.
    - exact (λ _ , tt).
    - simpl.
      unfold isweq.
      intro y.
      induction y.
      unfold hfiber.
      induction h as [cntr p].
      use tpair.
      + exact (cntr,,idpath tt).
      + simpl.
        intro t.
        induction t as [c q].
        rewrite (p c).
        rewrite (paths_in_unit q).
        apply idpath.
Defined.