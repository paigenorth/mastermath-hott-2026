Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Show Lemma 11.1.2 of Rijke. Give Def 11.1.1 yourself. *)

(* Hint: Follow the proof in Rijke, using `isweq_iso` at the end. For the statements, you will want to use `hfiber`, `∘` (`funcomp`), `~` (`homot`), `≃` (`weq`). *)

Definition tot {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) : (∑ x : A, B(x)) → (∑ x : A, C (x)).
Proof.
  intro s.
  induction s as [a b].
  set (c := f a b).
  exact (a,,c).
Defined.

Lemma lem_11_1_2_a {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) (t : ∑ x : A, C(x)) : hfiber (tot f) t → hfiber (f (pr1 t)) (pr2 t).
Proof.
  intro h.
  unfold hfiber in h.
  induction h as [s p].
  induction p.
  unfold hfiber.
  use tpair.
  + simpl.
    exact (pr2 s).
  + simpl.
    apply idpath.
Defined.

Lemma lem_11_1_2_b {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) (t : ∑ x : A, C(x)) : hfiber (f (pr1 t)) (pr2 t) → hfiber (tot f) t.
Proof.
  intro h.
  unfold hfiber in *.
  induction t as [a c].
  induction h as [b p].
  simpl in *.
  use tpair.
  - simpl in *.
    use tpair.
    + exact a.
    + simpl.
      exact b.
  - simpl.
    unfold tot.
    induction p.
    apply idpath.
Defined.

Lemma lem_11_1_2_c {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) (t : ∑ x : A, C(x)) : ((lem_11_1_2_b f t) ∘ (lem_11_1_2_a f t)) ~ (idfun (hfiber (tot f) t)).
Proof.
  unfold homot.
  intro h.
  simpl.
  unfold hfiber in h.
  induction h as [[a b] p].
  induction p.
  unfold lem_11_1_2_b.
  unfold lem_11_1_2_a.
  simpl.
  unfold tot.
  apply idpath.
Defined.

Lemma lem_11_1_2_d {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) (t : ∑ x : A, C(x)) : ((lem_11_1_2_a f t) ∘ (lem_11_1_2_b f t)) ~ (idfun (hfiber (f (pr1 t)) (pr2 t))).
Proof.
  unfold homot.
  intro h.
  unfold idfun.
  induction t as [a c].
  unfold hfiber in h.
  induction h as [b p].
  simpl in b.
  simpl in p.
  induction p.
  unfold lem_11_1_2_b.
  unfold lem_11_1_2_a.
  simpl.
  apply idpath.
Defined.

Theorem lem_11_1_2 {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) (t : ∑ x : A, C(x)) : hfiber (tot f) t ≃ hfiber (f (pr1 t)) (pr2 t).
Proof.
  unfold weq.
  use tpair.
  - exact (lem_11_1_2_a f t).
  - simpl.
    use isweq_iso.
    + exact (lem_11_1_2_b f t).
    + exact (lem_11_1_2_c f t).
    + exact (lem_11_1_2_d f t).
Defined.

(* Exercise 2 *)

(* Show that if two types are equivalent and one is contractible, then the other is. *)

Lemma iscontr_respects_equiv_forward {A B : UU} (c : iscontr A) (e : A ≃ B) : iscontr B.
Proof.
  unfold iscontr in *.
  induction c as [a ps].
  induction e as [f w].
  use tpair.
  - exact (f a).
  - simpl.
    intro b.
    unfold isweq in w.
    set (x := w b).
    set (ap' := pr1 x).
    induction ap' as [a' p'].
    set (p := maponpaths f (ps a')).
    exact (!p'@p).
Defined.

Lemma iscontr_respects_equiv_backward {A B : UU} (c : iscontr B) (e : A ≃ B) : iscontr A.
Proof.
  unfold iscontr in *.
  induction c as [b ps].
  unfold weq in e.
  induction e as [f w].
  unfold isweq in w.
  set (wb := w b).
  set (a := pr1 (pr1 wb)).
  use tpair.
  - exact a.
  - simpl.
    intro a'.
    set (qs := pr2 wb).
    simpl in qs.
    transparent assert (t : (hfiber f b)).
    + unfold hfiber.
      use tpair.
      * exact a'.
      * simpl.
        exact (ps (f a')).
    + set (q := qs t).
      set (q1 := maponpaths pr1 q).
      simpl in q1.
      exact q1.
Defined.

(* Exercise 3 *)

(* Show Theorem 11.1.3 of Rijke *)

Lemma thm_11_1_3_a {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) : (∏ x : A, isweq (f x)) → (isweq (tot f)).
Proof.
  intro h.
  unfold isweq in *.
  intro t.
  set (hy := h (pr1 t) (pr2 t)).
  set (e := lem_11_1_2 f t).
  use (iscontr_respects_equiv_backward hy e).
Defined.

Lemma thm_11_1_3_b {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) : (isweq (tot f)) → (∏ x : A, isweq (f x)).
Proof.
  intro w.
  intro a.
  unfold isweq in *.
  intro c.
  set (e := lem_11_1_2 f (a ,, c)).
  simpl in e.
  set (wac := w (a,,c)).
  use (iscontr_respects_equiv_forward wac e).
Defined.

Theorem thm_11_1_3 {A : UU} {B C : A → UU} (f : ∏ x : A, B(x) → C(x)) : (∏ x : A, isweq (f x)) <-> (isweq (tot f)).
Proof.
  Locate "<->".
  unfold logeq.
  use tpair.
  - exact (thm_11_1_3_a f).
  - simpl.
    exact (thm_11_1_3_b f).
Defined.

(* Exercise 4 *)

(* Show Thm 11.4.2 *)

Lemma equiv_to_emb_lem_a {A B : UU} (f : A ≃ B) {a a' : A}: (a = a') → (f a = f a').
Proof.
  intro e.
  induction e.
  apply idpath.
Defined.

Lemma equiv_to_emb_lem_b {A B : UU} (f : A ≃ B) {a a' : A}: (f a = f a') → (a = a').
Proof.
  intro p.
  induction f as [f w].
  unfold isweq in w.
  simpl in p.
  set (wfa' := w (f a')).
  transparent assert (ha : (hfiber f (f a'))).
  {
  use tpair.
  + exact a.
  + simpl.
    exact p.
  }
  transparent assert (ha' : (hfiber f (f a'))).
  {
  use tpair.
  * exact a'.
  * simpl.
    apply idpath.
  }
  set (hap := (pr2 wfa') ha).
  set (hap' := (pr2 wfa') ha').
  set (q := hap @ !hap').
  set (q1 := maponpaths pr1 q).
  simpl in q1.
  assumption.
Defined.

Lemma equiv_to_emb_lem_c {A B : UU} (f : A ≃ B) {a a' : A} (p : a = a'): 
equiv_to_emb_lem_b f (equiv_to_emb_lem_a f p) = p.
Proof.
  induction p.
  unfold equiv_to_emb_lem_a.
  simpl.
  unfold equiv_to_emb_lem_b.
  simpl.

(* Show Thm *)