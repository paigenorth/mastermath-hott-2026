Unset Universe Checking.
Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Hint: use `funextsec`. *)

(* Lemmas from earlier exercises/homework and other easy lemmas.*)

Lemma contr_to_path (C : UU) (c : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

Lemma contr_is_prop (C : UU) (c : iscontr C) (a b : C) : iscontr (a = b).
Proof.
  Admitted.

Lemma unit_iscontr : iscontr unit.
Proof.
  Admitted.

Lemma contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
  Admitted.

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  Admitted.

Lemma prop_equiv {P : UU} : isaprop P → (∏ p q : P, p = q).
Proof.
  exact (pr1 prop_thm).
Defined.

Theorem hlevel_cumulative {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma unit_is_hprop (a b : unit) : iscontr (a = b).
Proof.
  apply (@hlevel_cumulative 0 unit).
  exact unit_iscontr.
Defined.

Lemma unit_is_prop (x y : unit) : x = y.
Proof.
  apply prop_equiv.
  exact unit_is_hprop.
Defined.

Lemma unit_is_set : isaset unit.
Proof.
  apply hlevel_cumulative.
  apply hlevel_cumulative.
  exact unit_iscontr.
Defined.

Lemma contr_weq (A B : UU) (f : A → B) (c : iscontr A) (d : iscontr B) : isweq f.
Proof.
  (* induction c as [a c].
  induction d as [b d]. *)
  pose proof (a := pr1 c).
  pose proof (c' := contr_to_path A c).
  pose proof (d' := contr_to_path B d).
  intro b'.
  use tpair.
  - use tpair.
    + exact (pr1 c).
    + simpl.
      apply d'.
  - simpl.
    intro h.
    induction h as [a' e].
    pose proof (e' := c' a' (pr1 c)).
    induction e'.
    pose proof (x := contr_is_prop B d (f a') b').
    pose proof (y := contr_to_path (f a' = b') x).
    pose proof (z := y e (d' (f a') b')).
    rewrite z.
    apply idpath.
Defined.

(* Exercise 1 *)

(* Show that the propositional truncation of the booleans is the unit type. *)

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem ex_1 : prop_trunc bool ≃ unit.
Proof.
  apply (@contr_equiv_unit (prop_trunc bool)).
  use tpair.
  - intro P.
    intro f.
    exact (f true).
  - simpl.
    intro f.
    unfold prop_trunc in f.
    use funextsec.
    intro P.
    use funextsec.
    intro g.
    pose proof (Pisprop := prop_equiv (pr2 P)).
    apply Pisprop.
Defined.



(* Exercise 2 *)

(* Define the `singleton' univalent category: the category with one object and no nonidentity arrows.*)

(* I.e., define a term of `univalent_category`, defined in the library.*)

(* Hint: exercises 2 and 3 are very similar. Think about lemmas to use so that you don't have to duplicate your work. *)


(************)

Section ChaoticCategories.

Context (O : UU).

Lemma chaotic_precategory_ob_mor : precategory_ob_mor.
Proof.
  use tpair.
  - exact O.
  - simpl.
    intros x y.
    exact unit.
Defined.

Lemma chaotic_precategory_id_comp : precategory_id_comp chaotic_precategory_ob_mor.
Proof.
  split.
  - intro c.
    exact tt.
  - split.
Defined.

Lemma chaotic_precategory_data : precategory_data.
Proof.
  use tpair.
  - exact chaotic_precategory_ob_mor.
  - simpl.
    exact chaotic_precategory_id_comp.
Defined.

Lemma chaotic_is_precategory : is_precategory chaotic_precategory_data.
Proof.
  split.
  - split.
    + intros a b f.
      apply unit_is_prop.
    + intros a b f.
      apply unit_is_prop.
  - split.
    + intros a b c d f g h.
      apply unit_is_prop.
    + intros a b c d f g h.
      apply unit_is_prop.
Defined.

Lemma chaotic_precategory : precategory.
Proof.
  use tpair.
  - exact chaotic_precategory_data.
  - exact chaotic_is_precategory.
Defined.  

Lemma chaotic_category : category.
Proof.
  use tpair.
  - exact chaotic_precategory.
  - simpl.
    unfold has_homsets.
    intros a b.
    apply unit_is_set.
Defined.

Lemma chaotic_mor_isos (a b : chaotic_precategory) (f : chaotic_precategory_data ⟦ a, b ⟧) : is_z_isomorphism f.
Proof.
  induction f.
  unfold is_z_isomorphism.
  use tpair.
  - exact tt.
  - simpl.
    use tpair.
    + apply unit_is_prop.
    + simpl.
      apply unit_is_prop.
Defined.

Lemma chaotic_isos_contr (a b : chaotic_precategory) : iscontr (z_iso a b).
Proof.
  use tpair.
  - unfold z_iso.
    use tpair.
    + simpl.
      exact tt.
    + simpl.
      exact (chaotic_mor_isos a b tt). 
  - simpl.
    intro i.
    unfold z_iso in i.
    induction i as [f i].
    simpl in f.
    set (e := unit_is_prop tt f).
    induction e.
    unfold is_z_isomorphism in i. 
    induction i as [g i].
    simpl in g.
    set (e := unit_is_prop tt g).
    induction e.
    unfold is_inverse_in_precat in i.
    induction i as [i1 i2].
    set (tttta := @compose chaotic_precategory a b a tt tt).
    pose proof (c := unit_is_hprop tttta (id a)).
    set (i1e := contr_to_path (tttta = id a) c i1 (unit_is_prop tttta (id a))).
    rewrite i1e.
    set (ttttb := @compose chaotic_precategory b a b tt tt).
    set (i2e := contr_to_path (ttttb = id b) c i2 (unit_is_prop ttttb (id b))).
    rewrite i2e.
    apply idpath.
Defined.  

End ChaoticCategories.

(****************)

Definition singleton_category : category := chaotic_category unit.

Lemma singleton_is_univalent : is_univalent singleton_category.
Proof.
  intros a b.
  apply contr_weq.
  - apply contr_is_prop.
    unfold singleton_category.
    use tpair.
    + split. 
    + simpl.
      intro t.
      induction t.
      apply idpath.
  - apply chaotic_isos_contr.
Defined.

Theorem singleton : univalent_category.
Proof.
  use tpair.
  - exact singleton_category.
  - exact singleton_is_univalent.
Defined.

(* Exercise 3 *)

(* Define the `walking isomorphism' precategory: that is a category whose underlying set is the booleans and such that true ≅ false.
*)

(* I.e., define a term of type `category`. Unimath uses category to mean what the HoTT book calls precategory.*)

Definition walking_category : category := chaotic_category bool.

(* Exercise 4 *)

(* Show that the Rezk completion of the category from exercise 3 is the category from exercise 2.*)

(* I.e. construct a term of type `weak_equiv C D` where C and D are the categories defined above.*)

Definition weak_equiv (C D : category) : UU := ∑ H : functor C D, essentially_surjective H × fully_faithful H.

Lemma rezk_func : functor walking_category singleton_category.
Proof. 
  unfold functor.
  use tpair.
  - unfold functor_data.
    use tpair.
    + intro w.
      exact tt.
    + simpl.
      intros a b t.
      exact tt.
  - simpl.
    unfold is_functor.
    split.
    + unfold functor_idax.
      intro a.
      simpl.
      apply unit_is_prop.
    + unfold functor_compax.
      intros a b c f g.
      simpl.
      apply unit_is_prop.
Defined.      

Lemma rezk_essentially_surjective : essentially_surjective rezk_func.
Proof.
  unfold essentially_surjective.
  intro b.
  intro P.
  intro x.
  assert (i : z_iso (rezk_func true) b).
  {
    set (c := chaotic_isos_contr unit (rezk_func true) b).
    exact (pr1 c).
  }
  exact (x (true,,i)).
Defined.

Lemma rezk_fully_faithful : fully_faithful rezk_func.
Proof.
  unfold fully_faithful.
  intros a b.
  Locate "#".
  unfold functor_on_morphisms.
  unfold rezk_func.
  simpl.
  apply contr_weq.
  - exact unit_iscontr.
  - exact unit_iscontr. 
Defined.

Theorem rezk_eq : weak_equiv walking_category singleton_category.
Proof.
  use tpair.
  exact rezk_func.
  + use tpair.
    - exact rezk_essentially_surjective.
    - exact rezk_fully_faithful.
Defined.