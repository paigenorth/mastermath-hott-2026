Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* Hint: use `isweq_iso`, `funextsec`, `total2_paths_f`, `isapropiscontr`, `proofirrelevance `, `isapropisweq`, `univalenceAxiom`, `twooutof3a`, `isapropisaset`, `isapropifcontr`. *)

(* Exercise 1 *)

(* Show that equalities of subtypes are the same as the equalities in the super types. *)

Theorem subtype_equalities (A : UU) (P : A → UU) (a b : ∑ x : A, P x) (prop : ∏ a : A , isaprop (P a)) : (pr1 a = pr1 b) ≃ (a = b).
Proof.
  use tpair.
  - intro e.
    induction a as [a pa].
    induction b as [b pb].
    simpl in *.
    induction e.
    use total2_paths_f.
    + simpl.
      apply idpath.
    + simpl.
      apply prop.
  - use isweq_iso.
    + intro e.
      exact (maponpaths pr1 e).
    + induction a as [a pa].
      induction b as [b pb].
      simpl in *.
      intro e.
      induction e.
      simpl.
      unfold transportf.
      simpl.
      set (p := prop a pa pb).
      simpl in p.
      induction p as [p q].
      simpl.
      induction p.
      simpl.
      apply idpath.
    + intro e.
      simpl.
      induction e.
      simpl.
      unfold transportf.
      simpl.
      induction a as [a pa].
      set (ppa := pr1 (prop a pa pa)).
      simpl in *.
      assert (e : ppa = idpath pa).
      {
        set (x := (prop a pa pa)).
        set (y := isapropifcontr x).
        apply y.
      }
      rewrite e.
      simpl.
      apply idpath.
Defined.

(* Exercise 2 *)

(* Show univalence for sets. *)

Definition iso (S T : UU) : UU :=
  ∑ f : S → T ,
  ∑ g : T → S ,
  g ∘ f ~ idfun S
  ×
  f ∘ g ~ idfun T.

Notation "S ≅ T" := (iso S T).

Definition iso_to_equiv (S T : UU) : (S ≅ T) → (S ≃ T).
Proof.
  intro i.
  induction i as [f [g [H I]]].
  use tpair.
  - exact f.
  - simpl. 
    use isweq_iso.
    + exact g.
    + exact H.
    + exact I.
Defined.

Lemma equiv_to_iso (S T : UU) : (S ≃ T) → (S ≅ T).
Proof.
unfold isweq.
intro e.
induction e as [f w].
use tpair.
  - exact f.
  - simpl.
    use tpair.
    + intro t.
      unfold isweq in w.
      set (wt := w t).
      induction wt as [[s _] _].
      exact s.
    + simpl.
      split.
      * intro s.
        simpl.
        set (wfs := w (f s)).
        induction wfs as [p es].
        transparent assert (x : (hfiber f (f s))).
        {
          use tpair.
          + exact s.
          + simpl.
            apply idpath.  
        }
        set (e := es x).
        induction e.
        simpl.
        apply idpath.
      * intro t.
        simpl.
        set (wt := w t).
        induction wt as [[s e] es].
        exact e.
Defined.

Lemma set_iso_is_equiv (S T : UU) (SH : isaset S) (TH : isaset T) : isweq (iso_to_equiv S T).
Proof.
  use isweq_iso.
  - apply equiv_to_iso.
  - intro e.
    induction e as [f [g [H I]]].
    use total2_paths_f.
    + simpl.
      apply idpath.
    + use total2_paths_f.
      * simpl.
        apply idpath.  
      * use total2_paths_f.    
        --  unfold homot in H.
            simpl in H.
            apply funextsec.
            intro s. simpl in s.
            set (Hs := H s).
            set (Hs_in_prop := SH (g (f s)) s).
            apply Hs_in_prop.
        --  unfold homot in I.
            simpl in I.
            apply funextsec.
            intro t. simpl in t.
            set (It := I t).
            set (It_in_prop := TH (f (g t)) t).
            apply It_in_prop.
  - intro w. induction w as [f w].
    use total2_paths_f.
    + simpl.
      apply idpath.
    + simpl.
      set (winprop := isapropisweq f).
      apply winprop.   
Defined.

Definition id_to_iso (S T : UU) : (S = T) → (S ≅ T).
Proof.
  intro e.
  induction e.
  use tpair.
  - exact (idfun S).
  - use tpair.
    + exact (idfun S).
    + split.
      * intro s.
        simpl.
        apply idpath.
      * intro s.
        simpl.
        apply idpath.
Defined.

Lemma id_iso_equiv_commute (S T : UU) : (@eqweqmap S T) = (iso_to_equiv S T) ∘ (id_to_iso S T).
Proof.
  apply funextsec.
  intro e.
  induction e.
  simpl.
  use total2_paths_f.
  - simpl.
    apply idpath.
  - simpl.
    set (x := isweq_iso (idfun S) (idfun S)
    (λ s : S, idpath s) (λ s : S, idpath s)).
    set (xinprop := isapropisweq (idfun S)).
    apply xinprop.
Defined.

(*
= ---------> ≃
   \      /
      ≅
*)

Theorem set_univalence (S T : hSet) : isweq (id_to_iso S T).
Proof.
  induction S as [S SH].
  induction T as [T TH].
  simpl in *.
  use twooutof3a.
  + exact (S ≃ T).
  + exact (iso_to_equiv S T).
  + rewrite <- (id_iso_equiv_commute S T).
    apply univalenceAxiom.
  + apply set_iso_is_equiv.
    - exact SH.
    - exact TH.
Defined.

(* Exercise 3 *)

(* Define the type of categories and univalent categories. *)

Definition CatOb := UU.

Definition CatMor (Ob : CatOb) := Ob → Ob → hSet.

Definition CatId (Ob : CatOb) (Hom : CatMor Ob) := ∏ X : Ob , Hom X X.

Definition CatComp (Ob : CatOb) (Hom : CatMor Ob) := ∏ X Y Z : Ob, Hom X Y → Hom Y Z → Hom X Z.

Definition CatIdLeft (Ob : CatOb) (Hom : CatMor Ob) (idmor : CatId Ob Hom) (comp : CatComp Ob Hom) := ∏ (X Y : Ob), ∏ (f : Hom X Y),
  comp X X Y (idmor X) f = f.

Definition CatIdRight (Ob : CatOb) (Hom : CatMor Ob) (idmor : CatId Ob Hom) (comp : CatComp Ob Hom) := ∏ (X Y : Ob), ∏ (f : Hom X Y),
    comp X Y Y f (idmor Y) = f.

Definition CatAssoc (Ob : CatOb) (Hom : CatMor Ob) (comp : CatComp Ob Hom)
:= ∏ (W X Y Z : Ob), ∏ (f : Hom W X), ∏ (g : Hom X Y), ∏ (h : Hom Y Z),  
    comp W Y Z (comp W X Y f g) h = comp W X Z f (comp X Y Z g h).

Definition Cat :=
  ∑ Ob : CatOb,
  ∑ Hom : CatMor Ob,
  ∑ idmor : CatId Ob Hom,
  ∑ comp : CatComp Ob Hom,
  (CatIdLeft Ob Hom idmor comp) × (CatIdRight Ob Hom idmor comp) × (CatAssoc Ob Hom comp).

Definition Ob (C : Cat) : UU.
Proof.
  induction C.
  exact pr1.
Defined.

Definition Hom {C : Cat} (X Y : Ob C) : hSet.
Proof.
  induction C as [Ob [Hom Rest]].
  unfold CatMor in Hom.
  exact (Hom X Y).
Defined.

Definition comp {C : Cat} {X Y Z : Ob C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z.
Proof.
  induction C as [Ob [Hom [idmor [comp [catidleft rest]]]]].
  exact (comp X Y Z f g).
Defined.

Notation "f ∘ g" := (comp f g).

Definition idmor {C : Cat} (X : Ob C) : Hom X X.
Proof.
  induction C as [Ob [Hom [idmor [comp [catidleft rest]]]]].
  exact (idmor X).
Defined.

Notation "𝟙 X" := (idmor X) (at level 10).

Definition isiso {C : Cat} {X Y : Ob C} (f : Hom X Y) :=
  ∑ g : Hom Y X, (f ∘ g = 𝟙 X) × (g ∘ f = 𝟙 Y).

Notation "X ≅ Y" := (∑ f : Hom X Y, isiso f).

Definition id_to_iso_cat {C : Cat} (X Y : Ob C) : (X = Y) → (X ≅ Y).
Proof.
  induction C as [Ob [Hom [idmor [comp [catidleft rest]]]]].
  intro e.
  induction e.
  use tpair.
  - exact (𝟙 X).
  - simpl.
    use tpair.
    + exact (𝟙 X).
    + simpl.
      split.
      * apply catidleft.
      * apply catidleft.
Defined.
        
Definition univalent (C : Cat) := ∏ X Y : Ob C, isweq (id_to_iso_cat X Y).
