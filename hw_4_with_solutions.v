Unset Universe Checking.
Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

(* You can use any result from previous homeworks, exercises, or lectures without proof.*)

(* Exercise 1 *)

(* Define the type of groups. *)

Definition GroupCarrier := hSet.
Definition GroupToType : GroupCarrier → UU := @pr1 _ _.
Coercion GroupToType : GroupCarrier >-> UU.

Definition GroupMul (G : GroupCarrier) := G → G → G.
Definition GroupInv (G : GroupCarrier) := G → G.
Definition GroupUnit (G : GroupCarrier) := G.
Definition GroupAssoc (G : GroupCarrier) (m : GroupMul G) (i : GroupInv G) (u : GroupUnit G) 
  := ∏ a : G, ∏ b : G, ∏ c : G, m (m a b) c = m a (m b c).
Definition GroupInvLaws (G : GroupCarrier) (m : GroupMul G) (i : GroupInv G) (u : GroupUnit G) 
  := ∏ a : G, (m (i a) a = u) × (m a (i a) = u).
Definition GroupUnitLaws (G : GroupCarrier) (m : GroupMul G) (i : GroupInv G) (u : GroupUnit G) 
  := ∏ a : G, (m u a = a) × (m a u = a).

Definition Group :=
  ∑ G : GroupCarrier, 
  ∑ m : GroupMul G,
  ∑ i : GroupInv G,
  ∑ u : GroupUnit G,
  GroupAssoc G m i u ×
  GroupInvLaws G m i u ×
  GroupUnitLaws G m i u.

(* Definition Group :=
  ∑ A : hSet, ∑ m : A → A → A, ∑ i : A → A, ∑ u : A,
    (∏ a : A, ∏ b : A, ∏ c : A, m (m a b) c = m a (m b c)) ×
    (∏ a : A, (m (i a) a = u) × (m a (i a) = u)) ×
    (∏ a : A, (m u a = a) × (m a u = a)). *)

(* Exercise 2 *)

(* Give a group structure on the booleans ~bool~ and show that that produces a term of the type of groups. Use the fact ~isasetbool~ that ~bool~ is a set.*)

Definition iff : bool → bool → bool.
  intros a b.
  induction a.
  - induction b.
    + exact true.
    + exact false.
  - induction b.
    + exact false.
    + exact true.
Defined.

Definition Group_bool : Group.
  use tpair.
  - exact (bool ,, isasetbool).
  - use tpair. 
    + exact iff.
    + use tpair.
      * exact (idfun bool).
      * use tpair.
        -- exact true.
        -- use tpair.
           ** intros a b c. induction a; induction b; induction c; apply idpath.
           ** use tpair.
              --- intro a; induction a; use tpair; apply idpath.
              --- simpl. intro a; induction a; use tpair; apply idpath.
Defined.

(* Exercise 3 *)

(* Formalize a (simple) fact or construction about groups that you like. E.g., the fact that inverses are unique, or the definition of subgroup. *)

Definition mult (A : Group) := pr1 (pr2 A).
Definition inv (A : Group) := pr1 (pr2 (pr2 A)).
Definition unit (A : Group) := pr1 (pr2 (pr2 (pr2 A))).
Definition assoc (A : Group) := pr1 (pr2 (pr2 (pr2 (pr2 A)))).
Definition inv_laws (A : Group) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 A))))).
Definition unit_laws (A : Group) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 A))))).

Lemma uniq_inverses_group (A : Group) (a b : pr1 A) (p : mult A a b = unit A) : a = inv A b.
  rewrite <- (pr2 (unit_laws A a)).
  rewrite <- (pr2 (inv_laws A b)).
  rewrite <- (assoc A).
  unfold mult in p.
  rewrite p. 
  rewrite (pr1 (unit_laws A _)).
  apply idpath.
Defined.

(* Exercise 4 *)

(* Define the universe of pointed types as follows. *)

Definition PtdUU := ∑ T : UU, T.

(* Formulate a notion of equivalence between pointed types and show that such an equivalence induces an identity between pointed types (not only of the carriers).
   You may want to use the following lemmas from the libray: `total2_paths2_f`, `weqtopaths`, `weqpath_transport`. *)

Definition Ptd_map (A B : PtdUU) := 
  ∑ f : (pr1 A) → (pr1 B), f (pr2 A) = (pr2 B).

Definition Ptd_weq (A B : PtdUU) :=
  ∑ f : Ptd_map A B, isweq (pr1 f).
  
Definition idptdweq (A : PtdUU) : Ptd_weq A A.
  use tpair. 
  - use tpair.
    * exact (idfun (pr1 A)).
    * simpl. apply idpath.
  - simpl. apply idisweq.
Defined.

Lemma eqptdweqmap (A B : PtdUU) : A = B → Ptd_weq A B.
  intro p.
  induction p.
  apply idptdweq.
Defined.

Lemma ptdweqtoid (A B : PtdUU) : Ptd_weq A B → A = B.
  intros [[e p] isweqe].
  use total2_paths2_f.
  - apply weqtopaths.
    exact (e ,, isweqe).
  - simpl. use pathscomp0.
    + exact (e (pr2 A)).
    + apply (eqtohomot (weqpath_transport (e ,, isweqe))).
    + exact p.
Defined.

(* Exercise 5 *)

(* Show univalence for the universe of pointed types, i.e. that the function defined in Exercise 4 induces an equivalence. *)
(* Note: This is quite harder than all previous exercises! *)

(* This is a long-ish proof, read through `ptdunivalence` first, and only then
   work out what the lemmas are showing *)

(* Characterization between paths between paths in a ∑ type *)
Lemma total2_paths2_f_eq {A : UU} {a : A} (p q : A = A) 
  (p' : transportf (idfun UU) p a = a) (q' : transportf (idfun UU) q a = a) 
  (H1 : p = q) (H2 : transportf (λ r, transportf (idfun UU) r a = a) H1 p' = q') :
  total2_paths2_f p p' = total2_paths2_f q q'.
induction H1. induction H2. cbn. apply idpath.
Defined.

(* Computation of `weqpath_transport` *)
Lemma weqpath_transport_id {A :UU} :
  weqpath_transport (idfun A,, idisweq A) = 
    maponpaths 
      (λ x, transportf (idfun _) x)
      ( homotinvweqweq (univalence A A) (idpath A)).
  set (uasecrefl := homotinvweqweq (univalence A A) (idpath A)).
  set (mylemma := homotsec_natural (invhomot pr1_eqweqmap2) uasecrefl).
  cbn in mylemma. rewrite pathscomp0rid in mylemma. 
  refine (_ @ ! mylemma).
  apply (maponpaths (λ p, invhomot pr1_eqweqmap2 (invmap (univalence A A) (idweq A)) @ p)).
  refine (_ @ maponpathscomp eqweqmap pr1 uasecrefl). 
  apply maponpaths. 
  apply (! homotweqinvweqweq (univalence A A) (idpath A)).
Defined.

(* This is the tricky and key lemma *)
Lemma ptdweqtoid_idptdweq (A : PtdUU) : ptdweqtoid A A (idptdweq A) = idpath A.
  (* First we introduce variables and unfold/simplify *)
  induction A as [A a].
  unfold eqptdweqmap. unfold ptdweqtoid. cbn. rewrite pathscomp0rid.

  (* We set a name for convenience *)
  set (uasecrefl := homotinvweqweq (univalence A A) (idpath A)).

  (* We need to show an equality between equalities between pairs, so we apply `total2_paths2_f_eq` *)
  apply (total2_paths2_f_eq (weqtopaths (idfun A,, idisweq A)) (idpath A) (maponpaths (λ f, f a) (weqpath_transport (idfun A,, idisweq A))) (idpath _) uasecrefl).

  (* We now simplify using known lemmas *)
  cbn.
  rewrite transportf_paths_FlFr.
  rewrite maponpaths_for_constant_function.
  rewrite pathscomp0rid. 
  apply path_inverse_to_right.
  rewrite weqpath_transport_id.
  use (maponpathscomp (λ p, transportf (idfun UU) p)).
Defined.

(* "Equivalence induction" *)
Lemma weq_induction 
  (P : ∏ A : UU, ∏ B : UU, ∏ e : (A ≃ B), UU) 
  (A B : UU) (e : A ≃ B) :
  (P A A (idweq A)) → P A B e.
    intro H.
    rewrite <- (homotweqinvweq (univalence A B) e).
    apply (paths_ind UU A (λ B p, P A B (eqweqmap p)) H B (weqtopaths e)).
Defined.

(* Univalence for pointed types *)
Theorem ptdunivalence (A B : PtdUU) : isweq (eqptdweqmap A B).
  use isweq_iso.
  - exact (ptdweqtoid A B).
  - intro p. induction p. exact (ptdweqtoid_idptdweq A).
  - intros [[e p] isweqe]. induction A as [A a]. induction B as [B b]. cbn in *.
    induction p.
    apply (weq_induction (λ A B e, ∏ a : A, eqptdweqmap _ _ (ptdweqtoid (A,, a) (B,, e a) ((pr1 e ,, idpath (e a)),, pr2 e)) = (pr1 e,, idpath (e a)),, pr2 e)
      A B (e ,, isweqe) ).
    intro a'. 
    rewrite ptdweqtoid_idptdweq.
    apply idpath.
Defined.
