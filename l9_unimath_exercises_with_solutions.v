Unset Universe Checking.
(** * l9 Exercises *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.All.

(**                   **)
(** * Preliminaries * **)
(**                   **)

Section l9.

Variable funext : funextsecStatement.

(** Generalisation of [maponpaths] to dependent functions. *)
(** Called [apd] in the lecture *)
Definition maponpaths_dep {X:UU} {Y : X -> UU}
    (f : ∏ x:X, Y x) {x1 x2} (e : x1 = x2)
  : transportf _ e (f x1) = f x2.
Proof.
  induction e. apply idpath.
Defined.

(** A circle is something that looks like a circle! *)
Definition circle_ind_structure {S : UU} {b : S} (l : b = b) : UU
  := ∏ (Y : S -> UU) (y_b : Y b) (y_l : transportf _ l y_b = y_b),
  (* The dependent function *)
   ∑ (f : ∏ x:S, Y x)
  (* The computation rule for the basepoint *)
     (e_b : f b = y_b),
  (* The computation rule for the loop, note that
     some paths have been added for it to typecheck *)
       maponpaths_dep f l
     = maponpaths _ e_b @ y_l @ !e_b.

(** From now on, we fix a circle type *)
Context {S1 : UU} {base : S1} (loop : base = base)
  (circle_str : circle_ind_structure loop).

(* For ease of use, we provide "accessors" to the relevant data *)
Definition circle_ind
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : ∏ x:S1, Y x.
Proof.
  exact (pr1 (circle_str _ _ y_l)).
Defined.

Definition circle_ind_comp_base
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : circle_ind y_l base = y_b.
Proof.
  exact (pr12 (circle_str _ _ y_l)).
Defined.

Definition circle_ind_comp_loop
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : maponpaths_dep (circle_ind y_l) loop
  = maponpaths _ (circle_ind_comp_base _)
    @ y_l @ ! (circle_ind_comp_base _).
Proof.
  exact (pr22 (circle_str _ _ y_l)).
Defined.

(**                   **)
(** * Exercises     * **)
(**                   **)

(* Exercise 1 *, The uniqueness principle *)
(* Hint: you may need [pathscomp0rid] and you will need
   to state your own lemma(s) *)

(* A general lemma to get rid of the fixed paths *)
Theorem transport_f_g
    {A B : UU} {f g : A -> B} {x y : A} (l : x = y) (r : f x = g x)
  : transportf (λ x : A, f x = g x) l r = !(maponpaths f l) @ r @ maponpaths g l.
Proof.
  intros. induction l. simpl.
  rewrite (pathscomp0rid _). cbv. apply idpath.
Defined.

Theorem transport_id_id
    {A : UU} {x y : A} (l : x = y) (r : x = x)
  : transportf (λ x : A, x = x) l r = !l @ r @ l.
Proof.
  intros. induction l. simpl.
  rewrite (pathscomp0rid _). cbv. apply idpath.
Defined.

Definition circle_uniq
    {Y : UU} {f g : S1 -> Y}
    (p : f base = g base)
    (q : transportf (λ x, x = x) p (maponpaths f loop) = maponpaths g loop) :
    ∏ (x : S1), f x = g x.
Proof.
  (* Use induction *)
  apply (@circle_ind _ p).


  (* Use the lemmas on [q] and on the goal *)
  rewrite (transport_f_g loop p).
  set (H := transport_id_id p (maponpaths f loop)).
  rewrite H in q.
  rewrite <- q.

  (* The rest is just managing all the paths *)
  assert (H' : ∏ (x y z w : Y) (p : x = y) (q : x = z) (r : y = w),
         ! p @ q @ ! q @ p @ r = r).
  {
    intros. induction p0. induction q0. simpl. apply idpath.
  }
  apply (H' _ _ _ _ (maponpaths f loop) p p).
Defined.

(* Exercise 2 *, The non-dependent induction principle *)
(* Hint, you will probably need [transportf_const] and [eqtohomot] *)
Definition loop_dep
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : transportf (λ _ : S1, Y) loop y_b = y_b.
Proof.
  exact (eqtohomot (transportf_const loop Y) y_b @ y_l).
Defined.

Definition circle_rec
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : S1 → Y.
Proof.
  apply (circle_ind (loop_dep y_l)).
Defined.

Definition circle_rec_comp_base
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : circle_rec y_l base = y_b.
Proof.
  apply (circle_ind_comp_base (loop_dep y_l)).
Defined.

Lemma apd_transportf_const
  {A B : UU} {x y : A} (f : A -> B) (p : x = y)
  : maponpaths_dep f p = (eqtohomot (transportf_const p B) _) @ (maponpaths f p).
Proof.
  induction p. cbv. apply idpath.
Defined.

(* Hint, you will need a coherence lemma *)
Definition circle_rec_comp_loop
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : maponpaths (circle_rec y_l) loop
  = circle_rec_comp_base y_l @ y_l @ ! circle_rec_comp_base y_l.
Proof.
  unfold circle_rec.
  (* By induction, we get *)
  set (h1 := circle_ind_comp_loop (loop_dep y_l)).
  (* For out general lemma, this time we use *)
  set (h2 := apd_transportf_const (circle_ind (loop_dep y_l)) loop).

  (* Simplifying the notation a bit *)
  set (f := circle_ind (loop_dep y_l)) in *.
  simpl in *.
  unfold circle_rec_comp_base.
  set (q := circle_ind_comp_base (loop_dep y_l)) in *.

  (* Almost all the hard work is done, we just manage the paths *)
  set (h3 := !h1 @ h2).
  apply (path_inv_rotate_ll) in h3.
  rewrite <- h3.
  rewrite path_assoc. rewrite path_assoc. rewrite path_assoc.
  apply (maponpaths (fun p => p @ ! q)).
  unfold loop_dep.
  rewrite path_assoc.
  apply (maponpaths (fun p => p @ y_l)).
  assert (fb_path : f base = y_b).
  {
    unfold f. rewrite <- (circle_rec_comp_base y_l).
    unfold circle_rec. apply idpath.
  }
  (* Again, a small (unnecessary) lemma to simplify things *)
  assert (H : ∏ (y1 y2 : Y), ∏ (p : y1 = y2),
    (! eqtohomot (transportf_const loop Y) y1 @
       maponpaths (transportf (λ _ : S1, Y) loop) p) @
       eqtohomot (transportf_const loop Y) y2 = p).
    {
      induction p. simpl. rewrite (pathscomp0rid _).
      apply path_inverse_to_right. apply idpath.
    }
  apply H.
Defined.


(* Exercise 3 *, The universal principle *)
(* Hint: Use the above exercises and [total2_paths2_f] *)

Definition circle_ump_structure (Y : UU) :
  isweq ((fun f => (f base,, maponpaths f loop)) : (S1 -> Y) -> (∑ y:Y, y = y)).
Proof.
  use isweq_iso.
  (* The inverse *)
  - intros [y p]. apply (circle_rec p).
  (* The η law, esentially holds by uniqueness *)
  - intro f. simpl. apply funext. unfold homot. use circle_uniq.
      + apply circle_rec_comp_base.
      + rewrite (transport_id_id _ _).
        rewrite (circle_rec_comp_loop (maponpaths f loop)).
      (* The rest is just managing all the paths *)
      assert (H : ∏ (x y  : Y) (p : x = y) (q : y = y),
             ! p @ (p @ q @ !p) @ p = q).
      {
        intros. induction p. simpl.
        rewrite pathscomp0rid. rewrite pathscomp0rid. apply idpath.
      }
      apply (H _ _ _ _).
  (* The ϵ law *)
  - intros [y p]. use total2_paths2_f.
    + apply circle_rec_comp_base.
    + rewrite (circle_rec_comp_loop p).
      rewrite (transport_id_id _ _).

      (* The rest is just managing all the paths *)
      assert (H : ∏ (x y  : Y) (p : x = y) (q : y = y),
             ! p @ (p @ q @ !p) @ p = q).
      {
        intros. induction p0. simpl.
        rewrite pathscomp0rid. rewrite pathscomp0rid. apply idpath.
      }
      apply (H _ _ _ _).
Defined.

(* Exercise 4 *, The suspension HIT *)
(* Give a definition of the suspension HIT as was done above for the circle *)

Definition ΣA_ind_structure
  {A : UU} {ΣA : UU} {N S : ΣA} {m : A -> N = S} : UU
  := ∏ (Y : ΣA -> UU) (YN : Y N) (YS : Y S)
       (Ym : ∏ (a : A), transportf Y (m a) YN = YS),
  (* The dependent function *)
     ∑ (f : ∏ x:ΣA , Y x)
  (* The computation rule for the N and S *)
       (e_N : f N = YN)
       (e_S : f S = YS),
  (* The computation rule for the meridian, note that
     some paths have been added for it to typecheck *)
     ∏ (a : A),
       maponpaths_dep f (m a)
     = maponpaths _ e_N @ (Ym a) @ ! e_S.
