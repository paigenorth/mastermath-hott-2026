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

Definition circle_uniq
    {Y : UU} {f g : S1 -> Y}
    (p : f base = g base)
    (q : transportf (λ x, x = x) p (maponpaths f loop) = maponpaths g loop) :
    ∏ (x : S1), f x = g x.
Proof.
Admitted.

(* Exercise 2 *, The non-dependent induction principle *)
(* Hint, you will probably need [transportf_const] and [eqtohomot] *)

Definition circle_rec
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : S1 → Y.
Proof.
Admitted.

Definition circle_rec_comp_base
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : circle_rec y_l base = y_b.
Proof.
Admitted.

(* Hint, you will need a coherence lemma *)
Definition circle_rec_comp_loop
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : maponpaths (circle_rec y_l) loop
  = circle_rec_comp_base y_l @ y_l @ ! circle_rec_comp_base y_l.
Proof.
Admitted.


(* Exercise 3 *, The universal principle *)
(* Hint: Use the above exercises and [total2_paths2_f] *)

Definition circle_ump_structure (Y : UU) :
  isweq ((fun f => (f base,, maponpaths f loop)) : (S1 -> Y) -> (∑ y:Y, y = y)).
Proof.
Admitted.

(* Exercise 4 *, The suspension HIT *)
(* Give a definition of the suspension HIT as was done above for the circle *)

Definition ΣA_ind_structure : UU.
Admitted.
