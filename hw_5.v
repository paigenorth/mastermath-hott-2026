Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Instructions: do Exercises 1 and 2 here in UniMath. Do Exercise 3 in LaTeX. No exercise should be done both in UniMath and LaTeX. As usual, you will submit one .v file and one .pdf file.*)

(* You can use anything proven in previous exercises or homework, and
`impred_isaprop`, `funextsec`, `weqtopaths`, `isweqtoforallpathsAxiom`, `toforallpaths`, `isweqhomot`, `twooutof3c`,
and anything else from UniMath.Foundations.UnivalenceAxiom.*)

(* Exercise 1 *)

(* Define the category of sets. *)

Theorem set_category : category.
Proof.
  Admitted.

(* Exercise 2 *)

(* Show that the category from exercise 1 is univalent.*)

Definition setiso (S T : hSet) : UU :=
  ∑ f : S → T ,
  ∑ g : T → S ,
  g ∘ f ~ idfun S
  ×
  f ∘ g ~ idfun T.

Definition set_idtoiso (S T : hSet) : (S = T) → (setiso S T).
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

Theorem set_univalence (S T : hSet) : isweq (set_idtoiso S T).
Proof.
  Admitted.
  (* You don't have to fill this proof in; it is from previous exercises.*)

Theorem set : univalent_category.
Proof.
  Admitted.

(* Exercise 3 *)
(* Define the interval HIT, and use it to show that every homotopy induces an
   equality of functions *)

(* Exercise 4 *)

(* Do not do this one in Unimath, only in LaTeX. *)

(* Consider the category G of groupoids, and the class D ⊆ mor (G) of isofibrations. Show that this is a display map category, and that it has the two additional properties required of a display map category. That is, show that:
  i) every X → * is a display map
  ii) D is closed under isomorphisms
  iii) D is stable under pullback
  iv) D contains all isomorphisms
  v) D is closed under composition

  Use the definition for isofibration and any results from the nLab page https://ncatlab.org/nlab/show/isofibration. Hint: use Prop 3.1.
  *)


(* Extra credit *)

(* Watch a talk from the HoTT/UF workshop happening 15-16 April. Write ~200 words reporting on what it was about and what you learned. The link is below; the organizers recommend registering to receive the Zoom link (you can ignore the registration deadline).

https://hott-uf.github.io/2025/

There is also the Working group on type theory meeting 17-18 April. You can choose a talk from this event instead.

https://europroofnet.github.io/wg6-genoa/ *)