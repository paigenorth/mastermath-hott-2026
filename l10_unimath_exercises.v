Unset Universe Checking.
Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Exercise 1 *)

(* Show that the propositional truncation of the booleans is the unit type. *)

(* Hint: use `funextsec`. *)

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem ex_1 : prop_trunc bool ≃ unit.
Proof.
  Admitted.

(* Exercise 2 *)

(* Define the `singleton' univalent category: the category with one object and no nonidentity arrows.*)

(* I.e., define a term of `univalent_category`, defined in the library.*)

(* Hint: exercises 2 and 3 are very similar. Think about lemmas to use so that you don't have to duplicate your work. *)

(* Exercise 3 *)

(* Define the `walking isomorphism' precategory: that is a category whose underlying set is the booleans and such that true ≅ false.
*)

(* I.e., define a term of type `category`. Unimath uses category to mean what the HoTT book calls precategory.*)

(* Exercise 4 *)

(* Show that the Rezk completion of the category from exercise 3 is the category from exercise 2.*)

(* I.e. construct a term of type `weak_equiv C D` where C and D are the categories defined above.*)

Definition weak_equiv (C D : category) : UU := ∑ H : functor C D, essentially_surjective H × fully_faithful H.