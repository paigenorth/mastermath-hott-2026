Require Export UniMath.Foundations.All.

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P → Q) (g : Q → R) (p : P) : R.
Proof.
  Admitted.

(* Exercise 2 *)

Theorem curried_proj {P Q R : UU} : (P → (Q × R)) → (P → Q).
Proof.
  Admitted.

(* Exercise 3 *)

Theorem exp : nat → nat → nat.
Proof.
  Admitted.


Compute (exp 5 1).
(* Should output 5. *)

Compute (exp 3 2).
(* Should output 9. *)

(* Exercise 4 *)

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).

(* This command searches the library for functions of this type. You should see in the output that ~maponpaths~ is of this type. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
Proof.
  Admitted.