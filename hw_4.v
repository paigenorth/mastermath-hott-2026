Unset Universe Checking.
Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

(* You can use any result from previous homeworks, exercises, or lectures without proof.*)

(* Exercise 1 *)

(* Define the type of groups. *)

(* Exercise 2 *)

(* Give a group structure on the booleans ~bool~ and show that it produces a term of the type of groups. Use the fact ~isasetbool~ that ~bool~ is a set.*)

(* Exercise 3 *)

(* Formalize a (simple) fact or construction about groups that you like. E.g., the fact that inverses are unique, or the definition of subgroup. *)

(* Exercise 4 *)

(* Define the universe of pointed types as follows. *)

Definition PtdUU := ∑ T : UU, T.

(* Formulate a notion of equivalence between pointed types and show that such an equivalence induces an identity between pointed types (not only of the carriers).
   You may want to use the following lemmas from the libray: `total2_paths2_f`, `weqtopaths`, `weqpath_transport`. *)

(* Exercise 5 *)

(* Show univalence for the universe of pointed types, i.e. that the function defined in Exercise 4 induces an equivalence. *)
(* Note: This is quite harder than all previous exercises! You can use any lemma defined in the imported files *)
