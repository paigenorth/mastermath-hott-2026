Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Show Lemma 11.1.2 of Rijke. Give Def 11.1.1 yourself. *)

(* Hint: Follow the proof in Rijke, using `isweq_iso` at the end. For the statements, you will want to use `hfiber`, `∘` (`funcomp`), `~` (`homot`), `≃` (`weq`). *)

(* Exercise 2 *)

(* Show that if two types are equivalent and one is contractible, then the other is. *)

(* These proofs are starting to get more complicated, so you might want to the tactics `assert` or `transparent assert`. They basically let you prove small lemmas within your proof. If the lemma is not very small, I recommend making it a real lemma outside of your proof.*)
(* For assert you type 
`assert (x : T).`
where T is some specific type that you want to prove. Then a new goal (T) will be added, and you can open that goal by using the bullets (i.e. `-`, `+`, etc) or by putting the proof in curly braces. Once you are done, you can move back to the original goal by using the same kind of bullet or closing the curly braces, and then x : T will be added to the list of hypotheses.*)
(* If you want to use something about how x was constructed in the proof that follows, then you need `transparent assert`. Type:
`transparent assert (x : (T)).`
Note the extra parentheses.
*)

(* Exercise 3 *)

(* Show Theorem 11.1.3 of Rijke. *)

(* Exercise 4 *)

(* Show Thm 11.4.2 of Rijke. *)