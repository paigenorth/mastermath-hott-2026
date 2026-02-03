(* A lot of things are abbreviated with Unicode symbols. Depending on your editor, there is usually a way to get "Agda" or "Latex" input, and then you write the symbol as in (or similar to) Latex.
For me (using the Unicode Latex extension in VS Code), × is ~\times~ and → is ~\to~.
*)

(* When using Coq, there are usually three windows. One is where this text and the rest of the code should be. One is a window that displays the current hypotheses and goals when you are in tactic/proof mode. One displays other output (i.e. when you use ~Print.~ or ~Compute.~).

Coq has a very nice interactive mode where you `step' through a file, line by line, and Coq evaluates the file up to that point. So in particular, you can step through a proof line by line, and the window with the hypotheses and goals will (usually) change with each step. Thus, you can not only read the proof code but also what it is accomplishing. In VS Code, you can use the command ~Coq: Step Forward~, in ProofGeneral you use ~proof-assert-next-command-interactive~, and there is a down arrow button on https://unimath.github.io/live/. On all platforms, there are keyboard shortcuts. There are also other commands like `step back', or `interpret to point'.
*)

Require Export UniMath.Foundations.All.

(*The above line imports the definition of ~×~ and ~UU~ that we use below.*)

(* Example 1 *)

(* Show that Q follows from P ∧ (P → Q) *)

Theorem modusPonens {P Q : UU} (h : P × (P → Q)) : Q.

(*
By writing the keyword ~Theorem~ we are telling Coq that we are about to write down the statement for a theorem. Lemma, Corollary, etc, and Definition (!) are all synonyms here.

The next thing should be the name of the theorem. Really, it is the name that we want to give to the term that we will construct in the proof. The line above is of the form
    ~Theorem modusPonens ... : Q.~
This means that we are proving a theorem whose proof consists of constructing a term, that will be called modusPonens after construction in Q.

The hypotheses (analogous to a contect) go where the ~...~ is. Here we have three hypotheses: P, Q, and h.

Here we suppose that we have two types P and Q, and one term h of P × (P → Q).

Writing {P Q : UU} means that if we want to use modusPonens in a corollary, we can write ~modusPonens h~ for some previously defined or assumed ~h : P × (P → Q)~ and Coq will figure out from h the types P and Q. Otherwise we would have to write ~modusPonens P Q h~.
*)

Proof.

(* To start the interactive 'tactic' mode, write ~Proof.~*)
  induction h.
  (* The `canonical terms of a product type are pairs. By using the tactic ~induction~ on h, we are telling Coq to assume that h is a pair.*)
  exact (pr2 pr1).
  (* The tactic ~exact~ tells Coq that this is our answer for the goal. If we have something complicated after exact, we need to use parentheses. ~pr2 pr1~ is how we write function application.*)
Qed.

 (* or we could do *)

Theorem modusPonensAgain {P Q : UU} (h : P × (P → Q)) : Q.
Proof.
  induction h as [p f].
  (* Above, we used ~induction h~ and it made up names for the two new terms. Here we assert which names we want.*)
  set (q := f p).
  (* Here we can give a nice name to a derivable term and add it to the hypotheses.*)
  exact q.
Qed.

(* Example 2 *)

(* Show that (P ∧ Q) → P *)

Theorem firstProjection {P Q : UU} : (P × Q) → P.
Proof.
  intro.
  (* Usually, when we want to prove an implication / construct a function, we want to assume that we have a term of the domain. The ~intro~ tactic does that.*)
  induction X as [p q].
  exact p.
Qed.

(* or we could do *)

Theorem firstProjectionAgain {P Q : UU} : (P × Q) → P.
Proof.
  intro p.
  induction p as [p _].
  (* Using the _ tells Coq that we don't care about the second term. We will see _ used in other similar ways.*)
  exact p.
Qed.

(* Example 3 *)

(* Show that Q ∧ P follows from P ∧ Q *)

Theorem commute {P Q : UU} (c : Q × P) : P × Q.
Proof.
  induction c as [q p].
  exact (p,,q).
  (* In Unimath, you write terms of a product type as ~(?,,?)~ unfortunately.*)
Qed.

(* Exercise 4 *)

(* Show that multiplication of types is associative. *)

Theorem assoc {P Q R : UU} (c : (P × Q) × R ) : P × (Q × R).
Proof.
  induction c as [c r].
  induction c as [p q].
  set (c := (q,,r)).
  exact (p,,c).
Qed.

(* Exercise 5 *)

(* Show that functions can be composed.*)

Theorem comp {P Q R : UU} (f : P → Q) (g : Q → R) : P → R.
Proof.
  intro p.
  set (q := f p).
  set (r := g q).
  exact r.
Qed.

(* Exercise 6 *)

(* A weird version of modus ponens. *)

Theorem weirdModusPonens {P Q : UU} : ((P → Q) × P → (P × Q)).
Proof.
  intro c.
  induction c as [f p].
  set (q := f p).
  exact (p,,q).
Qed.

(* Exercise 7 *)

(* Define the identity function. *)

(* Here's one way to do it. *)

Definition lambdaIdentity (P : UU) : P → P :=
  λ x , x.

(* This definition does *not* use tactic/proof mode. Notice how there is no ~Proof.~ or ~Qed.~. Here we construct a `lambda term' by hand. Actually everything is a lambda term in Coq, and the tactic mode just helps you to build them up. You can see what lambda term you've built up by typing ~Print ?.~ *)

Print lambdaIdentity.

Print modusPonens.

(* Now define the identity function using tactic/proof mode and check if it's the same as ~lambdaIdentity~ by using ~Print.~*)

Definition identity (P : UU) : P → P.
Proof.
  intro p.
  exact p.
Defined.

Print identity.