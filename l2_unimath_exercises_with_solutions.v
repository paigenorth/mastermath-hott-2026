Require Export UniMath.Foundations.All.

(* Exercise 1*)

(*bool is defined as the following in UniMath.Foundations.Preamble:

Inductive bool : UU :=
  | true : bool
  | false : bool.

*)

Definition not : bool → bool.
Proof.
    intro b.
    induction b.
    - exact false.
    - exact true.
Defined.

Compute (not true).
Compute (not false).

Print not.
(*
 Notes:
 - bool_rect is what we call ind_bool in the lecture.
 - The argument (λ _ : bool, bool) : bool -> Type is implicit in the lecture.*)

(* Exercise 2 *)

Search (UU → UU → UU).
About coprod.

Definition distr {A B C : UU} : (A × B) ⨿ (A × C) → A × (B ⨿ C).
(* ⨿ is ~\amalg~ *)
Proof.
  intro.
  induction X.
  - induction a as [a b].
    split.
    + exact a.
    + exact (inl b).
  - induction b as [a c].
    split.
    + exact a.
    + exact (inr c).
Defined.

(* Exercise 3 *)

(* Write ∑ as ~\Sigma~ and terms as (a,,b).*)

Definition π1 {P : UU} (Q : P → UU) : (∑ (x : P), Q x) → P.
Proof.
  intro s.
  induction s as [p q].
  exact p.
Defined.

(*Exercise 4*)

Definition add : nat → nat → nat.
Proof. 
    intro n.
    intro m.
    induction m.
    - exact n.
    - exact (S IHm).
Defined.

Compute (add 5 7).
Compute (add 12 21).

Print add.


(*-------------------*)

(* Exercise 5 *)

Definition boolRep : bool → UU.
(* Send false to empty, the type with no constructors and true to unit, the type with one constructor. *)
Proof.
  intro b.
  induction b.
  - exact unit.
  - exact empty.
Defined.

(* Exercise 6 *)

Definition ι : bool → nat.
Proof.
  intro b.
  induction b.
  - exact 0.
  - exact 1.
Defined.

(* Exercise 7 *)

Definition mod2 : nat → bool.
Proof.
  intro n.
  induction n.
  - exact false.
  - exact (not IHn).
Defined.

Compute (mod2 15).
Compute (mod2 20).

(* Exercise 8 *)

Definition mult : nat → nat → nat.
Proof.
  intro n.
  intro m.
  induction m.
  - exact 0.
  - exact (add n IHm).
Defined.

Compute (mult 2 3).

(* Exercise 9 *)

Definition leq : nat → nat → bool.
Proof.
  intro n.
  induction n.
  - exact (λ x , true).
    (* Ensures 0 ≤ n ∀ n *)
  - intro m.
    induction m.
    + exact false.
    (* Ensures sn > m ∀ n,m *)
    + exact (IHn m).
    (* Ensures that sn ≤ sm reduces to n ≤ m.*)
Defined.

Compute (leq 0 0).
Compute (leq 0 1).
Compute (leq 1 0).
Compute (leq 1 1).
Compute (leq 1 2).
Compute (leq 2 1).
Compute (leq 2 3).
Compute (leq 3 2).

(* Exercise 10 *)

Theorem leqrefl : ∏ (n : nat) , boolRep (leq n n).
Proof.
  intro n.
  induction n.
  - simpl.
    exact tt.
  - simpl.
    exact IHn.
Defined.

(* Exercise 10 *)

Inductive leqUU : nat → nat → UU :=
| leq_0 : ∏ (m : nat) , leqUU 0 m
| leq_s : ∏ (n m : nat) ,leqUU n m → leqUU (S n) (S m).

Theorem leqbooltotype : ∏ (n m : nat) , boolRep (leq n m) → leqUU n m.
Proof.
  intro n.
  induction n.
  - intros m l.
    exact (leq_0 m).
  - intro m.
    induction m.
    + intro l.
      simpl in l.
      induction l.
    + intro l.
      apply leq_s.
      simpl in l.
      set (s := IHn m l).
      exact s.
Defined.




      










