Require Export UniMath.Foundations.All.

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P → Q) (g : Q → R) (p : P) : R.
Proof.
  pose proof (f p) as q.
  pose proof (g q) as r.
  exact r.
Defined.

comp_app f g p = g f p .

Print comp_app.

(* Exercise 2 *)

Theorem curried_proj {P Q R : UU} : (P → (Q × R)) → (P → Q).
Proof.
  intro f.
  intro p.
  pose proof (f p) as qr.
  induction qr as [q _].
  exact q.
Defined.

(* Exercise 3 *)

Theorem exp : nat → nat → nat.
Proof.
  intros n m.
  induction m.
  - (* We define n^0 to be 1.*)
    exact 1.
  - (* We define n^(Sm) to be n^m * n. *)
    exact (IHm * n).
Defined.

Compute (exp 5 1).

Compute (exp 3 2).