From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope nat_scope. (* avoid clashes with notations for [nat] *)
Declare Scope R_scope.

(* TODO:
   (1) instead of using axioms at the top level, use modules
       or type classes (probably better);
   (2) since [R] is a ring, define required instances for the [ring] tactic
        https://coq.inria.fr/refman/addendum/ring.html *)

Axiom R : Set.
Axiom zero: R.
Notation "'_0'" := (zero) : R_scope.

Axiom one: R.
Notation "'_1'" := (one) : R_scope.

Axiom add: R -> R -> R.
Notation "a + b" := (add a b) (at level 50, left associativity) : R_scope.

Axiom negate: R -> R.
Notation "- x" := (negate x) : R_scope.

(* Axiom 1: R is a commutative ring *)

Create HintDb real.

Open Scope R_scope.

(* add is an abelian group *)
Axiom add_assoc: forall (a b c: R), a + (b + c) = (a + b) + c.
Axiom add_zero: forall (a: R), _0 + a = a.
Axiom negate_inv: forall (a: R),  a + (- a) = _0.
Axiom add_commute: forall (a b: R), a + b = b + a.

Lemma add_zero_r: forall (a: R), a + _0 = a.
Proof.
  intro a.
  rewrite add_commute.
  apply add_zero.
Qed.

Hint Rewrite add_zero: real.
Hint Rewrite add_zero_r: real.
 
Hint Rewrite negate_inv: real.
Hint Rewrite add_zero: real.


(* mul is a commutative ring structure *)
Axiom mul: R -> R -> R.
Infix "×" := (mul) (at level 25). (* [mul] binds tighter then [add], so its level is lower*)

Axiom mul_commute: forall (a b: R), a × b = b × a.
Axiom mul_one: forall (a: R), _1 × a = a.
Axiom mul_zero: forall (a: R), _0 × a = _0.


Lemma mul_zero': forall (a: R), a × _0 = _0.
Proof.
  intros; rewrite mul_commute.
  apply mul_zero.
Qed.

Axiom mul_negate:
  forall (x: R) (x_neq_zero: x <> _0), exists (y: R), x × y = _1.

Hint Rewrite mul_one: real.
Hint Rewrite mul_zero: real.
Hint Rewrite mul_zero': real.

(* Axiom 2: relation that is transitive and irreflexive *)
Axiom lt : R -> R -> Prop.

Definition gt (x y: R) := lt y x.

Axiom lt_irreflexive: forall (a: R), not (lt a a).
Axiom lt_transitive: forall (a b c: R), lt a b -> lt b c -> lt a c.
Axiom zero_lt_one: lt zero one.
Axiom lt_add: forall (x y z: R), lt x y -> lt (x + z) (y + z).
Axiom lt_mul: forall (x y z: R), lt x y -> (gt z zero) -> lt (x × z) (y × z).

Notation "x ²" := (x × x) (at level 25).

(* Axiom 3: every positive real has a square root *)

Axiom exist_sqrt: forall (x: R), gt x _0 -> exists (y: R), y² = x.

Definition infinitesimal (d: R) : Prop := d² = _0.

Hint Unfold infinitesimal: real.

(* Axiom 4: Kock Lawvere *)
Definition D := { d : R | infinitesimal d }.

(* convert an element of D into an element of R *)
Definition D_to_R (d : D): R := proj1_sig d.

(* Using this coercion one can use an element of [D] whenever
   an element of [R] is expected *)
Coercion D_to_R : D >-> R.


(* _0 is an infinitesimal *)
Lemma _0_infinitesimal : infinitesimal _0.
Proof.
  unfold infinitesimal.
  now autorewrite with real.
Qed.

(* _0 as a member of D *)
Definition _0_D: D := exist _ _0 _0_infinitesimal.

(** Kock Lawvere **)

(* Danil: I think this order of quantifiers is right.
   Apart from the original Kock's SDG paper, see also
   https://www.fuw.edu.pl/~kostecki/sdg.pdf (Section 2)
   for explicitly quantified formula. *)
Axiom kl_exists_unique: forall (f : D -> R),
    { a: R | forall (d : D), f d = (f _0_D) + a × d /\
             (* the uniqueness part: if we can write [f] in the way
                that it differs only in [a'], then [a'] should be exactly [a] *)
             forall a', f d = (f _0_D) + a' × d -> a = a'}.

(* Now, we can prove more convenient uniqueness principle, using the uniqueness
   part of the [kl_exists_unique] axiom *)
Lemma kl_uniq (f: D -> R) (d: D) (a1 a2: R) :
  f d = (f _0_D) + a1 × d ->
  f d = (f _0_D) + a2 × d ->
  a1 = a2.
Proof.
  intros A1 A2.
  pose proof (kl_exists_unique f) as H1.
  destruct H1 as [a0 H].
  (* NOTE: at this point we should use some [d : D] to get the equalities,
     and in fact we have a perfect candidate for this: [_0_D : D]*)
  pose proof (H _0_D) as H0.
  repeat autorewrite with real in *.
  destruct H0 as [_ Huniq].
  assert (a0 = a1).
  { apply Huniq. now repeat autorewrite with real in *. }
  assert (a0 = a2).
  { apply Huniq. now repeat autorewrite with real in *. }
  congruence.
Qed.

(* If multiplication is equal for arbitrary infinitesimal, then the
numbers are equal *)
(* NOTE: the scope of quantification for [d] is limited to the first equality.
   Basically, we cannot choose for which [d] it works, it should work any [d] *)
Lemma microcancel (a b : R):
  (forall (d: D), a × d = b × d) -> a = b.
Proof.
  intros H.
  (* NOTE: follows directly from uniqueness *)
  eapply kl_uniq with (d:=_0_D) (f:=fun d => a × d);
    now repeat autorewrite with real in *.
Qed.


Definition der (f: R -> R) (x: R): { a: R | forall (d: D), f (x + d) = f x + a × d }.
Proof.
  pose proof (kl_exists_unique (fun d => f (x + d))) as f'.
  destruct f' as [f'x H].
  exists f'x. intros d. repeat autorewrite with real in *.
  destruct (H d). assumption.
Qed.

Definition mul_fn (f: R -> R) (g: R -> R) (x: R): R := mul (f x) (g x).
Definition add_fn(f: R -> R) (g: R -> R) (x: R): R := add (f x) (g x).

