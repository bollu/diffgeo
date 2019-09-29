From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Axiom R : Set.
Axiom zero: R.
Axiom one: R.
Axiom add: R -> R -> R.
Axiom negate: R -> R.

(* Axiom 1: R is a commutative ring *)

Create HintDb real.

(* add is an abelian group *)
Axiom add_assoc: forall (a b c: R), add a (add b c) = add (add a b) c.
Axiom add_zero: forall (a: R), add zero a = a.
Axiom negate_inv: forall (a: R),  add a (negate a) = zero.
Axiom add_commute: forall (a b: R), add a b = add b a.


Lemma add_zero_r: forall (a: R), add a zero = a.
  Proof. Admitted.

Hint Rewrite add_zero_r: real.
 
Hint Rewrite negate_inv: real.
Hint Rewrite add_zero: real.


(* mul is a commutative ring strcture *)
Axiom mul: R -> R -> R.
Axiom mul_commute: forall (a b: R), mul a b = mul b a.
Axiom mul_one: forall (a: R), mul one a = a.
Axiom mul_zero: forall (a: R), mul zero a = zero.



Lemma mul_zero': forall (a: R), mul a zero = zero.
Proof.  
  intros; rewrite mul_commute. apply mul_zero.
Qed.

Axiom mul_negate:
  forall (x: R) (x_neq_zero: x <> zero), exists (y: R), mul x y = one.

Hint Rewrite mul_one: real.
Hint Rewrite mul_zero: real.
Hint Rewrite mul_zero': real.

(* Axiom 2: relation that is transitive and irreflexive *)
Axiom lt : R -> R -> Prop.

Definition gt (x y: R) := lt y x.

Axiom lt_irreflexive: forall (a: R), not (lt a a).
Axiom lt_transitive: forall (a b c: R), lt a b -> lt b c -> lt a c.
Axiom zero_lt_one: lt zero one.
Axiom lt_add: forall (x y z: R), lt x y -> lt (add x z) (add y z).
Axiom lt_mul: forall (x y z: R), lt x y -> (gt z zero) -> lt (mul x z) (mul y z).


(* Axiom 3: every positive real has a square root *)

Axiom exist_sqrt: forall (x: R), gt x zero -> exists (y: R), mul y y = x.

Definition infinitesimal (d: R) : Prop := mul d d = zero.

Hint Unfold infinitesimal: real.

(* Axiom 4: Kock Lawvere *)
(* TODO: how do I state that f is from D -> R *)
Definition D := { d : R | infinitesimal d }.

(* zero is an infinitesimal *)
Lemma zero_infinitesimal : infinitesimal zero.
Proof.
  unfold infinitesimal.
  rewrite mul_zero.
  auto.
Qed.
(* zero as a member of D *)
Definition zero_D: D := exist _ zero zero_infinitesimal.
  

(* convert an element of D into an element of R *)
Definition D_to_R (d : D): R := proj1_sig d.


(** Kock Lawvere **)
(** it is EXISTS a, FORALL d. This flips the order ! **)
Axiom kl_exists: forall (f: D -> R),
    forall (d: D), { a: R |  f d = add (f zero_D) (mul (D_to_R d) a) }.

(* TODO: less clunky way to state uniqueness? *)
Axiom kl_uniq: forall (f: D -> R),forall (d: D) (a1 a2: R),
        forall (A1: f d = add (f zero_D) (mul (D_to_R d) a1))
               (A2: f d = add (f zero_D) (mul (D_to_R d) a2)), a1 = a2.


(** KL as a function **)
Definition kl_fn (f: D -> R) (d: D): { a: R | f d = add (f zero_D) (mul (D_to_R d) a) }.
Proof.
  destruct (kl_exists f d) as [a Ha].
  econstructor.
  exact Ha.
Qed.



  
(* If multiplication is equal for arbitrary infinitesimal, then the
numbers are equal *)
Lemma microcancel:
  forall (a b: R) (d: D) (muleq: mul a (D_to_R d) = mul b (D_to_R d)), a = b.
Proof.
  intros.
  eapply kl_uniq with (d := d) (a1 := a) (a2 := b) (f := fun d => mul a (D_to_R d)).
  simpl. autorewrite with real. rewrite mul_commute. reflexivity.
  simpl. autorewrite with real. rewrite  muleq. rewrite mul_commute. reflexivity.
Qed.

Definition der (f: R -> R) (x: R) (d: D): { a: R |  f (add x (D_to_R d)) = add (f x) (mul (D_to_R d) a) }.
Proof.
  intros.
  pose (kl_fn (fun d => f (add x (D_to_R d))) d) as f'.

  destruct f' as [a Ha].
  econstructor.
  rewrite Ha.
  autorewrite with real.
  reflexivity.
Qed.


(** Is synthetic differential geometry doomed? **)
(** There is no way to "get" an R without having a "D" at hand? **)
Definition der_what_we_want (f: R -> R) (x: R): { a: R | forall (d: D), f (add x (D_to_R d)) = add (f x) (mul (D_to_R d) a) }.
Proof.
  intros.
  pose (kl_fn (fun d => f (add x (D_to_R d)))) as f'.
  (** We are stuck here, since we have a forall d, exists a **)
  (** what we want is exists a, forall d **)
  destruct f'.
Abort.


Definition mul_fn (f: R -> R) (g: R -> R) (x: R): R := mul (f x) (g x).
Definition add_fn(f: R -> R) (g: R -> R) (x: R): R := add (f x) (g x).

