From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition R := Type.
Axiom zero: R.
Axiom one: R.
Axiom add: R -> R -> R.
Axiom negate: R -> R.

(* Axiom 1: R is a commutative ring *)

(* add is an abelian group *)
Axiom add_assoc: forall (a b c: R), add a (add b c) = add (add a b) c.
Axiom add_unit: forall (a: R), add zero a = a.
Axiom negate_inv: forall (a: R),  add a (negate a) = zero.
Axiom add_commute: forall (a b: R), add a b = add b a.

(* mul is a commutative ring strcture *)
Axiom mul: R -> R -> R.
Axiom mul_commute: forall (a b: R), mul a b = mul b a.
Axiom mul_unit: forall (a: R), mul one a = a.

Axiom mul_negate: forall (x: R) (x_neq_zero: x <> zero), exists (y: R), mul x y = one.

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

(* Axiom 4: Kock Lawvere *)
(* TODO: how do I state that f is from D -> R *)
Axiom kl: forall (f: R -> R), forall (d: R) (dinfin: infinitesimal d), exists (a: R),
        f d = add (f zero) (mul d a).

(* TODO: less clunky way to state uniqueness? *)
Axiom kl_uniq: forall (f: R -> R), forall (d: R) (dinfin: infinitesimal d), exists (a1 a2: R),
        forall (A1: f d = add (f zero) (mul d a1))
         (A2: f d = add (f zero) (mul d a2)), a1 = a2.
  
