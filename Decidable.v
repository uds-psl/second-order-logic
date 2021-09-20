(** ** Decidability *)

(** This file contains definition and facts regarding synthetic decidability 
    from the Coq Library of Undecidability Proofs. *)

Require Import Util.

Definition dec (P : Prop) := {P} + {~P}.
Definition ldec (P : Prop) := P \/ ~P.
Definition decidable {X} (p : X -> Prop) := exists f : X -> bool, forall x, p x <-> f x = true.
Definition ldecidable {X} (p : X -> Prop) := forall x, p x \/ ~ p x.
Definition eq_dec X := forall x y : X, dec (x = y).

Definition reduction {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) := forall x, P x <-> Q (f x).
Definition reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) := exists f : X -> Y, reduction f P Q.
Notation "P ⪯ Q" := (reduces P Q) (at level 70).

Existing Class eq_dec.

Definition tsat (f : nat -> bool) := exists n, f n = true.
Definition stable P := ~~P -> P.
Definition MP := forall f, stable (tsat f).


Existing Class dec.
Coercion dec2bool {P} (d: dec P) := if d then true else false.
Definition Dec (X: Prop) {d: dec X} : dec X := d.

Lemma Dec_reflect (X: Prop) (d: dec X) :
  is_true (Dec X) <-> X.
Proof.
  destruct d as [A|A]; cbv in *; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> is_true (Dec X).
Proof.
  destruct d as [A|A]; cbn; intuition congruence.
Qed.

Hint Extern 4 =>
  match goal with
    | [ |- dec ((fun _ => _) _) ] => cbn
  end : typeclass_instances.

Instance dec_eq_dec X `{eq_dec X} (x y : X) : dec (x = y) := H _ _.


Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).


Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  destruct (Dec P); cbv in *; firstorder.
  congruence.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  destruct (Dec P); cbv in *; firstorder.
  congruence.
Qed.

Hint Extern 4 =>
  match goal with
    [ H : dec2bool (Dec ?P) = true |- _ ] => apply Dec_true in H
  | [ H : dec2bool (Dec ?P) = true |- _ ] => apply Dec_false in H
  end : core.


Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

Existing Instance eqType_dec.


Instance True_dec :
  dec True.
Proof.
  unfold dec; tauto.
Qed.

Instance False_dec :
  dec False.
Proof.
  unfold dec; tauto.
Qed.

Instance impl_dec (X Y : Prop) :
  dec X -> dec Y -> dec (X -> Y).
Proof.
  unfold dec; tauto.
Qed.

Instance and_dec (X Y : Prop) :
  dec X -> dec Y -> dec (X /\ Y).
Proof.
  unfold dec; tauto.
Qed.

Instance or_dec (X Y : Prop) :
  dec X -> dec Y -> dec (X \/ Y).
Proof.
  unfold dec; tauto.
Qed.

Instance not_dec (X : Prop) :
  dec X -> dec (~ X).
Proof.
  unfold not. unfold dec. tauto.
Qed.

Instance iff_dec (X Y : Prop) :
  dec X -> dec Y -> dec (X <-> Y).
Proof.
  unfold iff. unfold dec. tauto.
Qed.



Lemma decidable_if X (p : X -> Prop) :
  (forall x, dec (p x)) -> decidable p.
Proof.
  intros H. exists (fun x => if H x then true else false). 
  split; now destruct (H x).
Qed.

Lemma decidable_ext X (p1 p2 : X -> Prop) :
  (forall x, p1 x <-> p2 x) -> decidable p1 -> decidable p2.
Proof.
  intros H [f Hf]. exists f. firstorder.
Qed.




Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold eq_dec, dec. decide equality. 
Defined.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold eq_dec, dec. decide equality. 
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold eq_dec, dec. decide equality.
Defined.

Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold eq_dec, dec. decide equality. 
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold eq_dec, dec. decide equality. 
Defined.

Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold eq_dec, dec. decide equality. 
Defined.

Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold eq_dec, dec. decide equality.
Defined.

Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold eq_dec, dec. decide equality.
Qed.

Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Qed.

Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Qed.


Lemma decidable_transport_red {X Y} (P : X -> Prop) (Q : Y -> Prop) :
  P ⪯ Q -> decidable Q -> decidable P.
Proof.
  intros [g Hg] [f Hf]. exists (fun y => f (g y)). intros x. split.
  - intros H. apply Hf, Hg, H.
  - intros H. apply Hg, Hf, H.
Qed.
