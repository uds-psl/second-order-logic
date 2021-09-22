(** ** Lists *)

(* Notations and tactics for working with lists from the Coq Library of Undecidability Proofs. *)

Require Import Decidable.

Require Import List.
Import ListNotations.

Notation "x 'el' L" := (List.In x L) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).

Notation "( A × B × .. × C )" := (List.list_prod .. (List.list_prod A B) .. C) (at level 0, left associativity).

Notation "[ s | p ∈ A ',' P ]" :=
  (map (fun p => s) (filter (fun p => dec2bool (Dec P)) A)) (p pattern).
Notation "[ s | p ∈ A ]" :=
  (map (fun p => s) A) (p pattern).



Lemma in_concat_iff A l (a:A) : 
  a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H.
  - rewrite in_app_iff, IHl. clear. firstorder subst. auto.
Qed.

Lemma in_filter_iff X (x : X) p A :
  x el filter p A <-> x el A /\ p x = true.
Proof.
  induction A as [|y A]; cbn.
  - tauto.
  - destruct (p y) eqn:E; cbn;
    rewrite IHA; intuition; subst; auto. congruence.
Qed.

Lemma list_prod_in X Y (x : X * Y) A B :
    x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
Proof.
  induction A; cbn.
  - intros [].
  - intros [H | H] % in_app_or. 2: firstorder.
    apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
Qed.

Ltac in_app n :=
  (match goal with
  | [ |- In _ (_ ++ _) ] =>
    match n with
    | 0 => idtac
    | 1 => eapply in_app_iff; left
    | S ?n => eapply in_app_iff; right; in_app n
    end
  | [ |- In _ (_ :: _) ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end
  end) || (repeat (try right; eapply in_app_iff; right)).

Lemma to_dec (P : Prop) `{dec P} : P <-> is_true (Dec P).
Proof.
  split; destruct (Dec P); cbn in *; firstorder congruence.
Qed.

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- In _ (filter _ _) ] => eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) | eapply Dec_auto; repeat split; eauto ] | _ => try (rewrite !in_prod_iff; repeat split) end ].

Ltac inv_collect :=
  repeat
    (match goal with
    | [ H : ?x el concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?)
    | [ H : ?x el map _ _ |- _ ] => let x := fresh "x" in eapply in_map_iff in H as (x & ? & ?)
    | [ x : ?A * ?B |- _ ] => destruct x; subst
    | [ H : ?x el filter _ _ |- _ ] => let H' := fresh "H" in eapply in_filter_iff in H as (? & H' % to_dec)
    | [ H : ?x el list_prod _ _ |- _ ] => eapply in_prod_iff in H
    | [ H : _ el _ ++ _ |- _ ] => try eapply in_app_iff in H as []
    | [H : _ el _ :: _ |- _ ] => destruct H
     end; intuition; subst).

Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
Global Hint Resolve in_eq in_nil in_cons in_or_app : core.


Instance in_dec X `{H : eq_dec X} (x : X) A :
  dec (x el A).
Proof.
  induction A.
  - now right.
  - destruct (H x a) as [->|]. now left. destruct IHA; firstorder.
Qed.
