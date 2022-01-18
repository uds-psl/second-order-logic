Require Import SOL.
Require Import Decidable Enumerable.

Require Import List.
Import ListNotations.


Inductive full_logic_sym : Type :=
| Conj : full_logic_sym
| Disj : full_logic_sym
| Impl : full_logic_sym.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
| Ex : full_logic_quant.

Instance full_operators : operators :=
{| binop := full_logic_sym ; quantop := full_logic_quant |}.


Instance eqdec_full_logic_sym : eq_dec full_logic_sym.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Instance eqdec_full_logic_quant : Decidable.eq_dec full_logic_quant.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Definition L_binop (n : nat) := [Conj; Impl; Disj].

Instance enum_binop :
  list_enumerator__T L_binop binop.
Proof.
  intros []; exists 0; cbn; tauto.
Qed.

Definition L_quantop (n : nat) := [All; Ex].

Instance enum_quantop :
  list_enumerator__T L_quantop quantop.
Proof.
  intros []; exists 0; cbn; tauto.
Qed.

Lemma enumT_binop :
  enumerable__T binop.
Proof.
  apply enum_enumT. exists L_binop. apply enum_binop.
Qed.

Lemma enumT_quantop :
  enumerable__T quantop.
Proof.
  apply enum_enumT. exists L_quantop. apply enum_quantop.
Qed.


(** Mutliple quantors and closing operations *)

Require Import Lia.

Section Close.

  Fixpoint iter {X} (f : X -> X) n x := match n with O => x | S n' => f (iter f n' x) end.

  Lemma iter_switch {X} f n (x : X) :
    iter f n (f x) = f (iter f n x).
  Proof.
    induction n; cbn; congruence.
  Qed.

  Context {Σf : funcs_signature}.
  Context {Σp : preds_signature}.

  Definition quant_indi_n op n := iter (@quant_indi _ _ full_operators op) n.
  Definition quant_pred_n op ar n := iter (quant_pred op ar) n.

  Definition close_indi op phi := quant_indi_n op (proj1_sig (find_bounded_indi phi)) phi.

  Definition close_pred' ar op phi := quant_pred_n op ar (proj1_sig (find_bounded_pred ar phi)) phi.
  Fixpoint close_pred'' n op phi := match n with 0 => phi | S n => close_pred' n op (close_pred'' n op phi) end.
  Definition close_pred op phi := close_pred'' (find_arity_bound_p phi) op phi.

  Definition close op phi := close_indi op (close_pred op phi).

  Fixpoint forall_n n phi := match n with
    | 0 => phi
    | S n => quant_indi All (forall_n n phi)
  end.

  Lemma nat_ind_2 (P : nat -> nat -> Prop) : 
    (forall x, P x 0) -> (forall x y, P x y -> P y x -> P x (S y)) -> forall x y, P x y.
  Proof.
    intros H1 H2. intros x y. revert x. induction y.
    - apply H1.
    - intros x. apply H2. apply IHy. induction x; firstorder.
  Qed.

  Lemma close_indi_correct op phi :
    bounded_indi 0 (close_indi op phi).
  Proof.
    enough (forall n m, bounded_indi n phi -> bounded_indi (n-m) (iter (quant_indi op) m phi)) as X.
    { unfold close_indi. destruct find_bounded_indi as [n H]. cbn.
      specialize (X n n). replace (n-n) with 0 in X by lia. now apply X. }
    apply (nat_ind_2 (fun n m => bounded_indi n phi -> bounded_indi (n - m) (iter (quant_indi op) m phi))); cbn.
    - intros n B. now replace (n-0) with n by lia.
    - intros n m IH _ B. eapply bounded_indi_up. 2: apply IH. lia. exact B.
  Qed.

  Lemma close_indi_bounded_pred ar n op phi :
    bounded_pred ar n phi -> bounded_pred ar n (close_indi op phi).
  Proof.
    intros H. unfold close_indi. destruct find_bounded_indi as [b B]; cbn. clear B. now induction b.
  Qed.

  Lemma close_pred'_correct ar op phi :
    bounded_pred ar 0 (close_pred' ar op phi).
  Proof.
    enough (forall n m, bounded_pred ar n phi -> bounded_pred ar (n-m) (iter (quant_pred op ar) m phi)) as X.
    { unfold close_pred'. destruct find_bounded_pred as [n H]. cbn.
      specialize (X n n). replace (n-n) with 0 in X by lia. now apply X. }
    apply (nat_ind_2 (fun n m => bounded_pred ar n phi -> bounded_pred ar (n - m) (iter (quant_pred op ar) m phi))); cbn.
    - intros n B. now replace (n-0) with n by lia.
    - intros n m IH _ B. left. split. reflexivity. eapply bounded_pred_up. 2: apply IH. lia. exact B.
  Qed.

  Lemma close_pred'_bounded_pred ar n m op phi :
    bounded_pred ar n phi -> bounded_pred ar n (close_pred' m op phi).
  Proof.
    intros H. unfold close_pred'. destruct find_bounded_pred as [b B]. cbn. 
    clear B. induction b; cbn. easy. assert (ar = m \/ ar <> m) as [] by lia.
    left. split. easy. eapply bounded_pred_up. 2: apply IHb. lia. now right.
  Qed.

  Lemma close_pred'_arity_bounded_p n m op phi :
    arity_bounded_p n phi -> arity_bounded_p n (close_pred' m op phi).
  Proof.
    intros H. unfold close_pred'. destruct find_bounded_pred as [b B]. cbn. 
    clear B. now induction b.
  Qed.

  Lemma close_pred''_arity_bounded_p n m op phi :
    arity_bounded_p n phi -> arity_bounded_p n (close_pred'' m op phi).
  Proof.
    intros H. induction m; cbn. easy. apply close_pred'_arity_bounded_p, IHm.
  Qed.

  Lemma close_pred_correct op phi :
    forall ar, bounded_pred ar 0 (close_pred op phi).
  Proof.
    intros ar. assert (ar >= find_arity_bound_p phi \/ ar < find_arity_bound_p phi) as [H|H] by lia.
    - eapply bounded_pred_arity_bound. 2: apply H.
      apply close_pred''_arity_bounded_p, find_arity_bound_p_correct.
    - revert H. enough (forall n, ar < n -> bounded_pred ar 0 (close_pred'' n op phi)) by eauto.
      induction n. lia. intros H. assert (ar = n \/ ar < n) as [->|] by lia.
      + apply close_pred'_correct.
      + now apply close_pred'_bounded_pred, IHn.
  Qed.

  Lemma close_indi_funcfree op phi :
    funcfree phi -> funcfree (close_indi op phi).
  Proof.
    intros F. unfold close_indi. destruct find_bounded_indi as [n B]. cbn.
    clear B. now induction n.
  Qed.

  Lemma close_pred_funcfree op phi :
    funcfree phi -> funcfree (close_pred op phi).
  Proof.
    intros F. unfold close_pred. enough (forall n, funcfree (close_pred'' n op phi)) by easy.
    induction n; cbn. apply F. enough (forall psi m, funcfree psi -> funcfree (close_pred' m op psi)) by firstorder.
    intros psi m. unfold close_pred'. destruct find_bounded_pred as [b B]. cbn.
    clear B. now induction b.
  Qed.

  Lemma forall_n_funcfree n phi :
    funcfree phi -> funcfree (forall_n n phi).
  Proof.
    now induction n.
  Qed.

End Close.



Notation "∀i Phi" := (@quant_indi _ _ full_operators All Phi) (at level 50).
Notation "∃i Phi" := (@quant_indi _ _ full_operators Ex Phi) (at level 50).

Notation "∀f ( ar ) Phi" := (@quant_func _ _ full_operators All ar Phi) (at level 50).
Notation "∃f ( ar ) Phi" := (@quant_func _ _ full_operators Ex ar Phi) (at level 50).

Notation "∀p ( ar ) Phi" := (@quant_pred _ _ full_operators All ar Phi) (at level 50).
Notation "∃p ( ar ) Phi" := (@quant_pred _ _ full_operators Ex ar Phi) (at level 50).

Notation "⊥" := fal.
Notation "A ∧ B" := (@bin _ _ full_operators Conj A B) (at level 41).
Notation "A ∨ B" := (@bin _ _ full_operators Disj A B) (at level 42).
Notation "A '-->' B" := (@bin _ _ full_operators Impl A B) (at level 43, right associativity).
Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43).
Notation "¬ A" := (A --> ⊥) (at level 20).
