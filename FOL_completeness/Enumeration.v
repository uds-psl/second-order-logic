(** *** Formula Enumeration *)
Require Export FOL FOL_facts.
Require Import List ListLib Enumerable.


(** **** Helper machinery **)

Lemma flat_map_app {X Y} A B (f : X -> list Y) :
  flat_map f (A ++ B) = flat_map f A ++ flat_map f B.
Proof.
  induction A; cbn.
  - reflexivity.
  - now rewrite IHA, app_assoc.
Qed.

Lemma switch_map {X Y} (P : Y -> Prop) (f : X -> Y) A :
  (forall x, x el A -> P (f x)) -> forall y, y el (map f A) -> P y.
Proof.
  intros H y (x & <- & Hx) % in_map_iff. eauto.
Qed.

Fixpoint at_pos {X} n x (A : list X) :=
  match A with
  | nil => False
  | a :: A' =>
    match n with
    | O => a = x
    | S n' => at_pos n' x A'
    end
  end.

Lemma el_at_pos {X} x (A : list X) :
  x el A <-> exists n, at_pos n x A.
Proof.
  induction A.
  - split. easy. intros [ [] [] ].
  - split.
    + intros [-> | H].
      * now exists 0.
      * apply IHA in H as [n H']. now exists (S n).
    + intros [ [] H].
      * now left.
      * right. apply IHA. now exists n.
Qed.



Instance enumerator__T_nat :
  enumerator__T (fun n => Some n) nat | 100.
Proof.
  intros x. now exists x.
Qed.

Instance enumerator__T_binops : 
  enumerator__T (fun _ => Some Impl) binop.
Proof.
  intros []. now exists 0.
Qed.

Instance enumerator__T_quantops : 
  enumerator__T (fun _ => Some All) quantop.
Proof.
  intros []. now exists 0.
Qed.


Section Positions.
  Variables (X: Type) (d: forall x y : X, {x = y} + {x <> y}).
  Implicit Types (x y: X) (A B : list X).

  Fixpoint pos x A : option nat :=
    match A with
    | nil => None
    | y :: A' => if d x y then Some 0
                else match pos x A' with
                     | Some n => Some (S n)
                     | None => None
                     end
    end.

  Lemma el_pos x A :
    x el A -> { n | pos x A = Some n }.
  Proof.
    induction A as [|y A IH]; cbn; intros H.
    - destruct H as [].
    - destruct (d x y) as [<-|H1].
      + now exists 0.
      + destruct IH as [n IH].
        * destruct H as [->|H]; tauto.
        * rewrite IH. now exists (S n).
  Qed.

  Notation nthe n A := (nth_error A n).

  Lemma nthe_length A n :
    length A > n -> { x | nthe n A = Some x }.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros n H.
    - exfalso. lia.
    - destruct n as [|n]; cbn.
      + now exists y.
      + destruct (IH n) as [x H1]. lia. now exists x.
  Qed.

 Lemma pos_nthe x A n :
    pos x A = Some n -> nthe n A = Some x.
 Proof.
   revert n.
   induction A as [|y A IH]; cbn; intros n.
    - intros [=].
    - destruct (d x y) as [<-|H1].
      + now intros [= <-].
      + destruct (pos x A) as [k|]; intros [= <-]; cbn.
        now apply IH.
  Qed.

  Lemma nthe_app_l x n A B :
    nthe n A = Some x -> nthe n (A ++ B) = Some x.
  Proof.
    revert n.
    induction A as [|y A IH]; cbn; intros k H.
    - destruct k; discriminate H.
    - destruct k as [|k]; cbn in *. exact H.
      apply IH, H.
  Qed.

End Positions.

Notation "| A |" := (List.length A) (at level 65).
Notation nthe n A := (nth_error A n).



(** **** Unused variables in the enumeration *)

Section L_T_unused.
  Context {Σf : funcs_signature}.
  Context {Σp : preds_signature}.

  Variable L_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T L_Funcs syms.

  Variable L_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T L_Preds preds.

  Lemma L_T_nat_le n m :
    n el L_T m -> n <= m.
  Proof.
    induction m.
    - intros []; now subst.
    - intros [ | [ | [] ] ] % in_app_or.
      + constructor. now apply IHm.
      + subst. auto.
  Qed.

  Lemma L_T_unused_t n m t :
    m <= n -> t el (L_term _ m) -> unused_term n t.
  Proof.
    revert n t. induction m; intros n t.
    - inversion 1; cbn; tauto.
    - intros H [ | [ | (A & H0 & (f & <- & Hf) % in_map_iff) % in_concat_iff ]] % in_app_or.
      * apply IHm. lia. assumption.
      * subst. constructor. lia.
      * revert H0. apply switch_map. intros v H'.  rewrite <- vecs_from_correct in H'. constructor.
        intros s Hs % H'. apply IHm. 1: lia. assumption.
  Qed.

  Lemma L_T_unused_v n m k (v : Vector.t term k) :
    m <= n -> v el (vecs_from (L_term _ m) k) -> (forall t, vec_in t v -> unused_term n t).
  Proof.
    induction k; cbn.
    - now intros ? [<-|[]].
    - intros H0 [[t' v'] [<- [H1 H2]%in_prod_iff]]%in_map_iff t H3. inv H3.
      now apply L_T_unused_t with m. now eapply IHk with v'.
  Qed.

  Lemma L_T_unused {ff : falsity_flag} n m phi :
    m <= n -> phi el (L_form _ _ _ _ m) -> unused n phi.
  Proof.
    revert n phi. induction m; intros n phi.
    - destruct ff. easy. intros ? [<- | []]. constructor.
    - cbn. intros H [ | [ | [ (A & H0 & (P & <- & HP) % in_map_iff)%in_concat_iff | [ (A & H0 & ([] & <- & HP) % in_map_iff)%in_concat_iff | (A & H0 & ([] & <- & HP) % in_map_iff)%in_concat_iff ] % in_app_or] % in_app_or] % in_app_or] % in_app_or;
        try (revert H0; apply switch_map).
      + apply IHm. lia. assumption.
      + destruct ff. easy. destruct H0 as [<-|[]]. constructor.
      + intros v H'. constructor. intros. apply L_T_unused_v with m (ar_preds P) v. all: lia + eauto.
      + intros [phi1 phi2] [] % in_prod_iff. constructor.
        all: apply IHm; [lia | assumption].
      + intros psi H'. constructor. apply IHm. lia. assumption.
  Qed.
End L_T_unused.

(** **** Single value enumeration *)

Section Enumeration.
  Variable X : Type.
  Variable L : nat -> list X.
  Hypothesis L_cumul : cumulative L.
  Context {Henum : list_enumerator__T L X}.
  Context {Hdec : eq_dec X}.

  Hypothesis Hlen : forall n, | L n | > n.

  Definition plain_enum n : X := proj1_sig (@nthe_length X (L n) n (Hlen n)).

  Lemma L_T_sub n m :
    n <= m -> exists A, L m = L n ++ A.
  Proof.
    induction 1.
    - exists nil. now rewrite app_nil_r.
    - cbn. destruct (L_cumul m) as [B ->]. destruct IHle as [A' ->]. 
      exists (A' ++ B). now rewrite app_assoc.
  Qed.

  Lemma L_T_sub_or n m :
    (exists A, L n = L m ++ A) \/ (exists A, L m = L n ++ A).
  Proof.
    destruct (PeanoNat.Nat.le_ge_cases n m) as [Hl | Hl]; [right | left]; now apply L_T_sub.
  Qed.

  Lemma plain_enum_enumerates x :
    exists n, plain_enum n = x.
  Proof.
    destruct (Henum x) as [m H]. destruct (el_pos _ Hdec _ _ H) as [n H'].
    exists n. unfold plain_enum. destruct (nthe_length _ _ _ (Hlen n)) as [y H'']. cbn.
    apply pos_nthe in H'. destruct (L_T_sub_or n m) as [ [A HA] | [A HA] ].
    - rewrite HA in H''. apply (nthe_app_l _ _ _ _ A) in H'. congruence.
    - rewrite HA in H'. apply (nthe_app_l _ _ _ _ A) in H''. congruence.
  Qed.

  Lemma plain_enum_slow n :
    plain_enum n el L n.
  Proof.
    unfold plain_enum. destruct (nthe_length _ _ _ (Hlen n)) as [y H'']. cbn. now apply nth_error_In in H''.
  Qed.
End Enumeration.

(** **** Single step enumeration for formulas *)

Section L_T_Enumeration.
  Context {Σf : funcs_signature}.
  Context {Σp : preds_signature}.
  Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.

  Variable eF : nat -> option Σf.
  Context {HeF : enumerator__T eF Σf}.

  Variable eP : nat -> option Σp.
  Context {HeP : enumerator__T eP Σp}.

  Existing Instance falsity_on.

  Lemma L_T_form_len n :
    | L_form _ _ _ _ n | > n.
  Proof.
    induction n; cbn.
    - lia.
    - rewrite! app_length. cbn. assert (forall m k, m > n -> m + S k > S n) as H by lia. now apply H.
  Qed.

  Definition form_enum n := plain_enum _ _ L_T_form_len n.

  Corollary form_enum_enumerates x :
    exists n, form_enum n = x.
  Proof. 
    apply plain_enum_enumerates. intuition. apply enum_form.
    apply dec_form; trivial; intros [] []; now left. 
  Qed.

  Lemma form_enum_fresh n m :
    n <= m -> unused m (form_enum n).
  Proof.
    intros H. apply (@L_T_unused _ _ _ _ _ _ _ m n). exact H.
    apply plain_enum_slow.
  Qed.
End L_T_Enumeration.
