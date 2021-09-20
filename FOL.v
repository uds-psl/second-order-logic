(** * First-Order Logic *)

(** Definition of first-order syntax, semantics, and deduction from the Library of Undecidability Proofs *)

Require Import Coq.Vectors.Vector.
Local Notation vec := t.

Require Import Equations.Equations Equations.Prop.DepElim.



(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(* Signatures are a record to allow for easier definitions of general transformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (* We use the stdlib definition of vectors to be maximally compatible  *)

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Set Elimination Schemes.

  Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
    match t with
    | var t => σ t
    | func f v => func f (map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  (* We use a flag to switch on and off a constant for falisity *)

  Inductive falsity_flag := falsity_off | falsity_on.
  Existing Class falsity_flag.
  Existing Instance falsity_on | 1.
  Existing Instance falsity_off | 0.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.

  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), vec term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b
  | quant {b} : quantop -> form b -> form b.
  Arguments form {_}.

  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form `{falsity_flag} (σ : nat -> term) (phi : form) : form :=
    match phi with
    | falsity => falsity
    | atom P v => atom P (map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

End fix_signature.


(* Setting implicit arguments is crucial  *)
(* We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _ _, _ _ {_ _}, {_ _ _ _}, {_ _ _} _.
Arguments atom  _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments bin   _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments quant _ _ _ _, _ _ {_ _}, {_ _ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _ _, _ _ {_ _}, {_ _ _ _}.



Section fix_signature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
    | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
    | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.

  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

End fix_signature.




Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Notation "$ x" := (var x) (at level 3, format "$ '/' x").
  Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]").
  Notation "phi [ sigma ]" := (subst_form sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]").
  Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity).
  Notation "f >> g" := (funcomp g f) (at level 50).
  Notation "s '..'" := (scons s var) (at level 4, format "s ..").
  Notation "↑" := (S >> var).

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext {ff : falsity_flag} (phi : form) sigma tau :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbn; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id {ff : falsity_flag} (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbn; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var {ff : falsity_flag} (phi : form) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp {ff : falsity_flag} (phi : form) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi1, IHphi2.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift {ff : falsity_flag} (phi : form) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_form {ff : falsity_flag} xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.

  Lemma up_decompose {ff : falsity_flag} sigma phi :
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.
  
End Subst.





Require Import ListLib Lia.

Section Bounded.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Inductive bounded_t n : term -> Prop :=
  | bounded_var x : n > x -> bounded_t n (var x)
  | bouded_func f v : (forall t, Vector.In t v -> bounded_t n t) -> bounded_t n (func f v).

  Inductive bounded : forall {ff}, nat -> form ff -> Prop :=
  | bounded_atom ff n P v : (forall t, Vector.In t v -> bounded_t n t) -> @bounded ff n (atom P v)
  | bounded_bin binop ff n phi psi : @bounded ff n phi -> @bounded ff n psi -> @bounded ff n (bin binop phi psi)
  | bounded_quant quantop ff n phi : @bounded ff (S n) phi -> @bounded ff n (quant quantop phi)
  | bounded_falsity n : @bounded falsity_on n falsity.

  Arguments bounded {_} _ _.

  Definition bounded_L {ff : falsity_flag} n A :=
    forall phi, phi el A -> bounded n phi.

  Lemma bounded_subst_t n t sigma tau :
    (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> subst_term sigma t = subst_term tau t.
  Proof.
    intros H. induction 1; cbn; auto.
    f_equal. now apply Vector.map_ext_in.
  Qed.

  Lemma bounded_subst {ff : falsity_flag} {n phi sigma tau} :
    bounded n phi -> (forall k, n > k -> sigma k = tau k) -> subst_form sigma phi = subst_form tau phi.
  Proof.
    induction 1 in sigma, tau |- *; cbn; intros HN; trivial.
    - f_equal. apply Vector.map_ext_in. intros t Ht.
      eapply bounded_subst_t; try apply HN. now apply H.
    - now rewrite (IHbounded1 sigma tau), (IHbounded2 sigma tau).
    - f_equal. apply IHbounded. intros [|k] Hk; cbn; trivial.
      unfold funcomp. rewrite HN; trivial. lia.
  Qed.

  Lemma bounded_up_t {n t k} :
    bounded_t n t -> k >= n -> bounded_t k t.
  Proof.
    induction 1; intros Hk; constructor; try lia. firstorder.
  Qed.

  Lemma bounded_up {ff : falsity_flag} {n phi k} :
    bounded n phi -> k >= n -> bounded k phi.
  Proof.
    induction 1 in k |- *; intros Hk; constructor; eauto.
    - intros t Ht. eapply bounded_up_t; eauto.
    - apply IHbounded. lia.
  Qed.

  (* Derive Signature for In. *)

  Lemma find_bounded_step n (v : vec term n) :
    (forall t : term, vec_in t v -> {n : nat | bounded_t n t}) -> { n | forall t, In t v -> bounded_t n t }.
  Proof.
    induction v; cbn; intros HV.
    - exists 0. intros t. inversion 1.
    - destruct IHv as [k Hk], (HV h) as [l Hl]; try left.
      + intros t Ht. apply HV. now right.
      + exists (k + l). intros t H. depelim H; cbn in *.
        * injection H. intros _ <-. apply (bounded_up_t Hl). lia.
        * injection H0. intros -> % Eqdep_dec.inj_pair2_eq_dec _; try decide equality.
          apply (bounded_up_t (Hk t H)). lia.
  Qed.

  Lemma find_bounded_t t :
    { n | bounded_t n t }.
  Proof.
    induction t using term_rect.
    - exists (S x). constructor. lia.
    - apply find_bounded_step in X as [n H]. exists n. now constructor.
  Qed.

  Lemma find_bounded {ff : falsity_flag} phi :
    { n | bounded n phi }.
  Proof.
    induction phi.
    - exists 0. constructor.
    - destruct (find_bounded_step _ t) as [n Hn].
      + eauto using find_bounded_t.
      + exists n. now constructor.
    - destruct IHphi1 as [n Hn], IHphi2 as [k Hk]. exists (n + k).
      constructor; eapply bounded_up; try eassumption; lia.
    - destruct IHphi as [n Hn]. exists n. constructor. apply (bounded_up Hn). lia.
  Qed.

  Lemma find_bounded_L {ff : falsity_flag} A :
    { n | bounded_L n A }.
  Proof.
    induction A; cbn.
    - exists 0. intros phi. inversion 1.
    - destruct IHA as [k Hk], (find_bounded a) as [l Hl].
      exists (k + l). intros t [<-|H]; eapply bounded_up; try eassumption; try (now apply Hk); lia.
  Qed.

  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.

  Fact iter_switch {X} f n x :
    f (@iter X f n x) = iter f n (f x).
  Proof.
    induction n; cbn; now try rewrite IHn.
  Qed.
  
  (* Lemma subst_up_var k x sigma :
    x < k -> (var x)`[iter up k sigma] = var x.
  Proof.
    induction k in x, sigma |-*.
    - now intros ?%PeanoNat.Nat.nlt_0_r.
    - intros H.
      destruct (Compare_dec.lt_eq_lt_dec x k) as [[| <-]|].
      + cbn [iter]. rewrite iter_switch. now apply IHk.
      + destruct x. reflexivity.
        change (iter _ _ _) with (up (iter up (S x) sigma)).
        change (var (S x)) with ((var x)`[↑]).
        rewrite up_term, IHk. reflexivity. constructor.
      + lia.
  Qed.
  
  Lemma subst_bounded_term t sigma k :
    bounded_t k t -> t`[iter up k sigma] = t.
  Proof.
    induction 1.
    - now apply subst_up_var.
    - cbn. f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in. auto.
  Qed.

  Lemma subst_bounded {ff : falsity_flag} k phi sigma :
    bounded k phi -> phi[iter up k sigma] = phi.
  Proof.
    induction 1 in sigma |-*; cbn.
    - f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in.
      intros t Ht. apply subst_bounded_term. auto.
    - now rewrite IHbounded1, IHbounded2.
    - f_equal.
      change (up _) with (iter up (S n) sigma).
      apply IHbounded.
    - reflexivity.
  Qed. *)

End Bounded.





Inductive full_logic_sym : Type :=
| Conj : full_logic_sym
| Disj : full_logic_sym
| Impl : full_logic_sym.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
| Ex : full_logic_quant.

Instance full_operators : operators :=
{| binop := full_logic_sym ; quantop := full_logic_quant |}.



Require Import List.
Require Import ListLib.

Section Deduction.

  Context {Σf : funcs_signature}.
  Context {Σp : preds_signature}.

  Notation "⊥" := falsity.
  Notation "A ∧ B" := (bin Conj A B) (at level 41).
  Notation "A ∨ B" := (FOL.bin Disj A B) (at level 42).
  Notation "A '-->' B" := (FOL.bin Impl A B) (at level 43, right associativity).
  Notation "∀ Phi" := (FOL.quant All Phi) (at level 50).
  Notation "∃ Phi" := (FOL.quant Ex Phi) (at level 50).

  Notation "$ x" := (var x) (at level 3, format "$ '/' x").
  Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]").
  Notation "phi [ sigma ]" := (subst_form sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]").
  Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity).
  Notation "f >> g" := (funcomp g f) (at level 50).
  Notation "s '..'" := (scons s var) (at level 4, format "s ..").
  Notation "↑" := (S >> var).

  Reserved Notation "A ⊢ phi" (at level 61).
  Implicit Type ff : falsity_flag.
  Inductive prv : forall (ff : falsity_flag), list form -> form -> Prop :=
    | II {ff} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
    | IE {ff} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
    | AllI {ff} A phi : List.map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
    | AllE {ff} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
    | ExI {ff} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
    | ExE {ff} A phi psi : A ⊢ ∃ phi -> phi::(List.map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi
    | Exp A phi : A ⊢ ⊥ -> A ⊢ phi
    | Ctx {ff} A phi : List.In phi A -> A ⊢ phi
    | CI {ff} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
    | CE1 {ff} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
    | CE2 {ff} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
    | DI1 {ff} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
    | DI2 {ff} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
    | DE {ff} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  where "A ⊢ phi" := (prv _ A phi).
  Notation "A ⊢ phi" := (prv _ A phi).

  Context {p : falsity_flag}.

  Definition tprv T phi := exists A, (forall psi, List.In psi A -> T psi) -> A ⊢ phi.

  Theorem Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    intros H. revert B.
    induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.

  Hint Constructors prv : core.

  Ltac comp := repeat (progress (cbn in *; autounfold in *)).

  Theorem subst_Weak A phi xi :
    A ⊢ phi -> [phi[xi] | phi ∈ A] ⊢ phi[xi].
  Proof.
    induction 1 in xi |-*; comp.
    1-2,7-14: eauto using List.in_map.
    - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
      apply IHprv. intros ?. cbn. now rewrite up_form.
    - specialize (IHprv xi). apply AllE with (t0 := t`[xi]) in IHprv. rewrite subst_comp in *.
      erewrite subst_ext; try apply IHprv. intros [|]; cbn; trivial.
      unfold funcomp. now setoid_rewrite subst_term_shift.
    - specialize (IHprv xi). eapply ExI with (t0 := t`[xi]). rewrite subst_comp in *.
      erewrite subst_ext; try apply IHprv. intros [|]; cbn; trivial.
      unfold funcomp. now setoid_rewrite subst_term_shift.
    - eapply ExE in IHprv1. eassumption. rewrite map_map.
      specialize (IHprv2 (up xi)). setoid_rewrite up_form in IHprv2.
      erewrite map_map, map_ext in IHprv2; try apply IHprv2. apply up_form.
  Qed.

  Definition cycle_shift n x :=
    if PeanoNat.Nat.eq_dec n x then $0 else $(S x).

  Lemma cycle_shift_shift n phi :
    bounded n phi -> phi[cycle_shift n] = phi[↑].
  Proof.
    intros H. apply (bounded_subst H). intros k. unfold cycle_shift. destruct PeanoNat.Nat.eq_dec; trivial; lia.
  Qed.

  Lemma cycle_shift_subject n phi :
    bounded (S n) phi -> phi[$n..][cycle_shift n] = phi.
  Proof.
    intros H. erewrite subst_comp, (bounded_subst H), subst_id; trivial.
    intros []; cbn; unfold cycle_shift; destruct PeanoNat.Nat.eq_dec; trivial; lia.
  Qed.

  Lemma nameless_equiv_all' A phi n :
    bounded_L n A -> bounded (S n) phi -> [p[↑] | p ∈ A] ⊢ phi <-> A ⊢ phi[$n..].
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak _ _ ($n..)) in H. rewrite map_map in *.
      erewrite map_ext, map_id in H; try apply H. intros. apply subst_shift.
    - apply (subst_Weak _ _ (cycle_shift n)) in H. rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject in H.
      + intros psi HP. now apply cycle_shift_shift, H1.
  Qed.

  Lemma nameless_equiv_ex' A phi psi n :
    bounded_L n A -> bounded n phi -> bounded (S n) psi -> (psi::[p0[↑] | p0 ∈ A]) ⊢ phi[↑] <-> (psi[$n..]::A) ⊢ phi.
  Proof.
    intros HL Hphi Hpsi. split.
    - intros H % (subst_Weak _ _ ($n..)). cbn in *.
      rewrite map_map, (map_ext _ id), map_id in H.
      + now rewrite subst_shift in H.
      + intros. apply subst_shift.
    - intros H % (subst_Weak _ _ (cycle_shift n)). cbn in *.
      rewrite (map_ext_in _ (subst_form ↑)) in H.
      + now rewrite cycle_shift_subject, cycle_shift_shift in H.
      + intros theta HT. now apply cycle_shift_shift, HL.
  Qed.

  Lemma nameless_equiv_all A phi :
    { t : term | map (subst_form ↑) A ⊢ phi <-> A ⊢ phi[t..] }.
  Proof.
    destruct (find_bounded_L (phi::A)) as [n H].
    exists $n. apply nameless_equiv_all'.
    - intros ? ?. apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_ex A phi psi :
    { t : term | (phi :: map (subst_form ↑) A) ⊢ psi[↑] <-> (phi[t..]::A) ⊢ psi }.
  Proof.
    destruct (find_bounded_L (phi::psi::A)) as [n H].
    exists $n. apply nameless_equiv_ex'.
    - intros ? ?. apply H. auto.
    - apply H. auto.
    - eapply bounded_up; try apply H; auto.
  Qed.

End Deduction.




(** Tarski Semantics ***)

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Semantic notions *)

  Section Semantics.

    Variable domain : Type.

    Class interp := B_I
      {
        i_func : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_atom : forall P : preds, vec domain (ar_preds P) -> Prop ;
      }.

    Definition env := nat -> domain.

    Context {I : interp}.

    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var s => rho s
      | func f v => i_func (Vector.map (eval rho) v)
      end.

    Fixpoint sat {ff : falsity_flag} (rho : env) (phi : form) : Prop :=
      match phi with
      | atom P v => i_atom (Vector.map (eval rho) v)
      | falsity => False
      | bin Impl phi psi => sat rho phi -> sat rho psi
      | bin Conj phi psi => sat rho phi /\ sat rho psi
      | bin Disj phi psi => sat rho phi \/ sat rho psi
      | quant All phi => forall d : domain, sat (scons d rho) phi
      | quant Ex phi => exists d : domain, sat (scons d rho) phi
      end.

  End Semantics.

End Tarski.

Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp {_ _} _, _ _ _.

Notation "p ⊨ phi" := (sat _ p phi) (at level 20).






(* ** Discreteness *)

Require Import EqdepFacts.
Require Import Decidable.

Lemma inj_pair2_eq_dec' A :
  eq_dec A -> forall (P : A -> Type) (p : A) (x y : P p), existT P p x = existT P p y -> x = y.
Proof.
  apply Eqdep_dec.inj_pair2_eq_dec.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2;
                                                      [subst | try (eauto || now intros; decide equality)]
  end.

Lemma dec_vec_in X n (v : vec X n) :
  (forall x, vec_in x v -> forall y, dec (x = y)) -> forall v', dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
  intros Hv. induction v; intros v'; dependent elimination v'...
  destruct (Hv h (vec_inB h v) h0)... edestruct IHv.
  - intros x H. apply Hv. now right.
  - left. f_equal. apply e.
  - right. intros H. inversion H. resolve_existT. tauto.
Qed.

Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
  intros v. now apply dec_vec_in.
Qed.

Section EqDec.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.
  Hypothesis eq_dec_binop : eq_dec binop.
  Hypothesis eq_dec_quantop : eq_dec quantop.

  Global Instance dec_term : eq_dec term.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    intros t. induction t as [ | ]; intros [|? v']...
    - decide (x = n)... 
    - decide (F = f)... destruct (dec_vec_in X v')...
  Qed.

  Instance dec_falsity : eq_dec falsity_flag.
  Proof.
    intros b b'. unfold dec. decide equality.
  Qed.

  Lemma eq_dep_falsity b phi psi :
    eq_dep falsity_flag (@form Σ_funcs Σ_preds ops) b phi b psi <-> phi = psi.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H. resolve_existT. reflexivity.
    - intros ->. reflexivity.
  Qed.

  Lemma dec_form_dep {b1 b2} phi1 phi2 : dec (eq_dep falsity_flag (@form _ _ _) b1 phi1 b2 phi2).
  Proof with subst; try (now left + (right; intros ? % eq_sigT_iff_eq_dep; resolve_existT; congruence)).
    unfold dec. revert phi2; induction phi1; intros; try destruct phi2.
    all: try now right; inversion 1. now left.
    - decide (b = b0)... decide (P = P0)... decide (t = t0)... right.
      intros [=] % eq_dep_falsity. resolve_existT. tauto.
    - decide (b = b1)... decide (b0 = b2)... destruct (IHphi1_1 phi2_1).
      + apply eq_dep_falsity in e as ->. destruct (IHphi1_2 phi2_2).
        * apply eq_dep_falsity in e as ->. now left.
        * right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
      + right. rewrite eq_dep_falsity in *. intros [=]. now repeat resolve_existT.
    - decide (b = b0)... decide (q = q0)... destruct (IHphi1 phi2).
      + apply eq_dep_falsity in e as ->. now left.
      + right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
  Qed.

  Global Instance dec_form {ff : falsity_flag} : eq_dec form.
  Proof.
    intros phi psi. destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
  Qed.

End EqDec.
