(** * Natural Deduction *)

Require Import List.
Import ListNotations.

Require Import Equations.Equations Equations.Prop.DepElim.
Require Import Lia.

Require Import SOL.
Require Import FullSyntax.
Require Import Subst.
Require Import Henkin Tarski.
Require Import VectorLib ListLib.
Require Import Decidable Enumerable.

Import SubstNotations.


Inductive peirce := class | intu.
Existing Class peirce.

Definition LEM := forall P, P \/ ~P.


Section ND.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.


  Implicit Type p : peirce.

  Reserved Notation "A ⊢ phi" (at level 61).
  Inductive prv : forall (p : peirce), list (form) -> form -> Prop :=

    (* Standard rules *)

    | II {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
    | IE {p} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
    | Exp {p} A phi : A ⊢ ⊥ -> A ⊢ phi
    | Ctx {p} A phi : phi el A -> A ⊢ phi
    | CI {p} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
    | CE1 {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
    | CE2 {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
    | DI1 {p} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
    | DI2 {p} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
    | DE {p} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
    | Peirce A phi psi : prv class A (((phi --> psi) --> phi) --> phi)

    (* Quantifiers *)

    | AllI_i {p} A phi : map (subst_form_i ↑) A ⊢ phi -> A ⊢ ∀i phi
    | AllI_f {p} A ar phi : map (subst_form_f (↑ ar)) A ⊢ phi -> A ⊢ ∀f(ar) phi
    | AllI_p {p} A ar phi : map (subst_form_p (↑ ar)) A ⊢ phi -> A ⊢ ∀p(ar) phi

    | AllE_i {p} A t phi : A ⊢ ∀i phi -> A ⊢ phi[t..]i
    | AllE_f {p} A ar (f : function ar) phi : A ⊢ ∀f(ar) phi -> A ⊢ phi[f..]f
    | AllE_p {p} A ar (P : predicate ar) phi : A ⊢ ∀p(ar) phi -> A ⊢ phi[P..]p

    | ExI_i {p} A t phi : A ⊢ phi[t..]i -> A ⊢ ∃i phi
    | ExI_f {p} A ar (f : function ar) phi : A ⊢ phi[f..]f -> A ⊢ ∃f(ar) phi
    | ExI_p {p} A ar (P : predicate ar) phi : A ⊢ phi[P..]p -> A ⊢ ∃p(ar) phi

    | ExE_i {p} A phi psi : A ⊢ ∃i phi -> phi::(map (subst_form_i ↑) A) ⊢ psi[↑]i -> A ⊢ psi
    | ExE_f {p} A ar phi psi : A ⊢ ∃f(ar) phi -> phi::(map (subst_form_f (↑ ar)) A) ⊢ psi[↑ ar]f -> A ⊢ psi
    | ExE_p {p} A ar phi psi : A ⊢ ∃p(ar) phi -> phi::(map (subst_form_p (↑ ar)) A) ⊢ psi[↑ ar]p -> A ⊢ psi

    (* Comprehension *)
    | Comp {p} A ar phi : funcfree phi -> A ⊢ comprehension_form ar phi

  where "A ⊢ phi" := (prv _ A phi).

  Definition tprv {p} (T : form -> Prop) (phi : form) := 
    exists A, (forall psi, List.In psi A -> T psi) /\ @prv p A phi.

  Notation "A ⊢c phi" := (@prv class A phi) (at level 55).
  Notation "A ⊢i phi" := (@prv intu A phi) (at level 55).
  Notation "A ⊩ phi" := (tprv A phi) (at level 55).
  Notation "A ⊩c phi" := (@tprv class A phi) (at level 55).
  Notation "A ⊩i phi" := (@tprv intu A phi) (at level 55).


  (** Lemmas establishing soundess of the comprehension axiom *)

  Lemma forall_n_subst_i ar phi sigma :
    (forall_n ar phi)[sigma]i = forall_n ar phi[iter up_i ar sigma]i.
  Proof.
    induction ar in sigma |-*; cbn. reflexivity. rewrite IHar. f_equal. f_equal. 
    apply subst_ext_i. now rewrite iter_switch.
  Qed.

  Lemma forall_n_subst_p ar phi sigma :
    (forall_n ar phi)[sigma]p = forall_n ar phi[sigma]p.
  Proof.
    induction ar; cbn; congruence.
  Qed.

  Lemma forall_n_subst_f ar phi sigma :
    (forall_n ar phi)[sigma]f = forall_n ar phi[sigma]f.
  Proof.
    induction ar; cbn; congruence.
  Qed.

  Lemma comprehension_subst_i phi ar sigma P :
    (forall_n ar (atom P (tabulate ar var_indi) <--> phi[↑ ar]p))[sigma]i = forall_n ar (atom P (tabulate ar var_indi) <--> phi[iter up_i ar sigma]i[↑ ar]p).
  Proof.
    rewrite forall_n_subst_i. cbn. erewrite <- subst_switch_i_p, map_tabulate, tabulate_ext.
    reflexivity. clear P. cbn. induction ar; intros m H; cbn. lia. destruct m; cbn. reflexivity.
    rewrite IHar. reflexivity. lia.
  Qed.

  Lemma comprehension_subst_f phi ar sigma P :
    (forall_n ar (atom P (tabulate ar var_indi) <--> phi[↑ ar]p))[sigma]f = forall_n ar (atom P (tabulate ar var_indi) <--> phi[sigma]f[↑ ar]p).
  Proof.
    rewrite forall_n_subst_f. cbn. erewrite <- subst_switch_f_p, map_tabulate, tabulate_ext.
    reflexivity. reflexivity.
  Qed.

  Lemma comprehension_subst_p phi ar sigma :
    (forall_n ar (p$0 (tabulate ar var_indi) <--> phi[↑ ar]p))[up_p sigma ar]p = forall_n ar (p$0 (tabulate ar var_indi) <--> phi[sigma]p[↑ ar]p).
  Proof.
    rewrite forall_n_subst_p. cbn. erewrite nat_eq_dec_same, up_form_p, tabulate_ext.
    reflexivity. reflexivity.
  Qed.

  Lemma forall_n_to_vec D (I : interp D) rho n phi :
    rho ⊨ forall_n n phi <-> forall v : vec D n, ⟨ VectorLib.fold_left scons (get_indi rho) v, get_func rho, get_pred rho ⟩ ⊨ phi.
  Proof.
    enough (forall rho_i rho_f rho_p, ⟨rho_i, rho_f, rho_p⟩ ⊨ forall_n n phi <-> forall v : vec D n, ⟨ VectorLib.fold_left scons rho_i v, rho_f, rho_p ⟩ ⊨ phi) by now destruct rho.
    intros. clear rho. revert rho_i. induction n; intros rho_i; cbn.
    - split.
      + intros H v. now dependent elimination v.
      + intros H. apply (H (Vector.nil _)).
    - split.
      + intros H v. dependent elimination v. cbn. apply IHn, H.
      + intros H d. apply IHn. intros v. apply (H (Vector.cons _ d _ v)).
  Qed.

  Lemma fold_left_scons_lookup D (rho_i : nat -> D) n m (v : vec D n) :
    VectorLib.fold_left scons rho_i v (n+m) = rho_i m.
  Proof.
    revert rho_i m. induction v; intros rho_i m; cbn.
    + reflexivity.
    + replace (S (n+m)) with (n + S m) by lia. rewrite IHv. reflexivity.
  Qed.

  Lemma eval_tabulate D (I : interp D) rho_i rho_f rho_p ar (v : vec D ar) :
    Vector.map (eval _ ⟨ VectorLib.fold_left scons rho_i v, rho_f, rho_p ⟩) (tabulate ar var_indi) = v.
  Proof.
    revert rho_i. induction v; intros rho_i; cbn.
    - reflexivity.
    - f_equal.
      + enough (VectorLib.fold_left scons (h .: rho_i) v (n + 0) = h) by now replace (n + 0) with n in H by lia.
        apply fold_left_scons_lookup.
      + apply IHv.
  Qed.

  Lemma comprehension_sound D (I : interp D) (rho : env D) ar phi :
    rho ⊨ comprehension_form ar phi.
  Proof.
    pose (Q := fun v : vec D ar => True).
    exists (fun v => ⟨ VectorLib.fold_left scons (get_indi rho) v, get_func rho, Q .: get_pred rho ⟩ ⊨ phi[↑ ar]p).
    apply forall_n_to_vec. intros v. cbn -[sat]. split.
    - intros H. cbn in H.
      destruct PeanoNat.Nat.eq_dec as [->|]; try easy. apply sat_comp_p. 
      eapply sat_ext. 2: apply sat_comp_p, H. split; cbn.
      + now rewrite eval_tabulate.
      + split; try easy; cbn. unfold shift, shift_p, scons, scons_env_pred, scons_ar.
        destruct PeanoNat.Nat.eq_dec as [->|]; cbn. reflexivity.
        destruct n. destruct PeanoNat.Nat.eq_dec as [|]; try easy. reflexivity.
    - intros H. cbn. destruct PeanoNat.Nat.eq_dec as [->|]; try easy.
      apply sat_comp_p. eapply sat_ext. 2: apply sat_comp_p, H. split; cbn.
      + now rewrite eval_tabulate.
      + split; try easy; cbn. unfold shift, shift_p, scons, scons_env_pred, scons_ar.
        destruct PeanoNat.Nat.eq_dec as [->|]; cbn. reflexivity.
        destruct n. destruct PeanoNat.Nat.eq_dec as [|]; try easy. reflexivity.
  Qed.


  (** ** Tarski Soundness *)

  (** Soundess of the deduction system *)

  Theorem SoundnessI A phi :
    A ⊢i phi -> Tarski.valid A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA.
    - intros H1. apply IHprv; trivial. intros phi' [->|]; firstorder.
    - apply IHprv1; trivial. apply IHprv2; trivial.
    - exfalso. eapply IHprv; trivial. apply HA.
    - firstorder.
    - split. now apply IHprv1. now apply IHprv2.
    - now apply IHprv.
    - now apply IHprv.
    - left. now apply IHprv.
    - right. now apply IHprv.
    - edestruct IHprv1; trivial. exact HA.
      + apply IHprv2; trivial. intros x [->|]; firstorder.
      + apply IHprv3; trivial. intros x [->|]; firstorder.
    - discriminate.
    - intros x. apply IHprv; trivial. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_i. now destruct rho; apply HA.
    - intros f. apply IHprv; trivial. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_f. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      (* Why is this replace necessary? *)
      replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
      now rewrite <- eval_function_subst_cons_shift_f.
    - intros P. apply IHprv; trivial. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_p. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
      now rewrite <- eval_predicate_subst_cons_shift_p.
    - eapply sat_comp_i, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval _ rho t)).
      split; try easy. now destruct n.
    - eapply sat_comp_f, sat_ext. 2: eapply (IHprv Heqp D I rho HA (eval_function _ rho f)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - eapply sat_comp_p, sat_ext. 2: eapply (IHprv Heqp D I rho HA (eval_predicate _ rho P)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - exists (eval _ rho t). eapply sat_ext. 2: apply sat_comp_i, IHprv, HA; trivial.
      split; try easy. now destruct n.
    - exists (eval_function _ rho f). eapply sat_ext. 2: apply sat_comp_f, IHprv, HA; trivial.
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - exists (eval_predicate _ rho P). eapply sat_ext. 2: apply sat_comp_p, IHprv, HA; trivial.
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - edestruct IHprv1 as [x Hx]; eauto.
      specialize (IHprv2 Heqp D I ⟨x .: get_indi rho, get_func rho, get_pred rho ⟩).
      apply sat_comp_i in IHprv2. destruct rho; apply IHprv2.
      intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hx.
      apply sat_comp_i. destruct rho; apply H'.
    - edestruct IHprv1 as [f Hf]; eauto.
      specialize (IHprv2 Heqp D I ⟨get_indi rho, f .: get_func rho, get_pred rho ⟩).
      apply sat_comp_f in IHprv2.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hf. 
        apply sat_comp_f. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
    - edestruct IHprv1 as [P HP]; eauto.
      specialize (IHprv2 Heqp D I ⟨get_indi rho, get_func rho, P .: get_pred rho ⟩).
      apply sat_comp_p in IHprv2.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact HP.
        apply sat_comp_p. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
    - apply comprehension_sound.
  Qed.

  Theorem SoundnessC A phi :
    LEM -> A ⊢c phi -> Tarski.valid A phi.
  Proof.
    intros lem. induction 1; intros D I rho HA.
    - intros H1. apply IHprv. intros phi' [->|]; firstorder.
    - apply IHprv1; trivial. apply IHprv2; trivial.
    - exfalso. eapply IHprv. apply HA.
    - firstorder.
    - split. now apply IHprv1. now apply IHprv2.
    - now apply IHprv.
    - now apply IHprv.
    - left. now apply IHprv.
    - right. now apply IHprv.
    - edestruct IHprv1. exact HA.
      + apply IHprv2. intros x [->|]; firstorder.
      + apply IHprv3. intros x [->|]; firstorder.
    - cbn. specialize (lem (rho ⊨ phi)). tauto.
    - intros x. apply IHprv. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_i. now destruct rho; apply HA.
    - intros f. apply IHprv. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_f. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      (* Why is this replace necessary? *)
      replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
      now rewrite <- eval_function_subst_cons_shift_f.
    - intros P. apply IHprv. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_p. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
      now rewrite <- eval_predicate_subst_cons_shift_p.
    - eapply sat_comp_i, sat_ext. 2: apply (IHprv D I rho HA (eval _ rho t)).
      split; try easy. now destruct n.
    - eapply sat_comp_f, sat_ext. 2: eapply (IHprv D I rho HA (eval_function _ rho f)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - eapply sat_comp_p, sat_ext. 2: eapply (IHprv D I rho HA (eval_predicate _ rho P)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - exists (eval _ rho t). eapply sat_ext. 2: apply sat_comp_i, IHprv, HA.
      split; try easy. now destruct n.
    - exists (eval_function _ rho f). eapply sat_ext. 2: apply sat_comp_f, IHprv, HA.
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - exists (eval_predicate _ rho P). eapply sat_ext. 2: apply sat_comp_p, IHprv, HA.
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - edestruct IHprv1 as [x Hx]; eauto.
      specialize (IHprv2 D I ⟨x .: get_indi rho, get_func rho, get_pred rho ⟩).
      apply sat_comp_i in IHprv2. destruct rho; apply IHprv2.
      intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hx.
      apply sat_comp_i. destruct rho; apply H'.
    - edestruct IHprv1 as [f Hf]; eauto.
      specialize (IHprv2 D I ⟨get_indi rho, f .: get_func rho, get_pred rho ⟩).
      apply sat_comp_f in IHprv2.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hf. 
        apply sat_comp_f. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
    - edestruct IHprv1 as [P HP]; eauto.
      specialize (IHprv2 D I ⟨get_indi rho, get_func rho, P .: get_pred rho ⟩).
      apply sat_comp_p in IHprv2.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact HP.
        apply sat_comp_p. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
    - apply comprehension_sound.
  Qed.

  (* Goal forall P, ~ ~ (P \/ ~ P). intros P. tauto. Show Proof. *)

  Lemma Soundness_to_LEM :
    (forall A phi, A ⊢c phi -> Tarski.valid A phi) -> LEM.
  Proof.
    intros H P. enough (valid List.nil (p$0 (Vector.nil _) ∨ ¬ p$0 (Vector.nil _))) as X.
    { pose (I := {| i_f f v := 0 ; i_P P v := False |}). 
      destruct (X nat I ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ => P⟩); auto. easy. }
    apply H. eapply IE. eapply Peirce with (psi := ⊥).
    apply II. apply Exp. eapply IE with (phi := ¬ p$0 (Vector.nil term)).
    - apply II. eapply IE. apply Ctx; now right. apply DI2. now apply Ctx.
    - apply II. eapply IE. apply Ctx; now right. apply DI1. now apply Ctx.
  Qed.

  Corollary SoundnessIT T phi :
    T ⊩i phi -> Tarski.validT T phi.
  Proof.
    intros [A [HA H1]] D I rho HT. eapply SoundnessI. apply H1.
    intros psi H2. apply HT, HA, H2.
  Qed.

  Corollary SoundnessCT :
    LEM <-> (forall T phi, T ⊩c phi -> Tarski.validT T phi).
  Proof.
    split.
    - intros lem T phi [A [HA H1]] D I rho HT. eapply SoundnessC; trivial. apply H1.
      intros psi H2. apply HT, HA, H2.
    - intros H P. enough (validT (fun _ => False) (p$0 (Vector.nil _) ∨ ¬ p$0 (Vector.nil _))) as X.
      { pose (I := {| i_f f v := 0 ; i_P P v := False |}). 
        destruct (X nat I ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ => P⟩); auto. easy. }
      apply H. exists List.nil. split; trivial. eapply IE. eapply Peirce with (psi := ⊥).
      apply II. apply Exp. eapply IE with (phi := ¬ p$0 (Vector.nil term)).
      + apply II. eapply IE. apply Ctx; now right. apply DI2. now apply Ctx.
      + apply II. eapply IE. apply Ctx; now right. apply DI1. now apply Ctx.
  Qed.

End ND.

Arguments prv {_ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 61).
Notation "A ⊢c phi" := (@prv _ _ class A phi) (at level 55).
Notation "A ⊢i phi" := (@prv _ _ intu A phi) (at level 55).
Notation "A ⊩ phi" := (tprv A phi) (at level 55).
Notation "A ⊩c phi" := (@tprv _ _ class A phi) (at level 55).
Notation "A ⊩i phi" := (@tprv _ _ intu A phi) (at level 55).


(** ** Enumerability *)

Section Enumerability.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {L_Funcs : nat -> list syms}.
  Hypothesis enum_Funcs' : list_enumerator__T L_Funcs syms.

  Context {L_Preds : nat -> list preds}.
  Hypothesis enum_Preds' : list_enumerator__T L_Preds preds.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.

  Instance enum_term' : list_enumerator__T (L_term _ _) term := enum_term _ _.
  Instance enum_form' : list_enumerator__T (L_form _ _ _ _ _ _ _ _) form := enum_form _ _ _ _ _ _ _ _.

  (** Redefine notation to avoid conflict with subst notation *)
  Notation "`[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).

  Instance funcfree_dec phi : dec (funcfree phi) := funcfree_dec phi.

  Fixpoint L_prv {p : peirce} (A : list form) (n : nat) : list form := match n with
    | 0 => A
    | S n => L_prv A n
                ++ concat `[ [ phi --> psi | psi ∈ L_prv (phi :: A) n ] | phi ∈ L_T form n ]
                ++ [ psi | (phi, psi) ∈ (L_prv A n × L_T form n) , (phi --> psi el L_prv A n) ]
                ++ [ phi | phi ∈ L_T form n, ⊥ el L_prv A n ]
                ++ [ phi ∧ psi | (phi, psi) ∈ (L_prv A n × L_prv A n) ]
                ++ [ phi | (phi, psi) ∈ (L_T form n × L_T form n), phi ∧ psi el L_prv A n]
                ++ [ psi | (phi, psi) ∈ (L_T form n × L_T form n), phi ∧ psi el L_prv A n]
                ++ [ phi ∨ psi | (phi, psi) ∈ (L_T form n × L_T form n), phi el L_prv A n]
                ++ [ phi ∨ psi | (phi, psi) ∈ (L_T form n × L_T form n), psi el L_prv A n]
                ++ [ theta | (phi, psi, theta) ∈ (L_T form n × L_T form n × L_T form n),
                             theta el L_prv (phi::A) n /\ theta el L_prv (psi::A) n /\ phi ∨ psi el L_prv A n]
                ++ (if p then [ ((phi --> psi) --> phi) --> phi | (phi, psi) ∈ (L_T form n × L_T form n) ] else nil )
                ++ [ ∀i phi | phi ∈ L_prv (map (subst_form_i ↑) A) n ]
                ++ concat `[ [ ∀f(ar) phi | phi ∈ L_prv (map (subst_form_f (↑ ar)) A) n ] | ar ∈ L_nat n ]
                ++ concat `[ [ ∀p(ar) phi | phi ∈ L_prv (map (subst_form_p (↑ ar)) A) n ] | ar ∈ L_nat n ]
                ++ [ phi[t..]i | (phi, t) ∈ (L_T form n × L_T term n), (∀i phi) el L_prv A n ]
                ++ [ phi[(var_func x ar)..]f | (x, ar, phi) ∈ (L_nat n × L_nat n × L_T form n), (∀f(ar) phi) el L_prv A n ]
                ++ [ phi[(sym f)..]f | (f, phi) ∈ (L_T n × L_T form n), (∀f(ar_syms f) phi) el L_prv A n ]
                ++ [ phi[(var_pred x ar)..]p | (x, ar, phi) ∈ (L_nat n × L_nat n × L_T form n), (∀p(ar) phi) el L_prv A n ]
                ++ [ phi[(pred P)..]p | (P, phi) ∈ (L_T n × L_T form n), (∀p(ar_preds P) phi) el L_prv A n ]
                ++ [ ∃i phi | (phi, t) ∈ (L_T form n × L_T term n), (phi[t..]i) el L_prv A n ]
                ++ [ ∃f(ar) phi | (x, ar, phi) ∈ (L_nat n × L_nat n × L_T form n), (phi[(var_func x ar)..]f) el L_prv A n ]
                ++ [ ∃f(ar_syms f) phi | (f, phi) ∈ (L_T n × L_T form n), (phi[(sym f)..]f) el L_prv A n ]
                ++ [ ∃p(ar) phi | (x, ar, phi) ∈ (L_nat n × L_nat n × L_T form n), (phi[(var_pred x ar)..]p) el L_prv A n ]
                ++ [ ∃p(ar_preds P) phi | (P, phi) ∈ (L_T n × L_T form n), (phi[(pred P)..]p) el L_prv A n ]
                ++ [ psi | (phi, psi) ∈ (L_T form n × L_T form n), (∃i phi) el L_prv A n /\ psi[↑]i el L_prv (phi::(map (subst_form_i ↑) A)) n ]
                ++ [ psi | (phi, psi, ar) ∈ (L_T form n × L_T form n × L_nat n), (∃f(ar) phi) el L_prv A n /\ psi[↑ ar]f el L_prv (phi::(map (subst_form_f (↑ ar)) A)) n ]
                ++ [ psi | (phi, psi, ar) ∈ (L_T form n × L_T form n × L_nat n), (∃p(ar) phi) el L_prv A n /\ psi[↑ ar]p el L_prv (phi::(map (subst_form_p (↑ ar)) A)) n ]
                ++ [ ∃p(ar) (forall_n ar (p$0 (tabulate ar var_indi) <--> phi[↑ ar]p)) | (ar, phi) ∈ (L_nat n × L_T form n), funcfree phi ]
  end.


  Lemma enum_prv {p : peirce} A :
    list_enumerator (L_prv A) (prv A).
  Proof with eapply cum_ge'; eauto; lia.
    split.
    - rename x into phi. induction 1.
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (S (m1 + m2)); cbn.
        in_app 2. eapply in_concat_iff. eexists. split. 2:in_collect phi... in_collect psi...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T psi) as [m3]. exists (S (m1 + m2 + m3)); cbn.
        in_app 3. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. exists (S (m1 + m2)); cbn. 
        in_app 4. in_collect phi...
      + now exists 0.
      + destruct IHprv1 as [m1], IHprv2 as [m2]. exists (S (m1 + m2)); cbn.
        in_app 5. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3]. exists (S (m1 + m2 + m3)); cbn.
        in_app 6. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3]. exists (S (m1 + m2 + m3)); cbn.
        in_app 7. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3]. exists (S (m1 + m2 + m3)); cbn.
        in_app 8. in_collect (phi, psi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T psi) as [m3]. exists (S (m1 + m2 + m3)); cbn.
        in_app 9. in_collect (phi, psi)...
      + destruct IHprv1 as [m1],  IHprv2 as [m2],  IHprv3 as [m3], (el_T phi) as [m4], (el_T psi) as [m5], (el_T theta) as [m6].
        exists (S (m1 + m2 + m3 + m4 + m5 + m6)); cbn.
        in_app 10. in_collect (phi, psi, theta)...
      + destruct (el_T phi) as [m1], (el_T psi) as [m2]. exists (S (m1 + m2)); cbn.
        in_app 11. in_collect (phi, psi)...
      + destruct IHprv as [m]. exists (S m); cbn. in_app 12. in_collect phi...
      + destruct IHprv as [m]. exists (S (m + ar)); cbn.
        in_app 13. apply in_concat_iff. eexists. split.
        2: in_collect ar; apply L_nat_correct; lia. in_collect phi...
      + destruct IHprv as [m]. exists (S (m + ar)); cbn.
        in_app 14. apply in_concat_iff. eexists. split.
        2: in_collect ar; apply L_nat_correct; lia. in_collect phi...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T t) as [m3]. exists (S(m1 + m2 + m3)); cbn.
        in_app 15. in_collect (phi, t)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. destruct f.
        * exists (S (m1 + m2 + n + ar)); cbn. in_app 16. in_collect (n, ar, phi); try (apply L_nat_correct; lia)...
        * destruct (el_T f) as [m3]. exists (S (m1 + m2+ m3)); cbn. in_app 17. in_collect (f, phi)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. destruct P.
        * exists (S (m1 + m2 + n + ar)); cbn. in_app 18. in_collect (n, ar, phi); try (apply L_nat_correct; lia)...
        * destruct (el_T P) as [m3]. exists (S (m1 + m2+ m3)); cbn. in_app 19. in_collect (P, phi)...
      + destruct IHprv as [m1], (el_T phi) as [m2], (el_T t) as [m3]. exists (S (m1 + m2 + m3)); cbn.
        in_app 20. in_collect (phi, t)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. destruct f.
        * exists (S (m1 + m2 + n + ar)); cbn. in_app 21. in_collect (n, ar, phi); try (apply L_nat_correct; lia)...
        * destruct (el_T f) as [m3]. exists (S (m1 + m2 + m3)); cbn. in_app 22. in_collect (f, phi)...
      + destruct IHprv as [m1], (el_T phi) as [m2]. destruct P.
        * exists (S (m1 + m2 + n + ar)); cbn. in_app 23. in_collect (n, ar, phi); try (apply L_nat_correct; lia)...
        * destruct (el_T P) as [m3]. exists (S (m1 + m2 + m3)); cbn. in_app 24. in_collect (P, phi)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T phi) as [m3], (el_T psi) as [m4]. exists (S (m1 + m2 + m3 + m4)); cbn.
        in_app 25. in_collect (phi, psi)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T phi) as [m3], (el_T psi) as [m4]. exists (S (m1 + m2 + m3 + m4 + ar)); cbn.
        in_app 26. in_collect (phi, psi, ar); try (apply L_nat_correct; lia)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (el_T phi) as [m3], (el_T psi) as [m4]. exists (S (m1 + m2 + m3 + m4 + ar)); cbn.
        in_app 27. in_collect (phi, psi, ar); try (apply L_nat_correct; lia)...
      + destruct (el_T phi) as [m]. exists (S (m + ar)); cbn.
        in_app 28. in_collect (ar, phi); try (apply L_nat_correct; lia)...
    - intros [m]; induction m in A, x, H |-*; cbn in *.
      + now apply Ctx.
      + inv_collect.
        * eapply II; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply Exp; apply IHm; eauto.
        * eapply CI; apply IHm; eauto.
        * eapply CE1; apply IHm; eauto.
        * eapply CE2; apply IHm; eauto.
        * eapply DI1; apply IHm; eauto.
        * eapply DI2; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * destruct p; cbn. inv_collect. apply Peirce. easy.
        * eapply AllI_i; apply IHm; eauto.
        * eapply AllI_f; apply IHm; eauto.
        * eapply AllI_p; apply IHm; eauto.
        * eapply AllE_i; apply IHm; eauto.
        * eapply AllE_f; apply IHm; eauto.
        * eapply AllE_f; apply IHm; eauto.
        * eapply AllE_p; apply IHm; eauto.
        * eapply AllE_p; apply IHm; eauto.
        * eapply ExI_i; apply IHm; eauto.
        * eapply ExI_f; apply IHm; eauto.
        * eapply ExI_f; apply IHm; eauto.
        * eapply ExI_p; apply IHm; eauto.
        * eapply ExI_p; apply IHm; eauto.
        * eapply ExE_i; apply IHm; eauto.
        * eapply ExE_f; apply IHm; eauto.
        * eapply ExE_p; apply IHm; eauto.
        * now eapply Comp.
  Qed.


  Lemma prv_enumerable {p : peirce} A :
    enumerable (fun phi => A ⊢ phi).
  Proof.
    apply list_enumerable_enumerable. exists (L_prv A). apply enum_prv.
  Qed.

End Enumerability.


(** ** Deduction Facts *)

Section Facts.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {p : peirce}.


  (** Weakening *)

  Theorem Weak A B phi :
    A <<= B -> A ⊢ phi -> B ⊢ phi.
  Proof.
    intros H1 H. revert B H1. induction H; intros B HB; 
    try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.

  Lemma subst_Weak_i sigma A phi :
    (forall x, funcfreeTerm (sigma x)) -> A ⊢ phi -> List.map (subst_form_i sigma) A ⊢ phi[sigma]i.
  Proof.
    intros Hsigma H. revert sigma Hsigma. induction H; intros sigma Hsigma; cbn in *.
    - now apply II, IHprv.
    - eapply IE. now apply IHprv1. now apply IHprv2.
    - now apply Exp, IHprv.
    - apply Ctx, List.in_map, H.
    - apply CI. now apply IHprv1. now apply IHprv2.
    - now eapply CE1, IHprv.
    - now eapply CE2, IHprv.
    - now eapply DI1, IHprv.
    - now eapply DI2, IHprv.
    - eapply DE. now apply IHprv1. now apply IHprv2. now apply IHprv3.
    - apply Peirce.
    - apply AllI_i. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros []; cbn. easy. now apply funcfreeTerm_subst_i. intros ?. now setoid_rewrite up_form_i.
    - apply AllI_f. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros x. now apply funcfreeTerm_subst_f. intros ?. apply subst_switch_i_f.
    - apply AllI_p. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. easy. intros ?. apply subst_switch_i_p.
    - specialize (IHprv sigma). apply AllE_i with (t0 := t[sigma]i) in IHprv; trivial.
      rewrite subst_comp_i in *. erewrite subst_ext_i. apply IHprv. intros []; cbn; trivial.
      now setoid_rewrite subst_term_shift_i.
    - specialize (IHprv sigma). apply AllE_f with (f0 := f) in IHprv; trivial.
      rewrite subst_switch_i_f in IHprv. erewrite subst_ext_i. apply IHprv. intros n. 
      now setoid_rewrite subst_term_shift_f.
    - specialize (IHprv sigma). apply AllE_p with (P0 := P) in IHprv; trivial.
      rewrite subst_switch_i_p in IHprv. erewrite subst_ext_p. apply IHprv. reflexivity.
    - specialize (IHprv sigma). eapply ExI_i with (t0 := t[sigma]i). rewrite subst_comp_i in *.
      erewrite subst_ext_i. apply IHprv; trivial. intros [|]; cbn; trivial.
      now setoid_rewrite subst_term_shift_i.
    - specialize (IHprv sigma). eapply ExI_f with (f0 := f). rewrite subst_switch_i_f.
      erewrite subst_ext_i. apply IHprv; trivial. intros n. now setoid_rewrite subst_term_shift_f.
    - specialize (IHprv sigma). eapply ExI_p with (P0 := P). rewrite subst_switch_i_p.
      erewrite subst_ext_i. apply IHprv; trivial. reflexivity.
    - eapply ExE_i in IHprv1; trivial. eassumption. rewrite List.map_map. specialize (IHprv2 (up_i sigma)). 
      setoid_rewrite up_form_i in IHprv2. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros []; cbn. easy. now apply funcfreeTerm_subst_i. intros ?. apply up_form_i.
    - eapply ExE_f in IHprv1; trivial. eassumption. rewrite List.map_map. specialize (IHprv2 (sigma >> subst_f (↑ ar))). 
      rewrite subst_switch_i_f. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros x. now apply funcfreeTerm_subst_f. intros ?. now setoid_rewrite subst_switch_i_f.
    - eapply ExE_p in IHprv1; trivial. eassumption. rewrite List.map_map. specialize (IHprv2 sigma). 
      rewrite subst_switch_i_p. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. easy. intros ?. now setoid_rewrite subst_switch_i_p.
    - rewrite comprehension_subst_i. apply Comp. apply funcfree_subst_i; trivial.
      induction ar; intros x; cbn. easy. destruct x; cbn. easy. now apply funcfreeTerm_subst_i.
  Qed.

  Lemma subst_Weak_f sigma A phi  :
    A ⊢ phi -> List.map (subst_form_f sigma) A ⊢ phi[sigma]f.
  Proof.
    induction 1 in sigma |- *; cbn in *.
    - apply II, IHprv.
    - eapply IE. apply IHprv1. apply IHprv2.
    - apply Exp, IHprv.
    - apply Ctx, List.in_map, H.
    - apply CI. apply IHprv1. apply IHprv2.
    - eapply CE1, IHprv.
    - eapply CE2, IHprv.
    - eapply DI1, IHprv.
    - eapply DI2, IHprv.
    - eapply DE. apply IHprv1. apply IHprv2. apply IHprv3.
    - apply Peirce.
    - apply AllI_i. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros ?. symmetry. now setoid_rewrite subst_switch_i_f.
    - apply AllI_f. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros ?. now setoid_rewrite up_form_f.
    - apply AllI_p. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros ?. apply subst_switch_f_p.
    - specialize (IHprv sigma). apply AllE_i with (t0 := t[sigma]f) in IHprv.
      rewrite subst_switch_i_f. erewrite subst_ext_i. apply IHprv. now intros [].
    - specialize (IHprv sigma). apply AllE_f with (f0 := f[sigma]f) in IHprv.
      rewrite subst_comp_f in *. erewrite subst_ext_f. apply IHprv. intros [] ar'; cbn;
      repeat (try rewrite nat_eq_dec_same; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn);
      now setoid_rewrite subst_function_shift_f.
    - specialize (IHprv sigma). apply AllE_p with (P0 := P) in IHprv.
      rewrite subst_switch_f_p in IHprv. erewrite subst_ext_p. apply IHprv. reflexivity.
    - specialize (IHprv sigma). eapply ExI_i with (t0 := t[sigma]f). rewrite subst_switch_i_f in IHprv.
      erewrite subst_ext_i. apply IHprv. intros [|]; cbn; trivial.
    - specialize (IHprv sigma). eapply ExI_f with (f0 := f[sigma]f). rewrite subst_comp_f in *.
      erewrite subst_ext_f. apply IHprv. intros [] ar'; cbn;
      repeat (try rewrite nat_eq_dec_same; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn);
      now setoid_rewrite subst_function_shift_f.
    - specialize (IHprv sigma). eapply ExI_p with (P0 := P). rewrite subst_switch_f_p.
      erewrite subst_ext_f. apply IHprv. reflexivity.
    - eapply ExE_i in IHprv1. eassumption. rewrite List.map_map. specialize (IHprv2 sigma). 
      rewrite subst_switch_i_f in IHprv2. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros ?. now setoid_rewrite subst_switch_i_f.
    - eapply ExE_f in IHprv1. eassumption. rewrite List.map_map. specialize (IHprv2 (up_f sigma ar)). 
      setoid_rewrite up_form_f in IHprv2. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros ?. apply up_form_f.
    - eapply ExE_p in IHprv1. eassumption. rewrite List.map_map. specialize (IHprv2 sigma). 
      rewrite subst_switch_f_p. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros ?. now setoid_rewrite subst_switch_f_p.
    - rewrite comprehension_subst_f. now apply Comp, funcfree_subst_f.
  Qed.

  Lemma subst_Weak_p sigma A phi :
    A ⊢ phi -> List.map (subst_form_p sigma) A ⊢ phi[sigma]p.
  Proof.
    induction 1 in sigma |- *; cbn in *.
    - apply II, IHprv.
    - eapply IE. apply IHprv1. apply IHprv2.
    - apply Exp, IHprv.
    - apply Ctx, List.in_map, H.
    - apply CI. apply IHprv1. apply IHprv2.
    - eapply CE1, IHprv.
    - eapply CE2, IHprv.
    - eapply DI1, IHprv.
    - eapply DI2, IHprv.
    - eapply DE. apply IHprv1. apply IHprv2. apply IHprv3.
    - apply Peirce.
    - apply AllI_i. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros ?. symmetry. apply subst_switch_i_p.
    - apply AllI_f. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros ?. symmetry. apply subst_switch_f_p.
    - apply AllI_p. setoid_rewrite List.map_map in IHprv. erewrite List.map_map, List.map_ext.
      apply IHprv. intros ?. now setoid_rewrite up_form_p. 
    - specialize (IHprv sigma). apply AllE_i with (t0 := t) in IHprv.
      rewrite subst_switch_i_p. erewrite subst_ext_i. apply IHprv. now intros [].
    - specialize (IHprv sigma). apply AllE_f with (f0 := f) in IHprv.
      rewrite <- subst_switch_f_p in IHprv. erewrite subst_ext_p. apply IHprv. reflexivity.
    - specialize (IHprv sigma). apply AllE_p with (P0 := P[sigma]p) in IHprv.
      rewrite subst_comp_p in *. erewrite subst_ext_p. apply IHprv. intros [] ar'; cbn;
      repeat (try rewrite nat_eq_dec_same; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn);
      now setoid_rewrite subst_predicate_shift_p.
    - specialize (IHprv sigma). eapply ExI_i with (t0 := t). rewrite subst_switch_i_p in IHprv.
      erewrite subst_ext_i. apply IHprv. intros [|]; cbn; trivial.
    - specialize (IHprv sigma). eapply ExI_f with (f0 := f). rewrite <- subst_switch_f_p.
      erewrite subst_ext_f. apply IHprv. reflexivity.
    - specialize (IHprv sigma). eapply ExI_p with (P0 := P[sigma]p). rewrite subst_comp_p in *.
      erewrite subst_ext_p. apply IHprv. intros [] ar'; cbn;
      repeat (try rewrite nat_eq_dec_same; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn);
      now setoid_rewrite subst_predicate_shift_p.
    - eapply ExE_i in IHprv1. eassumption. rewrite List.map_map. specialize (IHprv2 sigma). 
      rewrite subst_switch_i_p in IHprv2. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros ?. now setoid_rewrite subst_switch_i_p.
    - eapply ExE_f in IHprv1. eassumption. rewrite List.map_map. specialize (IHprv2 sigma). 
      rewrite <- subst_switch_f_p. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros ?. now setoid_rewrite subst_switch_f_p.
    - eapply ExE_p in IHprv1. eassumption. rewrite List.map_map. specialize (IHprv2 (up_p sigma ar)). 
      setoid_rewrite up_form_p in IHprv2. erewrite List.map_map, List.map_ext in IHprv2. 
      apply IHprv2. intros ?. apply up_form_p.
    - rewrite comprehension_subst_p. now apply Comp, funcfree_subst_p.
  Qed.


  (** Nameless quantifier rules *)

  Definition cycle_shift_i n : nat -> term := 
    fun x => if PeanoNat.Nat.eq_dec n x then i$0 else i$(S x).

  Definition cycle_shift_f n ar : nat -> forall ar, function ar :=
    fun x ar' => if PeanoNat.Nat.eq_dec ar' ar 
                 then if PeanoNat.Nat.eq_dec n x then var_func 0 else var_func (S x)
                 else var_func x.

  Definition cycle_shift_p n ar : nat -> forall ar, predicate ar :=
    fun x ar' => if PeanoNat.Nat.eq_dec ar' ar 
                 then if PeanoNat.Nat.eq_dec n x then var_pred 0 else var_pred (S x)
                 else var_pred x.

  Lemma cycle_shift_shift_i n phi :
    bounded_indi n phi -> phi[cycle_shift_i n]i = phi[↑]i.
  Proof.
    intros B. eapply subst_ext_bounded_i. apply B. intros k. unfold cycle_shift_i. 
    destruct PeanoNat.Nat.eq_dec; trivial; lia.
  Qed.

  Lemma cycle_shift_shift_f n ar phi :
    bounded_func ar n phi -> phi[cycle_shift_f n ar]f = phi[↑ ar]f.
  Proof.
    intros B. eapply subst_ext_bounded_f. apply B. intros k ar'. unfold cycle_shift_f, shift, shift_f. 
    repeat destruct PeanoNat.Nat.eq_dec; trivial; lia.
  Qed.

  Lemma cycle_shift_shift_p n ar phi :
    bounded_pred ar n phi -> phi[cycle_shift_p n ar]p = phi[↑ ar]p.
  Proof.
    intros B. eapply subst_ext_bounded_p. apply B. intros k ar'. unfold cycle_shift_p, shift, shift_p. 
    repeat destruct PeanoNat.Nat.eq_dec; trivial; lia.
  Qed.

  Lemma cycle_shift_subject_i n phi :
    bounded_indi (S n) phi -> phi[(i$n)..]i[cycle_shift_i n]i = phi.
  Proof.
    intros B. erewrite subst_comp_i, subst_ext_bounded_i, subst_id_i; trivial.
    apply B. intros []; cbn; unfold cycle_shift_i; destruct PeanoNat.Nat.eq_dec; trivial; lia.
  Qed.

  Lemma cycle_shift_subject_f n ar phi :
    bounded_func ar (S n) phi -> phi[(var_func n ar)..]f[cycle_shift_f n ar]f = phi.
  Proof.
    intros B. erewrite subst_comp_f, subst_ext_bounded_f, subst_id_f; trivial.
    apply B. intros [] ar'; cbn; unfold cycle_shift_f; 
    repeat (destruct PeanoNat.Nat.eq_dec as [->|]; cbn; try rewrite !nat_eq_dec_same; cbn); trivial; lia.
  Qed.

  Lemma cycle_shift_subject_p n ar phi :
    bounded_pred ar (S n) phi -> phi[(var_pred n ar)..]p[cycle_shift_p n ar]p = phi.
  Proof.
    intros B. erewrite subst_comp_p, subst_ext_bounded_p, subst_id_p; trivial.
    apply B. intros [] ar'; cbn; unfold cycle_shift_p; 
    repeat (destruct PeanoNat.Nat.eq_dec as [->|]; cbn; try rewrite !nat_eq_dec_same; cbn); trivial; lia.
  Qed.

  Lemma nameless_equiv_all_i' A phi n :
    bounded_indi_L n A -> bounded_indi (S n) phi -> [p[↑]i | p ∈ A] ⊢ phi <-> A ⊢ phi[(i$n)..]i.
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak_i (i$n)..) in H. rewrite map_map in *.
      erewrite List.map_ext, map_id in H; try apply H. intros. apply subst_form_shift_i.
      now intros [].
    - apply (subst_Weak_i (cycle_shift_i n)) in H. rewrite (List.map_ext_in _ (subst_form_i ↑)) in H.
      + now rewrite cycle_shift_subject_i in H.
      + intros psi HP. now apply cycle_shift_shift_i, H1.
      + intros x. unfold cycle_shift_i. now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma nameless_equiv_all_f' A phi n ar :
    bounded_func_L ar n A -> bounded_func ar (S n) phi -> [p[↑ ar]f | p ∈ A] ⊢ phi <-> A ⊢ phi[(var_func n ar)..]f.
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak_f (var_func n ar)..) in H. rewrite map_map in *.
      erewrite List.map_ext, map_id in H; try apply H. intros. apply subst_form_shift_f.
    - apply (subst_Weak_f (cycle_shift_f n ar)) in H. rewrite (List.map_ext_in _ (subst_form_f (↑ ar))) in H.
      + now rewrite cycle_shift_subject_f in H.
      + intros psi HP. now apply cycle_shift_shift_f, H1.
  Qed.

  Lemma nameless_equiv_all_p' A phi n ar :
    bounded_pred_L ar n A -> bounded_pred ar (S n) phi -> [p[↑ ar]p | p ∈ A] ⊢ phi <-> A ⊢ phi[(var_pred n ar)..]p.
  Proof.
    intros H1 H2. split; intros H.
    - apply (subst_Weak_p (var_pred n ar)..) in H. rewrite map_map in *.
      erewrite List.map_ext, map_id in H; try apply H. intros. apply subst_form_shift_p.
    - apply (subst_Weak_p (cycle_shift_p n ar)) in H. rewrite (List.map_ext_in _ (subst_form_p (↑ ar))) in H.
      + now rewrite cycle_shift_subject_p in H.
      + intros psi HP. now apply cycle_shift_shift_p, H1.
  Qed.

  Lemma nameless_equiv_ex_i' A phi psi n :
    bounded_indi_L n A -> bounded_indi n phi -> bounded_indi (S n) psi -> (psi::[p0[↑]i | p0 ∈ A]) ⊢ phi[↑]i <-> (psi[(i$n)..]i::A) ⊢ phi.
  Proof.
    intros HL Hphi Hpsi. split.
    - intros H % (subst_Weak_i ((i$n)..)). cbn in *.
      erewrite map_map, List.map_ext, map_id in H.
      + now rewrite subst_form_shift_i in H.
      + intros. apply subst_form_shift_i.
      + now intros [].
    - intros H % (subst_Weak_i (cycle_shift_i n)). cbn in *.
      rewrite (List.map_ext_in _ (subst_form_i ↑)) in H.
      + setoid_rewrite cycle_shift_subject_i in H. now rewrite cycle_shift_shift_i in H. easy.
      + intros theta HT. now apply cycle_shift_shift_i, HL.
      + intros x. unfold cycle_shift_i. now destruct PeanoNat.Nat.eq_dec.
  Qed.

  Lemma nameless_equiv_ex_f' A phi psi n ar :
    bounded_func_L ar n A -> bounded_func ar n phi -> bounded_func ar (S n) psi -> (psi::[p0[↑ ar]f | p0 ∈ A]) ⊢ phi[↑ ar]f <-> (psi[(var_func n ar)..]f::A) ⊢ phi.
  Proof.
    intros HL Hphi Hpsi. split.
    - intros H % (subst_Weak_f ((var_func n ar)..)). cbn in *.
      erewrite map_map, List.map_ext, map_id in H.
      + now rewrite subst_form_shift_f in H.
      + intros. apply subst_form_shift_f.
    - intros H % (subst_Weak_f (cycle_shift_f n ar)). cbn in *.
      rewrite (List.map_ext_in _ (subst_form_f (↑ ar))) in H.
      + setoid_rewrite cycle_shift_subject_f in H. now rewrite cycle_shift_shift_f in H. easy.
      + intros theta HT. now apply cycle_shift_shift_f, HL.
  Qed.

  Lemma nameless_equiv_ex_p' A phi psi n ar :
    bounded_pred_L ar n A -> bounded_pred ar n phi -> bounded_pred ar (S n) psi -> (psi::[p0[↑ ar]p | p0 ∈ A]) ⊢ phi[↑ ar]p <-> (psi[(var_pred n ar)..]p::A) ⊢ phi.
  Proof.
    intros HL Hphi Hpsi. split.
    - intros H % (subst_Weak_p ((var_pred n ar)..)). cbn in *.
      erewrite map_map, List.map_ext, map_id in H.
      + now rewrite subst_form_shift_p in H.
      + intros. apply subst_form_shift_p.
    - intros H % (subst_Weak_p (cycle_shift_p n ar)). cbn in *.
      rewrite (List.map_ext_in _ (subst_form_p (↑ ar))) in H.
      + setoid_rewrite cycle_shift_subject_p in H. now rewrite cycle_shift_shift_p in H. easy.
      + intros theta HT. now apply cycle_shift_shift_p, HL.
  Qed.

  Lemma nameless_equiv_all_i A phi :
    { t | map (subst_form_i ↑) A ⊢ phi <-> A ⊢ phi[t..]i }.
  Proof.
    destruct (find_bounded_indi_L (phi::A)) as [n H].
    exists i$n. apply nameless_equiv_all_i'.
    - intros ? ?. apply H. auto.
    - eapply bounded_indi_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_ex_i A phi psi :
    { t | (phi :: List.map (subst_form_i ↑) A) ⊢ psi[↑]i <-> (phi[t..]i::A) ⊢ psi }.
  Proof.
    destruct (find_bounded_indi_L (phi::psi::A)) as [n H].
    exists i$n. apply nameless_equiv_ex_i'.
    - intros ? ?. apply H. auto.
    - apply H. auto.
    - eapply bounded_indi_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_all_f A phi ar :
    { x | map (subst_form_f (↑ ar)) A ⊢ phi <-> A ⊢ phi[(var_func x ar)..]f }.
  Proof.
    destruct (find_bounded_func_L ar (phi::A)) as [n H].
    exists n. apply nameless_equiv_all_f'.
    - intros ? ?. apply H. auto.
    - eapply bounded_func_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_ex_f A phi psi ar :
    { x | (phi :: List.map (subst_form_f (↑ ar)) A) ⊢ psi[↑ ar]f <-> (phi[(var_func x ar)..]f::A) ⊢ psi }.
  Proof.
    destruct (find_bounded_func_L ar (phi::psi::A)) as [n H].
    exists n. apply nameless_equiv_ex_f'.
    - intros ? ?. apply H. auto.
    - apply H. auto.
    - eapply bounded_func_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_all_p A phi ar :
    { x | map (subst_form_p (↑ ar)) A ⊢ phi <-> A ⊢ phi[(var_pred x ar)..]p }.
  Proof.
    destruct (find_bounded_pred_L ar (phi::A)) as [n H].
    exists n. apply nameless_equiv_all_p'.
    - intros ? ?. apply H. auto.
    - eapply bounded_pred_up; try apply H; auto.
  Qed.

  Lemma nameless_equiv_ex_p A phi psi ar :
    { x | (phi :: List.map (subst_form_p (↑ ar)) A) ⊢ psi[↑ ar]p <-> (phi[(@var_pred _ x ar)..]p::A) ⊢ psi }.
  Proof.
    destruct (find_bounded_pred_L ar (phi::psi::A)) as [n H].
    exists n. apply nameless_equiv_ex_p'.
    - intros ? ?. apply H. auto.
    - apply H. auto.
    - eapply bounded_pred_up; try apply H; auto.
  Qed.



  (** Helper lemmas for proving equivalences *)

  Lemma switch_imp A phi psi :
    (phi::A ⊢ psi) <-> (A ⊢ phi --> psi).
  Proof.
    split; intros H. now apply II. eapply IE. eapply Weak. 2: apply H. firstorder. now apply Ctx.
  Qed.

  Lemma prv_equiv_bin op phi1 phi2 psi1 psi2 A :
    A ⊢ phi1 <--> psi1 -> A ⊢ phi2 <--> psi2 -> A ⊢ (bin op phi1 phi2) <--> (bin op psi1 psi2).
  Proof.
    intros H1 H2. destruct op; cbn.
    - apply CI.
      + apply II. apply CI.
        * eapply IE. eapply CE1. eapply Weak. 2: apply H1; firstorder. firstorder. eapply CE1. now apply Ctx.
        * eapply IE. eapply CE1. eapply Weak. 2: apply H2; firstorder. firstorder. eapply CE2. now apply Ctx.
      + apply II. apply CI.
        * eapply IE. eapply CE2. eapply Weak. 2: apply H1; firstorder. firstorder. eapply CE1. now apply Ctx.
        * eapply IE. eapply CE2. eapply Weak. 2: apply H2; firstorder. firstorder. eapply CE2. now apply Ctx.
    - apply CI. 
      + apply II. eapply DE. now apply Ctx.
        * apply DI1. eapply IE. eapply CE1. eapply Weak. 2: apply H1; firstorder. firstorder. now apply Ctx.
        * apply DI2. eapply IE. eapply CE1. eapply Weak. 2: apply H2; firstorder. firstorder. now apply Ctx.
      + apply II. eapply DE. now apply Ctx.
        * apply DI1. eapply IE. eapply CE2. eapply Weak. 2: apply H1; firstorder. firstorder. now apply Ctx.
        * apply DI2. eapply IE. eapply CE2. eapply Weak. 2: apply H2; firstorder. firstorder. now apply Ctx.
    - apply CI. 
      + apply II, II. eapply IE. eapply CE1. eapply Weak. 2: apply H2; firstorder. firstorder. eapply IE. 
        apply Ctx. right. now left. eapply IE. eapply CE2. eapply Weak. 2: apply H1; firstorder. firstorder. now apply Ctx.
      + apply II, II. eapply IE. eapply CE2. eapply Weak. 2: apply H2; firstorder. firstorder. eapply IE. 
        apply Ctx. right. now left. eapply IE. eapply CE1. eapply Weak. 2: apply H1; firstorder. firstorder. now apply Ctx.
  Qed.

  Lemma prv_equiv_quant_i op phi psi A :
    List.map (subst_form_i ↑) A ⊢ phi <--> psi -> A ⊢ (quant_indi op phi) <--> (quant_indi op psi).
  Proof.
    intros H. enough (A ⊢ (phi <--> psi)[(var_indi (proj1_sig (find_bounded_indi_L (phi::psi::A))))..]i) as X.
    - destruct find_bounded_indi_L as [b Hb]; cbn in *. destruct op.
      + apply CI.
        * apply II. apply AllI_i. eapply nameless_equiv_all_i'; revgoals.
          -- eapply IE. eapply CE1. eapply Weak. 2: apply X. firstorder. now apply AllE_i, Ctx.
          -- apply bounded_indi_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. apply bounded_indi_up with (n:=b). lia. all: apply Hb; firstorder.
        * apply II. apply AllI_i. eapply nameless_equiv_all_i'; revgoals.
          -- eapply IE. eapply CE2. eapply Weak. 2: apply X. firstorder. now apply AllE_i, Ctx.
          -- apply bounded_indi_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. apply bounded_indi_up with (n:=b). lia. all: apply Hb; firstorder.
      + apply CI.
        * apply II. eapply ExE_i. now apply Ctx. eapply nameless_equiv_ex_i'; revgoals.
          -- eapply ExI_i. eapply IE. eapply CE1. eapply Weak. 2: apply X. firstorder. now apply Ctx.
          -- apply bounded_indi_up with (n:=b). lia. apply Hb. firstorder.
          -- cbn. apply bounded_indi_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. apply bounded_indi_up with (n:=b). lia. all: apply Hb; firstorder.
        * apply II. eapply ExE_i. now apply Ctx. eapply nameless_equiv_ex_i'; revgoals.
          -- eapply ExI_i. eapply IE. eapply CE2. eapply Weak. 2: apply X. firstorder. now apply Ctx.
          -- apply bounded_indi_up with (n:=b). lia. apply Hb. firstorder.
          -- cbn. apply bounded_indi_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. apply bounded_indi_up with (n:=b). lia. all: apply Hb; firstorder.
    - eapply subst_Weak_i in H. erewrite List.map_map, List.map_ext in H. 
      2: intros; apply subst_form_shift_i. rewrite List.map_id in H. apply H. now intros [].
  Qed.

  Lemma prv_equiv_quant_f op phi psi A ar :
    List.map (subst_form_f (↑ ar)) A ⊢ phi <--> psi -> A ⊢ (quant_func op ar phi) <--> (quant_func op ar psi).
  Proof.
    intros H. enough (A ⊢ (phi <--> psi)[(@var_func _ (proj1_sig (find_bounded_func_L ar (phi::psi::A))) ar)..]f) as X.
    - destruct find_bounded_func_L as [b Hb]; cbn in *. destruct op.
      + apply CI.
        * apply II. apply AllI_f. eapply nameless_equiv_all_f'; revgoals.
          -- eapply IE. eapply CE1. eapply Weak. 2: apply X. firstorder. now apply AllE_f, Ctx.
          -- apply bounded_func_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_func_up with (n:=b). lia. all: apply Hb; firstorder.
        * apply II. apply AllI_f. eapply nameless_equiv_all_f'; revgoals.
          -- eapply IE. eapply CE2. eapply Weak. 2: apply X. firstorder. now apply AllE_f, Ctx.
          -- apply bounded_func_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_func_up with (n:=b). lia. all: apply Hb; firstorder.
      + apply CI.
        * apply II. eapply ExE_f. now apply Ctx. eapply nameless_equiv_ex_f'; revgoals.
          -- eapply ExI_f. eapply IE. eapply CE1. eapply Weak. 2: apply X. firstorder. now apply Ctx.
          -- apply bounded_func_up with (n:=b). lia. apply Hb. firstorder.
          -- cbn. left. split. reflexivity. apply bounded_func_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_func_up with (n:=b). lia. all: apply Hb; firstorder.
        * apply II. eapply ExE_f. now apply Ctx. eapply nameless_equiv_ex_f'; revgoals.
          -- eapply ExI_f. eapply IE. eapply CE2. eapply Weak. 2: apply X. firstorder. now apply Ctx.
          -- apply bounded_func_up with (n:=b). lia. apply Hb. firstorder.
          -- cbn. left. split. reflexivity. apply bounded_func_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_func_up with (n:=b). lia. all: apply Hb; firstorder. 
    - eapply subst_Weak_f in H. erewrite List.map_map, List.map_ext in H. 
      2: intros; apply subst_form_shift_f. rewrite List.map_id in H. apply H.
  Qed.

  Lemma prv_equiv_quant_p op phi psi A ar :
    List.map (subst_form_p (↑ ar)) A ⊢ phi <--> psi -> A ⊢ (quant_pred op ar phi) <--> (quant_pred op ar psi).
  Proof.
    intros H. enough (A ⊢ (phi <--> psi)[(@var_pred _ (proj1_sig (find_bounded_pred_L ar (phi::psi::A))) ar)..]p) as X.
    - destruct find_bounded_pred_L as [b Hb]; cbn in *. destruct op.
      + apply CI.
        * apply II. apply AllI_p. eapply nameless_equiv_all_p'; revgoals.
          -- eapply IE. eapply CE1. eapply Weak. 2: apply X. firstorder. now apply AllE_p, Ctx.
          -- apply bounded_pred_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_pred_up with (n:=b). lia. all: apply Hb; firstorder.
        * apply II. apply AllI_p. eapply nameless_equiv_all_p'; revgoals.
          -- eapply IE. eapply CE2. eapply Weak. 2: apply X. firstorder. now apply AllE_p, Ctx.
          -- apply bounded_pred_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_pred_up with (n:=b). lia. all: apply Hb; firstorder.
      + apply CI.
        * apply II. eapply ExE_p. now apply Ctx. eapply nameless_equiv_ex_p'; revgoals.
          -- eapply ExI_p. eapply IE. eapply CE1. eapply Weak. 2: apply X. firstorder. now apply Ctx.
          -- apply bounded_pred_up with (n:=b). lia. apply Hb. firstorder.
          -- cbn. left. split. reflexivity. apply bounded_pred_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_pred_up with (n:=b). lia. all: apply Hb; firstorder.
        * apply II. eapply ExE_p. now apply Ctx. eapply nameless_equiv_ex_p'; revgoals.
          -- eapply ExI_p. eapply IE. eapply CE2. eapply Weak. 2: apply X. firstorder. now apply Ctx.
          -- apply bounded_pred_up with (n:=b). lia. apply Hb. firstorder.
          -- cbn. left. split. reflexivity. apply bounded_pred_up with (n:=b). lia. apply Hb. firstorder.
          -- intros ? [<-|]. cbn. left. split. reflexivity. apply bounded_pred_up with (n:=b). lia. all: apply Hb; firstorder.
    - eapply subst_Weak_p in H. erewrite List.map_map, List.map_ext in H. 
      2: intros; apply subst_form_shift_p. rewrite List.map_id in H. apply H.
  Qed.

  Lemma prv_equiv_subst_p phi psi sigma :
    List.nil ⊢ phi <--> psi -> List.nil ⊢ phi[sigma]p <--> psi[sigma]p.
  Proof.
    intros H. change (List.map (subst_form_p sigma) List.nil ⊢ (phi <--> psi)[sigma]p). 
    apply subst_Weak_p, H.
  Qed.

  Lemma prv_equiv_symmetry A phi psi :
    A ⊢ phi <--> psi -> A ⊢ psi <--> phi.
  Proof.
    intros H. apply CI.
    - eapply II, IE. eapply CE2. eapply Weak. 2: apply H. firstorder. now apply Ctx.
    - eapply II, IE. eapply CE1. eapply Weak. 2: apply H. firstorder. now apply Ctx.
  Qed.


  (** Provability of forall_n *)

  Lemma iter_up_i_le sigma n m :
    m < n -> iter up_i n sigma m = var_indi m.
  Proof.
    induction n in m |-*; cbn; intros H.
    - lia.
    - destruct m; cbn. reflexivity. rewrite IHn. reflexivity. lia.
  Qed.

  Lemma iter_up_i_ge sigma n m :
    m >= n -> iter up_i n sigma m = (sigma (m-n))[fun x => var_indi (n+x)]i.
  Proof.
    induction n in m |-*; cbn; intros H.
    - replace (m-0) with m by lia. destruct sigma; cbn. reflexivity. f_equal. 
      erewrite Vector.map_ext, Vector.map_id. reflexivity. intros t. now setoid_rewrite subst_term_id_i.
    - destruct m; cbn; try lia. rewrite IHn. destruct sigma; cbn. reflexivity. f_equal. rewrite Vector.map_map.
      apply Vector.map_ext. intros t. now rewrite subst_term_comp_i. lia.
  Qed.

  Lemma prv_forall_n A n phi (v : vec term n) :
    A ⊢ forall_n n phi -> A ⊢ phi[fun x => if Compare_dec.lt_dec x n then nth_error (n - S x) v (i$0) else var_indi (x-n)]i.
  Proof.
    revert phi. induction n; intros phi H; cbn in *.
    - erewrite subst_ext_i. rewrite <- subst_id_i in H. apply H. intros n. 
      replace (n-0) with n by lia. reflexivity.
    - eapply AllE_i with (t := Vector.hd v) in H. rewrite forall_n_subst_i in H. 
      apply IHn with (v := Vector.tl v) in H. rewrite subst_comp_i in H. erewrite subst_ext_i. apply H.
      intros n'. destruct (PeanoNat.Nat.eq_dec n' n) as [->|].
      + destruct Compare_dec.lt_dec; try lia. rewrite iter_up_i_ge; cbn. 2: lia. replace (n-n) with 0 by lia. cbn. 
        setoid_rewrite subst_term_comp_i. cbn. erewrite subst_term_ext_i, subst_term_id_i.
        now destruct n; depelim v. intros x; cbn. destruct Compare_dec.lt_dec; try lia.
        now replace (n+x-n) with x by lia.
      + destruct Compare_dec.lt_dec.
        * rewrite iter_up_i_le. 2: lia. cbn. destruct Compare_dec.lt_dec; try lia.
          replace (n - n') with (S (n - S n')) by lia. now depelim v.
        * rewrite iter_up_i_ge. 2: lia. destruct (n'-n) eqn:H4; try lia; cbn.
          destruct Compare_dec.lt_dec; try lia. f_equal. lia.
  Qed.

  Lemma tabulate_var_indi_subst ar (v : vec term ar) :
    Vector.map (subst_term_i (fun x => if Compare_dec.lt_dec x ar then nth_error (ar - S x) v (var_indi 0) else var_indi (x-ar))) (tabulate ar var_indi) = v.
  Proof.
    rewrite map_tabulate; cbn. erewrite tabulate_ext. apply tabulate_nth. intros x H.
    destruct Compare_dec.lt_dec; try lia. reflexivity.
  Qed.

End Facts.



(** ** Incompleteness *)

(** The deduction system is not complete for Traski semantics *)

Require Import Incompleteness PA.

Section Incompleteness.

  Theorem InfinitarilyIncompleteI :
    ~ forall T phi, decidable T -> validT T phi -> T ⊩i phi.
  Proof.
    intros complete. apply InfinitaryIncompleteness with (prv := @prv _ _ intu).
    - apply SoundnessIT.
    - apply complete.
  Qed.

  Theorem InfinitarilyIncompleteC :
    LEM -> ~ forall T phi, decidable T -> validT T phi -> T ⊩c phi.
  Proof.
    intros lem complete. apply InfinitaryIncompleteness with (prv := @prv _ _ class).
    - intros. now apply SoundnessCT.
    - apply complete.
  Qed.


  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {L_Funcs : nat -> list syms}.
  Hypothesis enum_Funcs' : list_enumerator__T L_Funcs syms.

  Context {L_Preds : nat -> list preds}.
  Hypothesis enum_Preds' : list_enumerator__T L_Preds preds.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.

  Theorem IncompleteI :
    (forall A phi, valid A phi -> A ⊢i phi) -> bi_enumerable H10.
  Proof.
    intros H. apply (Incompleteness (@prv _ _ intu)).
    - apply SoundnessI.
    - apply H.
    - eapply prv_enumerable. apply enum_Funcs'. apply enum_Preds'. 
      apply eq_dec_Funcs. apply eq_dec_Preds.
    - apply eq_dec_Funcs.
    - apply eq_dec_Preds.
  Qed.

  Corollary IncompleteI' :
    MP -> (forall A phi, valid A phi -> A ⊢i phi) -> decidable H10.
  Proof.
    intros mp H. apply Post. easy. apply polynomial_pair_enumerable.
    all: now apply IncompleteI.
  Qed.

  Theorem IncompleteC :
    LEM -> (forall A phi, valid A phi -> A ⊢c phi) -> bi_enumerable H10.
  Proof.
    intros lem H. apply (Incompleteness (@prv _ _ class)).
    - intros. now apply SoundnessC.
    - apply H.
    - eapply prv_enumerable. apply enum_Funcs'. apply enum_Preds'. 
      apply eq_dec_Funcs. apply eq_dec_Preds.
    - apply eq_dec_Funcs.
    - apply eq_dec_Preds.
  Qed.

  Corollary IncompleteC' :
    LEM -> (forall A phi, valid A phi -> A ⊢c phi) -> decidable H10.
  Proof.
    intros lem H. apply Post. intros f H1. specialize (lem (tsat f)). tauto. 
    apply polynomial_pair_enumerable. all: now apply IncompleteC.
  Qed.

End Incompleteness.



(** ** Henkin Soundness *)

Require Import Henkin.

Section Henkin.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma comprehension_form_subst_i ar phi sigma :
    (comprehension_form ar phi)[sigma]i = comprehension_form ar (phi[iter up_i ar sigma]i).
  Proof.
    unfold comprehension_form. cbn. rewrite forall_n_subst_i. cbn. erewrite <- subst_switch_i_p, map_tabulate, tabulate_ext.
    reflexivity. induction ar; intros m H; cbn. lia. destruct m; cbn. reflexivity.
    setoid_rewrite IHar. reflexivity. lia.
  Qed.

  Lemma funcfreeTerm_subst_i t sigma :
    (forall n, funcfreeTerm (sigma n)) -> funcfreeTerm t -> funcfreeTerm (t[sigma]i).
  Proof.
    intros H1 H2. induction t; cbn. apply H1. easy.
    eapply Forall_map, Forall_ext_Forall. apply IH. apply H2.
  Qed.

  Lemma funcfree_subst_i phi sigma :
    (forall n, funcfreeTerm (sigma n)) -> funcfree phi -> funcfree(phi[sigma]i).
  Proof.
    induction phi in sigma |-*; intros H F; firstorder.
    - apply Forall_map. apply Forall_in. intros t H1. apply funcfreeTerm_subst_i.
      apply H. eapply Forall_in in F. apply F. easy.
    - apply IHphi; trivial. intros []; cbn; trivial. specialize (H n).
      destruct sigma; cbn in *. easy. destruct f. easy. 
      apply Forall_map. apply Forall_in. intros t H1. apply funcfreeTerm_subst_i.
      now intros ?. eapply Forall_in in H. apply H. easy.
  Qed.


  Section Model.

    Variable D : Type.
    Context {I : interp D}.
    Variable funcIncluded : forall ar, (vec D ar -> D) -> Prop.
    Variable predIncluded : forall ar, (vec D ar -> Prop) -> Prop.

    Lemma forall_n_to_vec_Henkin rho n phi :
      Henkin.sat funcIncluded predIncluded rho (forall_n n phi) <-> forall v : vec D n, Henkin.sat funcIncluded predIncluded ⟨ VectorLib.fold_left scons (get_indi rho) v, get_func rho, get_pred rho ⟩ phi.
    Proof.
      enough (forall rho_i rho_f rho_p, Henkin.sat funcIncluded predIncluded ⟨rho_i, rho_f, rho_p⟩ (forall_n n phi) <-> forall v : vec D n, Henkin.sat funcIncluded predIncluded ⟨ VectorLib.fold_left scons rho_i v, rho_f, rho_p ⟩ phi) by now destruct rho.
      intros. clear rho. revert rho_i. induction n; intros rho_i; cbn.
      - split.
        + intros H v. now dependent elimination v.
        + intros H. apply (H (Vector.nil _)).
      - split.
        + intros H v. dependent elimination v. cbn. apply IHn, H.
        + intros H d. apply IHn. intros v. apply (H (Vector.cons _ d _ v)).
    Qed.

    Lemma comprehension_form_correct ar phi rho :
      Henkin.sat funcIncluded predIncluded rho (comprehension_form ar phi) <-> exists P, predIncluded ar P /\ forall v, P v <-> Henkin.sat funcIncluded predIncluded ⟨ VectorLib.fold_left scons (get_indi rho) v, get_func rho, get_pred rho ⟩ phi.
    Proof.
      split; cbn.
      - intros [P [H1 H2]]. exists P. split. exact H1. intros v.
        apply forall_n_to_vec_Henkin with (v := v) in H2. cbn in H2. 
        rewrite nat_eq_dec_same, eval_tabulate in H2. setoid_rewrite sat_comp_p in H2.
        cbn in H2. erewrite sat_ext in H2. apply H2. split. reflexivity. intros ar' v'.
        split. reflexivity. cbn. unfold shift, shift_p. destruct PeanoNat.Nat.eq_dec as [->|]; cbn. 
        now rewrite nat_eq_dec_same. now destruct n; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
      - intros [P [H1 H2]]. exists P. split. exact H1. apply forall_n_to_vec_Henkin. 
        intros v. cbn. erewrite nat_eq_dec_same, eval_tabulate, sat_comp_p, sat_ext. 
        apply H2. cbn. split. reflexivity. intros ar' v'. split. reflexivity.
        cbn. unfold shift, shift_p. destruct PeanoNat.Nat.eq_dec as [->|]; cbn. 
        now rewrite nat_eq_dec_same. now destruct n; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
    Qed.

  End Model.


  Lemma HenkinSoundnessI A phi :
    A ⊢i phi -> Henkin.valid A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I funcs preds HI HCompr rho Hrho HA.
    - intros H1. apply IHprv; trivial. intros phi' [->|]; firstorder.
    - apply IHprv1; trivial. apply IHprv2; trivial.
    - exfalso. eapply IHprv; try easy. apply HI. apply HCompr.
    - firstorder.
    - split. now apply IHprv1. now apply IHprv2.
    - now apply IHprv.
    - now apply IHprv.
    - left. now apply IHprv.
    - right. now apply IHprv.
    - edestruct IHprv1; trivial. apply HI. apply HCompr. apply Hrho. apply HA.
      + apply IHprv2; trivial. intros x [->|]; auto.
      + apply IHprv3; trivial. intros x [->|]; auto.
    - discriminate.
    - intros x. apply IHprv; trivial. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_i. now destruct rho; apply HA.
    - intros f Hf. apply IHprv; trivial. now apply henkin_env_cons_f. 
      intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_f. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
      now rewrite <- eval_function_subst_cons_shift_f.
    - intros P HP. apply IHprv; trivial. now apply henkin_env_cons_p. 
      intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_p. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
      now rewrite <- eval_predicate_subst_cons_shift_p.
    - eapply sat_comp_i, sat_ext. 2: apply (IHprv Heqp D I funcs preds HI HCompr rho Hrho HA (eval _ rho t)).
      split; try easy. now destruct n.
    - eapply sat_comp_f, sat_ext. 2: eapply (IHprv Heqp D I funcs preds HI HCompr rho Hrho HA (eval_function _ rho f)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|]. 
      eapply eval_function_included. apply HI. apply Hrho.
    - eapply sat_comp_p, sat_ext. 2: eapply (IHprv Heqp D I funcs preds HI HCompr rho Hrho HA (eval_predicate _ rho P)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|]. 
      eapply eval_predicate_included. apply HI. apply Hrho.
    - exists (eval _ rho t). eapply sat_ext. 2: apply sat_comp_i, IHprv, HA; try easy.
      split; try easy. now destruct n.
    - exists (eval_function _ rho f). eexists.
      + eapply eval_function_included. apply HI. apply Hrho.
      + eapply sat_ext. 2: apply sat_comp_f, IHprv, HA; try easy. split; try easy.
        intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - exists (eval_predicate _ rho P). eexists.
      + eapply eval_predicate_included. apply HI. apply Hrho.
      + eapply sat_ext. 2: apply sat_comp_p, IHprv, HA; try easy. split; try easy.
        intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - edestruct IHprv1 as [x Hx]; eauto.
      specialize (IHprv2 Heqp D I funcs preds HI HCompr ⟨x .: get_indi rho, get_func rho, get_pred rho ⟩).
      apply sat_comp_i in IHprv2; try easy. destruct rho; apply IHprv2.
      intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hx.
      apply sat_comp_i. destruct rho; apply H'.
    - edestruct IHprv1 as [f [Hf' Hf]]; eauto.
      specialize (IHprv2 Heqp D I funcs preds HI HCompr ⟨get_indi rho, f .: get_func rho, get_pred rho ⟩).
      apply sat_comp_f in IHprv2; try easy.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
      + now apply henkin_env_cons_f.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hf.
        apply sat_comp_f. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
    - edestruct IHprv1 as [P [HP' HP]]; eauto.
      specialize (IHprv2 Heqp D I funcs preds HI HCompr ⟨get_indi rho, get_func rho, P .: get_pred rho ⟩).
      apply sat_comp_p in IHprv2; try easy.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
      + now apply henkin_env_cons_p.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact HP.
        apply sat_comp_p. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
    - apply HCompr. apply Hrho. easy.
  Qed.

  Lemma HenkinSoundnessC A phi :
    LEM -> A ⊢c phi -> Henkin.valid A phi.
  Proof.
    intros lem. induction 1; intros D I funcs preds HI HCompr rho Hrho HA.
    - intros H1. apply IHprv; trivial. intros phi' [->|]; firstorder.
    - apply IHprv1; trivial. apply IHprv2; trivial.
    - exfalso. eapply IHprv; try easy. apply HI. apply HCompr.
    - firstorder.
    - split. now apply IHprv1. now apply IHprv2.
    - now apply IHprv.
    - now apply IHprv.
    - left. now apply IHprv.
    - right. now apply IHprv.
    - edestruct IHprv1; trivial. apply HI. apply HCompr. apply Hrho. apply HA.
      + apply IHprv2; trivial. intros x [->|]; auto.
      + apply IHprv3; trivial. intros x [->|]; auto.
    - specialize (lem (sat funcs preds rho phi)). cbn. tauto. 
    - intros x. apply IHprv; trivial. intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_i. now destruct rho; apply HA.
    - intros f Hf. apply IHprv; trivial. now apply henkin_env_cons_f. 
      intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_f. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
      now rewrite <- eval_function_subst_cons_shift_f.
    - intros P HP. apply IHprv; trivial. now apply henkin_env_cons_p. 
      intros psi [psi' [<- H1]]%in_map_iff.
      apply sat_comp_p. cbn. eapply sat_ext. 2: apply HA, H1.
      split; try easy; split; try easy; cbn.
      replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
      now rewrite <- eval_predicate_subst_cons_shift_p.
    - eapply sat_comp_i, sat_ext. 2: apply (IHprv D I funcs preds HI HCompr rho Hrho HA (eval _ rho t)).
      split; try easy. now destruct n.
    - eapply sat_comp_f, sat_ext. 2: eapply (IHprv D I funcs preds HI HCompr rho Hrho HA (eval_function _ rho f)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|]. 
      eapply eval_function_included. apply HI. apply Hrho.
    - eapply sat_comp_p, sat_ext. 2: eapply (IHprv D I funcs preds HI HCompr rho Hrho HA (eval_predicate _ rho P)).
      split; try easy. intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|]. 
      eapply eval_predicate_included. apply HI. apply Hrho.
    - exists (eval _ rho t). eapply sat_ext. 2: apply sat_comp_i, IHprv, HA; try easy.
      split; try easy. now destruct n.
    - exists (eval_function _ rho f). eexists.
      + eapply eval_function_included. apply HI. apply Hrho.
      + eapply sat_ext. 2: apply sat_comp_f, IHprv, HA; try easy. split; try easy.
        intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - exists (eval_predicate _ rho P). eexists.
      + eapply eval_predicate_included. apply HI. apply Hrho.
      + eapply sat_ext. 2: apply sat_comp_p, IHprv, HA; try easy. split; try easy.
        intros; destruct n; cbn; now destruct PeanoNat.Nat.eq_dec as [->|].
    - edestruct IHprv1 as [x Hx]; eauto.
      specialize (IHprv2 D I funcs preds HI HCompr ⟨x .: get_indi rho, get_func rho, get_pred rho ⟩).
      apply sat_comp_i in IHprv2; try easy. destruct rho; apply IHprv2.
      intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hx.
      apply sat_comp_i. destruct rho; apply H'.
    - edestruct IHprv1 as [f [Hf' Hf]]; eauto.
      specialize (IHprv2 D I funcs preds HI HCompr ⟨get_indi rho, f .: get_func rho, get_pred rho ⟩).
      apply sat_comp_f in IHprv2; try easy.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
      + now apply henkin_env_cons_f.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact Hf.
        apply sat_comp_f. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_func n ar0)[@shift _ shift_f ar]f) by reflexivity.
        now rewrite <- eval_function_subst_cons_shift_f.
    - edestruct IHprv1 as [P [HP' HP]]; eauto.
      specialize (IHprv2 D I funcs preds HI HCompr ⟨get_indi rho, get_func rho, P .: get_pred rho ⟩).
      apply sat_comp_p in IHprv2; try easy.
      + eapply sat_ext. 2: apply IHprv2. split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
      + now apply henkin_env_cons_p.
      + intros phi'. intros [->|[psi' [<- H'%HA]] % in_map_iff]. exact HP.
        apply sat_comp_p. eapply sat_ext. 2: apply H'.
        split; try easy; split; try easy; cbn.
        replace (↑ ar n ar0) with ((var_pred n ar0)[@shift _ shift_p ar]p) by reflexivity.
        now rewrite <- eval_predicate_subst_cons_shift_p.
    - apply HCompr. apply Hrho. easy.
  Qed.

  Corollary HenkinSoundnessIT T phi :
    T ⊩i phi -> Henkin.validT T phi.
  Proof.
    intros [A [HA H1]] D I funcs preds HI HC rho Hrho HT. 
    eapply HenkinSoundnessI; try eassumption.
    intros psi H2. apply HT, HA, H2.
  Qed.

  Corollary HenkinSoundnessCT :
    LEM <-> (forall T phi, T ⊩c phi -> Henkin.validT T phi).
  Proof.
    split.
    - intros lem T phi [A [HA H1]] D I funcs preds HI HC rho Hrho HT. 
      eapply HenkinSoundnessC; try eassumption.
      intros psi H2. apply HT, HA, H2.
    - intros H P. enough (validT (fun _ => False) (p$0 (Vector.nil _) ∨ ¬ p$0 (Vector.nil _))) as X.
      { pose (I := {| i_f f v := 0 ; i_P P v := False |}).
        assert (henkin_interp I (fun _ _ => True) (fun _ _ => True)) as HI by easy.
        assert (forall rho, (nat -> nat -> True) -> forall ar phi, funcfree phi -> sat (fun _ _ => True) (fun _ _ => True) rho (comprehension_form ar phi)) as HC.
        { intros rho _ ar phi _. apply sat_full_henkin, comprehension_sound. }
        destruct (X nat I (fun _ _ => True) (fun _ _ => True) HI HC ⟨fun _ => 0, fun _ _ _ => 0, fun _ _ _ => P⟩); auto. easy. easy. }
      apply H. exists List.nil. split; trivial. eapply IE. eapply Peirce with (psi := ⊥).
      apply II. apply Exp. eapply IE with (phi := ¬ p$0 (Vector.nil term)).
      + apply II. eapply IE. apply Ctx; now right. apply DI2. now apply Ctx.
      + apply II. eapply IE. apply Ctx; now right. apply DI1. now apply Ctx.
  Qed.

End Henkin.