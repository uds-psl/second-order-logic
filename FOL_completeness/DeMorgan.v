Require Import GenCompleteness ND Tarski FOL.

(** ** De Morgan Translation  *)

Existing Instance full_operators.
Existing Instance falsity_on.

Notation "⊥" := falsity.
Notation "A ∧ B" := (bin Conj A B) (at level 41).
Notation "A ∨ B" := (bin Disj A B) (at level 42).
Notation "A '~>' B" := (@bin _ _ full_operators _ Impl A B) (at level 43, right associativity).
Notation "∀ Phi" := (@quant _ _ full_operators _ All Phi) (at level 50).
Notation "∃ Phi" := (quant Ex Phi) (at level 56, right associativity).
Notation "¬ phi" := (phi ~> ⊥) (at level 20).

Notation "A ⊢ phi" := (prv _ A phi) (at level 30).

Hint Constructors prv.

Section Prv.

  Context {Σ_funcs : FOL.funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma prv_cut A phi psi :
    A ⊢ phi -> (phi :: A) ⊢ psi -> A ⊢ psi.
  Proof.
    eauto.
  Qed.

  Lemma DN A phi :
    A ⊢ ¬ (¬ phi) -> A ⊢ phi.
  Proof.
    intros H. eapply IE.
    - apply (Peirce _ _ ⊥).
    - apply II. apply Exp. eapply IE.
      + apply (Weak _ _ _ H). auto.
      + apply Ctx. auto.
  Qed.

End Prv.

Ltac ointro_all :=
  match goal with
  | [ |- ?A ⊢ ∀ ?phi] => apply AllI; cbn
  end.

Ltac ointro_impl :=
  match goal with
  | [ |- _  ⊢ (_ ~> _)] => apply II
  | [ |- _  ⊢ (¬ _)] => apply II
  end.

Ltac ointro := ointro_impl + ointro_all + fail "Nothing to intro!".
Ltac ointros := repeat ointro.

Ltac ctx_index' n :=
  match n with
  | O => now left
  | S ?m => right; ctx_index' m
  end.
Ltac ctx_index n := apply Ctx; ctx_index' n.
Ltac ctx := apply Ctx; intuition.

Ltac oapply n := eapply IE; [ctx_index n|].

Ltac ospecialize n t :=
  eapply prv_cut; [eapply (@AllE _ _ _ _ t); ctx_index n|]; cbn.

Ltac ouse H := eapply Weak; [apply H |]; intuition.
Ltac oimport H := eapply prv_cut; [ouse H |].
Ltac oassert form := eapply (@prv_cut _ _ _ form).
Ltac oexfalso := apply Exp.
Ltac opeirce form := eapply IE; [apply (@Pc _ _ _ _ form) | apply II].

Ltac oindirect := apply DN, II.

Ltac osplit := eapply CI.
Ltac oleft := eapply DI1.
Ltac oright := eapply DI2.

Lemma AXM {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} A phi psi :
  (phi :: A) ⊢ psi -> (¬ phi :: A) ⊢ psi -> A ⊢ psi.
Proof.
  intros Ht Hf. oindirect. oassert (¬ phi). ointros. oapply 1.
  ouse Ht. oapply 1. ouse Hf.
Qed.

Ltac oxm form :=
  apply (@AXM _ _ _ form).

Section DM.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Fixpoint DM {ff : falsity_flag} (phi : form ff) : form falsity_on :=
    match phi with 
    | atom P v => atom P v
    | ⊥ => ⊥
    | bin Impl phi psi => DM phi ~> DM psi
    | phi ∧ psi => ¬ (DM phi ~> ¬ DM psi)
    | phi ∨ psi => ¬ DM phi ~> DM psi
    | quant All phi => ∀ DM phi
    | ∃ phi => ¬ (∀ ¬ DM phi)
    end.

  Lemma help phi :
    phi[up ↑][$0..] = phi.
  Proof.
    rewrite !subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma DM_prv A phi :
    prv _ A phi <-> prv _ A (DM phi).
  Proof.
    revert A. pattern phi. induction phi using form_ind_falsity; cbn; try tauto.
    1: destruct b0. 4: destruct q.
    - split; intros H.
      + ointros. eapply IE. oapply 0.
        * apply IHphi1. eapply CE1, (Weak _ _ _ H). auto.
        * apply IHphi2. eapply CE2, (Weak _ _ _ H). auto.
      + oimport H. osplit; oindirect.
        * oapply 1. ointros. oapply 2. apply IHphi1. ctx.
        * oapply 1. ointros. oapply 2. apply IHphi2. ctx.
    - split; intros H.
      + ointros. eapply DE. apply (Weak _ _ _ H). auto.
        * oexfalso. oapply 1. apply IHphi1. ctx.
        * apply IHphi2. ctx.
      + oxm phi1. oleft. ctx.
        oright. apply IHphi2. oimport H. oapply 0.
        ointros. oapply 2. apply IHphi1. ctx.
    - split; intros H.
      + ointros. oimport H. apply IHphi2. oapply 0. apply IHphi1. ctx.
      + ointros. oimport H. apply IHphi2. oapply 0. apply IHphi1. ctx.
    - split; intros H.
      + oimport H. ointros. ospecialize 0 (var 0). apply IHphi. rewrite help. ctx.
      + oimport H. ointros. ospecialize 0 (var 0). apply IHphi. rewrite help. ctx.
    - split; intros H.
      + apply (ExE _ _ _ H). cbn. ointros.
        ospecialize 0 (var 0). rewrite help. oapply 0. apply IHphi. ctx.
      + oindirect. oimport H. oapply 0. ointros. oapply 2.
        apply (ExI _ (var 0)). rewrite help. apply IHphi. ctx.
  Qed.
  
  Fixpoint convert {ff : falsity_flag} (phi : @form _ _ full_operators ff) : @form _ _ frag_operators falsity_on :=
    match phi with 
    | atom P v => atom P v
    | bin Impl phi psi => bin _ _ frag_operators _ FOL_facts.Impl (convert phi) (convert psi)
    | quant All phi => quant _ _ frag_operators _ FOL_facts.All (convert phi)
    | _ => ⊥
    end.

  Fixpoint embed {ff : falsity_flag} (phi : @form _ _ frag_operators ff) : @form _ _ full_operators ff :=
    match phi with 
    | atom P v => atom P v
    | bin FOL_facts.Impl phi psi => embed phi ~> embed psi
    | quant FOL_facts.All phi => ∀ embed phi
    | ⊥ => ⊥
    end.

  Lemma convert_embed {ff : falsity_flag} phi :
    convert (embed phi) = phi.
  Proof.
    induction phi using form_ind_falsity; try destruct b0; try destruct q; cbn; intuition congruence.
  Qed.

  Definition DMT {ff : falsity_flag} phi :=
    convert (DM phi).

  Lemma embed_DMT {ff : falsity_flag} phi :
    embed (DMT phi) = DM phi.
  Proof.
    unfold DMT. induction phi; try destruct b0; try destruct q; cbn; intuition congruence.
  Qed.

  Lemma DMT_subst {ff : falsity_flag} sigma phi :
    DMT phi[sigma] = (DMT phi)[sigma].
  Proof.
    revert sigma. induction phi; intros sigma;
      try destruct b0; try destruct q; cbn; unfold DMT in *.
    1, 2: reflexivity.
    1, 2, 3: now rewrite IHphi1, IHphi2.
    1, 2: now rewrite IHphi.
  Qed.

  Lemma incl_eq X (A B : list X) :
    A = B -> A <<= B.
  Proof.
    now intros ->.
  Qed.

  Lemma DMT_prv {ff : falsity_flag} A phi :
    prv ff A phi -> (map DMT A) ⊢CE (DMT phi).
  Proof.
    induction 1; intros; cbn in *.
    - apply ND.II. apply (ND.Weak IHprv). auto.
    - apply (ND.IE IHprv1 IHprv2).
    - apply ND.AllI. apply (ND.Weak IHprv).
      rewrite !map_map. apply incl_eq, map_ext, DMT_subst.
    - rewrite DMT_subst. eapply ND.AllE. apply IHprv.
    - eapply ND.ExI. rewrite DMT_subst in IHprv. apply IHprv.
    - eapply (ND.ExE IHprv1); fold DM convert. rewrite <- DMT_subst.
      apply (ND.Weak IHprv2). cbn. apply incl_shift.
      rewrite !map_map. apply incl_eq, map_ext, DMT_subst.
    - eapply ND.Exp. apply IHprv.
    - apply ND.Ctx. now apply in_map.
    - ND.ointros. eapply ND.IE. ND.oapply 0.
      + ND.ouse IHprv1.
      + ND.ouse IHprv2.
    - ND.oindirect. ND.oimport IHprv. ND.oapply 0.
      ND.ointros. ND.oapply 3. ND.ctx.
    - ND.oindirect. ND.oimport IHprv. ND.oapply 0.
      ND.ointros. ND.oapply 3. ND.ctx.
    - ND.ointros. ND.oexfalso. ND.oapply 0. ND.ouse IHprv.
    - ND.ointros. ND.ouse IHprv.
    - ND.oxm (DMT phi); try apply IHprv2. ND.oxm (DMT psi).
      + ND.ouse IHprv3.
      + ND.oexfalso. ND.oapply 0. ND.oimport IHprv1. ND.oapply 0. ND.ctx.
    - apply ND.Pc.
  Qed.

  Lemma embed_subst {ff : falsity_flag} sigma phi :
    embed phi[sigma] = (embed phi)[sigma].
  Proof.
    induction phi in sigma |- *; cbn; try reflexivity.
    1: destruct b0. 2: destruct q.
    - now rewrite IHphi1, IHphi2.
    - now rewrite IHphi.
  Qed.

  Lemma embed_prv A phi :
    A ⊢CE phi -> (map embed A) ⊢ (embed phi).
  Proof.
    induction 1; cbn.
    - apply II. apply (Weak _ _ _ IHprv). reflexivity.
    - apply (IE _ _ _ IHprv1 IHprv2).
    - apply AllI. apply (Weak _ _ _ IHprv).
      rewrite !map_map. apply incl_eq, map_ext, embed_subst.
    - setoid_rewrite embed_subst. apply (AllE _ t _ IHprv).
    - apply Exp, IHprv.
    - apply Ctx, in_map, H.
    - apply Peirce.
  Qed.

  Definition DNE := forall P, ~ ~ P -> P.

  Definition LEM := forall P, P \/ ~ P.

  Lemma LEM_DNE :
    LEM <-> DNE.
  Proof.
    split.
    - intros H X HX. destruct (H X); tauto.
    - intros H X. apply H. tauto.
  Qed.

  Notation "rho ⊨' phi" := (FOL_completeness.Tarski.sat _ rho phi) (at level 50).

  Lemma DMT_sat D (I : FOL.interp D) rho phi :
    DNE -> sat rho phi <-> rho ⊨' (DMT phi).
  Proof.
    intros HDN. revert rho.
    induction phi using form_ind_falsity; intros rho.
    all: try destruct b0; try destruct q; cbn.
    all: try specialize (IHphi1 rho); try specialize (IHphi2 rho); try tauto.
    - split; try tauto. split; apply HDN; tauto.
    - split; try tauto. intros H. apply HDN. tauto.
    - firstorder tauto.
    - split; try firstorder tauto. intros H. apply HDN. firstorder tauto.
  Qed.

  Definition DMTT (T : form -> Prop) :=
    fun phi => exists psi, T psi /\ phi = DMT psi.

  Notation "T ⊨= phi" := (forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi) (at level 50).
  Notation "T ⊨=' phi" := (forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨' psi) -> rho ⊨' phi) (at level 50).

  Lemma DMT_valid (T : form -> Prop) phi :
    DNE -> T ⊨= phi -> (DMTT T) ⊨=' DMT phi.
  Proof.
    intros HDN H D I rho HT. apply DMT_sat; trivial. apply H.
    - intros psi HP. apply DMT_sat; trivial. apply HT. now exists psi.
  Qed.

  Lemma DMT_incl T A :
    (forall phi, phi el A -> (DMTT T) phi) -> exists B, (forall phi, phi el B -> T phi) /\ A = map DMT B.
  Proof.
    induction A; intros H.
    - exists nil. split; trivial. now intros phi [].
    - assert (DMTT T a) as [phi[HP ->]] by now apply H.
      destruct IHA as [B[HB ->]]. firstorder.
      exists (phi::B). split; trivial. intros psi [->|]; auto.
  Qed.

  Lemma prv_cut_list A B phi :
    A ⊢ phi -> (forall psi, psi el A -> B ⊢ psi) -> B ⊢ phi.
  Proof.
    induction 1 in B |- *; intros HA.
    - apply II, IHprv. intros theta [->|HT]; try now ctx. ouse (HA theta HT).
    - eapply IE; try now apply IHprv1. now apply IHprv2.
    - apply AllI, IHprv. intros psi [theta[<- HT]] % in_map_iff. now apply subst_Weak, HA.
    - now apply AllE, IHprv.
    - now eapply ExI, IHprv.
    - eapply ExE; try now apply IHprv1. apply IHprv2. intros psi' [<-|[theta[<- HT]] % in_map_iff]; try now ctx.
      eapply Weak; try now apply incl_tl; try reflexivity. now apply subst_Weak, HA.
    - now apply Exp, IHprv.
    - now apply HA.
    - apply CI; auto.
    - now eapply CE1, IHprv.
    - now eapply CE2, IHprv.
    - now eapply DI1, IHprv.
    - now eapply DI2, IHprv.
    - eapply DE; try now apply IHprv1.
      + apply IHprv2. intros theta' [->|HT]; try now ctx. ouse (HA theta' HT).
      + apply IHprv3. intros theta' [->|HT]; try now ctx. ouse (HA theta' HT).
    - apply Peirce.
  Qed.

  Lemma DMT_bounded phi n :
    bounded n phi -> bounded n (DMT phi).
  Proof.
    induction 1.
    - constructor. apply H.
    - destruct binop; cbn; now repeat constructor.
    - destruct quantop; cbn; now repeat constructor.
    - constructor.
  Qed.

  Lemma vec_in_In {X} k (v : Vector.t X k) a :
    FOL_facts.vec_in a v -> Vector.In a v.
  Proof.
    induction 1. now left. now right.
  Qed.

  Lemma bounded_unused_term t n :
    bounded_t n t -> forall k, k >= n -> unused_term k t.
  Proof.
    induction 1.
    - intros k Hk. constructor. lia.
    - intros k Hk. constructor. intros t Ht. apply H0; trivial. now apply vec_in_In.
  Qed.

  Lemma bounded_unused phi n :
    bounded n phi -> forall k, k >= n -> unused k phi.
  Proof.
    induction 1; intros k Hk.
    - constructor. intros t Ht. apply bounded_unused_term with n; trivial. now apply H, vec_in_In.
    - destruct binop. constructor; intuition.
    - destruct quantop. constructor. apply IHbounded. lia.
    - constructor.
  Qed.

  Lemma bounded_closed phi :
    bounded 0 phi -> closed phi.
  Proof.
    intros H k. apply (bounded_unused H). lia.
  Qed.
  
  Context {HdF : eq_dec Σ_funcs} {HdP : eq_dec Σ_preds}.
  Context {HeF : enumerable__T Σ_funcs} {HeP : enumerable__T Σ_preds}.

  Theorem full_completeness (T : form -> Prop) phi :
    DNE -> (forall psi, T psi -> bounded 0 psi) -> bounded 0 phi -> T ⊨= phi -> exists A, (forall psi, psi el A -> T psi) /\ A ⊢ phi.
  Proof.
    intros HDN HB1 HB2 H'. assert (H : (DMTT T) ⊨=' DMT phi) by now apply DMT_valid.
    destruct HeF, HeP. eapply semi_completeness_standard in H; eauto.
    - apply HDN in H as [A[HA1 HA2 % embed_prv]]. apply DMT_incl in HA1 as [B[HB ->]].
      exists B. split; try apply HB. apply DM_prv. rewrite embed_DMT in HA2. apply (prv_cut_list HA2).
      rewrite map_map. intros psi [theta[<- H]] % in_map_iff. rewrite embed_DMT. apply -> DM_prv. now apply Ctx.
    - intros psi n [theta [Hp % HB1 ->]]. apply bounded_unused with 0; try lia. now apply DMT_bounded.
    - apply bounded_closed. now apply DMT_bounded.
  Qed.

End DM.

Print Assumptions full_completeness.
