(** * Reduction to FOL *)

Require Import FOL SOL FullSyntax Tarski Henkin Deduction.
Require Import Vector VectorLib Util.

Require Import Equations.Equations Equations.Prop.DepElim.
Require Import Lia.

Require Import Enumerable Decidable.

Import VectorNotations.
Import SubstNotations.


Definition toFOLBinop b := match b with
  | FullSyntax.Conj => FOL.Conj
  | FullSyntax.Disj => FOL.Disj
  | FullSyntax.Impl => FOL.Impl
end.

Definition toSOLBinop b := match b with
  | FOL.Conj => FullSyntax.Conj
  | FOL.Disj => FullSyntax.Disj
  | FOL.Impl => FullSyntax.Impl
end.

Definition toSOLQuantop b := match b with
  | FOL.All => FullSyntax.All
  | FOL.Ex => FullSyntax.Ex
end.

Definition toFOLQuantop b := match b with
  | FullSyntax.All => FOL.All
  | FullSyntax.Ex => FOL.Ex
end.

Lemma toSOLBinop_toFOLBinop b :
  toSOLBinop (toFOLBinop b) = b.
Proof.
  now destruct b.
Qed.



Section Signature.

  Context {Σf2 : SOL.funcs_signature}.
  Context {Σp2 : SOL.preds_signature}.

  (* Add symbols for predicate application to the SOL signature.  *)

  Inductive FOLSyms :=
    | NormalSym : syms -> FOLSyms.

  Inductive FOLPreds :=
    | NormalPred : preds -> FOLPreds
    | PredApp : nat -> FOLPreds.

  Instance Σf1 : FOL.funcs_signature := {|
    FOL.syms := FOLSyms ;
    FOL.ar_syms f := match f with NormalSym f => SOL.ar_syms f end
  |}.

  Instance Σp1 : FOL.preds_signature := {|
    FOL.preds := FOLPreds ;
    FOL.ar_preds P := match P with NormalPred P => SOL.ar_preds P | PredApp ar => S ar end
  |}.

  (** The extended signatures preserve discreteness and enumerablility *)

  Lemma Sigma_f1_eq_dec :
    eq_dec Σf2 -> eq_dec Σf1.
  Proof.
    intros H [x] [y]. enough (dec (x = y)) as [->|H1]. 
    now left. right. congruence. apply H.
  Qed.

  Lemma Sigma_p1_eq_dec :
    eq_dec Σp2 -> eq_dec Σp1.
  Proof.
    intros H [p|n] [p'|n'].
    - enough (dec (p = p')) as [->|H1]. now left. right. congruence. apply H.
    - right. congruence.
    - right. congruence.
    - decide (n = n') as [->|]. now left. right. congruence.
  Qed.

  Lemma Sigma_f1_enumerable :
    enumerable__T Σf2 -> enumerable__T Σf1.
  Proof.
    intros [f Hf]. exists (fun n => match f n with Some x => Some (NormalSym x) | None => None end).
    intros [x]. destruct (Hf x) as [n H]. exists n. now rewrite H.
  Qed.

  Lemma Sigma_p1_enumerable :
    enumerable__T Σp2 -> enumerable__T Σp1.
  Proof.
    intros [f Hf]. 
    exists (fun n => match pi1 n with
                      | 0 => match f (pi2 n) with Some x => Some (NormalPred x) | None => None end
                      | _ => Some (PredApp (pi2 n))
                    end).
    intros [x|n]. 
    - destruct (Hf x) as [n H]. exists (embed (0,n)). now rewrite pi1_correct, pi2_correct, H.
    - exists (embed (1,n)). now rewrite pi1_correct, pi2_correct.
  Qed.


  (** Notations for first-order syntax *)

  Notation "⊥'" := FOL.falsity.
  Notation "A ∧' B" := (@FOL.bin Σf1 Σp1 FOL.full_operators _ FOL.Conj A B) (at level 41).
  Notation "A ∨' B" := (@FOL.bin Σf1 Σp1 FOL.full_operators _ FOL.Disj A B) (at level 42).
  Notation "A '-->'' B" := (@FOL.bin Σf1 Σp1 FOL.full_operators _ FOL.Impl A B) (at level 43, right associativity).
  Notation "A '<-->'' B" := ((A -->' B) ∧' (B -->' A)) (at level 44, right associativity).
  Notation "∀' Phi" := (@FOL.quant Σf1 Σp1 FOL.full_operators _ FOL.All Phi) (at level 50).
  Notation "∃' Phi" := (@FOL.quant Σf1 Σp1 FOL.full_operators _ FOL.Ex Phi) (at level 50).

  Notation "phi `[ sigma ]" := (FOL.subst_form sigma phi) (at level 7, left associativity, format "phi '/' `[ sigma ]") : subst_scope.
  Notation "f >>' g" := (FOL.funcomp g f) (at level 50) : subst_scope.
  Notation "s '..''" := (FOL.scons s FOL.var) (at level 4, format "s ..'") : subst_scope.
  Notation "↑'" := (S >>' FOL.var) : subst_scope.

  Notation "A ⊢1 phi" := (FOL.prv _ A phi) (at level 61).
  Notation "A ⊢2 phi" := (Deduction.prv A phi) (at level 61).

  Lemma FOL_term_ind (p : FOL.term -> Prop) :
    (forall x, p (FOL.var x)) -> (forall F v (IH : VectorLib.Forall p v), p (FOL.func F v)) -> forall t, p t.
  Proof.
    intros f1 f2. fix F 1. intros [n|f v].
    - apply f1.
    - apply f2. induction v. easy. split. apply F. apply IHv.
  Qed.



  (** ** Definition of Translation Function *)

  (** The idea is to use functions pos_i, pos_f and pos_p that given a 
      position in the SOL environment tell us the positition of the same 
      object in the FOL environment.
      Quantifiers update those mappings by adding 0 the the matching
      kind and shiftig the other two. *)

  Definition pcons (pos : nat -> nat) : nat -> nat := 
    fun n => match n with 0 => 0 | S n => S (pos n) end.

  Definition pcons' (ar : nat) (pos : nat -> nat -> nat) : nat -> nat -> nat := 
    fun n ar' => match n with 
      | 0 => if PeanoNat.Nat.eq_dec ar ar' then 0 else S (pos 0 ar') 
      | S n => if PeanoNat.Nat.eq_dec ar ar' then S (pos n ar') else S (pos (S n) ar') end.

  Definition pshift (pos : nat -> nat) : nat -> nat := fun n => S (pos n).
  Definition pshift' (pos : nat -> nat -> nat) : nat -> nat -> nat := fun n ar => S (pos n ar).

  Fixpoint toFOLTerm (pos_i : nat -> nat) (t : SOL.term) : FOL.term := match t with
    | SOL.var_indi x => FOL.var (pos_i x)
    | SOL.func (var_func x ar) v => FOL.var 0
    | SOL.func (sym f) v => FOL.func (NormalSym f) (Vector.map (toFOLTerm pos_i) v)
  end.

  Fixpoint toFOLForm (pos_i : nat -> nat) (pos_p : nat -> nat -> nat) (phi : SOL.form) : FOL.form := match phi with
    | SOL.fal => FOL.falsity
    | SOL.atom (pred P) v => FOL.atom (NormalPred P) (Vector.map (toFOLTerm pos_i) v)
    | SOL.atom (var_pred x ar) v => FOL.atom (PredApp ar) (FOL.var (pos_p x ar) :: Vector.map (toFOLTerm pos_i) v)
    | SOL.bin op phi psi => FOL.bin (toFOLBinop op) (toFOLForm pos_i pos_p phi) (toFOLForm pos_i pos_p psi)
    | SOL.quant_indi op phi => FOL.quant (toFOLQuantop op) (toFOLForm (pcons pos_i) (pshift' pos_p) phi)
    | SOL.quant_func op ar phi => FOL.falsity
    | SOL.quant_pred op ar phi => FOL.quant (toFOLQuantop op) (toFOLForm (pshift pos_i) (pcons' ar pos_p) phi)
  end.

  Definition initial_pos_i n := embed (0, n).
  Definition initial_pos_p n ar := embed (1, embed (n, ar)).

  Definition toFOLForm' (phi : SOL.form) := toFOLForm initial_pos_i initial_pos_p phi.


  Lemma toFOLTerm_ext_i pos_i pos_i' t :
    (forall n, ~bounded_indi_term n t -> pos_i n = pos_i' n)
    -> toFOLTerm pos_i t = toFOLTerm pos_i' t.
  Proof.
    intros Hi. induction t; cbn.
    - rewrite Hi. reflexivity. cbn; lia.
    - reflexivity.
    - f_equal. apply map_ext_in. intros t H. eapply Forall_in in IH. apply IH.
      intros n H1. apply Hi. intros H2. apply H1. eapply Forall_in in H2. apply H2. all: easy.
  Qed.

  Lemma toFOLForm_ext_i pos_i pos_i' pos_p phi :
    (forall n, ~bounded_indi n phi -> pos_i n = pos_i' n)
    -> toFOLForm pos_i pos_p phi = toFOLForm pos_i' pos_p phi.
  Proof.
    induction phi in pos_i, pos_i', pos_p |-*; cbn; intros Hi.
    - reflexivity.
    - destruct p; cbn; f_equal. f_equal. all: apply map_ext_in; intros t H; 
      apply toFOLTerm_ext_i; intros n' H1; apply Hi; intros H2; apply H1;
      eapply Forall_in in H2; try apply H2; easy.
    - erewrite IHphi1, IHphi2; firstorder.
    - f_equal. apply IHphi. intros [] H; cbn. reflexivity. now rewrite Hi.
    - reflexivity.
    - f_equal. apply IHphi. intros n' H. unfold pshift. now rewrite Hi.
  Qed.

  Lemma toFOLForm_ext_p pos_i pos_p pos_p' phi :
    (forall n ar, ~bounded_pred ar n phi -> pos_p n ar = pos_p' n ar)
    -> toFOLForm pos_i pos_p phi = toFOLForm pos_i pos_p' phi.
  Proof.
    induction phi in pos_i, pos_p, pos_p' |-*; intros Hp; cbn.
    - reflexivity.
    - destruct p; f_equal. rewrite Hp. reflexivity. cbn; lia.
    - erewrite IHphi1, IHphi2; firstorder.
    - erewrite IHphi. reflexivity. intros n ar H. unfold pshift'. now rewrite Hp.
    - reflexivity.
    - erewrite IHphi. reflexivity. intros [] ar H; cbn; destruct PeanoNat.Nat.eq_dec as [->|].
      reflexivity. all: rewrite Hp; try reflexivity; cbn; now intros [[]|[]]; try lia.
  Qed.

  Definition closed phi := bounded_indi 0 phi /\ (forall ar, bounded_func ar 0 phi) /\ (forall ar, bounded_pred ar 0 phi).

  Lemma toFOLForm_closed_ext pos_i pos_p pos_i' pos_p' phi :
    closed phi -> toFOLForm pos_i pos_p phi = toFOLForm pos_i' pos_p' phi.
  Proof.
    intros C. erewrite toFOLForm_ext_p, toFOLForm_ext_i. reflexivity.
    - intros n H. exfalso. apply H. eapply bounded_indi_up. 2: apply C. lia.
    - intros n ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply C. lia.
  Qed.

  Lemma comprehension_form_funcfree ar phi :
    funcfree phi -> funcfree (comprehension_form ar phi).
  Proof.
    intros H. apply forall_n_funcfree. repeat split; cbn.
    1,4: induction ar; firstorder. all: now apply funcfree_subst_p.
  Qed.


  Definition C := fun phi => exists ar psi, funcfree psi /\ phi = close All (comprehension_form ar psi).
  Definition toFOLTheory (T : SOL.form -> Prop) := fun phi => exists phi', phi = toFOLForm' phi' /\ T phi'.

  Lemma toFOLTheory_enumerable T :
    enumerable T -> enumerable (toFOLTheory T).
  Proof.
    intros [f Hf]. exists (fun n => match f n with Some phi => Some (toFOLForm' phi) | None => None end).
    intros phi. split.
    - intros [psi [-> H]]. apply Hf in H as [n H]. exists n. now rewrite H.
    - intros [n H]. destruct f eqn:H1.
      + inversion H. eexists. split. reflexivity. apply Hf. now exists n.
      + easy.
  Qed.

  Lemma C_enumerable :
    enumerable__T Σf2 -> enumerable__T Σp2 -> enumerable C.
  Proof.
    intros E1 E2. unfold C. destruct form_enumerable as [f Hf]; trivial. 
    apply enumT_binop. apply enumT_quantop.
    exists (fun n => match f (pi1 n) with Some phi => if funcfree_dec phi then Some (close All (comprehension_form (pi2 n) phi)) else None | None => None end).
    intros phi. split.
    - intros [ar [psi [H1 H2]]]. destruct (Hf psi) as [n H3].
      exists (embed (n, ar)). rewrite pi1_correct, pi2_correct, H2, H3.
      now destruct funcfree_dec.
    - intros [n H1]. destruct f eqn:H2; try easy. destruct funcfree_dec; try easy. 
      inversion H1. eauto.
  Qed.


  (** ** Semantic Reduction *)


  (** *** Translate Henkin Model to First-Order Model. *)

  Section HenkinModel_To_FOModel.

    Variable D2 : Type.

    Context {I2 : Tarski.interp D2}.

    Variable funcs : forall ar, (vec D2 ar -> D2) -> Prop.
    Variable preds : forall ar, (vec D2 ar -> Prop) -> Prop.

    Inductive D1 := 
      | fromIndi : D2 -> D1
      | fromPred : forall ar (P : vec D2 ar -> Prop), preds ar P -> D1.

    Hypothesis D2_inhabited : D2.
    Hypothesis funcs_inhabited : forall ar, { f | funcs ar f }.
    Hypothesis preds_inhabited : forall ar, { P | preds ar P }.

    Definition error_i := D2_inhabited.
    Definition error_p ar := proj1_sig (preds_inhabited ar).

    Lemma error_p_included ar :
      preds ar (error_p ar).
    Proof.
      unfold error_p. now destruct preds_inhabited.
    Qed.

    Definition toIndi (d1 : D1) := match d1 with fromIndi d2 => d2 | _ => error_i end.

    Definition toPred ar (d1 : D1) := match d1 with 
      | fromPred ar' P2 _ => match PeanoNat.Nat.eq_dec ar ar' with
                            | left e => match eq_sym e in _ = ar return vec D2 ar -> Prop with eq_refl => P2 end
                            | right _ => error_p ar
                          end
      | _ => error_p ar
    end.

    Instance I1 : FOL.interp D1 := {|
      FOL.i_func f := match f with 
          | NormalSym f => fun v => fromIndi (Tarski.i_f _ f (Vector.map toIndi v))
        end ;
      FOL.i_atom P := match P with 
          | NormalPred P => fun v => Tarski.i_P _ P (Vector.map (fun d => match d with fromIndi d => d | _ => error_i end) v)
          | PredApp ar => fun v => match Vector.hd v with
                                    | fromPred ar' P _ => match PeanoNat.Nat.eq_dec ar ar' with
                                                          | left e => P match e in _ = ar' return vec _ ar' with eq_refl => Vector.map toIndi (Vector.tl v) end
                                                          | right _ => error_p ar (Vector.map toIndi (Vector.tl v))
                                                        end
                                    | _ => error_p ar (Vector.map toIndi (Vector.tl v))
                                  end
          end
    |}.

    Lemma toFOLTerm_correct_2To1 rho1 rho2 pos_i t :
      funcfreeTerm t
      -> (forall n, toIndi (rho1 (pos_i n)) = get_indi rho2 n)
      -> toIndi (FOL.eval rho1 (toFOLTerm pos_i t)) = Tarski.eval D2 rho2 t.
    Proof.
      intros F Hi. induction t; cbn.
      - apply Hi.
      - now exfalso.
      - f_equal. f_equal. rewrite !map_map. eapply map_ext_forall, Forall_ext_Forall. 
        apply IH. apply F.
    Qed.

    Ltac destruct_eq_dec := 
      repeat (cbn; try rewrite nat_eq_dec_same; cbn; try destruct PeanoNat.Nat.eq_dec as [->|]; try destruct PeanoNat.Nat.eq_dec as [<-|]).

    Lemma toFOLForm_correct_2To1 rho1 rho2 pos_i pos_p phi :
      funcfree phi
      -> (forall n, toIndi (rho1 (pos_i n)) = get_indi rho2 n)
      -> (forall n ar, toPred ar (rho1 (pos_p n ar)) = get_pred rho2 n ar)
      -> FOL.sat rho1 (toFOLForm pos_i pos_p phi) <-> Henkin.sat funcs preds rho2 phi.
    Proof.
      revert rho1 rho2 pos_i pos_p. induction phi; intros rho1 rho2 pos_i pos_p F Hi Hp; cbn.
      - reflexivity.
      - destruct p; cbn.
        + rewrite <- Hp.
          assert (map toIndi (map (FOL.eval rho1) (map (toFOLTerm pos_i) v)) = map (eval D2 rho2) v) as ->. {
            rewrite !map_map. eapply map_ext_forall, Forall_in.
            intros t H. erewrite toFOLTerm_correct_2To1. reflexivity.
            eapply Forall_in in F. apply F. easy. apply Hi. }
          destruct (rho1 (pos_p n ar)); try easy. cbn. now destruct PeanoNat.Nat.eq_dec as [<-|].
        + assert (forall x y, x = y -> x <-> y) as X by now intros x y ->. apply X; clear X.
          f_equal. rewrite !map_map. eapply map_ext, Forall2_identical, Forall_in.
          intros t H. rewrite <- (toFOLTerm_correct_2To1 rho1 _ pos_i). now destruct FOL.eval.
          eapply Forall_in in F. apply F. easy. apply Hi.
      - specialize (IHphi1 rho1 rho2 pos_i pos_p ltac:(firstorder) ltac:(firstorder) ltac:(firstorder)); 
        specialize (IHphi2 rho1 rho2 pos_i pos_p ltac:(firstorder) ltac:(firstorder) ltac:(firstorder)).
        destruct b; cbn; tauto.
      - destruct q; cbn; split.
        + intros H d. eapply IHphi. 4: apply (H (fromIndi d)). easy. intros []. all: firstorder.
        + intros H [d|ar P ?].
          * eapply IHphi. 4: apply (H d). easy. intros []. all: firstorder.
          * eapply IHphi. 4: apply (H error_i). easy. intros []. all: firstorder.
        + intros [[d|ar P ?] H].
          * exists d. eapply IHphi. 4: apply H. easy. intros []. all: firstorder.
          * exists error_i. eapply IHphi. 4: apply H. easy. intros []. all: firstorder.
        + intros [d H]. exists (fromIndi d). eapply IHphi. 4: apply H. easy. intros []. all: firstorder.
      - now exfalso.
      - destruct q; cbn; split.
        + intros H P HP'. eapply IHphi. 4: apply (H (fromPred _ P HP')). 3: intros [] ar'; destruct_eq_dec. all: firstorder.
        + intros H [d|ar P ?].
          * eapply IHphi. 4: apply (H (error_p _)), error_p_included. 3: intros [] ar'; destruct_eq_dec. all: firstorder.
          * destruct (PeanoNat.Nat.eq_dec n ar) as [->|].
            -- eapply IHphi. 4: apply (H P). 3: intros [] ar'; destruct_eq_dec. all: firstorder.
            -- eapply IHphi. 4: apply (H (error_p _)), error_p_included. 3: intros [] ar'; destruct_eq_dec. all: firstorder.
        + intros [[d|ar P HP'] H].
          * exists (error_p _), (error_p_included _). eapply IHphi. 4: apply H. 3: intros [] ar'; destruct_eq_dec. all: firstorder.
          * destruct (PeanoNat.Nat.eq_dec n ar) as [->|].
            -- exists P, HP'. eapply IHphi. 4: apply H. 3: intros [] ar'; destruct_eq_dec. all: firstorder.
            -- exists (error_p _), (error_p_included _). eapply IHphi. 4: apply H. 3: intros [] ar'; destruct_eq_dec. all: firstorder.
        + intros [P [HP' H]]. exists (fromPred _ P HP'). eapply IHphi. 4: apply H. 3: intros [] ar'; destruct_eq_dec. all: firstorder.
    Qed.

    Definition toFOLEnv rho2 (H : henkin_env funcs preds rho2) := fun n => match unembed n with
      | (0, n) => fromIndi (get_indi rho2 n)
      | (_, x) => fromPred _ (get_pred rho2 (pi1 x) (pi2 x)) ltac:(apply H)
    end.

    Lemma toFOLEnv_correct_i rho2 (H : henkin_env funcs preds rho2) :
      forall n, toIndi (toFOLEnv rho2 H (initial_pos_i n)) = get_indi rho2 n.
    Proof.
      intros n. unfold toFOLEnv, initial_pos_i. now rewrite unembed_embed.
    Qed.

    Lemma toFOLEnv_correct_p rho2 (H : henkin_env funcs preds rho2) :
      forall n ar, toPred ar (toFOLEnv rho2 H (initial_pos_p n ar)) = get_pred rho2 n ar.
    Proof.
      intros n ar. unfold toFOLEnv, initial_pos_p.
      rewrite unembed_embed, pi1_correct, pi2_correct.
      destruct H. cbn. now rewrite nat_eq_dec_same.
    Qed.

    Lemma toFOLForm_correct_2To1' rho2 (H : henkin_env funcs preds rho2) phi :
      funcfree phi -> FOL.sat (toFOLEnv rho2 H) (toFOLForm' phi) <-> Henkin.sat funcs preds rho2 phi.
    Proof.
      intros F. apply toFOLForm_correct_2To1. apply F. 
      apply toFOLEnv_correct_i. apply toFOLEnv_correct_p.
    Qed.

  End HenkinModel_To_FOModel.



  (** *** Translate First-Order Model to Henkin Model. *)

  Section FOModel_To_HenkinModel.

    Variable D1 : Type.
    Context {I1 : FOL.interp D1}.

    Definition D2 := D1.

    Definition funcs ar (f : vec D2 ar -> D2) := True.

    Definition preds ar (P : vec D2 ar -> Prop) :=
      exists d : D1, forall v, P v <-> i_atom (P:=PredApp ar) (d::v).

    Instance I2 : Tarski.interp D2 := {|
      Tarski.i_f f v := i_func (f:=NormalSym f) v ;
      Tarski.i_P P v := i_atom (P:=NormalPred P) v
    |}.

    Lemma toFOLTerm_correct_1To2 rho1 rho2 pos_i t :
      funcfreeTerm t
      -> (forall n, get_indi rho2 n = rho1 (pos_i n))
      -> Tarski.eval D2 rho2 t = FOL.eval rho1 (toFOLTerm pos_i t).
    Proof.
      intros F Hi. induction t; cbn.
      - apply Hi.
      - now exfalso.
      - f_equal. rewrite map_map. eapply map_ext_forall, Forall_ext_Forall. 
        apply IH. apply F.
    Qed.

    Ltac destruct_eq_dec := 
      repeat (cbn; try rewrite nat_eq_dec_same; cbn; try destruct PeanoNat.Nat.eq_dec as [->|]; try destruct PeanoNat.Nat.eq_dec as [<-|]).

    Lemma toFOLForm_correct_1To2 rho1 rho2 pos_i pos_p phi :
      funcfree phi
      -> (forall n, get_indi rho2 n = rho1 (pos_i n))
      -> (forall n ar, forall v, get_pred rho2 n ar v <-> i_atom (P:=PredApp ar) (rho1 (pos_p n ar) :: v))
      -> FOL.sat rho1 (toFOLForm pos_i pos_p phi) <-> Henkin.sat funcs preds rho2 phi.
    Proof.
      revert rho1 rho2 pos_i pos_p. induction phi; intros rho1 rho2 pos_i pos_p F Hi Hp; cbn.
      - reflexivity.
      - destruct p; cbn.
        + rewrite <- Hp. assert (forall x y, x = y -> x <-> y) as X by now intros x y ->. apply X; clear X. 
          f_equal. rewrite !map_map. eapply map_ext_forall, Forall_in. intros t H.
          erewrite <- toFOLTerm_correct_1To2. reflexivity.
          eapply Forall_in in F. apply F. easy. apply Hi.
        + assert (forall x y, x = y -> x <-> y) as X by now intros x y ->. apply X; clear X.
          f_equal. rewrite !map_map. eapply map_ext_forall, Forall_in. intros t H.
          erewrite <- toFOLTerm_correct_1To2. reflexivity.
          eapply Forall_in in F. apply F. easy. apply Hi.
      - destruct F as [F1 F2]. specialize (IHphi1 rho1 rho2 pos_i pos_p F1 Hi Hp);
        specialize (IHphi2 rho1 rho2 pos_i pos_p F2 Hi Hp). destruct b; cbn; tauto.
      - destruct q; cbn; split.
        + intros H d. eapply IHphi. 4: apply (H d). easy. intros []. all: trivial; apply Hi.
        + intros H d. eapply IHphi. 4: apply (H d). easy. intros []. all: trivial; apply Hi.
        + intros [d H]. exists d. eapply IHphi. 4: apply H. easy. intros []. all: trivial; apply Hi.
        + intros [d H]. exists d. eapply IHphi. 4: apply H. easy. intros []. all: trivial; apply Hi.
      - now exfalso.
      - destruct q; cbn; split.
          + intros H P [d Hd]. eapply IHphi. 4: apply (H d). 3: intros [] ar'; destruct_eq_dec. all: try easy.
          + intros H d. eapply IHphi. 4: apply (H (fun v => @i_atom Σf1 Σp1 _ _ (PredApp n) (d::v))).
            4: now exists d. 3: intros [] ar'; cbn; destruct_eq_dec. all: easy.
          + intros [d H]. exists (fun v => @i_atom Σf1 Σp1 _ _ (PredApp n) (d::v)).
            eexists. now exists d. eapply IHphi. 4: apply H. 3: intros [] ar'; cbn; destruct_eq_dec. all: easy.
          + intros [f [[d Hd] H]]. exists d. eapply IHphi. 4: apply H. 3: intros [] ar'; cbn; destruct_eq_dec. all: easy.
    Qed.

    Definition toSOLEnv rho1 := 
      ⟨ fun n => rho1 (initial_pos_i n), 
        fun _ ar v => rho1 0,
        fun n ar v => i_atom (P:=PredApp ar) (rho1 (initial_pos_p n ar) :: v) ⟩.

    Lemma toSOLEnv_henkin_env rho1 :
      henkin_env funcs preds (toSOLEnv rho1).
    Proof.
      intros n ar. split. easy. now exists (rho1 (initial_pos_p n ar)).
    Qed.

    Lemma toFOLForm_correct_1To2' rho1 phi :
      funcfree phi -> FOL.sat rho1 (toFOLForm' phi) <-> Henkin.sat funcs preds (toSOLEnv rho1) phi.
    Proof.
      intros F. apply toFOLForm_correct_1To2. apply F. reflexivity. reflexivity.
    Qed.

    Lemma constructed_henkin_model_comprehension rho1 :
      (forall phi, toFOLTheory C phi -> FOL.sat rho1 phi) -> forall rho2, (forall x ar, preds ar (get_pred rho2 x ar)) -> forall n phi, funcfree phi -> Henkin.sat funcs preds rho2 (comprehension_form n phi).
    Proof.
      intros H rho2 Hrho2 n phi F. apply close_sat_funcfree with (rho := toSOLEnv rho1).
      - apply comprehension_form_funcfree, F.
      - intros x ar'. unfold preds. eexists. cbn. reflexivity.
      - apply toFOLForm_correct_1To2'.
        + apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree, F.
        + apply H. eexists. split. reflexivity. now exists n, phi.
      - apply Hrho2.
    Qed.

    Lemma constructed_henkin_interp_correct rho :
      (forall x ar, preds ar (get_pred rho x ar)) -> (forall phi, C phi -> Henkin.sat funcs preds rho phi) -> henkin_interp I2 funcs preds.
    Proof.
      intros Hrho HC. split. easy.
      intros P. unfold preds. assert (Henkin.sat funcs preds rho (close All (comprehension_form (ar_preds P) (atom (pred P) (tabulate (ar_preds P) var_indi))))) as H1.
      { apply HC. eexists. eexists. split. 2: reflexivity. now apply tabulate_Forall. }
      eapply close_sat_funcfree with (sigma := rho) in H1.
      - apply comprehension_form_correct in H1 as [P' [[d H1] H2]]. exists d.
        intros v. specialize (H2 v). cbn in H2. rewrite Deduction.eval_tabulate in H2.
        cbn. setoid_rewrite <- H2. setoid_rewrite H1. reflexivity.
      - now apply comprehension_form_funcfree, tabulate_Forall.
      - apply Hrho.
      - apply Hrho.
    Qed.

  End FOModel_To_HenkinModel.




  (** *** Full Translation of Validity *)

  Notation "A ∪ B" := (fun x => A x \/ B x) (at level 30).

  Definition validFO `{falsity_flag} (T : FOL.form -> Prop) phi :=
    forall D (I : FOL.interp D) rho, (forall psi, T psi -> FOL.sat rho psi) -> FOL.sat rho phi.

  Lemma henkin_valid_iff_firstorder_valid (T : SOL.form -> Prop) phi :
    funcfree phi -> (forall psi, T psi -> funcfree psi) -> Henkin.validT T phi <-> validFO (toFOLTheory (T ∪ C)) (toFOLForm' phi).
  Proof.
    intros F TF. split.
    - intros H D1 I1 rho1 HT. apply toFOLForm_correct_1To2'; trivial. apply H.
      + apply constructed_henkin_interp_correct with (rho := toSOLEnv _ rho1).
        * intros x ar. unfold preds. eexists. cbn. reflexivity.
        * intros psi' [? [? [? ->]]]. apply toFOLForm_correct_1To2'.
          now apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree.
          apply HT. eexists. split. reflexivity. right. eexists. eexists. split. 2: reflexivity. easy.
      + eapply constructed_henkin_model_comprehension. 
        intros psi' [? [->]]. apply HT. eexists. split. reflexivity. now right.
      + apply toSOLEnv_henkin_env.
      + intros psi H1. apply toFOLForm_correct_1To2'. now apply TF. apply HT. firstorder. 
    - intros H D2 I2 funcs preds HI HC rho2 H_rho2 HT.
      unshelve eapply toFOLForm_correct_2To1'; trivial.
      + exact (get_indi rho2 0).
      + intros ar. exists (get_pred rho2 0 ar). apply H_rho2.
      + apply H. intros psi [phi' [-> [|[ar [phi'' [HF ->]]]]]].
        * eapply toFOLForm_correct_2To1'. now apply TF. now apply HT.
        * eapply toFOLForm_correct_2To1'. now apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree.
          eapply close_sat_funcfree. now apply comprehension_form_funcfree. 
          intros x ar'. apply H_rho2. intros sigma H2. now apply HC.
  Qed.




  (** Completeness of derived deduction system *)

  Section DerivedCompleteness.

    Existing Instance FOL.falsity_on.

    Notation "T ⊩1 phi" := (FOL.tprv T phi) (at level 61).

    Definition tprv2_derived A phi := toFOLTheory (A ∪ C) ⊩1 toFOLForm' phi.
    Notation "A ⊩2' phi" := (tprv2_derived A phi) (at level 61).

    Hypothesis tprv1_sound : forall (T : FOL.form -> Prop) phi, T ⊩1 phi -> validFO T phi.
    Hypothesis tprv1_complete : forall T phi, validFO T phi -> T ⊩1 phi.

    Hypothesis Σp2_enumerable : enumerable__T Σp2.
    Hypothesis Σf2_enumerable : enumerable__T Σf2.
    Hypothesis Σp2_eq_dec : eq_dec Σp2.
    Hypothesis Σf2_eq_dec : eq_dec Σf2.

    Hypothesis tprv1_enumerable : enumerable__T Σf1 -> enumerable__T Σp1 -> forall T, enumerable T -> enumerable (FOL.tprv T).

    Lemma tprv2_derived_sound (T : SOL.form -> Prop) phi :
      funcfree phi -> (forall psi, T psi -> funcfree psi) -> T ⊩2' phi -> Henkin.validT T phi.
    Proof.
      intros ? ? H. now apply henkin_valid_iff_firstorder_valid, tprv1_sound, H.
    Qed.

    Lemma tprv2_derived_complete (T : SOL.form -> Prop) phi :
      funcfree phi -> (forall psi, T psi -> funcfree psi) -> Henkin.validT T phi -> T ⊩2' phi.
    Proof.
      intros ? ? H. now apply tprv1_complete, henkin_valid_iff_firstorder_valid, H.
    Qed.

    Lemma tprv2_derived_enumerable (T : SOL.form -> Prop) :
      enumerable T -> enumerable (tprv2_derived T).
    Proof.
      intros H. unfold tprv2_derived. apply enumerable_comp.
      - apply tprv1_enumerable, toFOLTheory_enumerable, enumerable_disj.
        now apply Sigma_f1_enumerable. now apply Sigma_p1_enumerable.
        apply H. now apply C_enumerable.
      - apply form_enumerable; trivial. apply enumT_binop. apply enumT_quantop.
      - apply FOL.dec_form. now apply Sigma_f1_eq_dec. now apply Sigma_p1_eq_dec.
        all: intros x y; unfold dec; decide equality.
    Qed.

  End DerivedCompleteness.





  (** ** Deductive Reduction *)


  (** *** Preliminaries *)

  Section ArityBoundedSubst.

    Context {Σf2' : SOL.funcs_signature}.
    Context {Σp2' : SOL.preds_signature}.

    Definition subst_all_below_ar_p (sigma : nat -> forall ar, predicate ar) ar := 
      fun n ar' => if Compare_dec.lt_dec ar' ar then sigma n ar' else var_pred n.

    Definition subst_all_from_ar_p (sigma : nat -> forall ar, predicate ar) ar := 
      fun n ar' => if Compare_dec.lt_dec ar' ar then var_pred n else sigma n ar'.

    Lemma subst_all_below_ar_bounded b phi sigma :
      arity_bounded_p b phi -> phi[subst_all_below_ar_p sigma b]p = phi[sigma]p.
    Proof.
      intros B. eapply subst_ext_p_arity_bounded. apply B.
      intros x ar H. unfold subst_all_below_ar_p.
      now destruct Compare_dec.lt_dec; try lia.
    Qed.

    Lemma subst_all_from_ar_bounded b phi sigma :
      arity_bounded_p b phi -> phi[subst_all_from_ar_p sigma b]p = phi.
    Proof.
      intros B. erewrite <- subst_id_p. eapply subst_ext_p_arity_bounded. apply B.
      intros x ar H. unfold subst_all_from_ar_p.
      now destruct Compare_dec.lt_dec; try lia.
    Qed.

  End ArityBoundedSubst.


  (** Closing operation for predicate variables *)

  Section ClosePredicateAr.

    Context {Σf2' : SOL.funcs_signature}.
    Context {Σp2' : SOL.preds_signature}.

    Fixpoint close_p op phi n := match n with 0 => phi | S n => SOL.quant_pred op n (close_p op phi n) end.

    Lemma close_p_subst_i op phi sigma n :
      (close_p op phi n)[sigma]i = close_p op (phi[sigma]i) n.
    Proof.
      revert sigma. induction n; intros sigma; cbn. reflexivity. now rewrite IHn.
    Qed.

    Lemma close_p_subst_f op phi sigma n :
      (close_p op phi n)[sigma]f = close_p op (phi[sigma]f) n.
    Proof.
      revert sigma. induction n; intros sigma; cbn. reflexivity. now rewrite IHn.
    Qed.

    Definition all_up_p sigma : nat -> forall ar, predicate ar := 
      fun n ar => match n with 0 => var_pred 0 | S n => (sigma n ar)[↑ ar]p end.

    Lemma close_p_subst_p op phi sigma n :
      (close_p op phi n)[sigma]p = close_p op (phi[subst_all_below_ar_p (all_up_p sigma) n]p[subst_all_from_ar_p sigma n]p) n.
    Proof.
      rewrite subst_comp_p. revert sigma. induction n; intros sigma.
      - apply subst_ext_p. intros n ar. unfold subst_all_below_ar_p, subst_all_from_ar_p. 
        now destruct Compare_dec.lt_dec; try lia.
      - cbn. f_equal. rewrite IHn. f_equal. apply subst_ext_p. intros [] ar;
        unfold subst_all_from_ar_p, subst_all_below_ar_p;
        repeat (destruct Compare_dec.lt_dec, Compare_dec.lt_dec; try lia; try reflexivity; cbn).
        all: unfold up_p, scons, scons_pred, scons_ar, shift, shift_p;
        repeat (destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try easy; cbn).
        + destruct sigma; cbn; try easy. now destruct PeanoNat.Nat.eq_dec as [->|]; try lia.
        + destruct n0; repeat (destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try easy; cbn);
          destruct sigma; cbn; try reflexivity; repeat (try rewrite nat_eq_dec_same; 
          try destruct PeanoNat.Nat.eq_dec as [->|]; try destruct Compare_dec.lt_dec; try lia; try reflexivity; cbn).
        + destruct Compare_dec.lt_dec; try lia. destruct sigma; cbn; try easy. rewrite nat_eq_dec_same. 
          cbn. now destruct Compare_dec.lt_dec.
        + destruct sigma; cbn; try reflexivity. now destruct PeanoNat.Nat.eq_dec; try lia.
    Qed.

    Lemma close_p_subst_p' op phi sigma n :
      (close_p op phi n)[sigma]p = close_p op (phi[fun x ar => if Compare_dec.lt_dec ar n then match x with 0 => var_pred 0 ar | S x => (sigma x ar)[↑ ar]p end else sigma x ar]p) n.
    Proof.
      rewrite close_p_subst_p, subst_comp_p. f_equal. apply subst_ext_p.
      intros [] ar; destruct Compare_dec.lt_dec; cbn; unfold subst_all_below_ar_p, subst_all_from_ar_p;
      repeat (destruct Compare_dec.lt_dec; try lia; try reflexivity; cbn).
      unfold shift, shift_p. destruct sigma; cbn; try reflexivity. rewrite nat_eq_dec_same; cbn.
      now destruct Compare_dec.lt_dec.
    Qed.

    Lemma close_p_subst_p_bounded op b phi sigma :
      (arity_bounded_p b phi) -> (close_p op phi b)[sigma]p = close_p op (phi[all_up_p sigma]p) b.
    Proof.
      intros B. rewrite close_p_subst_p. f_equal. rewrite subst_all_from_ar_bounded.
      apply subst_all_below_ar_bounded. apply B. apply arity_bounded_p_subst_p, B.
    Qed.

    Lemma close_p_bounded_indi n b op phi :
      bounded_indi b phi -> bounded_indi b (close_p op phi n).
    Proof.
      now induction n.
    Qed.

    Lemma close_p_bounded_pred m ar b op phi :
      bounded_pred ar b phi -> bounded_pred ar b (close_p op phi m).
    Proof.
      revert b. induction m; intros b H; cbn.
      - exact H.
      - destruct (PeanoNat.Nat.eq_dec ar m).
        + left. split. easy. apply IHm. eapply bounded_pred_up. 2: apply H. lia.
        + right. split. easy. now apply IHm.
    Qed.

    Lemma close_p_bounded_pred_2 m ar b op phi :
      ar < m -> bounded_pred ar (S b) phi -> bounded_pred ar b (close_p op phi m).
    Proof.
      revert b. induction m; intros b H1 H2; cbn.
      - lia.
      - destruct (PeanoNat.Nat.eq_dec ar m).
        + left. split. easy. apply close_p_bounded_pred, H2.
        + right. split. easy. apply IHm. lia. apply H2.
    Qed.

    Lemma close_p_arity_bounded ar phi op n :
      arity_bounded_p ar phi -> arity_bounded_p ar (close_p op phi n).
    Proof.
      now induction n. 
    Qed.

    Lemma close_p_find_arity_bound_p op phi n :
      find_arity_bound_p (close_p op phi n) = find_arity_bound_p phi.
    Proof.
      now induction n.
    Qed.


    (* Deduction *)

    Definition shift_p_all : nat -> forall ar, predicate ar := fun n ar => var_pred (S n).

    Definition subst_first_p_all (P : forall ar, predicate ar) : nat -> forall ar, predicate ar := 
      fun n ar => match n with 0 => P ar | S n => var_pred n end.

    Notation "⇑" := shift_p_all.
    Notation "P ,," := (subst_first_p_all P) (at level 4, format "P ,,").

    Lemma close_p_AllI {p' : peirce} A phi n :
      List.map (subst_p (subst_all_below_ar_p ⇑ n)) A ⊢2 phi -> A ⊢2 close_p All phi n.
    Proof.
      revert A. induction n; intros A H; cbn.
      - enough (List.map (subst_p (subst_all_below_ar_p ⇑ 0)) A = A) as <- by apply H.
        clear H. induction A as [|psi A IH]; cbn. reflexivity. f_equal. rewrite <- subst_id_p.
        now apply subst_ext_p. apply IH.
      - apply AllI_p. apply IHn. rewrite List.map_map.
        enough (List.map (subst_form_p (↑ n) >> subst_p (subst_all_below_ar_p ⇑ n)) A = List.map (subst_p (subst_all_below_ar_p ⇑ (S n))) A) as -> by apply H.
        apply List.map_ext. intros psi. change (subst_form_p (↑ n) psi) with (psi[↑ n]p). 
        rewrite subst_comp_p. apply subst_ext_p. intros n' ar. unfold subst_all_below_ar_p, shift, shift_p.
        now destruct Compare_dec.lt_dec, PeanoNat.Nat.eq_dec; cbn; destruct Compare_dec.lt_dec; try lia.
    Qed.

    Lemma close_p_AllI_nameless' {p' : peirce} phi A b n :
      arity_bounded_p n phi
      -> (forall ar, ar < n -> bounded_pred_L ar b A)
      -> (forall ar, ar < n -> bounded_pred ar b phi)
      -> A ⊢2 phi[(@var_pred _ b),,]p
      -> A ⊢2 close_p All phi n.
    Proof.
      intros B B1. erewrite <- subst_all_below_ar_bounded. 2: apply B. clear B. 
      revert phi. induction n; intros phi B2 H; cbn.
      - enough (phi = phi[subst_all_below_ar_p (@var_pred _ b),, 0]p) as -> by apply H.
        rewrite <- subst_id_p at 1. apply subst_ext_p. intros n ar'. unfold subst_all_below_ar_p.
        now destruct Compare_dec.lt_dec; try lia.
      - apply AllI_p, nameless_equiv_all_p' with (n0:=b). apply B1. lia. apply close_p_bounded_pred.
        eapply bounded_pred_up. 2: apply B2. lia. lia. rewrite close_p_subst_p'. apply IHn.
        + intros ar H1 psi H2. apply B1. lia. exact H2.
        + intros ar H1. apply bounded_pred_subst_p. 2: apply B2; lia. 
          intros []; destruct Compare_dec.lt_dec; try easy. destruct n0; cbn;
          unfold subst_all_below_ar_p, shift, shift_p;
          now repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn).
        + rewrite subst_comp_p. erewrite subst_ext_p. apply H.
          intros [] ar; cbn; unfold subst_all_below_ar_p, shift, shift_p;
          repeat (try destruct Compare_dec.lt_dec; try destruct PeanoNat.Nat.eq_dec as [->|]; cbn; try lia; try reflexivity).
          destruct n0; cbn; repeat (try destruct Compare_dec.lt_dec; try destruct PeanoNat.Nat.eq_dec as [|]; cbn; try lia; try reflexivity).
    Qed.

    Lemma close_p_AllI_nameless {p' : peirce} phi A n :
      arity_bounded_p n phi -> { x | A ⊢2 phi[(@var_pred _ x),,]p -> A ⊢2 close_p All phi n }.
    Proof.
      intros B. enough { b | forall ar, ar < n -> bounded_pred_L ar b A /\ bounded_pred ar b phi } as [x H].
      { exists x. apply close_p_AllI_nameless'. apply B. apply H. apply H. }
      clear B. induction n.
      - exists 0. intros ar H; lia.
      - destruct IHn as [b H]. destruct (find_bounded_pred_L n (List.cons phi A)) as [b' H3].
        exists (max b b'). intros ar H1. assert (ar < n \/ ar = n) as [H2| ->] by lia.
        + split. intros psi' H4. all: eapply bounded_pred_up; [| apply H]; try lia; easy.
        + split. intros psi' H4. all: eapply bounded_pred_up; [| apply H3]; try lia; firstorder.
    Qed.


    Lemma close_p_AllE phi {p' : peirce} A n P :
      arity_bounded_p n phi -> A ⊢2 close_p All phi n -> A ⊢2 phi[P,,]p.
    Proof.
      intros B. erewrite <- subst_all_below_ar_bounded. 2: apply B. 
      clear B. induction n in phi |-*; cbn; intros H.
      - erewrite subst_ext_p, subst_id_p. apply H. reflexivity.
      - apply AllE_p with (P0 := P n) in H. rewrite close_p_subst_p' in H.
        apply IHn in H. rewrite subst_comp_p in H. erewrite subst_ext_p. apply H.
        intros [] ar; cbn; unfold subst_all_below_ar_p;
        repeat (try destruct Compare_dec.lt_dec; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn);
        destruct P; try reflexivity; cbn;
        destruct n0; cbn; unfold shift, shift_p; repeat (try destruct Compare_dec.lt_dec; 
        try destruct PeanoNat.Nat.eq_dec as [|]; try lia; try reflexivity; cbn).
    Qed.

    Lemma close_p_ExE_nameless' {p' : peirce} phi psi A b n :
      (forall ar, ar < n -> bounded_pred_L ar b A) 
      -> (forall ar, ar < n -> bounded_pred ar b phi)
      -> (forall ar, ar < n -> bounded_pred ar b psi)
      -> A ⊢2 close_p Ex phi n 
      -> phi[subst_all_below_ar_p (@var_pred _ b),, n]p :: A ⊢2 psi
      -> A ⊢2 psi.
    Proof.
      induction n in A, phi |-*; intros B1 B2 B3 H1 H2; cbn in *.
      - eapply IE. apply II, H2. enough (phi = phi[subst_all_below_ar_p (@var_pred _ b),, 0]p) as <- by apply H1.
        rewrite <- subst_id_p at 1. apply subst_ext_p. intros n ar'. unfold subst_all_below_ar_p.
        now destruct Compare_dec.lt_dec; try lia.
      - eapply ExE_p. apply H1. eapply nameless_equiv_ex_p' with (n0:=b).
        + apply B1. lia.
        + apply B3. lia.
        + eapply bounded_pred_up. 2: apply close_p_bounded_pred, B2. lia. lia.
        + eapply IHn. 4: rewrite <- close_p_subst_p' with (sigma := (var_pred b n)..).
          * intros ar H phi' [<-|]. apply bounded_pred_subst_p.
            now intros []; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
            apply close_p_bounded_pred, B2. lia. apply B1. lia. easy.
          * intros ar H. apply bounded_pred_subst_p. intros []; destruct Compare_dec.lt_dec; try lia.
            reflexivity. now destruct n0; cbn; destruct PeanoNat.Nat.eq_dec; try lia; unfold shift, shift_p; cbn;
            destruct PeanoNat.Nat.eq_dec; try lia. apply B2. lia.
          * intros. apply B3. lia.
          * apply Ctx. now left.
          * rewrite subst_comp_p. erewrite subst_ext_p with (tau := subst_all_below_ar_p (@var_pred _ b),, (S n)). 
            eapply Weak. 2: apply H2. clear -H2; firstorder.
            intros [|] ar; unfold subst_all_below_ar_p, shift, shift_p; destruct Compare_dec.lt_dec; cbn;
            repeat (try destruct Compare_dec.lt_dec; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn).
            destruct n0; cbn; repeat (destruct PeanoNat.Nat.eq_dec; try lia; cbn);
            now destruct Compare_dec.lt_dec; try lia.
    Qed.

    Lemma close_p_ExE_nameless {p' : peirce} phi psi A n :
      arity_bounded_p n phi -> A ⊢2 close_p Ex phi n -> { x | phi[(@var_pred _ x),,]p :: A ⊢2 psi -> A ⊢2 psi }.
    Proof.
      intros B. enough { b | (forall ar, ar < n -> (forall phi, List.In phi A -> bounded_pred ar b phi) /\ bounded_pred ar b phi /\ bounded_pred ar b psi) } as [x H].
      { exists x. erewrite <- subst_all_below_ar_bounded. 2: apply B. apply close_p_ExE_nameless'; firstorder. }
      clear B. induction n.
      - exists 0. intros ar H; lia.
      - destruct IHn as [b H]. destruct (find_bounded_pred_L n (List.cons phi (List.cons psi A))) as [b' H3].
        exists (max b b'). intros ar H1. assert (ar < n \/ ar = n) as [H2| ->] by lia.
        + repeat split. intros psi' H4. all: eapply bounded_pred_up; [| apply H]; try lia; easy.
        + repeat split. intros psi' H4. all: eapply bounded_pred_up; [| apply H3]; try lia; firstorder.
    Qed.

    Lemma close_p_ExI {p' : peirce} A phi n P :
      arity_bounded_p n phi -> A ⊢2 phi[P,,]p -> A ⊢2 close_p Ex phi n.
    Proof.
      intros B. erewrite <- subst_all_below_ar_bounded. 2: apply B.
      clear B. induction n in phi |-*; cbn; intros H.
      - erewrite <- subst_id_p, subst_ext_p. apply H. intros n ar. unfold subst_all_below_ar_p.
        now destruct Compare_dec.lt_dec; try lia.
      - apply ExI_p with (P0:=P n). rewrite close_p_subst_p'. apply IHn.
        erewrite subst_comp_p, subst_ext_p. apply H.
        intros [] ar; cbn; unfold subst_all_below_ar_p;
        repeat (try destruct Compare_dec.lt_dec; try destruct PeanoNat.Nat.eq_dec as [->|]; try lia; try reflexivity; cbn);
        destruct P; cbn; try reflexivity. now destruct Compare_dec.lt_dec.
        all: destruct n0; cbn; unfold shift, shift_p; repeat (try destruct Compare_dec.lt_dec; 
        try destruct PeanoNat.Nat.eq_dec as [|]; try lia; try reflexivity; cbn).
    Qed.

  End ClosePredicateAr.

  Notation "⇑" := shift_p_all.
  Notation "P ,," := (subst_first_p_all P) (at level 4, format "P ,,").



  (** Add falsity symbol to signature *)

  Inductive ExtendedPreds :=
    | OldPred : SOL.preds -> ExtendedPreds
    | FalsePred : nat -> ExtendedPreds.

  Instance Σp2' : SOL.preds_signature := {|
    SOL.preds := ExtendedPreds ;
    SOL.ar_preds P := match P with OldPred P => SOL.ar_preds P | FalsePred ar => ar end
  |}.


  (** *** Removal of Falsity Symbols *)

  Fixpoint removeFalsePred (phi : @SOL.form Σf2 Σp2' _) : @SOL.form Σf2 Σp2 _ := match phi with
    | SOL.atom (pred (OldPred p)) v => SOL.atom (pred p) v
    | SOL.atom (pred (FalsePred ar)) v => SOL.fal
    | SOL.atom (var_pred x ar) v => SOL.atom (var_pred x ar) v
    | SOL.fal => SOL.fal
    | SOL.bin op phi psi => SOL.bin op (removeFalsePred phi) (removeFalsePred psi)
    | SOL.quant_indi op phi => SOL.quant_indi op (removeFalsePred phi)
    | SOL.quant_func op ar phi => SOL.quant_func op ar (removeFalsePred phi)
    | SOL.quant_pred op ar phi => SOL.quant_pred op ar (removeFalsePred phi)
  end.


  Lemma removeFalsePred_subst_i phi sigma :
    (removeFalsePred phi)[sigma]i = removeFalsePred (phi[sigma]i).
  Proof.
    induction phi in sigma |- *; cbn; try congruence. now destruct p as [|[]].
  Qed.

  Lemma removeFalsePred_subst_f phi sigma :
    (removeFalsePred phi)[sigma]f = removeFalsePred (phi[sigma]f).
  Proof.
    induction phi in sigma |- *; cbn; try congruence. now destruct p as [|[]].
  Qed.

  Lemma removeFalsePred_subst_p phi sigma sigma' :
    (forall n ar, (exists x, sigma n ar = var_pred x /\ sigma' n ar = var_pred x) 
               \/ exists P (e : ar_preds P = ar), sigma n ar = Util.cast _ e (pred P) /\ sigma' n ar = Util.cast _ e (pred (OldPred P))) 
    -> (removeFalsePred phi)[sigma]p = removeFalsePred (phi[sigma']p).
  Proof. 
    induction phi in sigma, sigma' |- *; cbn; intros H.
    - reflexivity.
    - destruct p as [|[]]; cbn; try reflexivity. now destruct (H n ar) as [[x [-> ->]]|[P [<- [-> ->]]]].
    - erewrite IHphi1, IHphi2. reflexivity. apply H. apply H.
    - erewrite IHphi. reflexivity. apply H.
    - erewrite IHphi. reflexivity. apply H.
    - erewrite IHphi. reflexivity. intros [] ar; cbn.
      + destruct PeanoNat.Nat.eq_dec as [->|]. left. now exists 0. edestruct H as [[x [-> ->]]|[P [<- [-> ->]]]].
        * left. exists x; cbn. unfold shift, shift_p. now destruct PeanoNat.Nat.eq_dec.
        * right. now exists P, eq_refl.
      + destruct PeanoNat.Nat.eq_dec as [->|]; edestruct H as [[x [-> ->]]|[P [<- [-> ->]]]].
        * left. exists (S x). cbn; unfold shift, shift_p; now destruct PeanoNat.Nat.eq_dec.
        * right. now exists P, eq_refl.
        * left. exists x. cbn; unfold shift, shift_p; now destruct PeanoNat.Nat.eq_dec.
        * right. now exists P, eq_refl.
  Qed.

  Lemma removeFalsePred_forall_n n phi :
    removeFalsePred (forall_n n phi) = forall_n n (removeFalsePred phi).
  Proof.
    induction n; cbn; congruence.
  Qed.

  Lemma removeFalsePred_close_p op phi n :
    removeFalsePred (close_p op phi n) = close_p op (removeFalsePred phi) n.
  Proof.
    induction n; cbn. reflexivity. now rewrite IHn.
  Qed.

  Lemma removeFalsePred_arity_bounded_p phi n :
    arity_bounded_p n phi <-> arity_bounded_p n (removeFalsePred phi).
  Proof.
    induction phi. 2: now destruct p as [|[]]. all: firstorder.
  Qed.

  Lemma removeFalsePred_funcfree phi :
    funcfree phi -> funcfree (removeFalsePred phi).
  Proof.
    intros F. induction phi; cbn; firstorder. now destruct p as [|[]]; cbn.
  Qed.

  Lemma replace_FalsePred_subst {p' : peirce} (phi : @SOL.form Σf2 Σp2' _) ar n :
    List.nil ⊢2 (forall_n ar (p$n (tabulate ar var_indi) <--> ⊥)) --> (removeFalsePred phi[(@pred Σp2' (FalsePred ar))..]p <--> (removeFalsePred phi)[(var_pred n ar)..]p).
  Proof.
    enough (forall sigma1 sigma2 n m, 
                 sigma1 m ar = pred (FalsePred ar)
              -> sigma2 m ar = var_pred n ar
              -> (forall x ar', x <> m \/ ar' <> ar -> exists y, sigma1 x ar' = var_pred y /\ sigma2 x ar' = var_pred y)
              -> List.nil ⊢2 (forall_n ar (p$n (tabulate ar var_indi) <--> ⊥)) --> (removeFalsePred phi[sigma1]p <--> (removeFalsePred phi)[sigma2]p)) as X.
    { apply X with (m:=0); cbn -[PeanoNat.Nat.eq_dec].
      - now rewrite nat_eq_dec_same.
      - now rewrite nat_eq_dec_same.
      - intros x ar' [].
        + destruct x; try lia; cbn. destruct PeanoNat.Nat.eq_dec as [->|]; now eexists.
        + exists x. destruct x; cbn; now destruct PeanoNat.Nat.eq_dec as [->|]. }
    induction phi; cbn; intros sigma1 sigma2 n' m H1 H2 H3; apply II.
    - apply CI; apply II; apply Ctx; now left.
    - destruct p as [|[]]; cbn. 2,3: apply CI; apply II; apply Ctx; now left.
      specialize (H3 n0 ar0). destruct (PeanoNat.Nat.eq_dec n0 m) as [->|].
      + destruct (PeanoNat.Nat.eq_dec ar0 ar) as [->|].
        * rewrite H1, H2.
          Existing Instance Σp2. (* TODO: Better way to locally force the usage of Σp2 ? *)
          assert (forall_n ar (p$n' (tabulate ar var_indi) <--> ⊥) :: List.nil ⊢2forall_n ar (p$n' (tabulate ar var_indi) <--> ⊥)) as H by now apply Ctx.
          eapply prv_forall_n in H. cbn in H. rewrite tabulate_var_indi_subst in H.
          apply prv_equiv_symmetry, H.
        * destruct H3 as [? [-> ->]]. lia. apply CI; apply II; apply Ctx; now left.
      + destruct H3 as [? [-> ->]]. lia. apply CI; apply II; apply Ctx; now left.
    - apply prv_equiv_bin; apply switch_imp. eapply IHphi1; eassumption. eapply IHphi2; eassumption.
    - apply prv_equiv_quant_i. cbn. setoid_rewrite comprehension_subst_i with (phi0 := ⊥).
      eapply switch_imp, IHphi; eassumption.
    - apply prv_equiv_quant_f. cbn. setoid_rewrite comprehension_subst_f with (phi0 := ⊥). 
      eapply switch_imp, IHphi; eassumption.
    - apply prv_equiv_quant_p. cbn. destruct (PeanoNat.Nat.eq_dec n0 ar) as [->|].
      + setoid_rewrite forall_n_subst_p. cbn. unfold shift, shift_p. rewrite nat_eq_dec_same.
        apply switch_imp. eapply IHphi with (m := S m); cbn. now rewrite nat_eq_dec_same, H1.
        rewrite nat_eq_dec_same, H2; cbn; unfold shift, shift_p; now rewrite nat_eq_dec_same.
        intros x ar' [].
        * destruct x; cbn; destruct PeanoNat.Nat.eq_dec as [->|]. now exists 0.
          all: edestruct H3 as [? [-> ->]]; try lia; cbn; unfold shift, shift_p;  
          destruct PeanoNat.Nat.eq_dec; try lia; now eexists.
        * destruct x; cbn; destruct PeanoNat.Nat.eq_dec; try lia; edestruct H3 as [? [-> ->]]; try lia; 
          cbn; unfold shift, shift_p; destruct PeanoNat.Nat.eq_dec; try lia; now eexists.
      + setoid_rewrite forall_n_subst_p. cbn. unfold shift, shift_p. destruct PeanoNat.Nat.eq_dec; try lia.
        apply switch_imp. eapply IHphi with (m := m); cbn. destruct m; cbn; destruct PeanoNat.Nat.eq_dec; try lia;
        now rewrite H1. destruct m; cbn; destruct PeanoNat.Nat.eq_dec; try lia; rewrite H2; cbn;
        unfold shift, shift_p; now destruct PeanoNat.Nat.eq_dec.
        intros x ar' [].
        * destruct x; cbn; destruct PeanoNat.Nat.eq_dec as [->|]. now exists 0.
          all: edestruct H3 as [? [-> ->]]; try lia; cbn; unfold shift, shift_p;  
          destruct PeanoNat.Nat.eq_dec; try lia; now eexists.
        * destruct x; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try lia. now exists 0.
          all: edestruct H3 as [? [-> ->]]; try lia; cbn; unfold shift, shift_p;  
          destruct PeanoNat.Nat.eq_dec; try lia; now eexists.
  Qed.

  Lemma prv_removeFalsePred {p' : peirce} A (phi : @SOL.form Σf2 Σp2' _) :
    A ⊢2 phi -> (List.map removeFalsePred A) ⊢2 (removeFalsePred phi).
  Proof.
    induction 1; cbn in *.
    - apply II, IHprv.
    - eapply IE. apply IHprv1. apply IHprv2.
    - apply Exp, IHprv.
    - apply Ctx, List.in_map, H.
    - apply CI. apply IHprv1. apply IHprv2.
    - eapply CE1, IHprv.
    - eapply CE2, IHprv.
    - apply DI1, IHprv.
    - apply DI2, IHprv.
    - eapply DE. apply IHprv1. apply IHprv2. apply IHprv3.
    - apply Peirce.
    - apply AllI_i. rewrite List.map_map in *. erewrite List.map_ext. apply IHprv.
      intros ?. apply removeFalsePred_subst_i.
    - apply AllI_f. rewrite List.map_map in *. erewrite List.map_ext. apply IHprv.
      intros ?. apply removeFalsePred_subst_f.
    - apply AllI_p. rewrite List.map_map in *. erewrite List.map_ext. apply IHprv.
      intros ?. apply removeFalsePred_subst_p. intros n ar'. left. destruct (PeanoNat.Nat.eq_dec ar ar').
      all: eexists; unfold shift, shift_p; now destruct PeanoNat.Nat.eq_dec.
    - rewrite <- removeFalsePred_subst_i. eapply AllE_i, IHprv.
    - rewrite <- removeFalsePred_subst_f. eapply AllE_f, IHprv.
    - destruct P as [|[]].
      + erewrite <- removeFalsePred_subst_p. eapply AllE_p with (P:=var_pred n), IHprv. 
        intros [] ar'; cbn; left; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|]; eexists; split; reflexivity.
      + erewrite <- removeFalsePred_subst_p. eapply AllE_p with (P:=pred p0), IHprv.
        intros [] ar; cbn -[PeanoNat.Nat.eq_dec]; destruct PeanoNat.Nat.eq_dec as [<-|].
        right. now exists p0, eq_refl. all: left; now eexists.
      + eapply ExE_p with (ar := n). apply Comp with (phi0:=⊥). easy.
        destruct (find_bounded_pred_L n ((removeFalsePred phi[(@pred Σp2' (FalsePred n))..]p :: (forall_n n (p$0 (tabulate n var_indi) <--> ⊥[↑ n]p)) :: List.map removeFalsePred A))) as [b Hb].
        eapply nameless_equiv_ex_p' with (n0 := b).
        * intros ? ?. apply Hb. auto.
        * apply Hb. auto.
        * eapply bounded_pred_up. 2: apply Hb. lia. firstorder.
        * eapply IE. eapply CE2. apply switch_imp. eapply Weak; revgoals.
          rewrite forall_n_subst_p; cbn. destruct PeanoNat.Nat.eq_dec as [[]|]; try easy.
          eapply replace_FalsePred_subst. firstorder.
          eapply AllE_p in IHprv. eapply Weak. 2: apply IHprv. firstorder.
    - eapply ExI_i. rewrite removeFalsePred_subst_i. apply IHprv.
    - eapply ExI_f. rewrite removeFalsePred_subst_f. apply IHprv.
    - destruct P as [|[]].
      + eapply ExI_p. erewrite removeFalsePred_subst_p. apply IHprv.
        intros [] ar'; cbn; left; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|]; eexists; split; reflexivity.
      + eapply ExI_p. erewrite removeFalsePred_subst_p. apply IHprv.
        intros [] ar; cbn -[PeanoNat.Nat.eq_dec]; destruct PeanoNat.Nat.eq_dec as [<-|].
        right. now exists p0, eq_refl. all: left; now eexists.
      + eapply ExE_p with (ar := n). eapply Comp with (phi0:=⊥). easy.
        destruct (find_bounded_pred_L n ((removeFalsePred phi) :: (forall_n n (p$0 (tabulate n var_indi) <--> ⊥[↑ n]p) :: (List.map removeFalsePred A)))) as [b Hb].
        eapply nameless_equiv_ex_p' with (n0 := b).
        * intros ? ?. apply Hb. auto.
        * cbn. left. split. reflexivity. eapply bounded_pred_up. 2: apply Hb. lia. firstorder.
        * eapply bounded_pred_up. 2: apply Hb. lia. firstorder.
        * eapply ExI_p. eapply IE. eapply CE1. apply switch_imp. eapply Weak; revgoals.
          rewrite forall_n_subst_p; cbn. destruct PeanoNat.Nat.eq_dec as [[]|]; try easy.
          eapply replace_FalsePred_subst with (n0:=b). firstorder.
          eapply Weak. 2: apply IHprv. firstorder.
    - eapply ExE_i. apply IHprv1. rewrite removeFalsePred_subst_i. rewrite List.map_map in *. 
      erewrite List.map_ext. apply IHprv2. intros ?. apply removeFalsePred_subst_i.
    - eapply ExE_f. apply IHprv1. rewrite removeFalsePred_subst_f. rewrite List.map_map in *. 
      erewrite List.map_ext. apply IHprv2. intros ?. apply removeFalsePred_subst_f.
    - eapply ExE_p. apply IHprv1. erewrite removeFalsePred_subst_p. rewrite List.map_map in *. 
      erewrite List.map_ext. apply IHprv2. intros ?. eapply removeFalsePred_subst_p.
      all: intros n ar'; left; destruct (PeanoNat.Nat.eq_dec ar ar'); eexists; unfold shift, shift_p; 
      destruct PeanoNat.Nat.eq_dec; try lia; split; reflexivity.
    - rewrite removeFalsePred_forall_n. cbn. erewrite <- removeFalsePred_subst_p. apply Comp.
      now apply removeFalsePred_funcfree. intros n ar'. left.
      destruct (PeanoNat.Nat.eq_dec ar ar'); eexists; unfold shift, shift_p; 
      destruct PeanoNat.Nat.eq_dec; try lia; split; reflexivity.
  Qed.




  (** *** Backwards Translation Function *)

  Existing Instance Σp2'.

  Fixpoint toSOLTerm (t : FOL.term) := match t with 
    | FOL.var x => SOL.var_indi x
    | FOL.func (NormalSym f) v => SOL.func (sym f) (Vector.map toSOLTerm v)
  end.

  Fixpoint toSOLForm {ff : falsity_flag} (phi : FOL.form) : @SOL.form Σf2 Σp2' _ := match phi with
    | FOL.atom (NormalPred p) v => SOL.atom (@pred Σp2' (OldPred p)) (Vector.map toSOLTerm v)
    | FOL.atom (PredApp ar) v => match Vector.hd v with
                                  | FOL.var x => SOL.atom (var_pred x) (Vector.tl (Vector.map toSOLTerm v))
                                  | _ => SOL.atom (@pred Σp2' (FalsePred _)) (Vector.tl (Vector.map toSOLTerm v)) 
                                end
    | FOL.falsity => SOL.fal
    | FOL.bin op phi psi => SOL.bin (toSOLBinop op) (toSOLForm phi) (toSOLForm psi)
    | FOL.quant op phi => (close_p (toSOLQuantop op) (quant_indi (toSOLQuantop op) (toSOLForm phi)) (find_arity_bound_p (toSOLForm phi)))
  end.

  Definition toSOLSub_i (sigma : nat -> FOL.term) := fun n => toSOLTerm (sigma n).
  Definition toSOLSub_p (sigma : nat -> FOL.term) := fun n ar => match sigma n with FOL.var x => var_pred  x ar | _ => pred (FalsePred _) end.



  (** Substitutions *)

  Lemma toSOLTerm_subst {ff: falsity_flag} t sigma :
    (toSOLTerm t)[toSOLSub_i sigma]i = toSOLTerm (FOL.subst_term sigma t).
  Proof.
    induction t using FOL_term_ind; cbn.
    - reflexivity.
    - destruct F; cbn; f_equal. rewrite !Vector.map_map. apply VectorLib.map_ext_forall, IH.
  Qed.

  Lemma toSOLForm_subst {ff: falsity_flag} phi sigma :
    (toSOLForm phi)[toSOLSub_p sigma]p[toSOLSub_i sigma]i = toSOLForm (phi`[sigma]).
  Proof.
    revert sigma; induction phi; intros sigma; cbn.
    - reflexivity.
    - destruct P; cbn.
      + f_equal. rewrite !Vector.map_map. apply map_ext_forall, Forall_in. intros t' H.
        apply toSOLTerm_subst.
      + depelim t; destruct h; cbn; unfold toSOLSub_p. destruct (sigma n0).
        all: f_equal; rewrite !Vector.map_map; eapply VectorLib.map_ext_in; intros t' H;
        apply toSOLTerm_subst.
    - f_equal; firstorder.
    - f_equal. rewrite <- IHphi. rewrite close_p_subst_p_bounded, close_p_subst_i. 2: cbn; apply find_arity_bound_p_correct.
      cbn. f_equal. erewrite subst_ext_i, subst_ext_p. reflexivity.
      + intros [] ar; cbn. reflexivity. unfold toSOLSub_p, shift, shift_p, up, ">>'", FOL.scons. 
        destruct sigma; cbn. now rewrite nat_eq_dec_same. reflexivity.
      + intros []; cbn. reflexivity. now setoid_rewrite <- toSOLTerm_subst.
      + now rewrite <- find_arity_bound_p_subst_i, <- find_arity_bound_p_subst_p.
  Qed.


  (** Boundedness *)

  Hypothesis Σf2_eq_dec : forall f1 f2 : Σf2, f1 = f2 \/ f1 <> f2.
  Hypothesis Σp2_eq_dec : forall p1 p2 : Σp2, p1 = p2 \/ p1 <> p2.

  Lemma toSOLTerm_bounded_indi {ff : falsity_flag} t b :
    bounded_t b t -> bounded_indi_term b (toSOLTerm t).
  Proof.
    intros H. induction t using FOL_term_ind; cbn.
    - now inversion H.
    - destruct F; cbn. rewrite Forall_map. eapply Forall_ext_Forall. apply IH.
      apply Forall_in. intros t H1. inversion H. apply inj_pairT2 in H3 as ->.
      apply H2. now apply In_compat. decide equality.
  Qed.

  Lemma toSOLForm_bounded_indi {ff : falsity_flag} phi b :
    bounded b phi -> bounded_indi b (toSOLForm phi).
  Proof.
    revert b. induction phi; intros b' H; cbn.
    - easy.
    - inversion H. apply inj_pairT2 in H4 as ->. 2: decide equality; lia.
      destruct P; cbn. 2: depelim t; destruct h; cbn.
      all: apply Forall_in; intros ? [t' [<- H4]]%In_map_iff; apply toSOLTerm_bounded_indi;
      apply H3. now apply In_compat. all: constructor; now apply In_compat.
    - inversion H. apply inj_pairT2 in H1 as ->, H5 as ->. split. now apply IHphi1.
      now apply IHphi2. all: decide equality.
    - inversion H. apply inj_pairT2 in H4 as ->. 2: decide equality. 
      now apply close_p_bounded_indi, IHphi.
  Qed.

  Lemma toSOLForm_bounded_pred {ff : falsity_flag} phi b :
    bounded b phi -> forall ar, bounded_pred ar b (toSOLForm phi).
  Proof.
    revert b. induction phi; intros b' H ar; cbn.
    - easy.
    - destruct P; cbn. easy. depelim t; destruct h; cbn. left. inversion H.
      apply inj_pairT2 in H4 as ->. specialize (H3 (FOL.var n0) ltac:(constructor)). now inversion H3.
      decide equality. lia. easy.
    - inversion H. apply inj_pairT2 in H1 as ->, H5 as ->. split. now apply IHphi1.
      now apply IHphi2. all: decide equality.
    - inversion H. apply inj_pairT2 in H4 as ->. 2: decide equality.
      destruct (Compare_dec.lt_dec ar (find_arity_bound_p (toSOLForm phi))) as [H4|H4].
      + apply close_p_bounded_pred_2. easy. apply IHphi, H3.
      + eapply bounded_pred_arity_bound. apply close_p_arity_bounded, find_arity_bound_p_correct. 
        cbn. lia.
  Qed.



  (** *** Translation of Derivations *)

  (** Translate first-order derivation into second-order derivation *)

  Lemma prv1_to_prv2_AllI {ff : falsity_flag} {p' : peirce} A phi :
    List.map toSOLForm (List.map (subst_form ↑') A) ⊢2 toSOLForm phi -> List.map toSOLForm A ⊢2 toSOLForm (∀' phi).
  Proof.
    destruct (find_bounded_L (phi :: A)) as [x Hx].
    intros H. apply subst_Weak_p with (sigma := toSOLSub_p (var x)..') in H.
    apply subst_Weak_i with (sigma := toSOLSub_i (var x)..') in H.
    erewrite !List.map_map, toSOLForm_subst, List.map_ext with (g := toSOLForm) in H; revgoals.
    { intros psi. setoid_rewrite toSOLForm_subst. now rewrite subst_shift. }
    cbn. eapply close_p_AllI_nameless' with (b := x).
    - cbn. apply find_arity_bound_p_correct.
    - intros ar H1 ? [psi [<- H2]]%List.in_map_iff. apply toSOLForm_bounded_pred. apply Hx; auto.
    - intros ar H1. apply toSOLForm_bounded_pred. apply Hx; auto.
    - cbn; eapply AllI_i, nameless_equiv_all_i' with (n := x).
      + intros ? [psi [<- H1]]%List.in_map_iff. apply toSOLForm_bounded_indi. apply Hx; auto.
      + apply bounded_indi_subst_p. eapply bounded_indi_up. 2: apply toSOLForm_bounded_indi, Hx; auto. lia.
      + erewrite subst_ext_p, subst_ext_i, toSOLForm_subst. apply H. now intros []. now intros [].
    - now intros [].
  Qed.

  Lemma prv1_to_prv2_AllE {ff : falsity_flag} {p' : peirce} A phi (t : FOL.term) :
    List.map toSOLForm A ⊢2 toSOLForm (∀' phi) -> List.map toSOLForm A ⊢2 toSOLForm phi`[t..'].
  Proof.
    cbn. intros H. apply close_p_AllE with (P := fun ar => match t with FOL.var x => var_pred x | _ => @pred Σp2' (FalsePred ar) end) in H.
    cbn in H. eapply AllE_i with (t0 := toSOLTerm t) in H. rewrite <- toSOLForm_subst.
    erewrite subst_ext_i, subst_ext_p. apply H.
    - intros [] ar; cbn. now destruct t. reflexivity. 
    - now intros [].
    - cbn. apply find_arity_bound_p_correct.
  Qed.

  Lemma prv1_to_prv2_ExI {ff : falsity_flag} {p' : peirce} A phi (t : FOL.term) :
    List.map toSOLForm A ⊢2 toSOLForm phi`[t..'] -> List.map toSOLForm A ⊢2 toSOLForm (∃' phi).
  Proof.
    cbn. intros H. apply close_p_ExI with (P := fun ar => match t with FOL.var x => var_pred x | _ => @pred Σp2' (FalsePred ar) end); cbn. 
    apply find_arity_bound_p_correct. apply ExI_i with (t0 := toSOLTerm t).
    rewrite <- toSOLForm_subst in H. erewrite subst_ext_i, subst_ext_p_arity_bounded. 
    apply H.
    + apply find_arity_bound_p_correct.
    + intros [] ar H1; unfold toSOLSub_p, subst_all_below_ar_p; cbn. now destruct t. reflexivity.
    + now intros [].
  Qed.

  Lemma prv1_to_prv2_ExE {ff : falsity_flag} {p' : peirce} A phi psi :
    List.map toSOLForm A ⊢2 toSOLForm (∃' phi) -> List.map toSOLForm (phi :: List.map (subst_form ↑') A) ⊢2 toSOLForm psi`[↑'] -> List.map toSOLForm A ⊢2 toSOLForm psi.
  Proof.
    intros H1 H2. apply subst_Weak_p with (sigma := toSOLSub_p (var (proj1_sig (find_bounded_L (phi::psi::A))))..') in H2.
    apply subst_Weak_i with (sigma := toSOLSub_i (var (proj1_sig (find_bounded_L (phi::psi::A))))..') in H2.  cbn in H2.
    erewrite !List.map_map, toSOLForm_subst, subst_shift, List.map_ext with (g := toSOLForm) in H2; revgoals.
    { intros psi'. setoid_rewrite toSOLForm_subst. now rewrite subst_shift. }
    setoid_rewrite toSOLForm_subst in H2.
    cbn in H1. eapply close_p_ExE_nameless' with (b := proj1_sig (find_bounded_L (phi :: psi :: A))). 4: apply H1.
    + intros ar H3 ? [phi' [<- H4]]%List.in_map_iff. apply toSOLForm_bounded_pred. 
      destruct find_bounded_L as [b H5]; cbn. apply H5. firstorder.
    + intros ar H3. apply toSOLForm_bounded_pred. destruct find_bounded_L as [b H4]; cbn.
      apply H4. firstorder.
    + intros ar H3. apply toSOLForm_bounded_pred. destruct find_bounded_L as [b H4]; cbn.
      apply H4. firstorder.
    + cbn. eapply ExE_i. apply Ctx. now left. eapply nameless_equiv_ex_i' with (n := proj1_sig (find_bounded_L (phi :: psi :: A))).
      * intros ? [<-|[phi' [<- H3]]%List.in_map_iff].
        -- apply bounded_indi_subst_p. destruct find_bounded_L as [b H3]; cbn in *.
           eapply bounded_indi_up. 2: apply toSOLForm_bounded_indi, H3. lia. firstorder.
        -- destruct find_bounded_L as [b H4]; cbn in *. apply toSOLForm_bounded_indi, H4. firstorder.
      * destruct find_bounded_L as [b H3]; cbn in *. apply toSOLForm_bounded_indi, H3. firstorder.
      * apply bounded_indi_subst_p. destruct find_bounded_L as [b H3]; cbn in *.
        eapply bounded_indi_up. 2: apply toSOLForm_bounded_indi, H3. lia. firstorder.
      * rewrite <- toSOLForm_subst in H2. erewrite subst_ext_p_arity_bounded, subst_ext_i. 
        eapply Weak. 2: apply H2. intros ? [<-|]. now left. firstorder.
        -- now intros [].
        -- apply find_arity_bound_p_correct.
        -- now intros [] ar H; unfold subst_all_below_ar_p; destruct Compare_dec.lt_dec; try lia.
    + now intros [].
  Qed.

  Existing Instance class.

  Lemma prv1_to_prv2 {ff : falsity_flag} phi A :
    A ⊢1 phi -> (List.map toSOLForm A) ⊢2 toSOLForm phi.
  Proof.
    intros H. induction H.
    - apply II, IHprv.
    - eapply IE. apply IHprv1. apply IHprv2.
    - apply prv1_to_prv2_AllI, IHprv.
    - apply prv1_to_prv2_AllE, IHprv.
    - eapply prv1_to_prv2_ExI, IHprv.
    - eapply prv1_to_prv2_ExE. apply IHprv1. apply IHprv2.
    - eapply Exp, IHprv.
    - now apply Ctx, List.in_map.
    - apply CI. apply IHprv1. apply IHprv2.
    - eapply CE1, IHprv.
    - eapply CE2, IHprv.
    - eapply DI1, IHprv.
    - eapply DI2, IHprv.
    - eapply DE. apply IHprv1. apply IHprv2. apply IHprv3.
    - apply Peirce.
  Qed.



  (** *** Forwards-Backwards Equivalence *)

  (** Properties of combined fowrards- and backwards-translation *)

  Lemma toSOLFOLForm_find_arity_bound_p pos_i pos_p pos_i' pos_p' phi :
    find_arity_bound_p (toSOLForm (toFOLForm pos_i pos_p phi)) = find_arity_bound_p (toSOLForm (toFOLForm pos_i' pos_p' phi)).
  Proof.
    induction phi in pos_i, pos_p, pos_i', pos_p' |- *; cbn.
    - reflexivity.
    - now destruct p.
    - now erewrite IHphi1, IHphi2.
    - rewrite !close_p_find_arity_bound_p; cbn. apply IHphi.
    - reflexivity.
    - rewrite !close_p_find_arity_bound_p; cbn. apply IHphi.
  Qed.

  (** The pos functions can be moved into a substitution *)

  Lemma toSOLFOLTerm_pos_i_to_subst t pos_i :
    funcfreeTerm t
    -> toSOLTerm (toFOLTerm pos_i t) = (toSOLTerm (toFOLTerm (fun n => n) t))[pos_i >> var_indi]i.
  Proof.
    intros F. induction t; cbn in *.
    - reflexivity.
    - now exfalso.
    - f_equal. rewrite !Vector.map_map. eapply map_ext_forall, Forall_ext_Forall. 
      apply IH. apply F.
  Qed.

  Lemma toSOLFOLForm_pos_i_to_subst phi pos_i pos_p :
    funcfree phi
    -> toSOLForm (toFOLForm pos_i pos_p phi) = (toSOLForm (toFOLForm (fun n => n) pos_p phi))[pos_i >> var_indi]i.
  Proof.
    induction phi in pos_i, pos_p |-*; cbn; intros F.
    - reflexivity.
    - destruct p; cbn; f_equal; rewrite !Vector.map_map; eapply map_ext_in; intros t H;
      apply toSOLFOLTerm_pos_i_to_subst; eapply Forall_in in F; try apply F; easy.
    - now rewrite IHphi1, IHphi2.
    - rewrite close_p_subst_i; cbn. f_equal. f_equal. 2: apply toSOLFOLForm_find_arity_bound_p.
      rewrite IHphi, IHphi with (pos_i := pcons (fun n => n)); try easy.
      rewrite subst_comp_i. apply subst_ext_i. now intros [].
    - reflexivity.
    - rewrite close_p_subst_i; cbn. f_equal. f_equal. 2: apply toSOLFOLForm_find_arity_bound_p.
      rewrite IHphi, IHphi with (pos_i := pshift (fun n => n)); try easy.
      rewrite subst_comp_i. apply subst_ext_i. now intros [].
  Qed.

  Lemma toSOLFOLForm_pos_p_to_subst phi pos_i pos_p :
    funcfree phi
    -> toSOLForm (toFOLForm pos_i pos_p phi) = (toSOLForm (toFOLForm pos_i (fun n _ => n) phi))[fun x ar => var_pred (pos_p x ar)]p.
  Proof.
    induction phi in pos_i, pos_p |-*; cbn; intros F.
    - reflexivity.
    - now destruct p.
    - now rewrite IHphi1, IHphi2.
    - rewrite close_p_subst_p_bounded; cbn. 2: apply find_arity_bound_p_correct.
      f_equal. f_equal. 2: apply toSOLFOLForm_find_arity_bound_p.
      rewrite IHphi, IHphi with (pos_p := pshift' (fun n _ => n)); try easy.
      rewrite subst_comp_p. eapply subst_ext_p. intros n ar; cbn. unfold shift, shift_p.
      now rewrite nat_eq_dec_same.
    - reflexivity.
    - rewrite close_p_subst_p_bounded; cbn. 2: apply find_arity_bound_p_correct.
      f_equal. f_equal. 2: apply toSOLFOLForm_find_arity_bound_p.
      rewrite IHphi, IHphi with (pos_p := pcons' n (fun n _ => n)); try easy.
      rewrite subst_comp_p. eapply subst_ext_p.
      intros [] ar; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; cbn; try reflexivity;
      unfold shift, shift_p; now rewrite nat_eq_dec_same.
  Qed.

  (** This allows us to 'undo' pshift and pcons *)

  Lemma toSOLFOLForm_pshift_subst_i phi pos_i pos_p t :
    funcfree phi
    -> (toSOLForm (toFOLForm (pshift pos_i) pos_p phi))[t..]i = toSOLForm (toFOLForm pos_i pos_p phi).
  Proof.
    intros F. rewrite toSOLFOLForm_pos_i_to_subst, toSOLFOLForm_pos_i_to_subst with (pos_i := pos_i); try easy.
    rewrite subst_comp_i. apply subst_ext_i. now intros [].
  Qed.

  Lemma toSOLFOLForm_pshift_subst_p phi pos_i pos_p P :
    funcfree phi
    -> (toSOLForm (toFOLForm pos_i (pshift' pos_p) phi))[P,,]p = toSOLForm (toFOLForm pos_i pos_p phi).
  Proof.
    intros F. rewrite toSOLFOLForm_pos_p_to_subst, toSOLFOLForm_pos_p_to_subst with (pos_p := pos_p); try easy.
    rewrite subst_comp_p. apply subst_ext_p. now intros [] ar.
  Qed.

  Lemma toSOLFOLForm_pcons_subst_p phi pos_i pos_p x n :
    funcfree phi
    -> (forall n ar, pos_p n ar = n)
    -> (toSOLForm (toFOLForm pos_i (pcons' n pos_p) phi))[(@var_pred _ x),,]p = (toSOLForm (toFOLForm pos_i  pos_p phi))[(var_pred x n)..]p.
  Proof.
    intros F. revert pos_p. enough (forall pos_p, (forall x ar, pos_p x ar = x) -> (toSOLForm (toFOLForm pos_i  (pcons' n pos_p) phi))[(@var_pred _ x),,]p = (toSOLForm (toFOLForm pos_i pos_p phi))[(var_pred x n)..]p) as X.
    { intros pos_p H. erewrite toFOLForm_ext_p with (pos_p' := pcons' n (fun x _ => x)), toFOLForm_ext_p with (pos_p:=pos_p). 
      apply X. reflexivity. intros ? ? _; apply H. intros [] ar; cbn; destruct PeanoNat.Nat.eq_dec. reflexivity.
      all: rewrite H; try easy. }
    intros pos_p Hp. rewrite toSOLFOLForm_pos_p_to_subst, toSOLFOLForm_pos_p_to_subst with (pos_p := pos_p); try easy.
    rewrite !subst_comp_p. apply subst_ext_p. intros [] ar; cbn;
    destruct PeanoNat.Nat.eq_dec as [->|]; cbn; rewrite !Hp; cbn;
    try rewrite nat_eq_dec_same; try destruct PeanoNat.Nat.eq_dec; try lia; reflexivity.
  Qed.



  (** ⊢2 proves the translation equivalent to the intitial formula *)

  Lemma toSOLFOLTerm_id pos_i t :
    funcfreeTerm t
    -> (forall n, pos_i n = n)
    -> toSOLTerm (toFOLTerm pos_i t) = t.
  Proof.
    intros F H. induction t; cbn.
    - rewrite H. reflexivity.
    - now exfalso.
    - f_equal. rewrite Vector.map_map, <- Vector.map_id.
      eapply map_ext_forall, Forall_ext_Forall. apply IH. apply F.
  Qed.

  Lemma toSOLFOLForm_equiv {p' : peirce} phi pos_i pos_p :
    funcfree phi
    -> (forall n, pos_i n = n)
    -> (forall n ar, pos_p n ar = n)
    -> List.nil ⊢2 (removeFalsePred (toSOLForm (toFOLForm pos_i pos_p phi))) <--> phi.
  Proof.
    revert pos_i pos_p.
    enough (forall pos_i pos_p, funcfree phi -> (forall n, pos_i n = n) -> (forall n ar, pos_p n ar = n) -> List.nil ⊢2 (removeFalsePred (toSOLForm (toFOLForm pos_i pos_p phi))) <--> phi) as X.
    { intros pos_i pos_p F Hi Hp. erewrite toFOLForm_ext_i, toFOLForm_ext_p; trivial. now apply X. }
    intros pos_i pos_p. induction phi in pos_i, pos_p |-*; intros F Hi Hp; cbn.
    - now apply CI; apply II; apply Ctx.
    - destruct p; cbn.
      + rewrite Hp. rewrite Vector.map_map. erewrite VectorLib.map_ext_in, Vector.map_id.
        now apply CI; apply II; apply Ctx. intros t H. apply toSOLFOLTerm_id.
        eapply Forall_in in F. apply F. easy. apply Hi.
      + rewrite Vector.map_map. erewrite VectorLib.map_ext_in, Vector.map_id.
        now apply CI; apply II; apply Ctx. intros t H. apply toSOLFOLTerm_id.
        eapply Forall_in in F. apply F. easy. apply Hi.
    - rewrite toSOLBinop_toFOLBinop. apply prv_equiv_bin.
      apply IHphi1; firstorder. apply IHphi2; firstorder.
    - rewrite removeFalsePred_close_p; destruct q; cbn.
      + apply CI.
        * apply II. eapply IE. eapply CE1. eapply Weak with (A := List.nil). easy.
          apply prv_equiv_quant_i. eapply IHphi with (pos_i := pcons pos_i) (pos_p := pos_p); try easy. 
          intros []; cbn. reflexivity. now rewrite Hi.
          erewrite <- toSOLFOLForm_pshift_subst_p with (pos_p := pos_p) (P := @var_pred _ 0), <- removeFalsePred_subst_p with (sigma := (@var_pred _ 0),,); try easy.
          change (∀i (removeFalsePred (toSOLForm (toFOLForm (pcons pos_i) (pshift' pos_p) phi)))[(@var_pred _ 0),,]p) with ((∀i (removeFalsePred (toSOLForm (toFOLForm (pcons pos_i) (pshift' pos_p) phi))))[(@var_pred _ 0),,]p).
          eapply close_p_AllE; revgoals. now apply Ctx. apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct.
          intros [] ar; left; now eexists.
        * apply II. edestruct (@close_p_AllI_nameless _ Σp2) as [x X]. 2: apply X; clear X.
          apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct. cbn.
          rewrite removeFalsePred_subst_p with (sigma' := (@var_pred _ x),,), toSOLFOLForm_pshift_subst_p; try easy.
          eapply IE. eapply CE2. eapply Weak with (A := List.nil). easy. apply prv_equiv_quant_i, IHphi; try easy.
          intros []; cbn. reflexivity. now rewrite Hi. now apply Ctx. intros [] ar; left; now eexists.
      + apply CI.
        * apply II. eapply IE. eapply CE1. eapply Weak with (A := List.nil). easy.
          apply prv_equiv_quant_i. eapply IHphi with (pos_i := pcons pos_i) (pos_p := pos_p); try easy. 
          intros []; cbn. reflexivity. now rewrite Hi.
          edestruct (@close_p_ExE_nameless _ Σp2) as [x X]; revgoals. apply X; clear X.
          erewrite <- toSOLFOLForm_pshift_subst_p with (pos_p := pos_p) (P := @var_pred _ x), <- removeFalsePred_subst_p with (sigma := (@var_pred _ x),,); try easy.
          change (∃i (removeFalsePred (toSOLForm (toFOLForm (pcons pos_i) (pshift' pos_p) phi)))[(@var_pred _ x),,]p) with ((∃i (removeFalsePred (toSOLForm (toFOLForm (pcons pos_i) (pshift' pos_p) phi))))[(@var_pred _ x),,]p).
          apply Ctx; now left. intros [] ar; left; now eexists. now apply Ctx.
          apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct.
        * apply II. apply close_p_ExI with (P := @var_pred _ 0).
          apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct. cbn.
          rewrite removeFalsePred_subst_p with (sigma' := (@var_pred _ 0),,), toSOLFOLForm_pshift_subst_p; try easy.
          eapply IE. eapply CE2. eapply Weak with (A := List.nil). easy. apply prv_equiv_quant_i, IHphi; try easy.
          intros []; cbn. reflexivity. now rewrite Hi. now apply Ctx. intros [] ar; left; now eexists.
    - now exfalso.
    - rewrite removeFalsePred_close_p; destruct q; cbn.
      + apply CI.
        * apply II. apply AllI_p. edestruct (@nameless_equiv_all_p _ Σp2) as [x ->].
          eapply IE. eapply CE1. eapply Weak with (A := List.nil). easy.
          apply prv_equiv_subst_p, IHphi with (pos_i := pos_i) (pos_p := pos_p); try easy. 
          rewrite removeFalsePred_subst_p with (sigma' := (var_pred x n)..).
          rewrite <- toSOLFOLForm_pcons_subst_p, <- toSOLFOLForm_pshift_subst_i with (pos_i := pos_i) (t := var_indi 0); try easy.
          rewrite <- removeFalsePred_subst_p with (sigma := (@var_pred _ x),,), <- removeFalsePred_subst_i, subst_switch_i_p.
          apply AllE_i. change (∀i (removeFalsePred (toSOLForm (toFOLForm (pshift pos_i) (pcons' n pos_p) phi)))[(@var_pred _ x),,]p) with ((removeFalsePred (∀i (toSOLForm (toFOLForm (pshift pos_i) (pcons' n pos_p) phi))))[(@var_pred _ x),,]p).
          eapply close_p_AllE; revgoals. now apply Ctx.
          cbn. apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct.
          intros [] ar; left; now eexists. intros [] ar; left; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; now eexists.
        * apply II. edestruct (@close_p_AllI_nameless _ Σp2) as [x X]. 2: apply X; clear X.
          apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct. cbn.
          rewrite removeFalsePred_subst_p with (sigma' := (@var_pred _ x),,), toSOLFOLForm_pcons_subst_p; try easy.
          apply AllI_i. edestruct (@nameless_equiv_all_i _ Σp2) as [y ->].
          rewrite removeFalsePred_subst_i, <- subst_switch_i_p, toSOLFOLForm_pshift_subst_i; try easy.
          rewrite <- removeFalsePred_subst_p with (sigma := (var_pred x n)..).
          eapply IE. eapply CE2. eapply Weak with (A := List.nil). easy. apply prv_equiv_subst_p, IHphi; try easy.
          now apply AllE_p, Ctx. intros [] ar; left; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; now eexists.
          intros [] ar; left; now eexists.
      + apply CI.
        * apply II. edestruct (@close_p_ExE_nameless _ Σp2) as [x X]. 3: apply X; clear X. 2: now apply Ctx. 
          cbn. apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct.
          eapply ExE_i. apply Ctx; cbn; now left. edestruct (@nameless_equiv_ex_i _ Σp2) as [y ->].
          apply ExI_p with (P := var_pred x).
          eapply IE. eapply CE1. eapply Weak with (A := List.nil). easy. apply prv_equiv_subst_p, IHphi; try easy.
          rewrite removeFalsePred_subst_p with (sigma := (var_pred x n)..) (sigma' := (var_pred x n)..).
          rewrite <- toSOLFOLForm_pcons_subst_p, <- toSOLFOLForm_pshift_subst_i with (pos_i := pos_i) (t := y); try easy.
          rewrite <- removeFalsePred_subst_p with (sigma := (@var_pred _ x),,), <- removeFalsePred_subst_i, subst_switch_i_p.
          now apply Ctx. intros [] ar; left; now eexists.
          intros [] ar; left; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; now eexists.
        * apply II. eapply ExE_p. now apply Ctx. edestruct (@nameless_equiv_ex_p _ Σp2) as [x ->].
          apply close_p_ExI with (P := @var_pred _ x); cbn. apply removeFalsePred_arity_bounded_p, find_arity_bound_p_correct.
          apply ExI_i with (t := var_indi 0).
          rewrite <- subst_switch_i_p, removeFalsePred_subst_i, removeFalsePred_subst_p with (sigma' := (@var_pred _ x),,). 
          rewrite toSOLFOLForm_pshift_subst_i, toSOLFOLForm_pcons_subst_p; try easy.
          rewrite <- removeFalsePred_subst_p with (sigma := (var_pred x n)..).
          eapply IE. eapply CE2. eapply Weak with (A := List.nil). easy. apply prv_equiv_subst_p, IHphi; try easy.
          now apply Ctx. intros [] ar; left; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; now eexists. 
          intros [] ar; left; now eexists.
  Qed.


  Definition initial_pos_i_inv n := pi2 n.
  Definition initial_pos_p_inv n := pi1 (pi2 n).

  Lemma initial_pos_i_inv_correct :
    forall n, initial_pos_i_inv (initial_pos_i n) = n.
  Proof.
    intros n. unfold initial_pos_i_inv, initial_pos_i. now rewrite pi2_correct.
  Qed.

  Lemma initial_pos_p_inv_correct :
    forall n ar, initial_pos_p_inv (initial_pos_p n ar) = n.
  Proof.
    intros n ar. unfold initial_pos_p_inv, initial_pos_p. now rewrite pi2_correct, pi1_correct.
  Qed.

  Lemma initial_pos_i_inv_subst phi :
    phi[initial_pos_i >> var_indi]i[initial_pos_i_inv >> var_indi]i = phi.
  Proof.
    rewrite subst_comp_i, <- subst_id_i. apply subst_ext_i. intros n; cbn.
    now rewrite initial_pos_i_inv_correct.
  Qed.

  Lemma initial_pos_p_inv_subst phi :
    phi[fun x ar => var_pred (initial_pos_p x ar)]p[fun x ar => var_pred (initial_pos_p_inv x)]p = phi.
  Proof.
    rewrite subst_comp_p, <- subst_id_p. apply subst_ext_p. intros n ar; cbn.
    now rewrite initial_pos_p_inv_correct.
  Qed.

  Definition toSOLForm' {ff : falsity_flag} phi := (toSOLForm phi)[fun x ar => var_pred (initial_pos_p_inv x)]p[initial_pos_i_inv >> var_indi]i.

  Lemma toSOLFOLForm'_correct phi :
    funcfree phi -> toSOLForm' (toFOLForm' phi) = toSOLForm (toFOLForm (fun n => n) (fun n ar => n) phi).
  Proof.
    intros F. unfold toFOLForm', toSOLForm'.
    rewrite toSOLFOLForm_pos_p_to_subst, toSOLFOLForm_pos_i_to_subst; trivial.
    now rewrite initial_pos_p_inv_subst, initial_pos_i_inv_subst.
  Qed.

  Lemma toSOLFOLForm_equiv' {p' : peirce} phi :
    funcfree phi -> List.nil ⊢2 (removeFalsePred (toSOLForm' (toFOLForm' phi))) <--> phi.
  Proof.
    intros F. unfold toFOLForm', toSOLForm'.
    rewrite toSOLFOLForm_pos_p_to_subst, toSOLFOLForm_pos_i_to_subst; trivial.
    rewrite initial_pos_p_inv_subst, initial_pos_i_inv_subst. now apply toSOLFOLForm_equiv.
  Qed.

  Lemma prv1_to_prv2' {ff : falsity_flag} phi A :
    A ⊢1 phi -> List.map removeFalsePred (List.map toSOLForm' A) ⊢2 removeFalsePred (toSOLForm' phi).
  Proof.
    intros H. apply prv_removeFalsePred. unfold toSOLForm'.
    rewrite <- List.map_map. apply subst_Weak_i. easy.
    rewrite <- List.map_map. apply subst_Weak_p.
    now apply prv1_to_prv2.
  Qed.



  (** *** Final Provability Reduction *)

  Existing Instance Σp2.

  Definition tprv1 {ff : falsity_flag} (T : FOL.form -> Prop) phi := exists A, (forall psi, List.In psi A -> T psi) /\ A ⊢1 phi.
  Definition tprv2 {p' : peirce} (T : SOL.form -> Prop) phi := exists A, (forall psi, List.In psi A -> T psi) /\ A ⊢2 phi.

  Notation "T ⊩1 phi" := (tprv1 T phi) (at level 61).
  Notation "T ⊩2 phi" := (tprv2 T phi) (at level 61).

  Lemma prv_ext {p' : peirce} phi A1 A2 :
    A1 ⊢2 phi -> (forall psi, List.In psi A1 -> A2 ⊢2 psi) -> A2 ⊢2 phi.
  Proof.
    induction A1 in phi |-*; cbn; intros H1 H2.
    - eapply Weak. 2: apply H1. easy.
    - eapply IE. apply IHA1.
      + apply II, H1.
      + intros ? ?. apply H2. auto.
      + apply H2. auto.
  Qed.

  Lemma tprv_ext {p' : peirce} phi (T1 T2 : form -> Prop) :
    T1 ⊩2 phi -> (forall psi, T1 psi -> T2 ⊩2 psi) -> T2 ⊩2 phi.
  Proof.
    intros [A [H1 H2]] H3. revert A H1 H2 H3. induction A in phi, T1 |-*; intros H1 H2 H3.
    - now exists List.nil.
    - enough (T2 ⊩2 a --> phi) as [B1 X]. 
      { destruct (H3 a) as [B2]. now apply H1. exists (List.app B1 B2). split.
        - intros ? [|]%List.in_app_iff. now apply X. now apply H.
        - eapply IE; eapply Weak. 2: apply X. apply List.incl_appl, List.incl_refl.
          2: apply H. apply List.incl_appr, List.incl_refl. }
      apply (IHA _ T1).
      + intros ? ?. apply H1. auto.
      + now apply II.
      + apply H3.
  Qed.

  Lemma prv_closed_comprehension {p' : peirce} ar phi :
    funcfree phi -> List.nil ⊢2 close All (comprehension_form ar phi).
  Proof.
    intros F. unfold close, close_indi. destruct find_bounded_indi as [n B]; cbn.
    clear B. induction n; cbn.
    - enough (forall m, List.nil ⊢2 close_pred'' m All (comprehension_form ar phi)) by easy.
      induction m; cbn. apply Comp. apply F. unfold close_pred'. destruct find_bounded_pred as [k B]; cbn.
      clear B. induction k; cbn. easy. now apply AllI_p.
    - now apply AllI_i.
  Qed.

  Lemma prv_if_firstorder_prv (T : SOL.form -> Prop) phi :
    funcfree phi -> (forall psi, T psi -> funcfree psi) -> toFOLTheory (T ∪ C) ⊩1 (toFOLForm' phi) -> T ⊩2 phi.
  Proof.
    intros F TF.
    intros [A [HT H%prv1_to_prv2']]. apply tprv_ext with (T1 := T ∪ C). 
    apply tprv_ext with (T1 := fun phi => exists psi, phi = removeFalsePred (toSOLForm' (toFOLForm' psi)) /\ (T ∪ C) psi).
    + exists (List.map removeFalsePred (List.map toSOLForm' A)). split.
      * intros psi [psi1 [<- [psi2 [<- H1]]%List.in_map_iff]]%List.in_map_iff.
        destruct (HT psi2) as [psi3 [-> [|]]]. easy. all: exists psi3; auto.
      * eapply IE. eapply CE1, Weak. 2: apply toSOLFOLForm_equiv'. all: easy.
    + intros ? [psi [-> [|[? [? [? ->]]]]]]. exists (List.cons psi List.nil). split.
      * intros ? [<-|[]]. auto.
      * eapply IE. eapply CE2, Weak. 2: apply toSOLFOLForm_equiv'. easy.
        now apply TF. now apply Ctx.
      * exists List.nil. split. easy. eapply IE. eapply CE2, toSOLFOLForm_equiv'.
        now apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree. 
        now apply prv_closed_comprehension.
    + intros psi [|[? [? [? ->]]]].
      * exists (List.cons psi List.nil). split. intros ? [<-|[]]. auto. now apply Ctx.
      * exists List.nil. split. easy. now apply prv_closed_comprehension.
  Qed.


  (** * Consequences of Reduction *)

  (** ** Completeness *)

  Section Completeness.

    Hypothesis prv1_complete : forall {ff : falsity_flag} T phi, validFO T phi -> T ⊩1 phi.

    Existing Instance class.

    Theorem Completeness (T : SOL.form -> Prop) phi : 
      funcfree phi -> (forall psi, T psi -> funcfree psi) -> Henkin.validT T phi -> T ⊩2 phi.
    Proof.
      intros F TF H.
      apply prv_if_firstorder_prv; trivial.
      apply prv1_complete, henkin_valid_iff_firstorder_valid; trivial.
    Qed.

    Lemma first_order_prv_if_prv_C (T : SOL.form -> Prop) phi :
      LEM -> funcfree phi -> (forall psi, T psi -> funcfree psi) -> T ⊩2 phi -> toFOLTheory (T ∪ C) ⊩1 (toFOLForm' phi).
    Proof.
      intros lem F TF. intros H. 
      apply prv1_complete, henkin_valid_iff_firstorder_valid; trivial.
      now apply Deduction.HenkinSoundnessCT.
    Qed.

    Theorem prv_iff_firstorder_prv_C  (T : SOL.form -> Prop) phi :
      LEM -> funcfree phi -> (forall psi, T psi -> funcfree psi) -> toFOLTheory (T ∪ C) ⊩1 (toFOLForm' phi) <-> T ⊩2 phi.
    Proof.
      intros lem F TF. split.
      - now apply prv_if_firstorder_prv.
      - now apply first_order_prv_if_prv_C.
    Qed.

  End Completeness.





  (** ** Compactness *)

  Existing Instance FOL.falsity_on.

  Definition has_henkin_model_with P (T : form ->  Prop) := 
    exists D (I : interp D) funcs preds,
      P D /\ henkin_interp I funcs preds 
      /\ (forall rho, (forall x ar, preds ar (get_pred rho x ar)) -> (forall ar phi, funcfree phi -> Henkin.sat funcs preds rho (comprehension_form ar phi)))
      /\ exists rho, henkin_env funcs preds rho 
          /\ forall phi, T phi -> Henkin.sat funcs preds rho phi.

  Definition has_firstorder_model_with (P : Type -> Prop) (T : FOL.form -> Prop) :=
      exists D I rho, P D /\ forall phi, T phi -> @FOL.sat _ _ D I _ rho phi.

  Definition has_henkin_model := has_henkin_model_with (fun _ => True).
  Definition has_firstorder_model := has_firstorder_model_with (fun _ => True).

  Lemma has_firstorder_model_with_ext (T T' : FOL.form -> Prop) P :  
    (forall phi, T' phi -> T phi) -> has_firstorder_model_with P T -> has_firstorder_model_with P T'.
  Proof.
    intros HT [D [I [rho [H1 H2]]]]. exists D, I, rho. split. easy. intros phi H3. apply H2, HT, H3.
  Qed.

  Lemma has_henkin_model_with_ext (T T' : form -> Prop) (P P' : Type -> Prop) :  
    (forall phi, T' phi -> T phi) -> (forall D, P D -> P' D) -> has_henkin_model_with P T -> has_henkin_model_with P' T'.
  Proof.
    intros HT HP [D [I [funcs [preds [HDP [HI [HCompr [rho [Hrho H1]]]]]]]]]. 
    exists D, I, funcs, preds. split. now apply HP. split. easy. split. easy.
    exists rho. split. easy. intros phi H2. apply H1, HT, H2.
  Qed.

  Lemma has_henkin_model_compr T P :
    has_henkin_model_with P T -> has_henkin_model_with P (T ∪ C).
  Proof.
    intros [D [I [funcs [preds [HP [HI [HCompr [rho [Hrho H]]]]]]]]].
    exists D, I, funcs, preds. split. easy. split. easy. split. easy.
    exists rho. split. easy. intros phi [|[? [? [? ->]]]].
    - now apply H.
    - apply close_sat_funcfree. now apply comprehension_form_funcfree.
      apply Hrho. intros sigma H1. now apply HCompr.
  Qed.

  Lemma theory_has_firstorder_model_if_theory_has_henkin_model (T : form -> Prop) (P P' : Type -> Prop) :
    (forall phi, T phi -> funcfree phi) 
    -> (forall D preds, P D -> P' (D1 D preds) : Prop) 
    -> has_henkin_model_with P T 
    -> has_firstorder_model_with P' (toFOLTheory T).
  Proof.
    intros TF HP [D [I [funcs [preds [HDP [HI [HCompr [rho [Hrho H1]]]]]]]]].
    do 3 eexists. split. apply (HP D). apply HDP. intros phi [psi [-> H3]].
    unshelve eapply toFOLForm_correct_2To1 with (rho2 := rho) (rho1 := toFOLEnv _ funcs preds rho Hrho) (funcs := funcs) (preds := preds).
    - exact (get_indi rho 0).
    - intros ar. exists (get_pred rho 0 ar). apply Hrho.
    - now apply TF.
    - intros n. unfold initial_pos_i, toFOLEnv. now rewrite unembed_embed.
    - intros n ar. unfold initial_pos_p, toFOLEnv. rewrite unembed_embed, pi1_correct, pi2_correct. 
      cbn. now rewrite nat_eq_dec_same.
    - now apply H1.
  Qed.

  Lemma theory_has_henkin_model_if_theory_has_firstorder_model (T : form -> Prop) (P : Type -> Prop) :
    (forall phi, T phi -> funcfree phi) 
    -> has_firstorder_model_with P (toFOLTheory (T ∪ C)) 
    -> has_henkin_model_with P T.
  Proof.
    intros TF [D [I [rho [HDP H1]]]]. exists (D2 D). do 3 eexists. split. 
    easy. split; revgoals. split; revgoals.
    exists (toSOLEnv _ rho). split; revgoals. intros phi H2.
    eapply toFOLForm_correct_1To2. 4: apply (H1 (toFOLForm' phi)).
    - now apply TF.
    - reflexivity.
    - reflexivity.
    - eexists. split. reflexivity. now left.
    - apply toSOLEnv_henkin_env.
    - intros rho2 H2 ar phi F. eapply close_sat_funcfree with (rho0 := toSOLEnv _ rho). 
      apply comprehension_form_funcfree, F. cbn. unfold preds. eexists. reflexivity.
      eapply toFOLForm_correct_1To2.
      4: apply (H1 (toFOLForm' (close All (comprehension_form ar phi)))).
      + apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree, F.
      + reflexivity.
      + reflexivity.
      + eexists. split. reflexivity. right. eexists. eexists. split. apply F. reflexivity.
      + apply H2.
    - eapply constructed_henkin_interp_correct with (rho := toSOLEnv _ rho).
      + intros x ar. eexists. cbn. reflexivity.
      + intros phi [? [? [F ->]]]. eapply toFOLForm_correct_1To2. 4: apply H1.
        * apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree, F.
        * reflexivity.
        * cbn. reflexivity.
        * eexists. split. reflexivity. right. eexists. eexists. split. apply F. reflexivity.
  Qed.


  Section CompactnessByCompleteness.

    Hypothesis prv1_complete : forall {ff : falsity_flag} T phi, validFO T phi -> T ⊩1 phi.

    Theorem Compactness_by_Completeness :
      LEM -> forall (T : form -> Prop), (forall phi, T phi -> funcfree phi) -> has_henkin_model T <-> forall A, (forall phi, List.In phi A -> T phi) -> has_henkin_model (fun phi => List.In phi A).
    Proof.
      intros lem T TF. split.
      - intros H1 A H2. eapply has_henkin_model_with_ext. 3: apply H1. easy. easy.
      - intros H1.  enough (~ T ⊩ ⊥) as HT.
        { edestruct lem as [X|H]. apply X. exfalso. apply HT.
          apply Completeness; cbn; trivial. intros D I funcs preds HI HC rho Hrho H2.
          apply H. exists D, I, funcs, preds. split. easy. split. easy. split. easy. 
          exists rho. split. easy. easy. }
        intros [A [H2 H3]]. apply HenkinSoundnessC in H3; trivial.
        destruct (H1 A) as [D [I [funcs [preds [HDP [HI [HCompr [rho [Hrho H4]]]]]]]]]; trivial. 
        eapply H3; eauto.
    Qed.

  End CompactnessByCompleteness.


  Section CompactnessByReduction.

    Lemma theory_decompose (T1 T2 : form -> Prop) A :
      (forall phi, List.In phi A -> (T1 ∪ T2) phi) -> exists B1 B2, (forall phi, List.In phi B1 -> List.In phi A /\ T1 phi) /\ (forall phi, List.In phi B2 -> List.In phi A /\ T2 phi) /\ (forall phi, List.In phi A -> List.In phi B1 \/ List.In phi B2).
    Proof.
      intros H. induction A; cbn.
      - exists List.nil, List.nil. firstorder.
      - destruct IHA as [B1 [B2 [H1 [H2 H3]]]]. firstorder. destruct (H a) as [H4|H4]; trivial.
        + exists (List.cons a B1), B2. split. 2: split.
          * clear -H1 H4. intros phi [->|]; firstorder.
          * clear -H2. firstorder.
          * clear -H3. intros ? [->|]; firstorder.
        + exists B1, (List.cons a B2). split. 2: split.
          * clear -H1. firstorder.
          * clear -H2 H4. intros phi [->|]; firstorder.
          * clear -H3. intros ? [->|]; firstorder.
    Qed.

    Hypothesis FOL_compact :
      forall (T : FOL.form -> Prop), has_firstorder_model T <-> forall A, (forall phi, List.In phi A -> T phi) -> has_firstorder_model (fun phi => List.In phi A).

    Theorem Compactness :
      forall (T : form -> Prop), (forall phi, T phi -> funcfree phi) -> has_henkin_model T <-> forall A, (forall phi, List.In phi A -> T phi) -> has_henkin_model (fun phi => List.In phi A).
    Proof.
      intros T TF. split.
      - intros [D [I [funcs [preds [_ [HI [HCompr [rho [Hrho H1]]]]]]]]] A H2.
        exists D, I, funcs, preds. split. easy. split. easy. split. easy. exists rho. 
        split. easy. intros phi H3. apply H1, H2, H3.
      - intros H1. apply theory_has_henkin_model_if_theory_has_firstorder_model; trivial.
        apply FOL_compact. intros A H2.
        assert (exists B, A = List.map toFOLForm' B /\ forall phi,  List.In phi B -> T phi \/ C phi) as [B [-> HB]].
        { clear -H2. induction A; cbn. now exists List.nil.
          destruct IHA as [B [-> H3]]; firstorder. destruct (H2 a) as [phi [-> ]]; trivial. 
          exists (List.cons phi B). split. reflexivity. intros psi [->|]. easy. now apply H3. }
        destruct (theory_decompose T C B) as [BT [BC [HB1 [HB2 HB3]]]]; trivial.
        apply has_firstorder_model_with_ext with (T := toFOLTheory (fun phi => List.In phi B)).
        intros ? [? [<- ?]]%List.in_map_iff. eexists. split. reflexivity. easy.
        eapply theory_has_firstorder_model_if_theory_has_henkin_model with (P := fun _ => True).
        { intros phi [[]%HB1 | [? [? [? [? ->]]]]%HB2]%HB3. now apply TF.
          now apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree. }
        easy. destruct (H1 BT) as [D [I [funcs [preds [_ [HI [HCompr [rho [Hrho H3]]]]]]]]]. apply HB1.
        exists D, I, funcs, preds. split. easy. split. easy. split. easy. exists rho. split. easy. 
        intros phi [|[H4 [? [? [H5 ->]]]]%HB2]%HB3.
        + now apply H3.
        + apply close_sat_funcfree. now apply comprehension_form_funcfree.
          apply Hrho. intros sigma H6. now apply HCompr.
    Qed.

  End CompactnessByReduction.


  (** ** Löwenheim-Skolem *)

  Section LöwenheimSkolem.

    Definition injects X Y := exists f : X -> Y, forall x x', f x = f x' -> x = x'.
    Definition infinite X := injects nat X.
    Definition same_cardinality X Y := injects X Y /\ injects Y X.

    Hypothesis FOL_LöwenheimSkolem :
      forall T, has_firstorder_model_with infinite T -> forall X, infinite X -> has_firstorder_model_with (same_cardinality X) T.

    Theorem LöwenheimSkolem (T : form -> Prop) :
      (forall phi, T phi -> funcfree phi) -> has_henkin_model_with infinite T -> forall X, infinite X -> has_henkin_model_with (same_cardinality X) T.
    Proof.
      intros TF H X HX.
      apply theory_has_henkin_model_if_theory_has_firstorder_model; trivial.
      apply FOL_LöwenheimSkolem; trivial.
      apply theory_has_firstorder_model_if_theory_has_henkin_model with (P := infinite).
      - intros phi [|[? [? [? ->]]]]. now apply TF.
        now apply close_indi_funcfree, close_pred_funcfree, comprehension_form_funcfree.
      - intros D preds [f Hf]. exists (fun n => fromIndi D preds (f n)).
        intros x x' H1. apply Hf. congruence.
      - apply has_henkin_model_compr. apply H.
    Qed.

  End LöwenheimSkolem.


End Signature.

