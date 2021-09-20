(** * Henkin Semantics *)

Require Import SOL.
Require Import FullSyntax.
Require Export Subst.
Require Export Util.
Require Import Vector.
Require Import VectorLib.
Require Import Tarski.
Require Import Arith.
Import SubstNotations.

Require Import Equations.Equations Equations.Prop.DepElim.
Derive Signature for Vector.t.

Require Import Lia.


Section Henkin.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Definition comprehension_form ar phi := ∃p(ar) (forall_n ar (p$0 (tabulate ar var_indi) <--> phi[↑ ar]p)).


  Section Semantics.

    Context {domain : Type}.
    Context {I : interp domain}.
    Variable funcIncluded : forall ar, (vec domain ar -> domain) -> Prop.
    Variable predIncluded : forall ar, (vec domain ar -> Prop) -> Prop.

    Fixpoint sat (rho : env domain) (phi : form) : Prop :=
      match phi with
      | atom P v => eval_predicate domain rho P (Vector.map (Tarski.eval domain rho) v)
      | fal => False
      | bin Impl phi psi => sat rho phi -> sat rho psi
      | bin Conj phi psi => sat rho phi /\ sat rho psi
      | bin Disj phi psi => sat rho phi \/ sat rho psi
      | quant_indi Ex phi => exists d : domain, sat ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ phi
      | quant_indi All phi => forall d : domain, sat ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ phi
      (* TODO: Why doesn't the scons type inference work? *)
      | quant_func Ex ar phi => exists f (Hf : funcIncluded ar f), sat ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ phi
      | quant_func All ar phi => forall f (Hf : funcIncluded ar f), sat ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ phi
      | quant_pred Ex ar phi => exists P (HP : predIncluded ar P), sat ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ phi
      | quant_pred All ar phi => forall P (HP : predIncluded ar P), sat ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ phi
      end.


    Definition henkin_interp := (forall f : syms, funcIncluded (ar_syms f) (i_f _ f)) /\ (forall P : preds, predIncluded (ar_preds P) (i_P _ P)).
    Definition henkin_env rho := forall n ar, funcIncluded ar (get_func rho n ar) /\ predIncluded ar (get_pred rho n ar).

    Lemma henkin_env_cons_f rho ar (f : vec domain ar -> domain):
      henkin_env rho -> funcIncluded ar f -> henkin_env ⟨get_indi rho, f .: get_func rho, get_pred rho⟩.
    Proof.
      intros H1 H2. split; cbn. 2: apply H1. unfold scons, scons_env_func, scons_ar.
      destruct n; destruct Nat.eq_dec as [->|]; try easy; apply H1.
    Qed.

    Lemma henkin_env_cons_p rho ar (P : vec domain ar -> Prop):
      henkin_env rho -> predIncluded ar P -> henkin_env ⟨get_indi rho, get_func rho, P .: get_pred rho⟩.
    Proof.
      intros H1 H2. split; cbn. apply H1. unfold scons, scons_env_pred, scons_ar.
      destruct n; destruct Nat.eq_dec as [->|]; try easy; apply H1.
    Qed.

    Lemma eval_function_included rho  ar (f : function ar) :
      henkin_interp -> henkin_env rho -> funcIncluded ar (eval_function _ rho f).
    Proof.
      intros HI Hrho. destruct f; cbn. apply Hrho. apply HI.
    Qed.

    Lemma eval_predicate_included rho ar (P : predicate ar) :
      henkin_interp -> henkin_env rho -> predIncluded ar (eval_predicate _ rho P).
    Proof.
      intros HI Hrho. destruct P; cbn. apply Hrho. apply HI.
    Qed.


    Lemma sat_ext rho1 rho2 phi :
      rho1 ≡ rho2 -> sat rho1 phi <-> sat rho2 phi.
    Proof.
      revert rho1 rho2. induction phi; cbn; intros rho1 rho2 H.
      - easy.
      - destruct p. 
        + enough (map (eval _ rho1) v = map (eval _ rho2) v) as <- by apply H.
          apply map_ext. induction v; firstorder. apply eval_ext; apply H.
        + enough (map (eval _ rho1) v = map (eval _ rho2) v) as <- by easy.
          apply map_ext. induction v; firstorder. apply eval_ext; apply H.
      - specialize (IHphi1 rho1 rho2); specialize (IHphi2 rho1 rho2).
        destruct b; tauto.
      - destruct q; split; cbn.
        + intros H1 x. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_i.
        + intros H1 x. eapply IHphi. 2: apply H1. now apply env_equiv_cons_i.
        + intros [d H1]. exists d. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_i.
        + intros [d H1]. exists d. eapply IHphi. 2: apply H1. now apply env_equiv_cons_i.
      - destruct q; split; cbn.
        + intros H1 f Hf. eapply IHphi. 2: apply (H1 _ Hf). now apply env_equiv_symm, env_equiv_cons_f.
        + intros H1 f Hf. eapply IHphi. 2: apply (H1 _ Hf). now apply env_equiv_cons_f.
        + intros [f [Hf H1]]. exists f, Hf. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_f.
        + intros [f [Hf H1]]. exists f, Hf. eapply IHphi. 2: apply H1. now apply env_equiv_cons_f.
      - destruct q; split; cbn.
        + intros H1 P HP. eapply IHphi. 2: apply (H1 _ HP). now apply env_equiv_symm, env_equiv_cons_p.
        + intros H1 P HP. eapply IHphi. 2: apply (H1 _ HP). now apply env_equiv_cons_p.
        + intros [P [HP H1]]. exists P, HP. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_p.
        + intros [P [HP H1]]. exists P, HP. eapply IHphi. 2: apply H1. now apply env_equiv_cons_p.
    Qed.

  End Semantics.


  (** Closed formulas *)

  Section Bounded.

    Context {domain : Type}.
    Context {I : interp domain}.
    Variable funcs : forall ar, (vec domain ar -> domain) -> Prop.
    Variable preds : forall ar, (vec domain ar -> Prop) -> Prop.

    Lemma sat_ext_bounded_term t rho sigma :
      (forall x, ~ bounded_indi_term x t -> get_indi rho x = get_indi sigma x)
      -> (forall x ar, ~ bounded_func_term ar x t -> get_func rho x ar = get_func sigma x ar)
      -> eval domain rho t = eval domain sigma t.
    Proof.
      intros H1 H2. induction t; cbn.
      - apply H1. cbn. lia.
      - rewrite H2. f_equal. apply VectorLib.map_ext_in. intros t H. eapply Forall_in in IH.
        apply IH. intros x H3. apply H1. cbn. intros H4. apply H3. eapply Forall_in in H4. 
        apply H4. trivial. intros x ar' H3. apply H2. cbn. intros [H4 H5]. apply H3. eapply Forall_in in H5.
        apply H5. easy. easy. cbn. lia.
      - f_equal. apply VectorLib.map_ext_in. intros t H. eapply Forall_in in IH.
        apply IH. intros x H3. apply H1. cbn. intros H4. apply H3. eapply Forall_in in H4. 
        apply H4. trivial. intros x ar' H3. apply H2. cbn. intros H4. apply H3. eapply Forall_in in H4.
        apply H4. easy. easy.
    Qed.

    Lemma sat_ext_bounded phi rho sigma :
      (forall x, ~ bounded_indi x phi -> get_indi rho x = get_indi sigma x)
      -> (forall x ar, ~ bounded_func ar x phi -> get_func rho x ar = get_func sigma x ar)
      -> (forall x ar, ~ bounded_pred ar x phi -> get_pred rho x ar = get_pred sigma x ar)
      -> sat funcs preds rho phi <-> sat funcs preds sigma phi.
    Proof.
      revert rho sigma. induction phi; cbn; intros rho sigma H1 H2 H3.
      - reflexivity.
      - erewrite VectorLib.map_ext_in with (g := eval domain sigma); revgoals.
        intros t H. apply sat_ext_bounded_term. intros x H4. apply H1. intros H5. apply H4.
        eapply Forall_in in H5. apply H5. easy. intros x ar' H4. apply H2. intros H5. apply H4.
        eapply Forall_in in H5. apply H5. easy. destruct p; cbn.
        + rewrite H3. reflexivity. cbn. lia.
        + reflexivity.
      - specialize (IHphi1 rho sigma). specialize (IHphi2 rho sigma).
        destruct b; cbn; setoid_rewrite IHphi1; try setoid_rewrite IHphi2; try reflexivity; clear IHphi1 IHphi2; firstorder.
      - destruct q; split.
        + intros H d. eapply IHphi. 4: apply (H d). intros []. all: firstorder.
        + intros H d. eapply IHphi. 4: apply (H d). intros []. all: firstorder.
        + intros [d H]. exists d. eapply IHphi. 4: apply H. intros []. all: firstorder.
        + intros [d H]. exists d. eapply IHphi. 4: apply H. intros []. all: firstorder.
      - destruct q; split.
        + intros H f Hf. eapply IHphi. 4: eapply (H f); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros H f Hf. eapply IHphi. 4: eapply (H f); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [f [Hf H]]. exists f, Hf. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [f [Hf H]]. exists f, Hf. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      - destruct q; split.
        + intros H P HP. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros H P HP. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [P [HP H]]. exists P, HP. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [P [HP H]]. exists P, HP. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
    Qed.

    Lemma sat_ext_p_arity_bounded rho rho_p phi b :
      arity_bounded_p b phi
      -> (forall x ar, ar < b -> forall v, get_pred rho x ar v <-> rho_p x ar v) 
      -> sat funcs preds rho phi <-> Henkin.sat funcs preds ⟨get_indi rho, get_func rho, rho_p⟩ phi.
    Proof.
      induction phi in rho, rho_p |-*; cbn; intros B Hrho.
      - reflexivity.
      - destruct p; cbn.
        + rewrite Hrho; trivial. erewrite Vector.map_ext. reflexivity. intros t.
          apply sat_ext_bounded_term; reflexivity.
        + erewrite Vector.map_ext. reflexivity. intros t. apply sat_ext_bounded_term; reflexivity.
      - specialize (IHphi1 rho rho_p). specialize (IHphi2 rho rho_p). 
        destruct b0; tauto.
      - destruct q; split.
        + intros H d. eapply IHphi. 3: apply (H d). easy. intros [] ? ? ?; symmetry; now apply Hrho.
        + intros H d. eapply IHphi. 3: apply (H d). easy. intros [] ? ? ?; now apply Hrho.
        + intros [d H]. exists d. eapply IHphi. 3: apply H. easy. intros [] ? ? ?; symmetry; now apply Hrho.
        + intros [d H]. exists d. eapply IHphi. 3: apply H. easy. intros [] ? ? ?; now apply Hrho.
      - destruct q; split.
        + intros H f Hf. eapply IHphi. 3: apply (H f); trivial. easy. intros [] ? ? ?; symmetry; now apply Hrho.
        + intros H f Hf. eapply IHphi. 3: apply (H f); trivial. easy. intros [] ? ? ?; now apply Hrho.
        + intros [f [Hf H]]. exists f, Hf. eapply IHphi. 3: apply H. easy. intros [] ? ? ?; symmetry; now apply Hrho.
        + intros [f [Hf H]]. exists f, Hf. eapply IHphi. 3: apply H. easy. intros [] ? ? ?; now apply Hrho.
      - destruct q; split.
        + intros H P HP. eapply IHphi. 3: apply (H P); trivial. easy. intros [] ? ? ?; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try reflexivity; symmetry; now apply Hrho.
        + intros H P HP. eapply IHphi. 3: apply (H P); trivial. easy. intros [] ? ? ?; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try reflexivity; now apply Hrho.
        + intros [P [HP H]]. exists P, HP. eapply IHphi. 3: apply H. easy. intros [] ? ? ?; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try reflexivity; symmetry; now apply Hrho.
        + intros [P [HP H]]. exists P, HP. eapply IHphi. 3: apply H. easy. intros [] ? ? ?; cbn; destruct PeanoNat.Nat.eq_dec as [->|]; try reflexivity; now apply Hrho.
    Qed.

  End Bounded.



  (* Semantic properties of closing operation *)

  Section Close.

    Lemma fold_left_scons_i_lookup D (rho_i : nat -> D) n m (v : vec D n) :
      VectorLib.fold_left scons rho_i v (n+m) = rho_i m.
    Proof.
      revert rho_i m. induction v; intros rho_i m; cbn.
      - reflexivity.
      - replace (S (n+m)) with (n + S m) by lia. rewrite IHv. reflexivity.
    Qed.

    Lemma fold_left_scons_p_lookup D (rho_p : nat -> forall ar, vec D ar -> Prop) n m ar (v : vec (vec D ar -> Prop) n) :
      VectorLib.fold_left (scons_ar ar _) rho_p v (n+m) ar = rho_p m ar.
    Proof.
      revert rho_p m. induction v; intros rho_p m; cbn.
      - reflexivity.
      - replace (S (n+m)) with (n + S m) by lia. rewrite IHv. cbn. now rewrite nat_eq_dec_same.
    Qed.

    Lemma fold_left_scons_i_lookup' D (rho_i : nat -> D) n m (v : vec D n) err:
      m < n -> VectorLib.fold_left scons rho_i v m = VectorLib.nth_error (n - S m) v err.
    Proof.
      revert rho_i m. induction v; intros rho_i m; cbn -[minus].
      - lia.
      - intros H. replace m with (m+0) by lia. assert (m = n \/ m < n) as [->|] by lia.
        + rewrite fold_left_scons_i_lookup. now replace (S n - S (n + 0)) with 0 by lia.
        + rewrite IHv; try lia. cbn. now replace (n - (m + 0)) with (S (n - S (m + 0))) by lia.
    Qed.

    Lemma fold_left_scons_p_lookup' D (rho_p : nat -> forall ar, vec D ar -> Prop) ar n m (v : vec _ n) err:
      m < n -> VectorLib.fold_left (scons_ar ar _) rho_p v m ar = VectorLib.nth_error (n - S m) v err.
    Proof.
      revert rho_p m. induction v; intros rho_p m; cbn -[minus].
      - lia.
      - intros H. replace m with (m+0) by lia. assert (m = n \/ m < n) as [->|] by lia.
        + rewrite fold_left_scons_p_lookup. replace (S n - S (n + 0)) with 0 by lia. cbn.
          now rewrite nat_eq_dec_same.
        + rewrite IHv; try lia. cbn. now replace (n - (m + 0)) with (S (n - S (m + 0))) by lia.
    Qed.

    Lemma fold_left_scons_p_lookup'' D (rho_p : nat -> forall ar, vec D ar -> Prop) n ar ar' x (v : vec _ n) :
      ar' <> ar -> VectorLib.fold_left (scons_ar ar _) rho_p v x ar' = rho_p x ar'.
    Proof.
      intros H. revert rho_p. induction v; intros rho_p; cbn.
      - reflexivity.
      - rewrite IHv. now destruct x; cbn; destruct PeanoNat.Nat.eq_dec; try lia.
    Qed.

    Context {D : Type}.
    Context {I : interp D}.
    Variable funcs : forall ar, (vec D ar -> D) -> Prop.
    Variable preds : forall ar, (vec D ar -> Prop) -> Prop.

    Lemma forall_indi_n_to_vec rho n phi :
      sat funcs preds rho (quant_indi_n All n phi) <-> forall v : vec D n, sat funcs preds ⟨ VectorLib.fold_left scons (get_indi rho) v, get_func rho, get_pred rho ⟩ phi.
    Proof.
      enough (forall rho_i rho_f rho_p, sat funcs preds ⟨rho_i, rho_f, rho_p⟩ (quant_indi_n All n phi) <-> forall v : vec D n, sat funcs preds ⟨ VectorLib.fold_left scons rho_i v, rho_f, rho_p ⟩ phi) by now destruct rho.
      intros. clear rho. revert rho_i. induction n; intros rho_i; cbn.
      - split.
        + intros H v. now dependent elimination v.
        + intros H. apply (H (Vector.nil _)).
      - split.
        + intros H v. dependent elimination v. cbn. apply IHn, H.
        + intros H d. apply IHn. intros v. apply (H (Vector.cons _ d _ v)).
    Qed.

    Lemma forall_pred_n_to_vec rho n ar phi :
      sat funcs preds rho (quant_pred_n All ar n phi) <-> forall v : vec (vec D ar -> Prop) n, Forall (preds ar) v -> sat funcs preds ⟨ get_indi rho, get_func rho, VectorLib.fold_left (scons_ar ar _) (get_pred rho) v ⟩ phi.
    Proof.
      enough (forall rho_i rho_f rho_p, sat funcs preds ⟨rho_i, rho_f, rho_p⟩ (quant_pred_n All ar n phi) <-> forall v : vec _ n, Forall (preds ar) v -> sat funcs preds ⟨ rho_i, rho_f, VectorLib.fold_left (scons_ar ar _) rho_p v ⟩ phi) by (destruct rho; apply H).
      intros. clear rho. revert rho_p. induction n; intros rho_p; cbn.
      - split.
        + intros H v. now dependent elimination v.
        + intros H. now apply (H (Vector.nil _)).
      - split.
        + intros H v Hv. dependent elimination v. cbn. apply IHn. apply H, Hv. apply Hv.
        + intros H d Hd. apply IHn. intros v Hv. now apply (H (Vector.cons _ d _ v)).
    Qed.

    Lemma close_indi_sat rho phi :
      sat funcs preds rho (close_indi All phi) <-> forall rho_i, sat funcs preds ⟨ rho_i, get_func rho, get_pred rho ⟩ phi.
    Proof.
      split.
      - intros H rho_i. apply sat_ext_bounded with (sigma := ⟨fun x => rho_i (x + proj1_sig (find_bounded_indi phi)), get_func rho, get_pred rho⟩) in H; trivial. 
        eapply forall_indi_n_to_vec with (v := tabulate _ rho_i) in H. cbn in H.
        eapply sat_ext. 2: apply H.
        + intros x. split; try easy. destruct find_bounded_indi as [n B]; cbn in *.
          destruct (Compare_dec.lt_dec x n) as [H1|H1].
          * rewrite fold_left_scons_i_lookup' with (err := rho_i 0), nth_tabulate; try lia.
            f_equal. lia.
          * replace x with (n + (x - n)) at 2 by lia. rewrite fold_left_scons_i_lookup.
            f_equal. lia.
        + intros x H1. exfalso. apply H1. eapply bounded_indi_up. 
          2: apply close_indi_correct. lia.
      - intros H. apply forall_indi_n_to_vec. intros v. apply H.
    Qed.

    Lemma close_pred'_sat rho phi ar :
      (forall x ar, preds ar (get_pred rho x ar) : Prop) -> (sat funcs preds rho (close_pred' ar All phi) <-> forall P : nat -> vec D ar -> Prop, (forall x, preds ar (P x)) -> sat funcs preds ⟨ get_indi rho, get_func rho, fun x ar' => match PeanoNat.Nat.eq_dec ar ar' with left e => @cast _ _ _ (fun a => vec D a -> Prop) e (P x) | _ => get_pred rho x ar' end ⟩ phi).
    Proof.
      intros Hrho. split.
      - intros H P Hrho_p. apply sat_ext_bounded with (sigma := ⟨get_indi rho, get_func rho, fun x ar' => match PeanoNat.Nat.eq_dec ar ar' with left e => @cast _ _ _ (fun a => vec D a -> Prop) e (P (x + proj1_sig (find_bounded_pred ar phi))) | _ => get_pred rho x ar' end⟩) in H; trivial. 
        eapply forall_pred_n_to_vec in H. cbn in H. 
        instantiate (1 := tabulate (proj1_sig (find_bounded_pred ar phi)) P) in H.
        eapply sat_ext. 2: apply H.
        + intros x. split. easy. intros ar'. split; trivial. cbn. destruct find_bounded_pred as [n B]; cbn in *.
          assert (ar' = ar \/ ar' <> ar) as [->|] by lia.
          * destruct (Compare_dec.lt_dec x n) as [H1|H1].
            -- rewrite fold_left_scons_p_lookup' with (err := get_pred rho 0 ar), nth_tabulate, nat_eq_dec_same; try lia.
              now replace (n - S (n - S x)) with x by lia.
            -- replace x with (n + (x - n)) by lia. rewrite fold_left_scons_p_lookup.
              rewrite nat_eq_dec_same. now replace (n + (x - n)) with (x - n + n) by lia.
          * rewrite fold_left_scons_p_lookup''; trivial. now destruct PeanoNat.Nat.eq_dec; try lia.
        + apply tabulate_Forall. intros x _. apply Hrho_p.
        + intros x ar' H1. cbn. destruct PeanoNat.Nat.eq_dec as [->|].
          * exfalso. apply H1. eapply bounded_pred_up. 2: apply close_pred'_correct. lia.
          * reflexivity.
      - intros H. apply forall_pred_n_to_vec. intros v Hv. destruct find_bounded_pred as [n B]; cbn in *.
        eapply sat_ext_bounded. 4: apply (H (fun x => nth_error (n-S x) v (get_pred rho 0 ar))).
        reflexivity. reflexivity.
        + intros x ar' H1. cbn. destruct PeanoNat.Nat.eq_dec as [<-|].
          * rewrite fold_left_scons_p_lookup' with (err := get_pred rho 0 ar). reflexivity.
            assert (x < n \/ x >= n) as [|] by lia; trivial. exfalso. apply H1.
            eapply bounded_pred_up. 2: apply B. easy.
          * rewrite fold_left_scons_p_lookup''; auto.
        + intros x. clear -Hv Hrho. induction v; cbn. apply Hrho. assert (n > x \/ n <= x) as [|] by lia.
          * replace (n - x) with (S (n - S x)) by lia. apply IHv, Hv.
          * replace (n - x) with 0 by lia. apply Hv.
    Qed.

    Lemma close_pred_sat rho phi :
      (forall x ar, preds ar (get_pred rho x ar) : Prop) -> (sat funcs preds rho (close_pred All phi) <-> forall rho_p, (forall x ar, preds ar (rho_p x ar)) -> sat funcs preds ⟨ get_indi rho, get_func rho, rho_p ⟩ phi).
    Proof.
      intros Hrho.
      enough (forall n, sat funcs preds rho (close_pred'' n All phi) <-> forall rho_p, (forall x ar, preds ar (rho_p x ar)) -> sat funcs preds ⟨ get_indi rho, get_func rho, fun x ar => if Compare_dec.lt_dec ar n then rho_p x ar else get_pred rho x ar⟩ phi) as X.
      { split.
        - intros H1 rho_p H2. eapply sat_ext_p_arity_bounded. apply find_arity_bound_p_correct.
          2: apply (X (find_arity_bound_p phi)). intros x ar H3 v. cbn. now destruct Compare_dec.lt_dec; try lia.
          apply H1. apply H2.
        - intros H1. apply X. intros rho_p H2. apply H1. intros x ar. destruct Compare_dec.lt_dec.
          apply H2. apply Hrho. }
      intros n. revert rho Hrho. induction n; intros rho Hrho; cbn.
      - split.
        + intros H1 rho_p H2. eapply sat_ext. 2: apply H1. easy.
        + intros H1. destruct rho. eapply H1. apply Hrho.
      - setoid_rewrite close_pred'_sat; trivial. split.
        + intros H1 rho_p H2. specialize (H1 (fun x => rho_p x n) ltac:(firstorder)).
          eapply IHn in H1. cbn in H1. eapply sat_ext. 2: apply H1.
          * intros x. split. reflexivity. intros ar. split. reflexivity. cbn.
            repeat destruct Compare_dec.lt_dec; try lia. reflexivity.
            all: now destruct PeanoNat.Nat.eq_dec as [->|]; try lia.
          * intros x ar. cbn. destruct PeanoNat.Nat.eq_dec as [->|]. apply H2. apply Hrho.
          * apply H2.
        + intros H1 P H2. apply IHn.
          * intros x ar. cbn. destruct PeanoNat.Nat.eq_dec as [->|]. apply H2. apply Hrho.
          * intros rho_p H3. cbn. eapply sat_ext. 2: apply (H1 (fun x ar => match PeanoNat.Nat.eq_dec n ar with left e => @cast _ _ _ (fun a => vec D a -> Prop) e (P x) | _ => rho_p x ar end)). trivial.
            -- intros x. split. reflexivity. intros ar. split. reflexivity. cbn.
              repeat destruct Compare_dec.lt_dec; try lia.
              all: now destruct PeanoNat.Nat.eq_dec as [->|]; try lia.
            -- intros x ar. destruct PeanoNat.Nat.eq_dec as [->|]. apply H2. apply H3.
    Qed.

    Lemma close_sat_funcfree rho phi :
      funcfree phi -> (forall x ar, preds ar (get_pred rho x ar) : Prop) -> sat funcs preds rho (close All phi) <-> forall sigma, (forall x ar, preds ar (get_pred sigma x ar)) -> sat funcs preds sigma phi.
    Proof.
      intros F Hrho. split.
      - intros H1 [sigma_i sigma_f sigma_p] H2. apply close_pred_sat with (rho := ⟨sigma_i, sigma_f, sigma_p⟩); trivial.
        apply close_indi_sat with (rho := ⟨sigma_i, sigma_f, sigma_p⟩); trivial.
        eapply sat_ext_bounded. 4: apply H1.
        + intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply close_indi_correct. lia.
        + intros x ar H. exfalso. apply H. apply funcfree_bounded_func. 
          apply close_indi_funcfree, close_pred_funcfree, F.
        + intros x ar H. exfalso. apply H. eapply bounded_pred_up.
          2: apply close_indi_bounded_pred, close_pred_correct. lia.
      - intros H1. apply close_indi_sat. intros rho_i. apply close_pred_sat. apply Hrho.
        intros rho_p H2. cbn. apply H1, H2.
    Qed.

  End Close.



  Section FullModels.

    Context {D : Type}.
    Context {I : interp D}.

    Lemma sat_full_henkin rho phi :
      @sat D I (fun _ _ => True) (fun _ _ => True) rho phi <-> Tarski.sat _ _ D I rho phi.
    Proof.
      revert rho. induction phi; intros rho; cbn.
      - easy.
      - easy.
      - specialize (IHphi1 rho); specialize (IHphi2 rho). destruct b; tauto.
      - destruct q; cbn.
        + split; intros H d; apply IHphi, H.
        + split; intros [d H]; exists d; apply IHphi, H.
      - destruct q; cbn; split.
        + intros H f. now apply IHphi, H.
        + intros H f Hf. apply IHphi, H.
        + intros [f [Hf H]]. exists f. apply IHphi, H.
        + intros [f H]. exists f, Logic.I. apply IHphi, H.
      - destruct q; cbn; split.
        + intros H P. now apply IHphi, H.
        + intros H P HP. apply IHphi, H.
        + intros [P [HP H]]. exists P. apply IHphi, H.
        + intros [P H]. exists P, Logic.I. apply IHphi, H.
    Qed.

  End FullModels.



  (** Substitution Lemmas *)

  Section Substs.

    Variable domain : Type.
    Variable funcs : forall ar, (vec domain ar -> domain) -> Prop.
    Variable preds : forall ar, (vec domain ar -> Prop) -> Prop.
    Context {I : interp domain}.

    Lemma sat_comp_i (rho : env domain) σ phi :
      sat funcs preds rho (phi[σ]i) <-> sat funcs preds ⟨σ >> eval _ rho, get_func rho, get_pred rho⟩ phi.
    Proof.
      induction phi in rho, σ |- *; cbn.
      - reflexivity.
      - destruct p; cbn; erewrite map_map, map_ext; try reflexivity;
        induction v; firstorder; apply eval_comp_i.
      - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ). destruct b; tauto.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
          2, 4: apply (H d). all: intros []; split; try easy;
          cbn; erewrite eval_comp_i; now destruct rho.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
          2, 4: apply H. all: intros []; split; try easy;
          cbn; erewrite eval_comp_i; now destruct rho.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H f Hf; eapply sat_ext.
          2, 4: apply (H f Hf). all: split; try easy. 2: symmetry.
          all: apply eval_subst_cons_shift_f.
        + setoid_rewrite IHphi; split; intros [f [Hf H]]; exists f, Hf; eapply sat_ext.
          2, 4: apply H. all: split; try easy. 2: symmetry.
          all: apply eval_subst_cons_shift_f.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H P HP; eapply sat_ext.
          2, 4: apply (H P HP). all: split; try easy; now apply eval_ext.
        + setoid_rewrite IHphi; split; intros [P [HP H]]; exists P, HP; eapply sat_ext.
          2, 4: apply H. all: split; try easy; now apply eval_ext.
    Qed.

    Lemma sat_comp_f rho σ phi :
      sat funcs preds rho (phi[σ]f) <-> sat funcs preds ⟨get_indi rho, σ >>> eval_function _ rho, get_pred rho⟩ phi.
    Proof.
      induction phi in rho, σ |- *; cbn.
      - reflexivity.
      - destruct p; cbn; erewrite map_map, map_ext; try reflexivity;
        induction v; firstorder; apply eval_comp_f.
      - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ). destruct b; tauto.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
          2, 4: apply (H d). all: easy.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
          2, 4: apply H. all: easy.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H f Hf; eapply sat_ext.
          2, 4: apply (H f Hf). 
          all: intros []; repeat split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_function_subst_cons_shift_f with (g := f).
          all: now rewrite <- eval_function_subst_cons_shift_f with (g := f).
        + setoid_rewrite IHphi; split; intros [f [Hf H]]; exists f, Hf; eapply sat_ext.
          2, 4: apply H.
          all: intros []; repeat split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_function_subst_cons_shift_f with (g := f).
          all: now rewrite <- eval_function_subst_cons_shift_f with (g := f).
      - destruct q.
        + setoid_rewrite IHphi; split; intros H P HP; eapply sat_ext.
          2, 4: apply (H P HP). all: intros; split; try easy; now apply eval_ext.
        + setoid_rewrite IHphi; split; intros [P [HP H]]; exists P, HP; eapply sat_ext.
          2, 4: apply H. all: intros; split; try easy; now apply eval_ext.
    Qed.

    Lemma sat_comp_p rho σ phi :
      sat funcs preds rho (phi[σ]p) <-> sat funcs preds ⟨get_indi rho, get_func rho, σ >>> eval_predicate _ rho⟩ phi.
    Proof.
      induction phi in rho, σ |- *; cbn.
      - reflexivity.
      - destruct p; cbn;
        enough (map (eval _ rho) v = map (eval _ ⟨get_indi rho, get_func rho, σ >>> eval_predicate _ rho⟩) v) as -> by reflexivity;
        apply map_ext_forall; induction v; firstorder; now apply eval_ext.
      - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ). destruct b; tauto.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
          2, 4: apply (H d). all: easy.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
          2, 4: apply H. all: easy.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H f Hf; eapply sat_ext.
          2, 4: apply (H f Hf). all: easy.
        + setoid_rewrite IHphi. split; intros [f [Hf H]]; exists f, Hf; eapply sat_ext.
          2, 4: apply H. all: easy.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H P HP; eapply sat_ext.
          2, 4: apply (H P HP). 
          all: intros []; split; try easy; split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_predicate_subst_cons_shift_p with (Q := P).
          all: now rewrite <- eval_predicate_subst_cons_shift_p with (Q := P).
        + setoid_rewrite IHphi; split; intros [P [HP H]]; exists P, HP; eapply sat_ext.
          2, 4: apply H. 
          all: intros []; split; try easy; split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_predicate_subst_cons_shift_p with (Q := P).
          all: now rewrite <- eval_predicate_subst_cons_shift_p with (Q := P).
    Qed.

  End Substs.





  (** Bundle everything we need for a model in a record *)

  Section HenkinModel.

      Definition valid A phi :=
        forall D (I : interp D) funcs preds, 
          @henkin_interp _ I funcs preds 
          -> (forall rho, (forall x ar, preds ar (get_pred rho x ar)) -> (forall ar phi, funcfree phi -> Henkin.sat funcs preds rho (comprehension_form ar phi)))
          -> forall rho, henkin_env funcs preds rho 
              -> (forall a, List.In a A -> Henkin.sat funcs preds rho a) 
              -> Henkin.sat funcs preds rho phi.

    Definition validT (T : SOL.form -> Prop) phi :=
      forall D (I : Tarski.interp D) funcs preds, 
        @henkin_interp _ I funcs preds 
        -> (forall rho, (forall x ar, preds ar (get_pred rho x ar)) -> (forall ar phi, funcfree phi -> Henkin.sat funcs preds rho (comprehension_form ar phi)))
        -> forall rho, henkin_env funcs preds rho 
            -> (forall psi, T psi -> Henkin.sat funcs preds rho psi) 
            -> Henkin.sat funcs preds rho phi.

    Record HenkinModel := { 
      H_domain : Type ;
      H_interp : interp H_domain ;
      H_funcs : forall ar, (vec H_domain ar -> H_domain) -> Prop ;
      H_preds : forall ar, (vec H_domain ar -> Prop) -> Prop ;
      H_compr_p : forall rho, (forall x ar : nat, H_preds ar (get_pred rho x ar)) -> forall ar phi, funcfree phi -> sat H_funcs H_preds rho (comprehension_form ar phi) ;
    }.

    Coercion H_interp : HenkinModel >-> interp.
    Global Instance H_I H : interp (H_domain H) := H_interp H.

    Class EntH X := enth : X -> form -> Prop.

    (* rho ⊨h phi *)
    Global Instance enth_env domain I funcs preds : EntH (env domain) := fun rho phi => henkin_env funcs preds rho -> @sat domain I funcs preds rho phi.

    (* H ⊨h phi *)
    Global Instance enth_model : EntH HenkinModel := fun H phi => forall rho, henkin_env (H_funcs H) (H_preds H) rho -> @sat (H_domain H) (H_interp H) (H_funcs H) (H_preds H) rho phi.

    (* T ⊨h phi *)
    (* Global Instance enth_theory : EntH (form -> Prop) := fun T phi => forall rho, @sat (H_domain H) (H_interp H) (H_funcs H) (H_preds H) rho phi. *)

  End HenkinModel.


End Henkin.



Arguments henkin_interp {_ _ _}.

Notation "X ⊨h phi" := (enth X phi) (at level 20).
Notation "( H , rho ) ⊨h phi" := (henkin_env (H_funcs H) (H_preds H) rho -> @Henkin.sat _ _ (H_domain H) (H_interp H) (H_funcs H) (H_preds H) rho phi) (at level 0).
