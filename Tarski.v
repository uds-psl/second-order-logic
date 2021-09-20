(** ** Tarski Semantics *)

Require Import SOL.
Require Import FullSyntax.
Require Export Subst.
Require Export Util.
Require Import Vector.
Require Import VectorLib.
Require Import Arith.
Import SubstNotations.

Require Import Equations.Equations Equations.Prop.DepElim.
Derive Signature for Vector.t.

Require Import Lia.


Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.


  (** Default Semantics where functions are interpreted as Coq 
      functions *)

  Section Semantics.

    Definition env_indi domain := nat -> domain.
    Definition env_func domain := nat -> forall ar, vec domain ar -> domain.
    Definition env_pred domain := nat -> forall ar, vec domain ar -> Prop.
    Record env domain := new_env { get_indi : env_indi domain ; get_func : env_func domain ; get_pred : env_pred domain }.

    (* TODO: Why can't Coq find this automatically? *)
    Global Instance scons_env_func domain ar : Scons _ := scons_ar ar (fun ar => vec domain ar -> domain).
    Global Instance scons_env_pred domain ar : Scons _ := scons_ar ar (fun ar => vec domain ar -> Prop).

    Variable domain : Type.

    Arguments new_env {_} _ _ _.
    Arguments get_indi {_} _ _.
    Arguments get_func {_} _ _.
    Arguments get_pred {_} _ _.
    Notation "⟨ a , b , c ⟩" := (new_env a b c).

    Class interp := B_I {
      i_f : forall f : syms, vec domain (ar_syms f) -> domain ;
      i_P : forall P : preds, vec domain (ar_preds P) -> Prop ;
    }.


    Section Interp.

      Context { I : interp }.

      Definition eval_function {ar} (rho : env domain) (f : function ar) : vec domain ar -> domain :=
        match f with
        | var_func f => get_func rho f _
        | sym f => i_f f
        end.

      Definition eval_predicate {ar} (rho : env domain) (P : predicate ar) : vec domain ar -> Prop :=
        match P with
        | var_pred P => get_pred rho P _
        | pred P => i_P P
        end.

      Fixpoint eval (rho : env domain) (t : term) : domain := 
        match t with
        | var_indi x => get_indi rho x
        | func f v => eval_function rho f (Vector.map (eval rho) v)
        end.

      Fixpoint sat (rho : env domain) (phi : form) : Prop :=
        match phi with
        | atom P v => eval_predicate rho P (Vector.map (eval rho) v)
        | fal => False
        | bin Impl phi psi => sat rho phi -> sat rho psi
        | bin Conj phi psi => sat rho phi /\ sat rho psi
        | bin Disj phi psi => sat rho phi \/ sat rho psi
        | quant_indi Ex phi => exists d : domain, sat ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ phi
        | quant_indi All phi => forall d : domain, sat ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ phi
        | quant_func Ex ar phi => exists (f : vec domain ar -> domain), sat ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ phi
        | quant_func All ar phi => forall (f : vec domain ar -> domain), sat ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ phi
        | quant_pred Ex ar phi => exists (P : vec domain ar -> Prop), sat ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ phi
        | quant_pred All ar phi => forall (P : vec domain ar -> Prop), sat ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ phi
        end.

    End Interp.


    (** Equivalence of environments *)

    Definition env_equiv (rho1 : env domain) rho2 := forall n,
         get_indi rho1 n = get_indi rho2 n
      /\ forall ar v, get_func rho1 n ar v = get_func rho2 n ar v
                  /\ (get_pred rho1 n ar v <-> get_pred rho2 n ar v).
    Notation "rho1 ≡ rho2" := (env_equiv rho1 rho2) (at level 30).

    Lemma env_equiv_symm rho1 rho2 :
      rho1 ≡ rho2 -> rho2 ≡ rho1.
    Proof.
      intros H. intros n. specialize (H n). split. easy. 
      intros ar v. destruct H as [_ H]. specialize (H ar v). easy.
    Qed.

    Lemma env_equiv_cons_i rho1 rho2 x :
    rho1 ≡ rho2 -> ⟨ x .: get_indi rho1, get_func rho1, get_pred rho1 ⟩ ≡ ⟨ x .: get_indi rho2, get_func rho2, get_pred rho2 ⟩.
    Proof.
      intros H n. split. 2:split. destruct n. all: firstorder.
    Qed.

    Lemma env_equiv_cons_f rho1 rho2 ar (f : vec domain ar -> domain) f' :
      rho1 ≡ rho2 -> (forall v, f v = f' v) 
      -> ⟨ get_indi rho1, f .: get_func rho1, get_pred rho1 ⟩ ≡ ⟨ get_indi rho2, f' .: get_func rho2, get_pred rho2 ⟩.
    Proof.
      intros H Hf n. split. 2:split.
      - apply H.
      - destruct n; cbn; destruct (Nat.eq_dec ar ar0) as [->|]; firstorder.
      - apply H.
    Qed.

    Lemma env_equiv_cons_p rho1 rho2 ar (P : vec domain ar -> Prop) :
      rho1 ≡ rho2 -> ⟨ get_indi rho1, get_func rho1, P .: get_pred rho1 ⟩ ≡ ⟨ get_indi rho2, get_func rho2, P .: get_pred rho2 ⟩.
    Proof.
      intros H n. split. 2:split.
      - apply H.
      - apply H.
      - destruct n; cbn; destruct (Nat.eq_dec ar ar0) as [->|]. all: firstorder.
    Qed.

    Section Interp.
      Context {I : interp}.

      Lemma eval_function_ext rho1 rho2 ar (f : function ar) :
      (forall n ar v, get_func rho1 n ar v = get_func rho2 n ar v)
        -> forall v, eval_function rho1 f v = eval_function rho2 f v.
      Proof.
        intros H v. destruct f; cbn. apply H. reflexivity.
      Qed.

      Lemma eval_predicate_ext rho1 rho2 ar (P : predicate ar) :
      (forall n ar v, get_pred rho1 n ar v <-> get_pred rho2 n ar v)
        -> forall v, eval_predicate rho1 P v <-> eval_predicate rho2 P v.
      Proof.
        intros H v. destruct P; cbn. apply H. reflexivity.
      Qed.

      Lemma eval_ext rho1 rho2 t :
        (forall n, get_indi rho1 n = get_indi rho2 n) 
        -> (forall n ar v, get_func rho1 n ar v = get_func rho2 n ar v)
        -> eval rho1 t = eval rho2 t.
      Proof.
        intros H1 H2. induction t.
        - apply H1.
        - cbn. enough (map (eval rho1) v = map (eval rho2) v) as -> by apply H2.
          apply map_ext. induction v; firstorder.
        - cbn. f_equal. apply map_ext. induction v; firstorder.
      Qed.

      Lemma sat_ext rho1 rho2 phi :
        rho1 ≡ rho2 -> sat rho1 phi <-> sat rho2 phi.
      Proof.
        revert rho1 rho2. induction phi; cbn; intros rho1 rho2 H.
        - easy.
        - destruct p. 
          + enough (map (eval rho1) v = map (eval rho2) v) as <- by apply H.
            apply map_ext. induction v; firstorder. apply eval_ext; apply H.
          + enough (map (eval rho1) v = map (eval rho2) v) as <- by easy.
            apply map_ext. induction v; firstorder. apply eval_ext; apply H.
        - specialize (IHphi1 rho1 rho2); specialize (IHphi2 rho1 rho2).
          destruct b; cbn; firstorder.
        - destruct q; split; cbn.
          + intros H1 x. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_i.
          + intros H1 x. eapply IHphi. 2: apply H1. now apply env_equiv_cons_i.
          + intros [d H1]. exists d. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_i.
          + intros [d H1]. exists d. eapply IHphi. 2: apply H1. now apply env_equiv_cons_i.
        - destruct q; split; cbn.
          + intros H1 f. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_f.
          + intros H1 f. eapply IHphi. 2: apply H1. now apply env_equiv_cons_f.
          + intros [f H1]. exists f. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_f.
          + intros [f H1]. exists f. eapply IHphi. 2: apply H1. now apply env_equiv_cons_f.
        - destruct q; split; cbn.
          + intros H1 P. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_p.
          + intros H1 P. eapply IHphi. 2: apply H1. now apply env_equiv_cons_p.
          + intros [P H1]. exists P. eapply IHphi. 2: apply H1. now apply env_equiv_symm, env_equiv_cons_p.
          + intros [P H1]. exists P. eapply IHphi. 2: apply H1. now apply env_equiv_cons_p.
      Qed.

    End Interp.



    (** Closed formulas *)

    Section Interp.
      Context {I : interp}.

      (*Lemma bounded_eval_term_FO  n t rho sigma :
        first_order_term t
        -> (forall k, n > k -> get_indi rho k = get_indi sigma k)
        -> bounded_indi_term n t 
        -> eval rho t = eval sigma t.
      Proof.
        intros FO H1 H2. induction t; cbn.
        - apply H1, H2.
        - easy.
        - f_equal. apply map_ext_forall. cbn in *. induction v; firstorder.
      Qed.

      Lemma bounded_sat_ext_FO  n phi rho sigma :
        first_order phi 
        -> (forall k, n > k -> get_indi rho k = get_indi sigma k)
        -> bounded_indi n phi
        -> (sat rho phi <-> sat sigma phi).
      Proof.
        intros FO. revert n rho sigma. induction phi; intros n' rho sigma H1 H2.
        - easy.
        - destruct p; cbn in *.
          + easy.
          + enough (map (eval rho) v = map (eval sigma) v) as -> by easy.
            apply map_ext_forall. induction v; firstorder using bounded_eval_term_FO.
        - destruct FO as [FO1 FO2].
          assert (sat rho phi1 <-> sat sigma phi1) by (apply (IHphi1 FO1 n'); firstorder).
          assert (sat rho phi2 <-> sat sigma phi2) by (apply (IHphi2 FO2 n'); firstorder).
          destruct b; cbn; tauto.
        - destruct q; cbn; split.
          + intros H d. eapply IHphi with (n := S n'). 4: apply H. easy.
            intros [] H'. reflexivity. symmetry. apply H1. lia. easy.
          + intros H d. eapply IHphi with (n := S n'). 4: apply H. easy.
            intros [] H'. reflexivity. apply H1. lia. easy.
          + intros [d H]. exists d. eapply IHphi with (n := S n'). 4: apply H. easy.
            intros [] H'. reflexivity. symmetry. apply H1. lia. easy.
          + intros [d H]. exists d. eapply IHphi with (n := S n'). 4: apply H. easy.
            intros [] H'. reflexivity. apply H1. lia. easy.
        - easy.
        - easy.
      Qed. *)

      Lemma sat_ext_bounded_term t rho sigma :
        (forall x, ~ bounded_indi_term x t -> get_indi rho x = get_indi sigma x)
        -> (forall x ar, ~ bounded_func_term ar x t -> get_func rho x ar = get_func sigma x ar)
        -> eval rho t = eval sigma t.
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
        -> sat rho phi <-> sat sigma phi.
      Proof.
        revert rho sigma. induction phi; cbn; intros rho sigma H1 H2 H3.
        - reflexivity.
        - erewrite VectorLib.map_ext_in with (g := eval sigma); revgoals.
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
          + intros H f. eapply IHphi. 4: eapply (H f); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
          + intros H f. eapply IHphi. 4: eapply (H f); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
          + intros [f H]. exists f. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
          + intros [f H]. exists f. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        - destruct q; split.
          + intros H P. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
          + intros H P. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
          + intros [P H]. exists P. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
          + intros [P H]. exists P. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      Qed.

      Lemma sat_ext_closed phi rho sigma :
        bounded_indi 0 phi -> (forall ar, bounded_func ar 0 phi) -> (forall ar, bounded_pred ar 0 phi) 
        -> (sat rho phi <-> sat sigma phi).
      Proof.
        intros Bi Bf Bp. apply sat_ext_bounded.
        - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply Bi. lia.
        - intros x ar H. exfalso. apply H. eapply bounded_func_up. 2: apply Bf. lia.
        - intros x ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply Bp. lia.
      Qed.

      Lemma sat_ext_closed_funcfree phi rho sigma :
        funcfree phi -> bounded_indi 0 phi -> (forall ar, bounded_pred ar 0 phi) 
        -> (sat rho phi <-> sat sigma phi).
      Proof.
        intros F Bi Bp. apply sat_ext_bounded.
        - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply Bi. lia.
        - intros x ar H. exfalso. apply H. apply funcfree_bounded_func, F.
        - intros x ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply Bp. lia.
      Qed.

      Lemma sat_ext_closed_FO phi rho sigma :
        first_order phi -> bounded_indi 0 phi -> (sat rho phi <-> sat sigma phi).
      Proof.
        intros F B. apply sat_ext_bounded.
        - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply B. lia.
        - intros x ar H. exfalso. apply H. apply funcfree_bounded_func, firstorder_funcfree, F.
        - intros x ar H. exfalso. apply H. apply firstorder_bounded_pred, F.
      Qed.

    End Interp.

  End Semantics.

  Arguments new_env {_} _ _ _.
  Arguments get_indi {_} _ _.
  Arguments get_func {_} _ _.
  Arguments get_pred {_} _ _.
  Notation "⟨ a , b , c ⟩" := (new_env a b c).
  Notation "rho1 ≡ rho2" := (env_equiv _ rho1 rho2) (at level 30).


  (** *** Relational Models *)

  (** Alternative semantics where functions are interpreted as
      predicates. This creates larger models as functions no
      longer need to be computable. *)

  Section PredicateSemantics.

    Definition functional {X Y} (f : X -> Y -> Prop) := forall x y y', f x y -> f x y' -> y = y'.
    Definition total {X Y} (f : X -> Y -> Prop) := forall x, exists y, f x y.

    Definition func_p domain ar := { f : vec domain ar -> domain -> Prop | functional f /\ total f }. 
    Definition env_func_p domain := nat -> forall ar, func_p domain ar.
    Record env_p domain := new_env_p { get_indi_p : env_indi domain ; get_func_p : env_func_p domain ; get_pred_p : env_pred domain }.

    (* TODO: Why can't Coq find this automatically? *)
    Global Instance scons_env_func_p domain ar : Scons _ := scons_ar ar (func_p domain).

    Definition default_func_p {D} ar (d : D) :
      func_p D ar.
    Proof.
      exists (fun v d' => d' = d). split.
      - intros v y y'. congruence.
      - intros v. now exists d.
    Qed.

    Variable domain : Type.

    Arguments new_env_p {_}.
    Arguments get_indi_p {_}.
    Arguments get_func_p {_}.
    Arguments get_pred_p {_}.
    Notation "⟨⟨ a , b , c ⟩⟩" := (new_env_p a b c).


    (** Turn normal interp into predicate interp *)

    Definition to_pred ar (f : vec domain ar -> domain) : func_p domain ar.
    Proof.
      exists (fun x y => f x = y). split.
      - now intros x y y' -> ->.
      - intros x. now exists (f x).
    Defined.

    Class interp_p := {
      i_f_p : forall f : syms, func_p domain (ar_syms f) ;
      i_P_p : forall P : preds, vec domain (ar_preds P) -> Prop ;
    }.

    Global Instance to_interp_p (I : interp domain) : interp_p := {|
      i_f_p f := to_pred _ (i_f domain f) ;
      i_P_p P := i_P domain P
    |}.

    Definition to_pred_env (rho : env domain) : env_p domain :=
      ⟨⟨ get_indi rho, fun n ar => to_pred ar (get_func rho n ar), get_pred rho ⟩⟩.



    (** Semantics *)

    Context { I : interp_p }.

    Fixpoint eval_p (rho : env_p domain) (t : term) (res : domain) : Prop := 
      match t with
      | var_indi x => get_indi_p rho x = res
      | func (var_func f) v => exists v', Forall2 (eval_p rho) v v' /\ proj1_sig (get_func_p rho f _) v' res
      | func (sym f) v => exists v', Forall2 (eval_p rho) v v' /\ proj1_sig (i_f_p f) v' res
      end.

    Fixpoint sat_p (rho : env_p domain) (phi : form) : Prop :=
      match phi with
      | atom (var_pred P) v => exists v', Forall2 (eval_p rho) v v' /\ get_pred_p rho P _ v'
      | atom (pred P) v => exists v', Forall2 (eval_p rho) v v' /\ i_P_p P v'
      | fal => False
      | bin Impl phi psi => sat_p rho phi -> sat_p rho psi
      | bin Conj phi psi => sat_p rho phi /\ sat_p rho psi
      | bin Disj phi psi => sat_p rho phi \/ sat_p rho psi
      | quant_indi Ex phi => exists d : domain, sat_p ⟨⟨d .: get_indi_p rho, get_func_p rho, get_pred_p rho⟩⟩ phi
      | quant_indi All phi => forall d : domain, sat_p ⟨⟨d .: get_indi_p rho, get_func_p rho, get_pred_p rho⟩⟩ phi
      | quant_func Ex ar phi => exists (f : vec domain ar -> domain -> Prop) (H1 : functional f) (H2 : total f), sat_p ⟨⟨get_indi_p rho, exist _ f (conj H1 H2) .: get_func_p rho, get_pred_p rho⟩⟩ phi
      | quant_func All ar phi => forall (f : vec domain ar -> domain -> Prop) (H1 : functional f) (H2 : total f), sat_p ⟨⟨get_indi_p rho, exist _ f (conj H1 H2) .: get_func_p rho, get_pred_p rho⟩⟩ phi
      | quant_pred Ex ar phi => exists (P : vec domain ar -> Prop), sat_p ⟨⟨get_indi_p rho, get_func_p rho, P .: get_pred_p rho⟩⟩ phi
      | quant_pred All ar phi => forall (P : vec domain ar -> Prop), sat_p ⟨⟨get_indi_p rho, get_func_p rho, P .: get_pred_p rho⟩⟩ phi
      end.


    (** Functionality and totality of eval_p *)

    Lemma eval_p_functional rho t x y :
      eval_p rho t x -> eval_p rho t y -> x = y.
    Proof.
      revert x y. induction t; intros x y.
      - now intros <- <-.
      - intros [v1 [H1 H2]] [v2 [H3 H4]].
        destruct (get_func_p rho n ar) as [F [F_functional F_total]]; cbn in *. 
        assert (v1 = v2) as ->. {
          clear H2 H4 F_functional F_total F.
          induction v; dependent elimination v1; dependent elimination v2. 
          reflexivity. f_equal.
          - apply IH. apply H1. apply H3.
          - eapply IHv. apply IH. apply H1. apply H3. }
        eapply F_functional. apply H2. apply H4.
      - intros [v1 [H1 H2]] [v2 [H3 H4]].
        destruct (i_f_p f) as [F [F_functional F_total]]; cbn in *.
        assert (v1 = v2) as ->. {
          clear H2 H4 F_functional F_total F.
          induction v; dependent elimination v1; dependent elimination v2. 
          reflexivity. f_equal.
          - apply IH. apply H1. apply H3.
          - eapply IHv. apply IH. apply H1. apply H3. }
        eapply F_functional. apply H2. apply H4.
    Qed.

    Lemma eval_p_total rho t :
      exists x, eval_p rho t x.
    Proof.
      revert t. induction t.
      - now exists (get_indi_p rho n).
      - assert (exists v', Forall2 (eval_p rho) v v') as [v' H]. {
          induction v. now exists (nil _). destruct IHv as [v' H].
          apply IH. destruct IH as [[x' IH1] IH2]. now exists (cons _ x' _ v'). }
        destruct (get_func_p rho n ar) as [F [HF1 HF2]] eqn:H1. 
        destruct (HF2 v') as [x' H2]. exists x', v'. split. apply H.
        rewrite H1. apply H2.
      - assert (exists v', Forall2 (eval_p rho) v v') as [v' H]. {
          induction v. now exists (nil _). destruct IHv as [v' H].
          apply IH. destruct IH as [[x' IH1] IH2]. now exists (cons _ x' _ v'). }
        destruct (i_f_p f) as [F [HF1 HF2]] eqn:H1. 
        destruct (HF2 v') as [x' H2]. exists x', v'. split. apply H.
        rewrite H1. apply H2.
    Qed.


    (** Equivalence of environments *)

    Definition env_p_equiv (rho1 : env_p domain) rho2 := forall n,
      get_indi_p rho1 n = get_indi_p rho2 n
      /\ forall ar v, (forall x, proj1_sig (get_func_p rho1 n ar) v x <-> proj1_sig (get_func_p rho2 n ar) v x)
                   /\ (get_pred_p rho1 n ar v <-> get_pred_p rho2 n ar v).
    Notation "rho1 ≡p rho2" := (env_p_equiv rho1 rho2) (at level 30).

    Lemma env_p_equiv_symm rho1 rho2 :
      rho1 ≡p rho2 -> rho2 ≡p rho1.
    Proof.
      intros H. intros n. specialize (H n). split. easy. 
      intros ar v. destruct H as [_ H]. specialize (H ar v). easy.
    Qed.

    Lemma env_p_equiv_cons_i rho1 rho2 x :
    rho1 ≡p rho2 -> ⟨⟨ x .: get_indi_p rho1, get_func_p rho1, get_pred_p rho1 ⟩⟩ ≡p ⟨⟨ x .: get_indi_p rho2, get_func_p rho2, get_pred_p rho2 ⟩⟩.
    Proof.
      intros H n. split. 2:split.
      - destruct n. reflexivity. apply H.
      - apply H.
      - apply H.
    Qed.

    Lemma env_p_equiv_cons_f rho1 rho2 ar (f : func_p domain ar) (f' : func_p domain ar) :
      rho1 ≡p rho2 -> (forall v x, proj1_sig f v x <-> proj1_sig f' v x) 
      -> ⟨⟨ get_indi_p rho1, f .: get_func_p rho1, get_pred_p rho1 ⟩⟩ ≡p ⟨⟨ get_indi_p rho2, f' .: get_func_p rho2, get_pred_p rho2 ⟩⟩.
    Proof.
      intros H Hf n. split. 2:split.
      - apply H.
      - destruct n; cbn; destruct (Nat.eq_dec ar ar0) as [->|]; try easy; apply H.
      - apply H.
    Qed.

    Lemma env_p_equiv_cons_p rho1 rho2 ar (P : vec domain ar -> Prop) :
      rho1 ≡p rho2 -> ⟨⟨ get_indi_p rho1, get_func_p rho1, P .: get_pred_p rho1 ⟩⟩ ≡p ⟨⟨ get_indi_p rho2, get_func_p rho2, P .: get_pred_p rho2 ⟩⟩.
    Proof.
      intros H n. split. 2:split.
      - apply H.
      - apply H.
      - destruct n; cbn; destruct (Nat.eq_dec ar ar0) as [->|]; try easy; apply H.
    Qed.

    Lemma eval_p_ext rho1 rho2 t :
      rho1 ≡p rho2 -> forall x, eval_p rho1 t x -> eval_p rho2 t x.
    Proof.
      intros H. induction t; intros x.
      - intros <-. symmetry. apply H.
      - intros [v' H1]. exists v'. split.
        + destruct H1 as [H1 _]. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
        + apply H, H1.
      - intros [v' H1]. exists v'. split.
        + destruct H1 as [H1 _]. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
        + apply H1.
    Qed.

    Lemma sat_p_ext rho1 rho2 phi :
      rho1 ≡p rho2 -> sat_p rho1 phi <-> sat_p rho2 phi.
    Proof.
      revert rho1 rho2. induction phi; intros rho1 rho2 H.
      - easy.
      - destruct p; split.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'.
            easy. split. eapply eval_p_ext. apply H. apply H1.
            apply IHv. apply H1.
          * apply H, H1.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'.
            easy. split. eapply eval_p_ext. apply env_p_equiv_symm, H.
            apply H1. apply IHv. apply H1.
          * apply H, H1.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'. 
            easy. split. eapply eval_p_ext. apply H. apply H1. 
            apply IHv. apply H1.
          * apply H1.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'. 
            easy. split. eapply eval_p_ext. apply env_p_equiv_symm, H. 
            apply H1. apply IHv. apply H1.
          * apply H1.
      - specialize (IHphi1 rho1 rho2 H); specialize (IHphi2 rho1 rho2 H).
        destruct b; cbn; try tauto.
      - destruct q; split; cbn.
        + intros H1 x. eapply IHphi. 2: apply H1. 
          now apply env_p_equiv_symm, env_p_equiv_cons_i.
        + intros H1 x. eapply IHphi. 2: apply H1. 
          now apply env_p_equiv_cons_i.
        + intros [d H1]. exists d. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_symm, env_p_equiv_cons_i.
        + intros [d H1]. exists d. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_cons_i.
      - destruct q; split; cbn.
        + intros H1 f Hf1 Hf2. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_symm, env_p_equiv_cons_f.
        + intros H1 f Hf1 Hf2. eapply IHphi. 2: apply H1. 
          now apply env_p_equiv_cons_f.
        + intros [f [Hf1 [Hf2 H1]]]. exists f, Hf1, Hf2. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_symm, env_p_equiv_cons_f.
        + intros [f [Hf1 [Hf2 H1]]]. exists f, Hf1, Hf2. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_cons_f.
      - destruct q; split; cbn.
        + intros H1 P. eapply IHphi. 2: apply H1. 
          now apply env_p_equiv_symm, env_p_equiv_cons_p.
        + intros H1 P. eapply IHphi. 2: apply H1. 
          now apply env_p_equiv_cons_p.
        + intros [P H1]. exists P. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_symm, env_p_equiv_cons_p.
        + intros [P H1]. exists P. eapply IHphi. 2: apply H1.
          now apply env_p_equiv_cons_p.
    Qed.


    Fixpoint zip {A B : Type} {n : nat} (a : Vector.t A n) (b : Vector.t B n) : Vector.t (A * B) n :=
      match a in Vector.t _ n return Vector.t B n -> Vector.t (A * B) n  with
      | Vector.cons _ ha _ ta => fun b => Vector.cons _ (ha, Vector.hd b) _ (zip ta (Vector.tl b))
      | Vector.nil _ => fun _ => Vector.nil _
      end b.

    Lemma Forall2_Forall_pair {X Y n} (p : X -> Y -> Prop) (v1 : vec X n) (v2 : vec Y n) :
      Forall2 p v1 v2 <-> Forall (fun '(x, y) => p x y) (zip v1 v2).
    Proof.
      induction v1; dependent elimination v2; firstorder.
    Qed.

    Lemma In_zip_1 {X Y n} (v1 : vec X n) (v2 : vec Y n) x y :
      In (x, y) (zip v1 v2) -> In x v1.
    Proof.
      induction v1; dependent elimination v2; cbn; trivial.
      intros [H|H]. inversion H. now left. firstorder.
    Qed.


    Lemma eval_p_ext_bounded rho sigma t :
      (forall x, ~ bounded_indi_term x t -> get_indi_p rho x = get_indi_p sigma x)
      -> (forall x ar, ~ bounded_func_term ar x t -> get_func_p rho x ar = get_func_p sigma x ar)
      -> forall x, eval_p rho t x -> eval_p sigma t x.
    Proof.
      intros Hi Hf. induction t; intros x.
      - intros <-. symmetry. apply Hi. cbn. lia.
      - intros [v' H1]. exists v'. split.
        + destruct H1 as [H1%Forall2_Forall_pair _]. apply Forall2_Forall_pair, Forall_in. intros [t d] H. eapply Forall_in in IH.
          apply IH. intros x' H4. apply Hi. intros H5. apply H4. eapply Forall_in in H5.
          apply H5. eapply In_zip_1; eauto. intros x' ar' H4. apply Hf. intros [[] H5]; apply H4; eapply Forall_in in H5;
          try apply H5; eapply In_zip_1; eauto. eapply Forall_in in H1. 2: apply H. apply H1.
          eapply In_zip_1, H.
        + rewrite <- Hf. apply H1. cbn; lia.
      - intros [v' H1]. exists v'. split.
        + destruct H1 as [H1%Forall2_Forall_pair _]. apply Forall2_Forall_pair, Forall_in. intros [t d] H. eapply Forall_in in IH.
          apply IH. intros x' H4. apply Hi. intros H5. apply H4. eapply Forall_in in H5.
          apply H5. eapply In_zip_1; eauto. intros x' ar' H4. apply Hf. intros H5. apply H4. eapply Forall_in in H5.
          apply H5. eapply In_zip_1; eauto. eapply Forall_in in H1. 2: apply H. apply H1.
          eapply In_zip_1, H.
        + apply H1.
    Qed.

    Lemma sat_p_ext_bounded rho sigma phi :
      (forall x, ~ bounded_indi x phi -> get_indi_p rho x = get_indi_p sigma x)
      -> (forall x ar, ~ bounded_func ar x phi -> get_func_p rho x ar = get_func_p sigma x ar)
      -> (forall x ar, ~ bounded_pred ar x phi -> get_pred_p rho x ar = get_pred_p sigma x ar)
      -> sat_p rho phi <-> sat_p sigma phi.
    Proof.
      revert rho sigma. induction phi; intros rho sigma Hi Hf Hp; cbn.
      - easy.
      - destruct p; split.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1%Forall2_Forall_pair _]. apply Forall2_Forall_pair, Forall_in. intros [t d] H. 
            eapply eval_p_ext_bounded. intros x' H4. apply Hi. intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. intros x' ar' H4. apply Hf.  intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. eapply Forall_in in H1. 2: apply H. apply H1.
          * rewrite <- Hp. apply H1. cbn. lia.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1%Forall2_Forall_pair _]. apply Forall2_Forall_pair, Forall_in. intros [t d] H. 
            eapply eval_p_ext_bounded. intros x' H4. symmetry. apply Hi. intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. intros x' ar' H4. symmetry. apply Hf.  intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. eapply Forall_in in H1. 2: apply H. apply H1.
          * rewrite Hp. apply H1. cbn. lia.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1%Forall2_Forall_pair _]. apply Forall2_Forall_pair, Forall_in. intros [t d] H. 
            eapply eval_p_ext_bounded. intros x' H4. apply Hi. intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. intros x' ar' H4. apply Hf.  intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. eapply Forall_in in H1. 2: apply H. apply H1.
          * apply H1.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1%Forall2_Forall_pair _]. apply Forall2_Forall_pair, Forall_in. intros [t d] H. 
            eapply eval_p_ext_bounded. intros x' H4. symmetry. apply Hi. intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. intros x' ar' H4. symmetry. apply Hf.  intros H5. apply H4. eapply Forall_in in H5.
            apply H5. eapply In_zip_1; eauto. eapply Forall_in in H1. 2: apply H. apply H1.
          * apply H1.
      - specialize (IHphi1 rho sigma ltac:(clear -Hi;firstorder) ltac:(clear -Hf;firstorder) ltac:(clear -Hp;firstorder)).
        specialize (IHphi2 rho sigma ltac:(clear -Hi;firstorder) ltac:(clear -Hf;firstorder) ltac:(clear -Hp;firstorder)).
        destruct b; cbn; tauto.
      - destruct q; split.
        + intros H d. eapply IHphi. 4: apply (H d). intros []. all: firstorder.
        + intros H d. eapply IHphi. 4: apply (H d). intros []. all: firstorder.
        + intros [d H]. exists d. eapply IHphi. 4: apply H. intros []. all: firstorder.
        + intros [d H]. exists d. eapply IHphi. 4: apply H. intros []. all: firstorder.
      - destruct q; split.
        + intros H f HF HT. eapply IHphi. 4: eapply (H f HF HT); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros H f HF HT. eapply IHphi. 4: eapply (H f HF HT); trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [f [HF [HT H]]]. exists f, HF, HT. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [f [HF [HT H]]]. exists f, HF, HT. eapply IHphi. 4: eapply H; trivial. 2: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
      - destruct q; split.
        + intros H P. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros H P. eapply IHphi. 4: eapply (H P); trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [P H]. exists P. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
        + intros [P H]. exists P. eapply IHphi. 4: eapply H; trivial. 3: intros [] ar H4; cbn; destruct Nat.eq_dec as [->|]. all: firstorder.
    Qed.

    Lemma sat_p_ext_closed phi rho sigma :
      bounded_indi 0 phi -> (forall ar, bounded_func ar 0 phi) -> (forall ar, bounded_pred ar 0 phi) 
      -> (sat_p rho phi <-> sat_p sigma phi).
    Proof.
      intros Bi Bf Bp. apply sat_p_ext_bounded.
      - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply Bi. lia.
      - intros x ar H. exfalso. apply H. eapply bounded_func_up. 2: apply Bf. lia.
      - intros x ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply Bp. lia.
    Qed.

    Lemma sat_p_ext_closed_funcfree phi rho sigma :
      funcfree phi -> bounded_indi 0 phi -> (forall ar, bounded_pred ar 0 phi) 
      -> (sat_p rho phi <-> sat_p sigma phi).
    Proof.
      intros F Bi Bp. apply sat_p_ext_bounded.
      - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply Bi. lia.
      - intros x ar H. exfalso. apply H. apply funcfree_bounded_func, F.
      - intros x ar H. exfalso. apply H. eapply bounded_pred_up. 2: apply Bp. lia.
    Qed.

    Lemma sat_p_ext_closed_FO phi rho sigma :
      first_order phi -> bounded_indi 0 phi -> (sat_p rho phi <-> sat_p sigma phi).
    Proof.
      intros F B. apply sat_p_ext_bounded.
      - intros x H. exfalso. apply H. eapply bounded_indi_up. 2: apply B. lia.
      - intros x ar H. exfalso. apply H. apply funcfree_bounded_func, firstorder_funcfree, F.
      - intros x ar H. exfalso. apply H. apply firstorder_bounded_pred, F.
    Qed.

  End PredicateSemantics.


  Section InterpExt_p.

    Variable domain : Type.

    (** Equivalence of interpretations *)

    Definition interp_p_equiv (I1 I2 : interp_p domain) := 
      (forall f v d, proj1_sig (@i_f_p _ I1 f) v d <-> proj1_sig (@i_f_p _ I2 f) v d)
      /\ (forall P v, @i_P_p _ I1 P v <-> @i_P_p _ I2 P v).
    Notation "I1 ≡Ip I2" := (interp_p_equiv I1 I2) (at level 30).

    Lemma interp_p_equiv_sym I1 I2 :
      I1 ≡Ip I2 -> I2 ≡Ip I1.
    Proof.
      firstorder.
    Qed.

    Lemma eval_p_ext_interp I1 I2 rho t :
      I1 ≡Ip I2 -> forall d, @eval_p domain I1 rho t d -> @eval_p domain I2 rho t d.
    Proof.
      intros HI. induction t; intros d; cbn.
      - easy.
      - intros [v' H1]. exists v'. split.
        + destruct H1 as [H1 _]. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
        + apply H1.
      - intros [v' H1]. exists v'. split.
        + destruct H1 as [H1 _]. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
        + apply HI, H1.
    Qed.

    Lemma sat_p_ext_interp I1 I2 rho phi :
      I1 ≡Ip I2 -> @sat_p domain I1 rho phi <-> @sat_p domain I2 rho phi.
    Proof.
      intros H. revert rho. induction phi; intros rho; cbn.
      - reflexivity.
      - destruct p; split.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'.
            easy. split. eapply eval_p_ext_interp with (I1 := I1). apply H. apply H1.
            apply IHv. apply H1.
          * easy.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'.
            easy. split. eapply eval_p_ext_interp. firstorder.
            apply H1. apply IHv. apply H1.
          * easy.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'. 
            easy. split. eapply eval_p_ext_interp with (I1 := I1). apply H. apply H1. 
            apply IHv. apply H1.
          * apply H, H1.
        + intros [v' H1]. exists v'. split.
          * destruct H1 as [H1 _]. induction v; dependent elimination v'. 
            easy. split. eapply eval_p_ext_interp. firstorder.
            apply H1. apply IHv. apply H1.
          * apply H, H1.
      - specialize (IHphi1 rho); specialize (IHphi2 rho). destruct b; tauto.
      - destruct q. split; intros ? ?; now apply IHphi. split; intros [d ?]; exists d; now apply IHphi.
      - destruct q. split; intros ? ? ? ?; now apply IHphi. split; intros [f [Hf1 [Hf2 ?]]]; exists f, Hf1, Hf2; now apply IHphi.
      - destruct q. split; intros ? ?; now apply IHphi. split; intros [P ?]; exists P; now apply IHphi.
    Qed.

  End InterpExt_p.




  Arguments new_env_p {_}.
  Arguments get_indi_p {_}.
  Arguments get_func_p {_}.
  Arguments get_pred_p {_}.
  Arguments env_p_equiv {_}.
  Arguments interp_p_equiv {_}.
  Arguments to_pred_env {_}.
  Notation "⟨⟨ a , b , c ⟩⟩" := (new_env_p a b c).
  Notation "rho1 ≡p rho2" := (env_p_equiv rho1 rho2) (at level 30).
  Notation "I1 ≡Ip I2" := (interp_p_equiv I1 I2) (at level 30).



  (** Under unique choice both semantics are equivalent *)

  Section UniqueChoice.

    Variable domain : Type.

    Definition UniqueChoice X Y := 
      forall (R : X -> Y -> Prop), functional R -> total R -> forall x, { y | R x y }.

    (** We actually only require UC for retalations D^n -> D *)
    Variable UC : forall ar, UniqueChoice (vec domain ar) domain.


    Definition to_func ar (F : func_p domain ar) : { f : vec domain ar -> domain | forall v, proj1_sig F v (f v) }.
    Proof.
      destruct F as [F [F_functional F_total]].
      exists (fun v => proj1_sig (UC _ F F_functional F_total v)).
      intros v; cbn.
      now destruct (UC _ F F_functional F_total v) as [y H].
    Defined.

    Global Instance to_interp (I : interp_p domain) : interp domain := {|
      i_f f := proj1_sig (to_func _ (i_f_p domain f)) ;
      i_P P := i_P_p domain P
    |}.


    (** Auxiliary lemmas for the relationship between to_pred,
        to_func and environments *)

    Lemma to_pred_env_cons_F ar (F : func_p domain ar) (rho : env domain) :
      to_pred_env ⟨ get_indi rho, proj1_sig (to_func _ F) .: get_func rho, get_pred rho ⟩
      ≡p ⟨⟨ get_indi rho, F .: get_func_p (to_pred_env rho), get_pred rho ⟩⟩.
    Proof.
      intros n. split. reflexivity. intros ar' v. split. 2: easy.
      destruct n; cbn.
      - destruct (Nat.eq_dec ar ar') as [->|H]; cbn.
        + destruct (to_func ar' F) as [f Hf]. cbn. split.
          * intros <-. apply Hf.
          * intros H. destruct F as [F [F_functional F_total]]. cbn in *. 
            eapply F_functional. apply Hf. exact H.
        + easy.
      - now destruct (Nat.eq_dec ar ar').
    Qed.

    Lemma to_pred_env_cons_f ar (f : vec domain ar -> domain) (rho : env domain) :
      to_pred_env ⟨ get_indi rho, f .: get_func rho, get_pred rho ⟩ 
      ≡p ⟨⟨ get_indi rho, to_pred _ _ f .: get_func_p (to_pred_env rho), get_pred rho ⟩⟩.
    Proof.
      intros n. split. reflexivity. intros ar' v. split. 2: easy.
      destruct n; cbn.
      - destruct (Nat.eq_dec ar ar') as [->|H]; cbn; easy.
      - now destruct (Nat.eq_dec ar ar').
    Qed.


    (* Main result *)

    Lemma eval_p_eval {I : interp domain} rho t :
      eval_p _ (to_pred_env rho) t (eval _ rho t).
    Proof.
      induction t.
      - reflexivity.
      - exists (map (eval _ rho) v). split. 2: reflexivity. 
        induction v. easy. split. apply IH. apply IHv. apply IH.
      - exists (map (eval _ rho) v). split. 2: reflexivity. 
        induction v. easy. split. apply IH. apply IHv. apply IH.
    Qed.

    Lemma sat_iff_sat_p {I : interp domain} rho phi :
      sat _ rho phi <-> sat_p _ (to_pred_env rho) phi.
    Proof.
      revert rho. induction phi; intros.
      - easy.
      - destruct p; cbn; split.
        + intros H. exists (map (eval domain rho) v). split. 2: exact H.
          clear H. induction v. easy. split. cbn. apply eval_p_eval. apply IHv.
        + intros [v' [H1 H2]]. enough (map (eval domain rho) v = v') by congruence.
          clear H2. induction v; dependent elimination v'. reflexivity.
          cbn. f_equal.
          * eapply eval_p_functional. apply eval_p_eval. apply H1.
          * apply IHv. apply H1.
        + intros H. exists (map (eval domain rho) v). split. 2: exact H.
          clear H. induction v. easy. split. cbn. apply eval_p_eval. apply IHv.
        + intros [v' [H1 H2]]. enough (map (eval domain rho) v = v') by congruence.
          clear H2. induction v; dependent elimination v'. reflexivity.
          cbn. f_equal.
          * eapply eval_p_functional. apply eval_p_eval. apply H1.
          * apply IHv. apply H1.
      - specialize (IHphi1 rho); specialize (IHphi2 rho).
        destruct b; cbn; tauto.
      - destruct q; split.
        + intros H x. cbn. pose (IHphi ⟨x .: get_indi rho, get_func rho, get_pred rho⟩) as X; apply X, H.
        + intros H x. apply IHphi, H.
        + intros [x H]. exists x. pose (IHphi ⟨x .: get_indi rho, get_func rho, get_pred rho⟩) as X; apply X, H.
        + intros [x H]. exists x. apply IHphi, H.
      - destruct q; split.
        + intros H F HF1 HF2. eapply sat_p_ext.
          apply env_p_equiv_symm, to_pred_env_cons_F. apply IHphi, H.
        + intros H f. apply IHphi. cbn in H. eapply sat_p_ext in H. apply H.
          apply to_pred_env_cons_f.
        + intros [f H]. assert (H1 := to_pred_env_cons_f n f rho).
          destruct (to_pred _ _ f) as [F [HF1 HF2]].
          exists F, HF1, HF2. apply IHphi in H. eapply sat_p_ext in H.
          apply H. apply env_p_equiv_symm, H1.
        + intros [F [HF1 [HF2 H]]]. exists (proj1_sig (to_func _ (exist _ F (conj HF1 HF2)))).
          apply IHphi. eapply sat_p_ext.
          apply to_pred_env_cons_F. apply H.
      - destruct q; split.
        + intros H P. cbn. pose (IHphi ⟨get_indi rho, get_func rho, P .: get_pred rho⟩) as X; apply X, H.
        + intros H P. apply IHphi, H.
        + intros [P H]. exists P. pose (IHphi ⟨get_indi rho, get_func rho, P .: get_pred rho⟩) as X; apply X, H.
        + intros [P H]. exists P. apply IHphi, H.
    Qed.


    (** We can also convert predicate environments to function
        environments and get a similar result *)

    Definition to_func_env (rho : env_p domain) : env domain :=
      ⟨ get_indi_p rho, fun n ar => proj1_sig (to_func ar (get_func_p rho n ar)), get_pred_p rho ⟩.

    Lemma to_pred_to_func_env rho :
      rho ≡p to_pred_env (to_func_env rho).
    Proof.
      split. 2: split.
      - reflexivity.
      - cbn. destruct (get_func_p rho n ar) as [F [HF1 HF2]]; cbn.
        destruct (UC _ F HF1 HF2 v) as [x' H]; cbn.
        split. now apply HF1. now intros <-.
      - reflexivity.
    Qed.

    Lemma to_pred_to_func_interp (I : interp_p domain) :
      I ≡Ip to_interp_p _ (to_interp I).
    Proof.
      split. 2: easy. intros f v. cbn. destruct to_func as [P HP].  split.
      - intros H1. destruct i_f_p as [P' [HF HT]]; cbn in *. eapply HF. 
        2: apply H1. cbn. apply HP.
      - intros <-. apply HP.
    Qed.

    Lemma sat_iff_sat_p2 {I : interp_p domain} rho phi :
      sat _ (to_func_env rho) phi <-> sat_p _ rho phi.
    Proof.
      split.
      - intros H%sat_iff_sat_p. eapply sat_p_ext. apply to_pred_to_func_env.
        eapply sat_p_ext_interp in H. apply H. apply to_pred_to_func_interp.
      - intros H. apply sat_iff_sat_p. eapply sat_p_ext. apply env_p_equiv_symm, to_pred_to_func_env.
        eapply sat_p_ext_interp. 2: apply H. apply interp_p_equiv_sym, to_pred_to_func_interp.
    Qed.

  End UniqueChoice.



  (** Substitution Lemmas *)

  Section Substs.

    Variable domain : Type.
    Context {I : interp domain}.

    Arguments eval_function {_ _ _}.
    Arguments eval_predicate {_ _ _}.
    Arguments eval {_ _}.
    Arguments sat {_ _}.

    Lemma eval_function_subst_cons_shift_f (rho : env domain) ar (f : function ar) ar' (g : vec domain ar' -> domain) :
      eval_function rho f = eval_function ⟨ get_indi rho, g .: get_func rho, get_pred rho ⟩ (f[↑ ar']f).
    Proof.
      destruct f.
      - unfold scons, scons_env_func, scons_ar, shift, shift_f; cbn.
        destruct Nat.eq_dec as [->|]; cbn. now destruct Nat.eq_dec.
        destruct n. destruct Nat.eq_dec; try easy. now destruct Nat.eq_dec.
      - reflexivity.
    Qed.

    Lemma eval_predicate_subst_cons_shift_p (rho : env domain) ar (P : predicate ar) ar' (Q : vec domain ar' -> Prop) :
      eval_predicate rho P = eval_predicate ⟨ get_indi rho, get_func rho, Q .: get_pred rho ⟩ (P[↑ ar']p).
    Proof.
      destruct P.
      - unfold scons, scons_env_pred, scons_ar, shift, shift_p; cbn.
        destruct Nat.eq_dec as [->|]; cbn. now destruct Nat.eq_dec.
        destruct n. destruct Nat.eq_dec; try easy. now destruct Nat.eq_dec.
      - reflexivity.
    Qed.

    Lemma eval_subst_cons_shift_f (rho : env domain) ar (f : vec domain ar -> domain) t :
      eval rho t = eval ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ t[↑ ar]f.
    Proof.
      induction t; cbn [eval].
      - reflexivity.
      - rewrite eval_function_subst_cons_shift_f with (g := f).
        cbn. f_equal. rewrite map_map. apply map_ext_forall, IH.
      - cbn. f_equal. rewrite map_map. apply map_ext_forall, IH.
    Qed.

    Lemma eval_comp_i (rho : env domain) σ t :
      eval rho (t[σ]i) = eval ⟨σ >> eval rho, get_func rho, get_pred rho⟩ t.
    Proof.
      induction t; cbn. reflexivity. all: f_equal; rewrite map_map; apply map_ext_forall, IH.
    Qed.

    Lemma eval_comp_f (rho : env domain) σ t :
      eval rho (t[σ]f) = eval ⟨get_indi rho, σ >>> eval_function rho, get_pred rho⟩ t.
    Proof.
      induction t; cbn. reflexivity. all: f_equal; rewrite map_map; apply map_ext_forall, IH.
    Qed.

    Lemma sat_comp_i rho σ phi :
      sat rho (phi[σ]i) <-> sat ⟨σ >> eval rho, get_func rho, get_pred rho⟩ phi.
    Proof.
      induction phi in rho, σ |- *; cbn.
      - reflexivity.
      - destruct p; cbn; erewrite map_map, map_ext; try reflexivity;
        induction v; firstorder using eval_comp_i.
      - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ).
        destruct b; cbn; firstorder.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
          2, 4: apply (H d). all: intros []; split; try easy;
          cbn; erewrite eval_comp_i; now destruct rho.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
          2, 4: apply H. all: intros []; split; try easy;
          cbn; erewrite eval_comp_i; now destruct rho.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H f; eapply sat_ext.
          2, 4: apply (H f). all: split; try easy. 2: symmetry.
          all: apply eval_subst_cons_shift_f.
        + setoid_rewrite IHphi; split; intros [f H]; exists f; eapply sat_ext.
          2, 4: apply H. all: split; try easy. 2: symmetry.
          all: apply eval_subst_cons_shift_f.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H P; eapply sat_ext.
          2, 4: apply (H P). all: split; try easy; now apply eval_ext.
        + setoid_rewrite IHphi; split; intros [P H]; exists P; eapply sat_ext.
          2, 4: apply H. all: split; try easy; now apply eval_ext.
    Qed.

    Lemma sat_comp_f rho σ phi :
      sat rho (phi[σ]f) <-> sat ⟨get_indi rho, σ >>> eval_function rho, get_pred rho⟩ phi.
    Proof.
      induction phi in rho, σ |- *; cbn.
      - reflexivity.
      - destruct p; cbn; erewrite map_map, map_ext; try reflexivity;
        induction v; firstorder using eval_comp_f.
      - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ).
        destruct b; cbn; firstorder.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
          2, 4: apply (H d). all: easy.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
          2, 4: apply H. all: easy.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H f; eapply sat_ext.
          2, 4: apply (H f). 
          all: intros []; repeat split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_function_subst_cons_shift_f with (g := f).
          all: now rewrite <- eval_function_subst_cons_shift_f with (g := f).
        + setoid_rewrite IHphi; split; intros [f H]; exists f; eapply sat_ext.
          2, 4: apply H.
          all: intros []; repeat split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_function_subst_cons_shift_f with (g := f).
          all: now rewrite <- eval_function_subst_cons_shift_f with (g := f).
      - destruct q.
        + setoid_rewrite IHphi; split; intros H P; eapply sat_ext.
          2, 4: apply (H P). all: intros; split; try easy; now apply eval_ext.
        + setoid_rewrite IHphi; split; intros [P H]; exists P; eapply sat_ext.
          2, 4: apply H. all: intros; split; try easy; now apply eval_ext.
    Qed.

    Lemma sat_comp_p rho σ phi :
      sat rho (phi[σ]p) <-> sat ⟨get_indi rho, get_func rho, σ >>> eval_predicate rho⟩ phi.
    Proof.
      induction phi in rho, σ |- *; cbn.
      - reflexivity.
      - destruct p; cbn;
        enough (map (eval rho) v = map (eval ⟨get_indi rho, get_func rho, σ >>> eval_predicate rho⟩) v) as -> by reflexivity;
        apply map_ext_forall; induction v; firstorder; now apply eval_ext.
      - specialize (IHphi1 rho σ); specialize (IHphi2 rho σ).
        destruct b; cbn; firstorder.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext.
          2, 4: apply (H d). all: easy.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext.
          2, 4: apply H. all: easy.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H f; eapply sat_ext.
          2, 4: apply (H f). all: easy.
        + setoid_rewrite IHphi. split; intros [f H]; exists f; eapply sat_ext.
          2, 4: apply H. all: easy.
      - destruct q.
        + setoid_rewrite IHphi; split; intros H P; eapply sat_ext.
          2, 4: apply (H P). 
          all: intros []; split; try easy; split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_predicate_subst_cons_shift_p with (Q := P).
          all: now rewrite <- eval_predicate_subst_cons_shift_p with (Q := P).
        + setoid_rewrite IHphi; split; intros [P H]; exists P; eapply sat_ext.
          2, 4: apply H. 
          all: intros []; split; try easy; split; try easy; cbn; destruct Nat.eq_dec as [->|]; cbn.
          1, 5: destruct Nat.eq_dec; try easy; rewrite uip' with (e := e); try easy; lia.
          1-3: now rewrite eval_predicate_subst_cons_shift_p with (Q := P).
          all: now rewrite <- eval_predicate_subst_cons_shift_p with (Q := P).
    Qed.

  End Substs.


  Section Substs_p.

    Variable domain : Type.
    Context {I : interp_p domain}.

    Arguments eval {_ _}.
    Arguments eval_p {_ _}.
    Arguments sat_p {_ _}.

    Lemma eval_p_comp_i rho σ t :
      (forall n, exists x, σ n = i$x) -> forall d, eval_p rho (t[σ]i) d <-> eval_p ⟨⟨fun n => match σ n with i$x => get_indi_p rho x | _ => get_indi_p rho 0 end, get_func_p rho, get_pred_p rho⟩⟩ t d.
    Proof.
      intros H. induction t; intros d; cbn. 
      - now edestruct (H n) as [x ->].
      - split.
        + intros [v' [H1 H2]]. exists v'. split; trivial.
          clear H2. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
        + intros [v' [H1 H2]]. exists v'. split; trivial.
          clear H2. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
      - split.
        + intros [v' [H1 H2]]. exists v'. split; trivial.
          clear H2. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
        + intros [v' [H1 H2]]. exists v'. split; trivial.
          clear H2. induction v; dependent elimination v'.
          easy. split. apply IH. apply H1. apply IHv. apply IH. apply H1.
    Qed.

    Lemma sat_p_comp_i rho σ phi :
      funcfree phi -> (forall n, exists x, σ n = i$x) -> sat_p rho (phi[σ]i) <-> sat_p ⟨⟨fun n => match σ n with i$x => get_indi_p rho x | _ => get_indi_p rho 0 end, get_func_p rho, get_pred_p rho⟩⟩ phi.
    Proof.
      induction phi in rho, σ |- *; intros F Hsigma; cbn.
      - reflexivity.
      - destruct p; cbn.
        + split.
          * intros [v' [H1 H2]]. exists v'. split; trivial.
            clear H2. induction v; dependent elimination v'.
            easy. split. apply eval_p_comp_i; trivial. apply H1. apply IHv. apply F. apply H1.
          * intros [v' [H1 H2]]. exists v'. split; trivial.
            clear H2. induction v; dependent elimination v'.
            easy. split. apply eval_p_comp_i; trivial. apply H1. apply IHv. apply F. apply H1.
        + split.
          * intros [v' [H1 H2]]. exists v'. split; trivial. cbn in F.
            clear H2. induction v; dependent elimination v'.
            easy. split. apply eval_p_comp_i; trivial. apply H1. apply IHv. apply F. apply H1.
          * intros [v' [H1 H2]]. exists v'. split; trivial. cbn in F.
            clear H2. induction v; dependent elimination v'.
            easy. split. apply eval_p_comp_i; trivial. apply H1. apply IHv. apply F. apply H1.
      - destruct F as [F1 F2]. specialize (IHphi1 rho σ F1); specialize (IHphi2 rho σ F2).
        destruct b; cbn; tauto.
      - destruct q; split.
        + intros H d. specialize (H d). apply IHphi in H; trivial. eapply sat_p_ext. 2: apply H.
          split. 2: easy. destruct n; cbn. reflexivity. now edestruct Hsigma as [x ->].
          intros []; cbn. 2: edestruct Hsigma as [x ->]. all: now eexists.
        + intros H d. specialize (H d). apply IHphi; trivial; revgoals. eapply sat_p_ext. 2: apply H.
          split. 2: easy. destruct n; cbn. reflexivity. now edestruct Hsigma as [x ->].
          intros []; cbn. 2: edestruct Hsigma as [x ->]. all: now eexists.
        + intros [d H]. exists d. apply IHphi in H; trivial. eapply sat_p_ext. 2: apply H.
          split. 2: easy. destruct n; cbn. reflexivity. now edestruct Hsigma as [x ->].
          intros []; cbn. 2: edestruct Hsigma as [x ->]. all: now eexists.
        + intros [d H]. exists d. apply IHphi; trivial; revgoals. eapply sat_p_ext. 2: apply H.
          split. 2: easy. destruct n; cbn. reflexivity. now edestruct Hsigma as [x ->].
          intros []; cbn. 2: edestruct Hsigma as [x ->]. all: now eexists.
      - now exfalso.
      - destruct q; cbn.
        + split; intros H P; specialize (H P). now apply IHphi in H. now apply IHphi.
        + split; intros [P H]; exists P. now apply IHphi in H. now apply IHphi.
    Qed.

  End Substs_p.


  (** Bundle everything we need for a model in a record *)

  Section Model.

    Definition valid A phi :=
      forall D (I : interp D) (rho : env D), (forall a, List.In a A -> sat _ rho a) -> sat _ rho phi.

    Definition validT (T : form -> Prop) phi :=
      forall D (I : interp D) (rho : env D), (forall a, T a -> sat _ rho a) -> sat _ rho phi.

    Record Model := { 
      M_domain : Type ;
      M_interp : interp M_domain
    }.

    Record Model_p := { 
      M_p_domain : Type ;
      M_p_interp : interp_p M_p_domain
    }.

    Coercion M_interp : Model >-> interp.
    Coercion M_p_interp : Model_p >-> interp_p.
    Global Instance M_I M : interp (M_domain M) := M_interp M.
    Global Instance M_p_I M : interp_p (M_p_domain M) := M_p_interp M.


    (* Type class for ⊨ notations *)
    Class Ent X := ent : X -> form -> Prop.
    Notation "X ⊨ phi" := (ent X phi) (at level 20).

    Class EntP X := entp : X -> form -> Prop.
    Notation "X ⊨p phi" := (entp X phi) (at level 20).

    (* rho ⊨ phi *)
    Global Instance ent_env domain I : Ent (env domain) := @sat domain I.
    Global Instance entp_env domain I : EntP (env_p domain) := @sat_p domain I.

    (* H ⊨ phi *)
    Global Instance ent_model : Ent Model := fun M phi => forall rho, @sat (M_domain M) (M_interp M) rho phi.
    Global Instance entp_model : EntP Model_p := fun M phi => forall rho, @sat_p (M_p_domain M) (M_p_interp M) rho phi.


    (** Special record for a model satisfying some theory *)

    Record Model_of (T : form -> Prop) := {
      M_model : Model ;
      M_correct : forall phi, T phi -> M_model ⊨ phi 
    }.

    Record Model_p_of (T : form -> Prop) := {
      M_p_model : Model_p ;
      M_p_correct : forall phi, T phi -> M_p_model ⊨p phi
    }.

    Coercion M_model : Model_of >-> Model.
    Coercion M_p_model : Model_p_of >-> Model_p.

    (* M_of ⊨ phi *)
    Global Instance ent_model_of T : Ent (Model_of T) := fun M phi => forall rho, @sat (M_domain M) (M_interp M) rho phi.
    Global Instance entp_model_of T : EntP (Model_p_of T) := fun M phi => forall rho, @sat_p (M_p_domain M) (M_p_interp M) rho phi.

    (* T ⊨ phi *)
    Global Instance ent_theory : Ent (form -> Prop) := fun T phi => forall M : Model_of T, M ⊨ phi.
    Global Instance entp_theory : EntP (form -> Prop) := fun T phi => forall M : Model_p_of T, M ⊨p phi.

  End Model.


End Tarski.


Arguments new_env {_} _ _ _.
Arguments get_indi {_} _ _.
Arguments get_func {_} _ _.
Arguments get_pred {_} _ _.
Notation "⟨ a , b , c ⟩" := (new_env a b c).

Arguments new_env_p {_} _ _ _.
Arguments get_indi_p {_} _ _.
Arguments get_func_p {_} _ _.
Arguments get_pred_p {_} _ _.
Notation "⟨⟨ a , b , c ⟩⟩" := (new_env_p a b c).

Notation "rho1 ≡ rho2" := (env_equiv _ rho1 rho2) (at level 30).
Notation "rho1 ≡p rho2" := (env_p_equiv _ rho1 rho2) (at level 30).

Arguments sat {_ _ _} _ _, _ _ _ _ _.
Arguments sat_p {_ _ _} _ _, _ _ _ _ _.

(** Dont require the axioms set when extracting info from a model *)
Arguments M_model {_ _ _}.
Arguments M_p_model {_ _ _}.
Arguments M_correct {_ _ _}.
Arguments M_p_correct {_ _ _}.

(* Printing notation for the primitive sat *)
Notation "rho ⊨ phi" := (sat _ rho phi) (at level 20, only printing).
Notation "rho ⊨p phi" := (sat_p _ rho phi) (at level 20, only printing).

(* General entailment symbol notation using typeclass *)
Notation "X ⊨ phi" := (ent X phi) (at level 20).
Notation "X ⊨p phi" := (entp X phi) (at level 20).

(* Special case for Model + Env. Notation level needs to 0, otherwise
   tuples would stop working. *)
Notation "( M , rho ) ⊨ phi" := (@sat _ _ (M_domain M) (M_interp M) rho phi) (at level 0).
Notation "( M , rho ) ⊨p phi" := (@sat_p _ _ (M_p_domain M) (M_p_interp M) rho phi) (at level 0).

(* Declare Coercion on the outside because otherwise the domain
   argument would make problems *)
Coercion to_interp_p : interp >-> interp_p.
