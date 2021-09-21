(** * Incompleteness and Undecidability *)

Require Import SOL.
Require Import FullSyntax.
Require Import Subst.
Require Import Tarski.
Require Import PA.
Require Import Vector List.
Import VectorNotations.
Require Import VectorLib.
Require Import Decidable Enumerable.
Require Import Util.

Require Import Equations.Equations Equations.Prop.DepElim.
Require Import Equations.Equations.
Derive Signature for Vector.t.
Require Import Lia.

Import ListNotations.


Inductive polynomial : Set :=
  | number : nat -> polynomial
  | variable : nat -> polynomial
  | add : polynomial -> polynomial -> polynomial
  | mul : polynomial -> polynomial -> polynomial.

Fixpoint eval_polynomial alpha p :=
  match p with
  | number n => n
  | variable x => alpha x
  | add p q => eval_polynomial alpha p + eval_polynomial alpha q
  | mul p q => eval_polynomial alpha p * eval_polynomial alpha q
  end.

Definition H10 equation := exists alpha, eval_polynomial alpha (fst equation) = eval_polynomial alpha (snd equation).


(** Polynomials have equality deciders and are enumerable *)

Lemma polynomial_eq_dec :
  Decidable.eq_dec polynomial.
Proof.
  intros p. induction p; intros []; try (right; congruence).
  - destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. now left. right; congruence.
  - destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. now left. right; congruence.
  - destruct (IHp1 p) as [->|]. 2: right; congruence.
    destruct (IHp2 p0) as [->|]. now left. right; congruence.
  - destruct (IHp1 p) as [->|]. 2: right; congruence.
    destruct (IHp2 p0) as [->|]. now left. right; congruence.
Qed.


Unset Equations With Funext.

Equations? E_polynomial (n : nat) : option polynomial by wf n lt :=
{
    E_polynomial 0 := Some (number 0) ;
    E_polynomial (S n) := match pi1 (S n) with
      | 0 => Some (number (pi2 (S n)))
      | 1 => Some (variable (pi2 (S n)))
      | 2 => match E_polynomial (pi1 (pi2 (S n))), E_polynomial (pi2 (pi2 (S n))) with
              | Some p, Some q => Some (add p q)
              | _, _ => None
            end
      | 3 => match E_polynomial (pi1 (pi2 (S n))), E_polynomial (pi2 (pi2 (S n))) with
              | Some p, Some q => Some (mul p q)
              | _, _ => None
            end
      | _ => None
    end
}.
Proof.
  all: try apply pi1_pi2_le. all: apply pi2_pi2_le.
Qed.
Next Obligation.
  unfold E_polynomial. Init.unfold_recursor.
  - destruct x. reflexivity. now repeat rewrite H0.
  - destruct n. reflexivity. now repeat rewrite H0.
Defined.

Lemma polynomial_enumerable__T :
  enumerable__T polynomial.
Proof.
  exists E_polynomial. intros p. induction p.
  - exists (embed (0, n)). destruct n.
    + rewrite embed_zero. now funelim (E_polynomial 0).
    + funelim (E_polynomial (embed (0, S n))). now pose (embed_not_zero_r 0 n). 
      now rewrite eqargs, pi1_correct, pi2_correct.
  - exists (embed (1, n)). 
    funelim (E_polynomial (embed (1, n))). now pose (embed_not_zero_l 0 n).
    now rewrite eqargs, pi1_correct, pi2_correct.
  - destruct IHp1 as [n1 H1], IHp2 as [n2 H2]. exists (embed (2, embed (n1, n2))).
    funelim (E_polynomial (embed (2, embed (n1, n2)))). now pose (embed_not_zero_l 1 (embed (n1, n2))).
    now rewrite eqargs, pi1_correct, pi2_correct, pi1_correct, H3, pi2_correct, H4.
  - destruct IHp1 as [n1 H1], IHp2 as [n2 H2]. exists (embed (3, (embed (n1, n2)))).
    funelim (E_polynomial (embed (3, (embed (n1, n2))))). now pose (embed_not_zero_l 2 (embed (n1, n2))).
    now rewrite eqargs, pi1_correct, pi2_correct, pi1_correct, H3, pi2_correct, H4.
Qed.


(** ** Definition of Reduction Function *)

Section Reduction.

  (** Encode diophantine equations as (first-order) formulas *)

  Fixpoint encode_number n := match n with 
    | 0 => zero 
    | S n => σ (encode_number n) 
  end.

  Fixpoint encode_polynomial p := match p with
    | number n => encode_number n
    | variable x => $x
    | add p q => encode_polynomial p ⊕ encode_polynomial q
    | mul p q => encode_polynomial p ⊗ encode_polynomial q
  end.

  Lemma find_largest_variable p :
    { n | bounded_indi_term n (encode_polynomial p) }.
  Proof.
    induction p; cbn.
    - exists 0. now induction n.
    - exists (S n). lia.
    - destruct IHp1 as [n], IHp2 as [m]. destruct (Arith.Compare_dec.le_lt_dec n m).
      + exists m. repeat split. 2: easy.
        now apply (bounded_indi_term_up n m).
      + exists n. repeat split. easy. 
        apply (bounded_indi_term_up m n). lia. easy.
    - destruct IHp1 as [n], IHp2 as [m]. destruct (Arith.Compare_dec.le_lt_dec n m).
      + exists m. repeat split. 2: easy.
        now apply (bounded_indi_term_up n m).
      + exists n. repeat split. easy. 
        apply (bounded_indi_term_up m n). lia. easy.
  Qed.

  Fixpoint exists_n n phi := match n with
    | 0 => phi
    | S n => ∃i exists_n n phi
  end.

  Definition encode_problem equation := match equation with
    | (p, q) => exists_n (max (proj1_sig (find_largest_variable p)) (proj1_sig (find_largest_variable q))) (encode_polynomial p == encode_polynomial q)
  end.


  (** Encoding is closed *)

  Lemma exists_n_switch n phi :
    ∃i exists_n n phi = exists_n n (∃i phi).
  Proof.
    induction n. easy. cbn. now rewrite IHn.
  Qed.

  Lemma exists_n_bounded n phi :
    bounded_indi 0 (exists_n n phi) <-> bounded_indi n phi.
  Proof.
    induction n in phi |- *.
    - easy.
    - cbn [exists_n]. rewrite exists_n_switch. apply IHn.
  Qed.

  Lemma encoding_closed e :
    bounded_indi 0 (encode_problem e).
  Proof.
    destruct e as [p q]; cbn.
    destruct (find_largest_variable p) as [n H1].
    destruct (find_largest_variable q) as [m H2].
    apply exists_n_bounded. cbn.
    destruct (Arith.Compare_dec.le_lt_dec n m).
    - assert (max n m = m) as -> by lia. repeat split. 2: easy.
      now apply (bounded_indi_term_up n m).
    - assert (max n m = n) as -> by lia. repeat split. easy.
      apply (bounded_indi_term_up m n). lia. easy.
  Qed.


  (** Encoding is first-order *)

  Lemma polynomial_first_order p :
    first_order_term (encode_polynomial p).
  Proof.
    induction p; try easy. now induction n.
  Qed.

  Lemma exists_n_first_order n phi :
    first_order phi -> first_order (exists_n n phi).
  Proof.
    now induction n.
  Qed.

  Lemma encoding_first_order e :
    first_order (encode_problem e).
  Proof.
    destruct e as [p q]; cbn.
    destruct (find_largest_variable p) as [n H1].
    destruct (find_largest_variable q) as [m H2].
    apply exists_n_first_order.
    repeat split; apply polynomial_first_order.
  Qed.


  (** Encoding is satisfiable iff the diophantine equation has
      a solution. *)

  Lemma eval_encoding alpha rho p :
    eval (M_domain Standard_PA_Model) ⟨alpha, get_func rho, get_pred rho⟩ (encode_polynomial p) = eval_polynomial alpha p.
  Proof.
    induction p; cbn.
    - induction n. reflexivity. cbn. now repeat f_equal.
    - reflexivity.
    - now repeat f_equal.
    - now repeat f_equal.
  Qed.

  Lemma sat_encoding alpha rho p q :
    sat (M_interp Standard_PA_Model) ⟨alpha, get_func rho, get_pred rho⟩ (encode_polynomial p == encode_polynomial q) 
    <-> eval_polynomial alpha p = eval_polynomial alpha q.
  Proof.
    split.
    - intros H%eq_sem. now repeat rewrite eval_encoding in H.
    - intros. apply eq_sem. now repeat rewrite eval_encoding.
  Qed.

  Section Model.
    Variable M : Model_of PA.

    Lemma exists_n_sat phi n :
      first_order phi -> bounded_indi n phi -> M ⊨ exists_n n phi <-> exists rho, (M, rho) ⊨ phi.
    Proof.
      intros FO B. split.
      - enough (forall rho, (M, rho) ⊨ (exists_n n phi) -> exists sigma, (M, sigma) ⊨ phi) as X.
        { intros H. apply (X (empty_PA_env _)), H. }
        revert phi FO B. induction n; intros phi FO B rho H.
        + now exists rho.
        + cbn [exists_n] in H. rewrite exists_n_switch in H.
          destruct (IHn (∃i phi) FO B rho H) as [sigma [x H1]]. eexists. apply H1.
      - intros [rho H]. revert rho phi FO B H. induction n; intros rho phi FO B H sigma.
        + eapply sat_ext_closed_FO; try easy. apply H.
        + cbn [exists_n]. rewrite exists_n_switch. 
          apply (IHn ⟨fun n => get_indi rho (S n), get_func rho, get_pred rho⟩).
          apply FO. apply B. cbn. exists (get_indi rho 0).
          eapply sat_ext. 2: apply H. split. now induction n0. easy.
    Qed.

    Lemma exists_n_sat_1 rho phi n :
      (M, rho) ⊨ phi -> first_order phi -> bounded_indi n phi -> forall sigma, (M, sigma) ⊨ (exists_n n phi).
    Proof.
      intros. apply exists_n_sat; eauto.
    Qed.

    Lemma exists_n_sat_2 rho phi n :
      (M, rho) ⊨ (exists_n n phi) -> first_order phi -> bounded_indi n phi -> exists sigma, (M, sigma) ⊨ phi.
    Proof.
      intros. eapply exists_n_sat; eauto. intros sigma. eapply sat_ext_closed_FO.
      now apply exists_n_first_order. now apply exists_n_bounded. eassumption.
    Qed.
  End Model.


  (** ** Undecidability *)

  Lemma H10_to_PA_standard_model_sat e :
    H10 e <-> Standard_PA_Model ⊨ encode_problem e.
  Proof.
    split.
    - destruct e as [p q]; cbn; intros [alpha H]; hnf.
      eapply (exists_n_sat_1 Standard_PA_Model).
      + now apply (sat_encoding alpha (empty_PA_env _)).
      + repeat split; apply polynomial_first_order.
      + apply exists_n_bounded. apply (encoding_closed (p, q)).
    - destruct e as [p q]; unfold H10; cbn. intros H.
      specialize (H (empty_PA_env Standard_PA_Model)).
      apply (exists_n_sat_2 Standard_PA_Model) in H.
      + destruct H as [sigma H]. exists (get_indi sigma).
        apply (sat_encoding _ sigma). eapply sat_ext.
        2: apply H. easy.
      + repeat split; apply polynomial_first_order.
      + apply exists_n_bounded. apply (encoding_closed (p, q)).
  Qed.

  Lemma solution_from_PA_model (M : Model_of PA) e :
    M ⊨ encode_problem e -> H10 e.
  Proof.
    intros H. eapply H10_to_PA_standard_model_sat, PA_models_agree_FO with (rho := empty_PA_env _).
    apply encoding_first_order. apply encoding_closed. apply H.
  Qed. 

  Theorem H10_to_PA_model_sat e (M : Model_of PA) :
    H10 e <-> M ⊨ encode_problem e.
  Proof.
    split.
    - intros H. eapply PA_models_agree_FO with (rho := empty_PA_env _).
      apply encoding_first_order. apply encoding_closed.
      now apply H10_to_PA_standard_model_sat.
    - intros H. eapply H10_to_PA_standard_model_sat, PA_models_agree_FO with (rho := empty_PA_env _).
      apply encoding_first_order. apply encoding_closed. apply H.
  Qed.

  Theorem H10_to_PA_validity e :
    H10 e <-> PA ⊨ encode_problem e.
  Proof.
    split.
    - intros H M. now apply H10_to_PA_model_sat.
    - intros H. eapply H10_to_PA_model_sat, (H Standard_PA_Model).
  Qed.

  Theorem H10_to_PA_satisfiability e :
    H10 e <-> exists (M : Model_of PA) rho, (M, rho) ⊨ (encode_problem e).
  Proof.
    split.
    - intros H. exists Standard_PA_Model, (empty_PA_env _).
      now apply H10_to_PA_standard_model_sat.
    - intros [M [rho H]]. apply H10_to_PA_model_sat with (M := M). intros rho'.
      eapply sat_ext_closed_FO. apply encoding_first_order. apply encoding_closed. apply H.
  Qed.

  Theorem H10_to_validity Σf Σp e :
    H10 e <-> forall M : @Model Σf Σp, M ⊨ (∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (embed_form 0 0 0 0 (PA_form --> encode_problem e))).
  Proof.
    split.
    - intros H M. apply PA_model_valid_iff_model_valid. intros M_PA.
      now apply H10_to_PA_model_sat.
    - intros H. now apply H10_to_PA_standard_model_sat, PA_model_valid_iff_model_valid.
  Qed.

  Theorem H10_to_satisfiability Σf Σp e :
    H10 e <-> exists (M : @Model Σf Σp) rho, (M, rho) ⊨ (∃f(0) ∃f(1) ∃f(2) ∃f(2) ∃p(2) (embed_form 0 0 0 0 (PA_form ∧ encode_problem e))).
  Proof.
    split.
    - intros H. apply PA_model_sat_iff_model_sat. exists Standard_PA_Model, (empty_PA_env _).
      now apply H10_to_PA_standard_model_sat.
    - intros [M [rho H]]. edestruct PA_model_sat_iff_model_sat as [_ H1].
      destruct H1 as [M_PA [rho' H1]]. exists M, rho. apply H.
      apply H10_to_PA_model_sat with (M := M_PA). intros rho''. eapply sat_ext_closed_FO.
      apply encoding_first_order. apply encoding_closed. apply H1.
  Qed.

  Theorem H10_to_validity_funcfree e :
    H10 e <-> forall M : Model, M ⊨ (PA_form --> encode_problem e).
  Proof.
    split.
    - intros H M rho HPA. assert (forall phi, PA phi -> forall rho, (M, rho) ⊨ phi) as M_correct.
      { intros phi H1 rho'. repeat destruct H1 as [<-|H1]; try apply HPA. easy. }
      pose (M_PA := {| M_model := M ; M_correct := M_correct |}).
      now apply H10_to_PA_model_sat with (M := M_PA).
    - intros H. apply H10_to_PA_standard_model_sat. intros rho. apply H. cbn.
      repeat split; intros; try congruence. induction d; auto.
  Qed.

  Theorem H10_to_satisfiability_funcfree e :
    H10 e <-> exists (M : Model) rho, (M, rho) ⊨ (PA_form ∧ encode_problem e).
  Proof.
    split.
    - intros H. exists Standard_PA_Model, (empty_PA_env _). split. 
      + cbn. repeat split; intros; try congruence. induction d; auto.
      + now apply H10_to_PA_model_sat.
    - intros [M [rho [HPA H]]]. assert (forall phi, PA phi -> forall rho, (M, rho) ⊨ phi) as M_correct.
      { intros phi H1 rho'. repeat destruct H1 as [<-|H1]; try apply HPA. easy. }
      pose (M_PA := {| M_model := M ; M_correct := M_correct |}).
      eapply H10_to_PA_model_sat with (M := M_PA). intros rho'.
      eapply sat_ext_closed_FO. apply encoding_first_order. apply encoding_closed. 
      apply H.
  Qed.


  (** Undecidability for funcfree fragment *)

  Lemma PA_env_p_exists (M : Model_p) :
    inhabited (env_p (M_p_domain M)).
  Proof.
    destruct (@i_f_p PA_funcs_signature PA_preds_signature (M_p_domain M) _ Zero) as [Z [HF HT]].
    destruct (HT ([])) as [z _].
    assert (forall ar, func_p (M_p_domain M) ar) as F.
    { intros ar. exists (fun _ d => d = z). split.
      now intros v y y' -> ->. intros v. now exists z. }
    econstructor. exact ⟨⟨ fun _ => z, fun _ ar => F ar, fun _ _ _ => True ⟩⟩.
  Qed.

  Section Model.
    Variable M : Model_p_of PA.

    Lemma exists_n_sat_p phi n :
      first_order phi -> bounded_indi n phi -> M ⊨p exists_n n phi <-> exists rho, (M, rho) ⊨p phi.
    Proof.
      intros FO B. split.
      - enough (forall rho, (M, rho) ⊨p (exists_n n phi) -> exists sigma, (M, sigma) ⊨p phi) as X.
        { intros H. destruct (PA_env_p_exists M) as [rho]. apply (X rho), H. }
        revert phi FO B. induction n; intros phi FO B rho H.
        + now exists rho.
        + cbn [exists_n] in H. rewrite exists_n_switch in H.
          destruct (IHn (∃i phi) FO B rho H) as [sigma [x H1]]. eexists. apply H1.
      - intros [rho H]. revert rho phi FO B H. induction n; intros rho phi FO B H sigma.
        + eapply sat_p_ext_closed_FO; try easy. apply H.
        + cbn [exists_n]. rewrite exists_n_switch. 
          apply (IHn ⟨⟨fun n => get_indi_p rho (S n), get_func_p rho, get_pred_p rho⟩⟩).
          apply FO. apply B. cbn. exists (get_indi_p rho 0).
          eapply sat_p_ext. 2: apply H. split. now induction n0. easy.
    Qed.

    Lemma exists_n_sat_p_1 rho phi n :
      (M, rho) ⊨p phi -> first_order phi -> bounded_indi n phi -> forall sigma, (M, sigma) ⊨p (exists_n n phi).
    Proof.
      intros. apply exists_n_sat_p; eauto.
    Qed.

    Lemma exists_n_sat_p_2 rho phi n :
      (M, rho) ⊨p (exists_n n phi) -> first_order phi -> bounded_indi n phi -> exists sigma, (M, sigma) ⊨p phi.
    Proof.
      intros. eapply exists_n_sat_p; eauto. intros sigma. eapply sat_p_ext_closed_FO.
      now apply exists_n_first_order. now apply exists_n_bounded. eassumption.
    Qed.
  End Model.

  Lemma eval_p_encoding alpha rho p :
    eval_p (M_p_domain Standard_PA_Model_p) ⟨⟨alpha, get_func_p rho, get_pred_p rho⟩⟩ (encode_polynomial p) (eval_polynomial alpha p).
  Proof.
    induction p; cbn.
    - induction n; cbn. now exists []. now exists [n].
    - reflexivity.
    - now exists [eval_polynomial alpha p1 ; eval_polynomial alpha p2].
    - now exists [eval_polynomial alpha p1 ; eval_polynomial alpha p2].
  Qed.

  Lemma sat_p_encoding alpha rho p q :
    sat_p (M_p_interp Standard_PA_Model_p) ⟨⟨alpha, get_func_p rho, get_pred_p rho⟩⟩ (encode_polynomial p == encode_polynomial q) 
    <-> eval_polynomial alpha p = eval_polynomial alpha q.
  Proof.
    split.
    - intros [v H]. repeat depelim v. cbn in H. destruct H as [[H1 [H2 _]] H].
      assert (h = eval_polynomial alpha p) as ->. { eapply eval_p_functional. apply H1. apply eval_p_encoding. }
      assert (h0 = eval_polynomial alpha q) as ->. { eapply eval_p_functional. apply H2. apply eval_p_encoding. }
      exact H.
    - intros H. exists [eval_polynomial alpha p ; eval_polynomial alpha q].
      repeat split; cbn; trivial; apply eval_p_encoding.
  Qed.

  Lemma H10_to_PA_standard_model_p_sat e :
    H10 e <-> Standard_PA_Model_p ⊨p encode_problem e.
  Proof.
    destruct (PA_env_p_exists Standard_PA_Model_p) as [rho]. split.
    - destruct e as [p q]; cbn; intros [alpha H]; hnf.
      eapply (exists_n_sat_p_1 Standard_PA_Model_p).
      + now apply (sat_p_encoding alpha rho).
      + repeat split; apply polynomial_first_order.
      + apply exists_n_bounded. apply (encoding_closed (p, q)).
    - destruct e as [p q]; unfold H10; cbn. intros H.
      specialize (H rho).
      apply (exists_n_sat_p_2 Standard_PA_Model_p) in H.
      + destruct H as [sigma H]. exists (get_indi_p sigma).
        apply (sat_p_encoding _ sigma). eapply sat_p_ext.
        2: apply H. easy.
      + repeat split; apply polynomial_first_order.
      + apply exists_n_bounded. apply (encoding_closed (p, q)).
  Qed.



  (** ** Not enumerable *)

  Definition bi_enumerable {X} (P : X -> Prop) := enumerable P /\ enumerable (fun x => ~ P x).

  Lemma bi_enumerable_ext X (P Q : X -> Prop) :
    (forall x, P x <-> Q x) -> bi_enumerable P -> bi_enumerable Q.
  Proof.
    intros H [H1 H2]. split.
    - eapply enumerable_ext. apply H. apply H1.
    - eapply enumerable_ext. intros x. assert (forall P Q, (P <-> Q) -> (~P <-> ~Q)) as H3 by tauto.
      apply H3, H. apply H2.
  Qed.

  Lemma polynomial_pair_enumerable :
    Decidable.eq_dec (polynomial * polynomial).
  Proof.
    intros [p q] [p' q'].
    destruct (polynomial_eq_dec p p') as [->|]. 2: right; congruence.
    destruct (polynomial_eq_dec q q') as [->|]. now left. right; congruence.
  Qed.

  Lemma PA_sat_neg phi :
    first_order phi -> bounded_indi 0 phi -> PA ⊨ (¬ phi) <-> ~ PA ⊨ phi.
  Proof.
    intros FO B. split.
    - intros H1 H2. apply (H1 Standard_PA_Model (empty_PA_env _)). apply H2.
    - intros H1 M rho H2. apply H1. hnf. eapply PA_models_agree_FO; try easy. apply H2.
  Qed.

  Lemma PA_validity_not_enumerable :
    enumerable (fun phi => PA ⊨ phi) -> bi_enumerable H10.
  Proof.
    intros H. eapply bi_enumerable_ext. intros e. symmetry. apply H10_to_PA_validity. split.
    - eapply enumerable_comp with (f := encode_problem) in H.
      + apply H.
      + apply enumerable__T_pair; apply polynomial_enumerable__T.
      + apply form_eq_dec.
    - eapply enumerable_comp with (f := fun x => ¬ encode_problem x) in H.
      + eapply enumerable_ext in H. apply H. cbn. intros e. 
        setoid_rewrite PA_sat_neg. reflexivity. apply encoding_first_order.
        apply encoding_closed.
      + apply enumerable__T_pair; apply polynomial_enumerable__T.
      + apply form_eq_dec.
  Qed.

  Corollary PA_validity_not_enumerable' :
    MP -> enumerable (fun phi => PA ⊨ phi) -> decidable H10.
  Proof.
    intros mp H. apply Post. easy. apply polynomial_pair_enumerable. 
    all: now apply PA_validity_not_enumerable.
  Qed.

  Lemma PA_satisfiability_not_enumerable :
    enumerable (fun phi => exists (M : Model_of PA) rho, (M, rho) ⊨ phi) -> bi_enumerable H10.
  Proof.
    intros H. eapply bi_enumerable_ext. intros e. symmetry. apply H10_to_PA_satisfiability. split.
    - eapply enumerable_comp with (f := encode_problem) in H.
      + apply H.
      + apply enumerable__T_pair; apply polynomial_enumerable__T.
      + apply form_eq_dec.
    - eapply enumerable_comp with (f := fun x => ¬ encode_problem x) in H.
      + eapply enumerable_ext in H. apply H. cbn. intros e. split.
        * intros [M1 [rho1 H1]] [M2 [rho2 H2]]. apply H1.
          eapply PA_models_agree_FO. 3: apply H2. apply encoding_first_order.
          apply encoding_closed.
        * intros H1. exists Standard_PA_Model, (empty_PA_env _). intros H2.
          apply H1. eexists. eexists. apply H2.
      + apply enumerable__T_pair; apply polynomial_enumerable__T.
      + apply form_eq_dec.
  Qed.

  Corollary PA_satisfiability_not_enumerable' :
    MP -> enumerable (fun phi => exists (M : Model_of PA) rho, (M, rho) ⊨ phi) -> decidable H10.
  Proof.
    intros mp H. apply Post. easy. apply polynomial_pair_enumerable. 
    all: now apply PA_satisfiability_not_enumerable.
  Qed.

  Section Signature.

    Context {Σf : funcs_signature}.
    Context {Σp : preds_signature}.

    Context `{eq_dec_Σf : Decidable.eq_dec Σf}.
    Context `{eq_dec_Σp : Decidable.eq_dec Σp}.

    Lemma validity_not_enumerable :
      enumerable (fun phi => forall M : Model, M ⊨ phi) -> bi_enumerable H10.
    Proof.
      intros H. apply PA_validity_not_enumerable; trivial.
      apply enumerable_comp with (f := fun phi => (∀f (0) (∀f (1) (∀f (2) (∀f (2) (∀p (2) embed_form 0 0 0 0 (PA_form --> phi))))))) in H.
      eapply enumerable_ext. 2: apply H.
      - symmetry. apply PA_model_valid_iff_model_valid.
      - apply PA_form_enumerable.
      - apply form_eq_dec.
    Qed.

    Corollary validity_not_enumerable' :
      MP -> enumerable (fun phi => forall M : Model, M ⊨ phi) -> decidable H10.
    Proof.
      intros mp H. apply Post. easy. apply polynomial_pair_enumerable. 
      all: now apply validity_not_enumerable.
    Qed.

    Lemma satisfiability_not_enumerable :
      enumerable (fun phi => exists (M : Model) rho, (M, rho) ⊨ phi) -> bi_enumerable H10.
    Proof.
      intros H. apply PA_satisfiability_not_enumerable; trivial.
      apply enumerable_comp with (f := fun phi => (∃f (0) (∃f (1) (∃f (2) (∃f (2) (∃p (2) embed_form 0 0 0 0 (PA_form ∧ phi))))))) in H.
      eapply enumerable_ext. 2: apply H.
      - symmetry. apply PA_model_sat_iff_model_sat.
      - apply PA_form_enumerable.
      - apply form_eq_dec.
    Qed.

    Lemma satisfiability_not_enumerable' :
      MP -> enumerable (fun phi => exists (M : Model) rho, (M, rho) ⊨ phi) -> decidable H10.
    Proof.
      intros mp H. apply Post. easy. apply polynomial_pair_enumerable. 
      all: now apply satisfiability_not_enumerable.
    Qed.

  End Signature.



  Lemma standard_model_validity_not_enumerable :
    enumerable (fun phi => first_order phi /\ bounded_indi 0 phi /\ Standard_Model ⊨ phi) -> bi_enumerable H10.
  Proof.
    intros H. eapply bi_enumerable_ext. intros e. symmetry.
    apply H10_to_PA_standard_model_sat. split.
    - eapply enumerable_comp with (f := encode_problem) in H.
      + eapply enumerable_ext in H. apply H. cbn. intros x. split.
        easy. intros H1. repeat split; trivial. apply encoding_first_order.
        apply encoding_closed.
      + apply enumerable__T_pair; apply polynomial_enumerable__T.
      + apply form_eq_dec.
    - eapply enumerable_comp with (f := fun x => ¬ encode_problem x) in H.
      + eapply enumerable_ext in H. apply H. cbn. intros x. split.
        intros [_ [_ H1]] H2. apply H1 with (rho := empty_PA_env _), H2. 
        intros H1. repeat split; trivial. apply encoding_first_order.
        apply encoding_closed. intros rho H2. apply H1. intros rho'.
        eapply sat_ext_closed_FO. apply encoding_first_order.
        apply encoding_closed. apply H2.
      + apply enumerable__T_pair; apply polynomial_enumerable__T.
      + apply form_eq_dec.
  Qed.

  Corollary standard_model_validity_not_enumerable' :
    MP -> enumerable (fun phi => first_order phi /\ bounded_indi 0 phi /\ Standard_Model ⊨ phi) -> decidable H10.
  Proof.
    intros mp H. apply Post. easy. apply polynomial_pair_enumerable. 
    all: now apply standard_model_validity_not_enumerable.
  Qed.

End Reduction.


(** ** Incompleteness *)

(* Incompleteness in PA signature*)
Section IncompletenessPA.

  Variable prv : list (@form Σf Σp full_operators) -> @form Σf Σp full_operators -> Prop.
  Notation "T ⊢ phi" := (prv T phi) (at level 20).

  Hypothesis sound : forall A phi, A ⊢ phi -> valid A phi.
  Hypothesis complete : forall A phi, valid A phi -> A ⊢ phi.
  Hypothesis prv_enumerable : forall A, enumerable (fun phi => A ⊢ phi).

  Lemma PA_valid_to_model phi :
    PA ⊨ phi <-> valid PA_L phi.
  Proof.
    split.
    - intros H D I rho H1. pose (M := {| M_domain := D ; M_interp := I |}).
      assert (forall psi, PA psi -> M ⊨ psi) as H2. { 
        intros psi H2 rho'. repeat destruct H2 as [<-|H2]. apply (H1 ax_eq_refl). 2: apply (H1 ax_eq_symm). 3: apply (H1 ax_zero_succ). 4: apply (H1 ax_succ_inj). 5: apply (H1 ax_add_zero). 6: apply (H1 ax_add_rec). 7: apply (H1 ax_mul_zero). 8: apply (H1 ax_mul_rec). 9: apply (H1 ax_ind). 10: easy. all: clear; firstorder.
      } apply (H {| M_model := M ; M_correct := H2 |}).
    - intros H M rho. apply H. intros psi H1. repeat destruct H1 as [<-|H1]; try easy; apply (M_correct M); clear; firstorder.
  Qed.

  Lemma validity_enumerable_PA :
    enumerable (fun phi => PA ⊨ phi).
  Proof.
    eapply enumerable_ext. 2: apply (prv_enumerable PA_L). intros phi. setoid_rewrite PA_valid_to_model.
    split. apply sound. apply complete.
  Qed.

  Theorem Incompleteness_PA :
    bi_enumerable H10.
  Proof.
   apply PA_validity_not_enumerable, validity_enumerable_PA.
  Qed.

  Theorem Incompleteness_PA' :
    MP -> decidable H10.
  Proof.
    intros mp. now apply PA_validity_not_enumerable', validity_enumerable_PA.
  Qed.

End IncompletenessPA.



Section Incompleteness.

  (** Suppose we have a sound and complete deduction system *)

  Context {Σf : funcs_signature}.
  Context {Σp : preds_signature}.

  Variable prv : list (@form Σf Σp full_operators) -> @form Σf Σp full_operators -> Prop.
  Notation "T ⊢ phi" := (prv T phi) (at level 20).

  Hypothesis sound : forall A phi, A ⊢ phi -> valid A phi.
  Hypothesis complete : forall A phi, valid A phi -> A ⊢ phi.
  Hypothesis prv_enumerable : forall A, enumerable (fun phi => A ⊢ phi).

  Lemma valid_to_model phi :
    (forall M : Model, M ⊨ phi) <-> valid ([]) phi.
  Proof.
    split.
    - intros H D I rho H1. apply (H {| M_domain := D ; M_interp := I |}).
    - intros H M rho. apply H. now intros psi H1.
  Qed.

  Context `{eq_dec_Σf : Decidable.eq_dec Σf}.
  Context `{eq_dec_Σp : Decidable.eq_dec Σp}.

  Lemma validity_enumerable :
    enumerable (fun phi => forall M : Model, M ⊨ phi).
  Proof.
    eapply enumerable_ext. 2: apply (prv_enumerable ([])). intros phi. setoid_rewrite valid_to_model.
    split. apply sound. apply complete.
  Qed.

  Theorem Incompleteness :
    bi_enumerable H10.
  Proof.
    apply validity_not_enumerable, validity_enumerable.
  Qed.

  Theorem Incompleteness' :
    MP -> decidable H10.
  Proof.
    intros MP. now apply validity_not_enumerable', validity_enumerable.
  Qed.

End Incompleteness.

