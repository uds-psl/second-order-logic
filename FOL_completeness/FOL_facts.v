(** ** Operations & Properties of FOL* *)

Set Implicit Arguments.
Unset Strict Implicit.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Export FOL List ListLib Lia Vector.
Require Export Decidable Enumerable RelationClasses.
Export ListNotations.

(* **** Setup *)

Instance le_dec x n :
  dec (x <= n).
Proof.
  unfold dec. apply Compare_dec.le_dec.
Qed.

Instance falsity_eq_dec : eq_dec falsity_flag.
Proof.
  intros b b'. unfold dec. decide equality.
Qed.

Ltac capply H := eapply H; try eassumption.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.

Ltac inv H :=
  inversion H; subst; resolve_existT.

Local Notation vector := t.
Hint Constructors vec_in.

Arguments nil {A}.
Arguments cons {A} _ {n}.
Derive Signature for vector.

(* **** Notation *)

Inductive frag_logic_binop : Type :=
| Impl : frag_logic_binop.

Inductive frag_logic_quant : Type :=
| All : frag_logic_quant.

Instance frag_operators : operators :=
  {| binop := frag_logic_binop ; quantop := frag_logic_quant |}.

Global Instance frag_logic_binop_dec :
  eq_dec frag_logic_binop.
Proof.
  intros [] []. now left.
Qed.

Global Instance frag_logic_quant_dec :
  eq_dec frag_logic_quant.
Proof.
  intros [] []. now left.
Qed.


#[export] Hint Immediate frag_operators : typeclass_instances.

Notation "∀ Phi" := (@quant _ _ frag_operators _ All Phi) (at level 50).
Notation "phi '~>' psi" := (@bin _ _ frag_operators _ Impl phi psi) (at level 43, right associativity).
Notation "⊥" := (falsity).
Notation "¬ phi" := (phi ~> ⊥) (at level 20).
Notation "∃ phi" := (¬ ∀ ¬ phi) (at level 56, right associativity).

Section FOL.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* **** Subformula *)

  (*Inductive sf : form -> form -> Prop :=
  | SImplL phi psi : sf phi (phi --> psi)
  | SImplR phi psi : sf psi (phi --> psi)
  | SAll phi t : sf (phi [t .: fun n => var n]) (∀ phi).
  Hint Constructors sf.

  Lemma sf_acc phi rho :
    Acc sf (phi [rho]).
  Proof.
    revert rho; induction phi; intros rho; constructor; intros psi Hpsi; inversion Hpsi;
      subst; eauto.
  Qed.

  Lemma sf_well_founded :
    well_founded sf.
  Proof.
    intros phi. pose proof (sf_acc phi ids) as H. now asimpl in H.
  Qed.*)

  (* **** Formula size *)

  Fixpoint size {ff : falsity_flag} (phi : form ) :=
    match phi with
    | atom _ _ => 0
    | falsity => 0
    | bin Impl phi psi => S (size phi + size psi)
    | quant All phi => S (size phi)
    end.

  Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
    intros H x. apply H.
    induction (f x).
    - intros y. lia.
    - intros y. intros [] % Lt.le_lt_or_eq.
      + apply IHn; lia.
      + apply H. injection H0. now intros ->.
  Qed.

  Lemma subst_size {ff : falsity_flag} rho phi :
    size (subst_form rho phi) = size phi.
  Proof.
    revert rho; induction phi; try destruct b0; try destruct q; intros rho; cbn; congruence.
  Qed.

  Lemma form_ind_subst (P : form -> Prop) :
    P ⊥ -> (forall p v, P (atom p v)) ->
    (forall phi psi, P phi -> P psi -> P (phi ~> psi)) ->
    (forall phi, (forall t, P phi[t..]) -> P (∀ phi)) ->
    forall phi, P phi.
  Proof.
    intros H0 H1 H2 H3 phi.
    induction phi using (@size_ind _ size).
    depelim phi; trivial; try destruct b0; try destruct q.
    - injection H. intros -> % Eqdep_dec.inj_pair2_eq_dec; trivial. decide equality.
    - apply H2; apply H; cbn; lia.
    - apply H3. intros t. apply H.
      cbn. rewrite subst_size. lia.
  Qed.

  (* **** Forall and Vector.t technology **)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, vector A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : vector A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, vector A n -> Type :=
  | vec_inB {n} (v : vector A n) : vec_in a (cons a v)
  | vec_inS a' {n} (v :vector A n) : vec_in a v -> vec_in a (cons a' v).
  Hint Constructors vec_in.

  Lemma strong_term_ind' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.  

  Lemma strong_term_ind (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply strong_term_ind'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inv X; eauto.
  Qed.
  
  (* **** Unused variable **)

  Inductive unused_term (n : nat) : term -> Prop :=
  | uft_var m : n <> m -> unused_term n (var m)
  | uft_Func F v : (forall t, vec_in t v -> unused_term n t) -> unused_term n (func F v).

  Lemma vec_unused n (v : vector term n)  :
    (forall t, vec_in t v -> { n | forall m, n <= m -> unused_term m t }) ->
    { k | forall t, vec_in t v -> forall m, k <= m -> unused_term m t }.
  Proof.
    intros Hun. induction v in Hun |-*.
    - exists 0. intros n H. inv H.
    - destruct IHv as [k H]. 1: eauto. destruct (Hun h (vec_inB h v)) as [k' H'].
      exists (k + k'). intros t H2. inv H2; intros m Hm; [apply H' | apply H]; now try lia.
  Qed.

  Lemma find_unused_term t :
    { n | forall m, n <= m -> unused_term m t }.
  Proof.
    induction t using strong_term_ind.
    - exists (S x). intros m Hm. constructor. lia.
    - destruct (vec_unused X) as [k H]. exists k. eauto using unused_term.
  Qed.

  Inductive unused : forall {ff}, nat -> form ff -> Prop :=
  | uf_Fal n : @unused falsity_on n falsity
  | uf_Pred ff n P v : (forall t, vec_in t v -> unused_term n t) -> @unused ff n (atom P v)
  | uf_Impl ff n phi psi : @unused ff n phi -> @unused ff n psi -> @unused ff n (bin Impl phi psi)
  | uf_All ff n phi : @unused ff (S n) phi -> @unused ff n (quant All phi).
  
  Definition unused_L ff n A := forall phi, phi el A -> @unused ff n phi.
  Definition closed ff phi := forall n, @unused ff n phi.

  Lemma find_unused {ff : falsity_flag} phi :
    { n | forall m, n <= m -> unused m phi }.
  Proof.
    induction phi; try destruct b0; try destruct q.
    - exists 0. intros m _. constructor.
    - destruct (@vec_unused _ t) as [k H]. 1: eauto using find_unused_term. exists k.
      intros m Hm. constructor. intuition.
    - destruct IHphi1, IHphi2. exists (x + x0). intros m Hm. constructor; [ apply u | apply u0 ]; lia.
    - destruct IHphi. exists x. intros m Hm. constructor. apply u. lia.
  Qed.

  Lemma find_unused_L {ff : falsity_flag} A :
    { n | forall m, n <= m -> unused_L m A }.
  Proof.
    induction A.
    - exists 0. unfold unused_L. cbn. intuition.
    - destruct IHA. destruct (find_unused a).
      exists (x + x0). intros m Hm. intros phi []; subst.
      + apply u0. lia.
      + apply u. lia. auto.
  Qed.

  Definition capture {ff : falsity_flag} n phi := nat_rect _ phi (fun _ => quant All) n.

  Lemma capture_captures {ff : falsity_flag} n m phi :
    (forall i, n <= i -> unused i phi) -> (forall i, n - m <= i -> unused i (capture m phi)).
  Proof.
    intros H. induction m; cbn; intros i Hi.
    - rewrite <- Minus.minus_n_O in *. intuition.
    - constructor. apply IHm. lia.
  Qed.

  Definition close {ff : falsity_flag} phi := capture (proj1_sig (find_unused phi)) phi.

  Lemma close_closed {ff : falsity_flag} phi :
    closed (close phi).
  Proof.
    intros n. unfold close. destruct (find_unused phi) as [m Hm]; cbn.
    apply (capture_captures Hm). lia.
  Qed.

  Fixpoint big_imp {ff : falsity_flag} A phi :=
    match A with
    | List.nil => phi
    | a :: A' => a ~> (big_imp A' phi)
    end.

  (* **** Substituting unused variables *)

  Definition shift_P P n :=
    match n with
    | O => False
    | S n' => P n'
    end.

  Lemma vec_map_ext X Y (f g : X -> Y) n (v : vector X n) :
    (forall x, vec_in x v -> f x = g x) -> map f v = map g v.
  Proof.
    intros Hext; induction v in Hext |-*; cbn.
    - reflexivity.
    - rewrite IHv, (Hext h). 1: reflexivity. all: eauto.
  Qed.

  Context {Funcs_eq_dec : eq_dec Σ_funcs}.

  Lemma subst_unused_term xi sigma (P : nat -> Prop) t :
    (forall x, dec (P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused_term m t) ->
    subst_term xi t = subst_term sigma t.
  Proof.
    intros Hdec Hext Hunused. induction t using strong_term_ind; cbn.
    - destruct (Hdec x) as [H % Hunused | H % Hext].
      + inversion H; subst; congruence.
      + congruence.
    - f_equal. apply vec_map_ext. intros t H'. apply (H t H'). intros n H2 % Hunused. inv H2. eauto.
  Qed.

  Context {Preds_eq_dec : eq_dec Σ_preds}.

  Lemma subst_unused_form {ff : falsity_flag} xi sigma P phi :
    (forall x, dec (P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused m phi) ->
    subst_form xi phi = subst_form sigma phi.
  Proof.
    induction phi in xi,sigma,P |-*; intros Hdec Hext Hunused; try destruct b0; try destruct q; cbn.
    - reflexivity.
    - f_equal. apply vec_map_ext. intros s H. apply (subst_unused_term Hdec Hext).
      intros m H' % Hunused. inv H'. eauto. 
    - rewrite IHphi1 with (sigma := sigma) (P := P). rewrite IHphi2 with (sigma := sigma) (P := P).
      all: try tauto. all: intros m H % Hunused; inv H; trivial. now inv H0.
    - erewrite IHphi with (P := shift_P P). 1: reflexivity.
      + intros [| x]; [now right| now apply Hdec].
      + intros [| m]; [reflexivity|]. intros Heq % Hext. cbn. unfold funcomp. congruence.
      + intros [| m]; [destruct 1| ]. intros H % Hunused; now inv H.
  Qed.

  Lemma subst_unused_single {ff : falsity_flag} xi sigma n phi :
    unused n phi -> (forall m, n <> m -> xi m = sigma m) -> subst_form xi phi = subst_form sigma phi.
  Proof.
    intros Hext Hunused. apply subst_unused_form with (P := fun m => n = m). all: intuition.
    now subst.
  Qed.

  Lemma subst_unused_range {ff : falsity_flag} xi sigma phi n :
    (forall m, n <= m -> unused m phi) -> (forall x, x < n -> xi x = sigma x) -> subst_form xi phi = subst_form sigma phi.
  Proof.
    intros Hle Hext. apply subst_unused_form with (P := fun x => n <= x); [ exact _ | |assumption].
    intros ? ? % Compare_dec.not_le; intuition.
  Qed.

  Lemma subst_unused_closed {ff : falsity_flag} xi sigma phi :
    closed phi -> subst_form xi phi = subst_form sigma phi.
  Proof.
    intros Hcl. apply subst_unused_range with (n := 0); intuition. lia.
  Qed.

  Lemma subst_unused_closed' {ff : falsity_flag} xi phi :
    closed phi -> subst_form xi phi = phi.
  Proof.
    intros Hcl. erewrite <- subst_id. 2: reflexivity.
    apply subst_unused_range with (n := 0). all: intuition; lia.
  Qed.

  Lemma vec_forall_map X Y (f : X -> Y) n (v : vector X n) (p : Y -> Type) :
    (forall x, vec_in x v -> p (f x)) -> forall y, vec_in y (map f v) -> p y.
  Proof.
    intros H y Hmap. induction v; cbn; inv Hmap; eauto.
  Qed.

  Lemma unused_after_subst_term t sigma y :
    (forall x, unused_term x t \/ unused_term y (sigma x)) -> unused_term y (subst_term sigma t).
  Proof.
    induction t using strong_term_ind; intros Hvars.
    - destruct (Hvars x) as [H | H]; [inv H; congruence | assumption].
    - constructor. apply vec_forall_map. intros t H'. apply (H t H'). intros x. destruct (Hvars x). 2: tauto.
      left. inv H0. eauto.
  Qed.

  Lemma unused_after_subst {ff : falsity_flag} phi sigma y :
    (forall x, unused x phi \/ unused_term y (sigma x)) -> unused y (subst_form sigma phi).
  Proof.
    intros Hvars. induction phi in Hvars, sigma, y |-*; try destruct b0; try destruct q; cbn; constructor.
    1: apply vec_forall_map; intros s H; apply unused_after_subst_term. 2: apply IHphi1. 3: apply IHphi2.
    1-3: intros x; destruct (Hvars x) as [H' | H']; [left; inv H'; inv H; eauto | tauto].
    apply IHphi. intros [].
    - right. cbn; constructor. congruence.
    - destruct (Hvars n). 1: left; now inv H. right. cbn. unfold ">>".
      apply unused_after_subst_term. intros x. decide (x = y).
      * subst. tauto.
      * right. constructor. unfold "↑". congruence.
  Qed.

  (* **** Theories *)

  Context {ff : falsity_flag}.

  Definition theory := form -> Prop.
  Definition contains phi (T : theory) := T phi.
  Definition contains_L (A : list form) (T : theory) := forall f, f el A -> contains f T.
  Definition subset_T (T1 T2 : theory) := forall (phi : form), contains phi T1 -> contains phi T2.
  Definition list_T A : theory := fun phi => phi el A.

  Infix "⊏" := contains_L (at level 20).
  Infix "⊑" := subset_T (at level 20).
  Infix "∈" := contains (at level 70).

  Hint Unfold contains.
  Hint Unfold contains_L.
  Hint Unfold subset_T.

  Global Instance subset_T_trans : Transitive subset_T.
  Proof.
    intros T1 T2 T3. intuition.
  Qed.

  Definition extend T (phi : form) := fun psi => T psi \/ psi = phi.
  Infix "⋄" := extend (at level 20).

  Definition closed_T (T : theory) := forall phi n, contains phi T -> unused n phi.
  Lemma closed_T_extend T phi :
    closed_T T -> closed phi -> closed_T (T ⋄ phi).
  Proof.
    intros ? ? ? ? []; subst; intuition.
  Qed.

  Section ContainsAutomation.
    Lemma contains_nil T :
      List.nil ⊏ T.
    Proof. intros phi. cbn. intuition. Qed.

    Lemma contains_cons a A T :
      a ∈ T -> A ⊏ T -> (a :: A) ⊏ T.
    Proof. intros ? ? ? []; subst; intuition. Qed.

    Lemma contains_cons2 a A T :
      (a :: A) ⊏ T -> A ⊏ T.
    Proof. firstorder. Qed.

    Lemma contains_app A B T :
      A ⊏ T -> B ⊏ T -> (A ++ B) ⊏ T.
    Proof. intros ? ? ? [] % in_app_or; intuition. Qed.

    Lemma contains_extend1 phi T :
      phi ∈ (T ⋄ phi).
    Proof. now right. Qed.

    Lemma contains_extend2 phi psi T :
      phi ∈ T -> phi ∈ (T ⋄ psi).
    Proof. intros ?. now left. Qed.

    Lemma contains_extend3 A T phi :
      A ⊏ T -> A ⊏ (T ⋄ phi).
    Proof.
      intros ? ? ?. left. intuition.
    Qed.
  End ContainsAutomation.
End FOL.

(*Definition tmap {S1 S2 : Signature} (f : @form S1 -> @form S2) (T : @theory S1) : @theory S2 :=
  fun phi => exists psi, T psi /\ f psi = phi.

Lemma enum_tmap {S1 S2 : Signature} (f : @form S1 -> @form S2) (T : @theory S1) L :
  enum T L -> enum (tmap f T) (L >> List.map f).
Proof.
  intros []. split; unfold ">>".
  - intros n. destruct (H n) as [A ->]. exists (List.map f A). apply map_app.
  - intros x; split.
    + intros (phi & [m Hin] % H0 & <-). exists m. apply in_map_iff. firstorder.
    + intros (m & (phi & <- & Hphi) % in_map_iff). firstorder.
Qed.

Lemma tmap_contains_L {S1 S2 : Signature} (f : @form S1 -> @form S2) T A :
  contains_L A (tmap f T) -> exists B, A = List.map f B /\ contains_L B T.
Proof.
  induction A.
  - intros. now exists List.nil.
  - intros H. destruct IHA as (B & -> & HB). 1: firstorder.
    destruct (H a (or_introl eq_refl)) as (b & Hb & <-).
    exists (b :: B). split. 1: auto. intros ? []; subst; auto.
Qed.*)

Hint Constructors vec_in.

Infix "⊏" := contains_L (at level 20).
Infix "⊑" := subset_T (at level 20).
Infix "∈" := contains (at level 70).
Infix "⋄" := extend (at level 20).

Notation "A ⟹ phi" := (big_imp A phi) (at level 60, right associativity).

Hint Resolve contains_nil contains_cons contains_cons2 contains_app : contains_theory.
Hint Resolve contains_extend1 contains_extend2 contains_extend3 : contains_theory.
Ltac use_theory A := exists A; split; [eauto 15 with contains_theory|].

(* ** Enumerability *)

Section Enumerability.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.

  Variable list_binop : nat -> list binop.
  Hypothesis enum_binop' : list_enumerator__T list_binop binop.

  Variable list_quantop : nat -> list quantop.
  Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.

  Fixpoint vecs_from X (A : list X) (n : nat) : list (vector X n) :=
    match n with
    | 0 => [Vector.nil]
    | S n => [ Vector.cons x v | (x,  v) ∈ (A × vecs_from A n) ]
    end.

  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from (L_term n) (ar_syms F) ] | F ∈ L_T n])
    end.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
    x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vector X n) :
    (forall x, vec_in x v -> x el A) <-> v el vecs_from A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. now dependent elimination v.
      + intros [<- | []] x H. inv H.
    - split.
      + intros. dependent elimination v. in_collect (pair h t0); destruct (IHn t0).
        eauto using vec_inB. apply H0. intros x Hx. apply H. now right. 
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        intros x H. inv H; destruct (IHn v'); eauto.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vector X n) :
    cumulative L -> (forall x, FOL.vec_in x v -> exists m, x el L m) -> exists m, v el vecs_from (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. tauto.
    - destruct IHv as [m H], (Hv h) as [m' H']. 1,3: eauto using vec_inB.
      + intros x Hx. apply Hv. now right.
      + exists (m + m'). in_collect (pair h v). 1: apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H. intros x Hx.
      apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with try (eapply cum_ge'; eauto; lia).
    intros t. induction t using term_rect.
    - exists (S x); cbn; eauto.
    - apply vec_forall_cml in H as [m H]. 2: exact L_term_cml. destruct (el_T F) as [m' H'].
      exists (S (m + m')); cbn. in_app 3. eapply in_concat_iff. eexists. split. 2: in_collect F...
      apply in_map. rewrite <- vecs_from_correct in H |-*. intros x H''. specialize (H x H'')...
  Qed.

  Lemma enumT_term :
    enumerable__T term.
  Proof.
    apply enum_enumT. exists L_term. apply enum_term.
  Qed.

  Fixpoint L_form {ff : falsity_flag} n : list form :=
    match n with
    | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end
    | S n => L_form n
              ++ concat ([ [ atom P v | v ∈ vecs_from (L_term n) (ar_preds P) ] | P ∈ L_T n])
              ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n])
              ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ L_T n])
    end.

  Lemma L_form_cml {ff : falsity_flag} :
    cumulative L_form.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_form {ff : falsity_flag} :
    list_enumerator__T L_form form.
  Proof with (try eapply cum_ge'; eauto; lia).
    intros phi. induction phi.
    - exists 1. cbn; eauto.
    - rename t into v. destruct (el_T P) as [m Hm], (@vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
      exists (S (m + m')); cbn. in_app 2. eapply in_concat_iff. eexists. split.
      2: in_collect P... eapply in_map. rewrite <- vecs_from_correct in *. intuition...
    - destruct (el_T b0) as [m Hm], IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m + m1 + m2). cbn.
      in_app 3. apply in_concat. eexists. split. apply in_map... in_collect (pair phi1 phi2)...
    - destruct (el_T q) as [m Hm], IHphi as [m' Hm']. exists (1 + m + m'). cbn -[L_T].
      in_app 4. apply in_concat. eexists. split. apply in_map... in_collect phi...
  Qed.

End Enumerability.

Definition enumT_form {ff : falsity_flag} {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators} :
  enumerable__T Σ_funcs -> enumerable__T Σ_preds -> enumerable__T binop -> enumerable__T quantop -> enumerable__T form.
Proof.
  intros. apply enum_enumT.
  apply enum_enumT in H as [L1 HL1].
  apply enum_enumT in H0 as [L2 HL2].
  apply enum_enumT in H1 as [L3 HL3].
  apply enum_enumT in H2 as [L4 HL4].
  exists (L_form HL1 HL2 HL3 HL4). apply enum_form.
Qed.

(* **** Subterm relation *)

(*Section Subterm.
  Context {Sigma : Signature}.

  Definition form_shift n := var_term (S n).
  Notation "↑" := form_shift.

  Inductive subterm t : term -> Prop :=
  | stB : subterm t t
  | stF F v s : vec_in s v -> subterm t s -> subterm t (Func F v).

  Inductive subterm_form t : form -> Prop :=
  | stP P v s : vec_in s v -> subterm t s -> subterm_form t (Pred P v)
  | stIL phi psi : subterm_form t phi -> subterm_form t (phi --> psi)
  | stIR phi psi : subterm_form t psi -> subterm_form t (phi --> psi)
  | stA phi : subterm_form t[↑] phi -> subterm_form t (∀ phi).
End Subterm.*)

(* **** Signature extension *)

(*Section SigExt.
  Hint Unfold axioms.funcomp.

  Definition sig_ext (Sigma : Signature) : Signature :=
    match Sigma with
      B_S Funcs fun_ar Preds pred_ar =>
      B_S (Funcs + nat)
          (fun f => match f with inl f' => fun_ar f' | inr _ => 0 end)
          Preds
          pred_ar
    end.

  Global Instance dec_sig_ext_Funcs {Sigma : Signature} (H : eq_dec Funcs) : eq_dec (@Funcs (sig_ext Sigma)).
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    destruct Sigma. intros [] []...
    - decide (f = f0)...
    - decide (n = n0)...
  Qed.

  Global Instance dec_sig_ext_Preds {Sigma : Signature} (H : eq_dec Preds) : eq_dec (@Preds (sig_ext Sigma)).
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    destruct Sigma. exact H. 
  Qed.

  Global Instance enumT_sig_ext_Funcs {Sigma : Signature} (H : enumT Funcs) : enumT (@Funcs (sig_ext Sigma)).
  Proof with (try eapply cum_ge'; eauto; lia).
    destruct Sigma. destruct H. exists (fix f n := match n with 0 => List.map inl (L_T 0) | S n' => f n' ++ (inr n') :: List.map inl (L_T n') end).
    1: eauto. intros []. 2: exists (S n); in_app 2... destruct (el_T f) as [m Hin]. exists (S m). in_app 3. in_collect f...
  Qed.

  Global Instance enumT_sig_ext_Preds {Sigma : Signature} (H : enumT Preds) : enumT (@Preds (sig_ext Sigma)).
  Proof.
    destruct Sigma. exact H.
  Qed.

  Fixpoint sig_lift_term' F F_ar P P_ar (t : @term (B_S F F_ar P P_ar)) :
    (@term (sig_ext (B_S F F_ar P P_ar))) :=
      match t with
      | var_term x => var_term x
      | Func f v => @Func (sig_ext (B_S F F_ar P P_ar)) (inl f) (map (fun x => sig_lift_term' x) v)
      end.

  Definition sig_lift_term {Sigma : Signature} : @term Sigma -> @term (sig_ext Sigma) :=
    match Sigma return @term Sigma -> @term (sig_ext Sigma) with
      B_S Funcs fun_ar Preds pred_ar as S => fun t => sig_lift_term' t
    end.
  Hint Unfold sig_lift_term.

  Fixpoint sig_lift' F F_ar P P_ar (phi : @form (B_S F F_ar P P_ar)) :
    (@form (sig_ext (B_S F F_ar P P_ar))) :=
      match phi with
      | Fal => Fal
      | Pred p v => @Pred (sig_ext (B_S F F_ar P P_ar)) p (map sig_lift_term v)
      | Impl phi psi => Impl (sig_lift' phi) (sig_lift' psi)
      | All phi => All (sig_lift' phi)
      end.

  Definition sig_lift {Sigma : Signature} : @form Sigma -> @form (sig_ext Sigma) :=
    match Sigma return @form Sigma -> @form (sig_ext Sigma) with
      B_S Funcs fun_ar Preds pred_ar as Sig => fun phi => sig_lift' phi
    end.
  Hint Unfold sig_lift.

  Lemma sig_lift_subst_term {Sigma : Signature} xi t :
    sig_lift_term (subst_term xi t) = subst_term (xi >> sig_lift_term) (sig_lift_term t).
  Proof.
    destruct Sigma. induction t using strong_term_ind; comp.
    - reflexivity.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. now apply vec_map_ext.
  Qed.

  Lemma sig_lift_subst {Sigma : Signature} xi phi :
    sig_lift (subst_form xi phi) = subst_form (xi >> sig_lift_term) (sig_lift phi).
  Proof.
    destruct Sigma. induction phi in xi |-*; comp; try congruence.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_map_ext. intros x.
      specialize (sig_lift_subst_term xi x) as ?. now comp.
    - f_equal. rewrite IHphi. comp. apply ext_form. intros []. 1: reflexivity.
      comp. unfold ">>". specialize (sig_lift_subst_term (fun x => var_term (shift x)) (xi n)) as H.
      comp. now rewrite H.
  Qed.

  Fixpoint fin_minus (n m : nat) : (n < m) + {x | x = n - m} :=
    match n, m with
    | n', 0 => inr (exist (fun x => x = n' - 0) n' eq_refl)
    | 0, S m' => inl (le_n_S 0 m' (Nat.le_0_l m'))
    | S n', S m' =>
      match fin_minus n' m' with
      | inr (exist _ x H) => inr (exist _ x H)
      | inl H => inl (le_n_S (S n') m' H)
      end
    end.

  Definition vsubs {Sigma : Signature} (n m : nat) (v : vector term n) (x : nat) : term :=
    match fin_minus x n with
    | inl i => nth_order v i
    | inr (exist _ y _) => var_term (y + m)
    end.
  Hint Unfold vsubs.

  Lemma up_term_term_vsubs {Sigma : Signature }n (v : vector term n) i x :
    up_term_term (vsubs i v) x = vsubs (S i) (cons (var_term 0) (map (subst_term (vsubs 1 nil)) v)) x.
  Proof.
    destruct x; comp. 1: reflexivity. destruct (fin_minus x n); comp.
    - rewrite nth_map with (p2 := Fin.of_nat_lt l). 2: apply Fin.of_nat_ext. apply ext_term. intros y.
      destruct (fin_minus y 0). 1: lia. destruct s; subst. unfold ">>", shift. f_equal; omega.
    - destruct s. comp. now rewrite <- (plus_n_Sm x0 i).
  Qed.

  Fixpoint sig_drop_term' F F_ar P P_ar (n : nat) (t : @term (sig_ext (B_S F F_ar P P_ar))) :
    @term (B_S F F_ar P P_ar) :=
    match t with
    | var_term x => var_term x
    | Func (inl f') v => @Func (B_S F F_ar P P_ar) f' (map (fun x => sig_drop_term' n x) v)
    | Func (inr y) _ => var_term (n + y)
    end.

  Definition sig_drop_term {Sigma : Signature} (n : nat) : @term (sig_ext Sigma) -> @term Sigma :=
    match Sigma return @term (sig_ext Sigma) -> @term Sigma with
      B_S Funcs fun_ar Preds pred_ar as S => sig_drop_term' n
    end.
  Hint Unfold sig_drop_term.

  Fixpoint sig_drop' F F_ar P P_ar (n : nat) (phi : @form (sig_ext (B_S F F_ar P P_ar))) :
    @form (B_S F F_ar P P_ar) :=
      match phi with
      | Fal => Fal
      | Pred p v => @Pred (B_S F F_ar P P_ar) p (map (sig_drop_term n) v)
      | Impl phi psi => Impl (sig_drop' n phi) (sig_drop' n psi)
      | All phi => All (sig_drop' (S n) phi)
      end.

  Definition sig_drop {Sigma : Signature} (n : nat) : @form (sig_ext Sigma) -> @form Sigma :=
    match Sigma return @form (sig_ext Sigma) -> @form Sigma with
      B_S Funcs fun_ar Preds pred_ar as Sig => sig_drop' n
    end.
  Hint Unfold sig_drop.

  Lemma nth_order_map X Y (f : X -> Y) n (v : vector X n) i (H : i < n) :
    nth_order (map f v) H = f (nth_order v H).
  Proof.
    now apply nth_map.
  Qed.

  Lemma sig_drop_subst_term' f f_ar P P_ar t n m i (v : vector (@term (sig_ext (B_S f f_ar P P_ar))) m) :
    sig_drop_term' (n + i) (t [vsubs i v]) = (sig_drop_term' (n + m) t)[vsubs i (map (sig_drop_term' (n + i)) v)].
  Proof.
    induction t using strong_term_ind; comp.
    - destruct (fin_minus x m); comp; [now rewrite nth_order_map | now destruct s].
    - destruct F; comp. 2: destruct (fin_minus (n + m + n0) m); [| destruct s; subst; f_equal]; lia.
      f_equal. erewrite! vec_comp. 2,3 : reflexivity. apply vec_map_ext. intros t Ht. now apply H.
  Qed.

  Lemma sig_drop_subst' f f_ar P P_ar phi n m i (v : vector (@term (sig_ext (B_S f f_ar P P_ar))) m) :
    sig_drop' (n + i) (subst_form (vsubs i v) phi) = subst_form (vsubs i (map (sig_drop_term' (n + i)) v)) (sig_drop' (n + m) phi).
  Proof.
    induction phi in i, m, v |-*. 1,2,3: comp.
    - reflexivity.
    - f_equal. erewrite! vec_comp. 2,3 : reflexivity. apply vec_ext. intros s. now apply sig_drop_subst_term'.
    - now rewrite IHphi1, IHphi2.
    - cbn. f_equal. erewrite ext_form with (s := phi). 2: apply up_term_term_vsubs.
      erewrite ext_form with (s := (sig_drop' (S (n + m)) phi)). 2: apply up_term_term_vsubs.
      specialize (IHphi (S m) (S i) (cons (var_term 0) (map (subst_term (vsubs 1 nil)) v))).
      replace (S (n + i)) with (n + S i) by lia. rewrite IHphi.
      replace (n + S m) with (S (n + m)) by lia. apply ext_form. intros []. 1: reflexivity.
      cbn. unfold vsubs at 1 3. cbn. destruct (fin_minus n0 m); cbn. 2: now destruct s.
      f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_ext. intros t. unfold axioms.funcomp.
      replace (n + S i) with (n + i + 1) by lia. replace (n + i) with (n + i + 0) at 2 by lia.
      change nil with (map (@sig_drop_term' f f_ar P P_ar (n + i + 1)) nil) at 2.
      apply sig_drop_subst_term' with (v := nil) (m := 0) (i := 1) (n := n + i) (t0 := t).
  Qed.

  Definition ext_c' f f_ar P P_ar (n : nat) : term := @Func (sig_ext (B_S f f_ar P P_ar)) (inr n) Vector.nil.
  Definition ext_c {Sigma : Signature} (n : nat) : @term (sig_ext Sigma) :=
    match Sigma with
      B_S f f_ar P P_ar => ext_c' f_ar P_ar n
    end.

  Definition pref {Sigma : Signature} (n : nat) (rho : nat -> term) (x : nat) : term :=
    match fin_minus x n with
    | inl i => var_term x
    | inr (exist _ y _) => rho y
    end.
  Definition raise {Sigma : Signature} (n : nat) (x : nat) : term := var_term (n + x).

  Hint Unfold ext_c' pref raise.

  Lemma up_term_term_pref_ext_c' f (f_ar : f -> nat) P (P_ar : P -> nat) n x :
    up_term_term (pref n (ext_c' f_ar P_ar)) x = pref (S n) (ext_c' f_ar P_ar) x.
  Proof.
    destruct x. 1: reflexivity. comp. destruct (fin_minus x n). 1: now comp; unfold ">>", shift.
    destruct s. now comp.
  Qed.

  Lemma up_term_term_pref_raise {Sigma : Signature} n m x :
    up_term_term (pref n (raise m)) x = pref (S n) (raise (S m)) x.
  Proof.
    destruct x. 1: reflexivity. comp. destruct (fin_minus x n). 1: now comp; unfold ">>", shift.
    destruct s. unfold ">>", shift; now comp.
  Qed.

  Lemma lift_drop_inverse_term' f f_ar P P_ar n (t : @term (B_S f f_ar P P_ar)) :
    sig_drop_term' n (sig_lift_term' t)[pref n (ext_c' f_ar P_ar)] = t[pref n (@raise (B_S f f_ar P P_ar) n)].
  Proof.
    induction t using strong_term_ind; cbn.
    - comp. destruct (fin_minus x n). 1: reflexivity. now destruct s.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_map_ext. intros t Ht. now apply H.
  Qed.

  Lemma lift_drop_inverse' f f_ar P P_ar n (phi : @form (B_S f f_ar P P_ar)) :
    sig_drop' n (subst_form (pref n (ext_c' f_ar P_ar)) (sig_lift' phi)) = subst_form (pref n (@raise (B_S f f_ar P P_ar) n)) phi.
  Proof.
    induction phi in n |-*. 1,2,3: comp.
    - reflexivity.
    - f_equal. erewrite! vec_comp. 2,3: reflexivity. apply vec_ext, lift_drop_inverse_term'.
    - now rewrite IHphi1, IHphi2.
    - cbn. f_equal. erewrite ext_form with (s := phi). 2: apply up_term_term_pref_raise.
      erewrite ext_form with (s := (sig_lift' phi)). 2: apply up_term_term_pref_ext_c'.
      apply IHphi.
  Qed.

  Lemma lift_drop_inverse {Sigma : Signature} phi :
    sig_drop 0 (subst_form ext_c (sig_lift phi)) = phi.
  Proof.
    destruct Sigma. erewrite ext_form with (s := sig_lift phi) (tauterm := @pref (sig_ext (B_S Funcs fun_ar Preds pred_ar)) 0 (ext_c' fun_ar pred_ar)).
    1: comp; rewrite lift_drop_inverse'; apply idSubst_form; now intros [].
    intros x. comp. destruct (fin_minus x 0). 1: lia. destruct s; subst. now replace (x - 0) with x by lia.
  Qed.

  Lemma ext_c'_unused_term f f_ar P P_ar (n : nat) (t : @term (sig_ext (B_S f f_ar P P_ar))) m :
    n <= m -> @unused_term (sig_ext (B_S f f_ar P P_ar)) m t[pref n (ext_c' f_ar P_ar)].
  Proof.
    intros Hm; induction t using strong_term_ind; comp.
    - destruct (fin_minus x n); comp. 1: constructor; lia.
      destruct s. constructor. intros ?. inversion 1.
    - constructor. apply vec_forall_map, H. 
  Qed.

  Lemma ext_c'_unused f f_ar P P_ar (n : nat) (phi : @form (sig_ext (B_S f f_ar P P_ar))) m :
    n <= m -> @unused (sig_ext (B_S f f_ar P P_ar)) m phi[pref n (ext_c' f_ar P_ar)].
  Proof.
    intros Hm; induction phi in n, m, Hm |-*. 1,2,3 : comp; constructor; auto.
    - apply vec_forall_map. intros. capply ext_c'_unused_term.
    - cbn. auto_unfold. erewrite ext_form with (s := phi). 2: apply up_term_term_pref_ext_c'.
      constructor. apply IHphi. lia.
  Qed.

  Lemma lift_ext_c_closes {Sigma : Signature} phi :
    @closed (sig_ext Sigma) (sig_lift phi)[ext_c].
  Proof.
    destruct Sigma. unfold ext_c. intros n. auto_unfold; erewrite ext_form. apply ext_c'_unused with (n := 0) (m := n).
    1: lia. now intros [].
  Qed.

  Lemma lift_ext_c_closes_T {Sigma : Signature} (T : theory) :
    @closed_T (sig_ext Sigma) (tmap (fun psi => (sig_lift psi)[@ext_c Sigma]) T).
  Proof.
    intros ? n [phi [_ <-]]. apply lift_ext_c_closes.
  Qed.
End SigExt.*)
