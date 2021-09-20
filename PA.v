(** * Second-Order Peano Arithmetic *)

Require Import SOL.
Require Import FullSyntax.
Require Import Subst.
Require Import Tarski.
Require Import Vector.
Import VectorNotations.
Require Import VectorLib.
Require Import Decidable Enumerable.
Require Import Util.
Import SubstNotations.

Require Import Equations.Equations Equations.Prop.DepElim.
Derive Signature for Vector.t.
Derive Signature for function.
Derive Signature for predicate.
Require Import Lia.
Require Import PeanoNat.


Inductive PA_funcs : Type := Zero | Succ | Plus | Mult.
Definition PA_funcs_ar (f : PA_funcs ) :=
  match f with
  | Zero => 0
  | Succ => 1
  | Plus => 2
  | Mult => 2
  end.

Inductive PA_preds : Type := Eq : PA_preds.
Definition PA_preds_ar (P : PA_preds) := match P with Eq => 2 end.

Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.


Arguments Vector.cons {_} _ {_} _, _ _ _ _.
Definition zero := func (sym Zero) ([]).
Notation "'σ' x" := (func (sym Succ) ([x])) (at level 37).
Notation "x '⊕' y" := (func (sym Plus) ([x ; y])) (at level 39).
Notation "x '⊗' y" := (func (sym Mult) ([x ; y])) (at level 38).
Notation "x '==' y" := (atom (pred Eq) ([x ; y])) (at level 40).


(** With concrete instances for functions and predicates
    we get a real equality decider. *)

Instance PA_funcs_signature_eq_dec :
  Decidable.eq_dec PA_funcs_signature.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Instance PA_preds_signature_eq_dec :
  Decidable.eq_dec PA_preds_signature.
Proof.
  intros [] []. now left.
Qed.

Definition L_PA_funcs (n : nat) := List.cons Zero (List.cons Succ (List.cons Plus (List.cons Mult List.nil))).
Definition L_PA_preds (n : nat) := List.cons Eq List.nil.

Instance PA_funcs_enum : 
  list_enumerator__T L_PA_funcs PA_funcs.
Proof.
  intros []; exists 0; firstorder.
Qed.

Instance PA_preds_enum : 
  list_enumerator__T L_PA_preds PA_preds.
Proof.
  intros []; exists 0; firstorder.
Qed.

Lemma PA_form_enumerable :
  enumerable__T form.
Proof.
  apply form_enumerable.
  - apply list_enumerable__T_enumerable. exists L_PA_funcs. apply PA_funcs_enum.
  - apply list_enumerable__T_enumerable. exists L_PA_preds. apply PA_preds_enum.
  - apply enumT_binop.
  - apply enumT_quantop.
Qed.



(** ** Axioms *)

Section Model.

  Definition ax_eq_refl :=   ∀i $0 == $0.
  Definition ax_eq_symm :=   ∀i ∀i $1 == $0 --> $0 == $1.
  Definition ax_eq_trans :=  ∀i ∀i ∀i $2 == $1 --> $1 == $0 --> $2 == $0.
  Definition ax_zero_succ := ∀i zero == σ $0 --> fal.
  Definition ax_succ_inj :=  ∀i ∀i σ $1 == σ $0 --> $1 == $0.
  Definition ax_add_zero :=  ∀i zero ⊕ $0 == $0.
  Definition ax_add_rec :=   ∀i ∀i (σ $0) ⊕ $1 == σ ($0 ⊕ $1).
  Definition ax_mul_zero :=  ∀i zero ⊗ $0 == zero.
  Definition ax_mul_rec :=   ∀i ∀i σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0.
  Definition ax_ind := ∀p(1) p$0 ([zero]) --> (∀i p$0 ([$0]) --> p$0 ([σ $0])) --> ∀i p$0 ([$0]).

  Import List ListNotations.
  Definition PA_L := [ ax_eq_refl ; ax_eq_symm ; ax_zero_succ ; ax_succ_inj ; ax_add_zero ; ax_add_rec ; ax_mul_zero ; ax_mul_rec ; ax_ind ].
  Definition PA phi := In phi PA_L.
  Import VectorNotations.

  Lemma PA_enumerable :
    enumerable PA.
  Proof.
    exists (fun n => nth n (map Some PA_L) None). intros phi. split.
    - intros H. repeat destruct H as [<-|H]. 
      now exists 0. now exists 1. now exists 2. now exists 3. now exists 4.
      now exists 5. now exists 6. now exists 7. now exists 8. easy.
    - intros [n H]. assert (forall x y : form, Some x = Some y -> x = y) as Some_inj by congruence.
      do 9 try destruct n as [|n]; try apply Some_inj in H as <-. 1-9: firstorder.
      destruct n; cbn in H; congruence.
  Qed.

  Definition empty_PA_env M : env (M_domain M) := ⟨ fun n => i_f (M_domain M) Zero ([]) , fun n ar v => i_f (M_domain M) Zero ([]), fun n ar v => True ⟩.

  Variable PA_M : Model_of PA.

  Notation "'izero'" := (@i_f _ _ (M_domain (M_model PA_M)) (M_interp (M_model PA_M)) Zero ([])).
  Notation "'iσ' x" := (@i_f _ _ (M_domain (M_model PA_M)) (M_interp (M_model PA_M)) Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_f _ _ (M_domain (M_model PA_M)) (M_interp (M_model PA_M)) Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_f _ _ (M_domain (M_model PA_M)) (M_interp (M_model PA_M)) Mult ([x ; y])) (at level 38).
  Notation "x 'i==' y" := (@i_P _ _ (M_domain (M_model PA_M)) (M_interp (M_model PA_M)) Eq ([x ; y])) (at level 40).

  Lemma eq_reflexive x :
    x i== x.
  Proof. revert x. apply (M_correct PA_M ax_eq_refl ltac:(firstorder) (empty_PA_env _)). Qed.

  Lemma eq_symm x y :
    x i== y -> y i== x.
  Proof. apply (M_correct PA_M ax_eq_symm ltac:(firstorder) (empty_PA_env _)). Qed.

  Lemma zero_succ' x :
    izero i== iσ x -> False.
  Proof. apply (M_correct PA_M ax_zero_succ ltac:(firstorder) (empty_PA_env _)). Qed.

  Lemma succ_inj' x y :
    iσ x i== iσ y -> x i== y.
  Proof. apply (M_correct PA_M ax_succ_inj ltac:(firstorder) (empty_PA_env _)). Qed.

  (** Simplify induction axiom by removing the vector *)
  Lemma induction (P : M_domain PA_M -> Prop) :
    P izero -> (forall x, P x -> P (iσ x)) -> forall x, P x.
  Proof.
    pose (P' := fun v : vec _ 1 => P (Vector.hd v)).
    change (P' ([izero]) -> (forall x, P' ([x]) -> P' ([iσ x])) -> forall x, P' ([x])).
    apply (M_correct PA_M ax_ind ltac:(firstorder) (empty_PA_env _)).
  Qed.

  Lemma case_analysis x :
    x = izero \/ exists x', x = iσ x'.
  Proof.
    revert x. apply induction.
    - now left.
    - intros x _. right. now exists x.
  Qed.

  Lemma eq_sem x y :
    x i== y <-> x = y.
  Proof.
    split.
    - revert x y. apply (induction (fun x => forall y, x i== y -> x = y)).
      + intros y H. destruct (case_analysis y) as [->|[y' ->]].
        * reflexivity. 
        * now apply zero_succ' in H.
      + intros x IH y H. destruct (case_analysis y) as [->|[y' ->]].
        * now apply eq_symm, zero_succ' in H.
        * rewrite (IH y'). reflexivity. now apply succ_inj'.
    - intros ->. apply eq_reflexive.
  Qed.

  Lemma zero_succ x :
    izero = iσ x -> False.
  Proof. intros H%eq_sem. now apply (zero_succ' x). Qed.

  Lemma succ_inj x y :
    iσ x = iσ y -> x = y.
  Proof. intros H%eq_sem. now apply eq_sem, (succ_inj' x y). Qed.

  Lemma add_zero x :
    izero i⊕ x = x.
  Proof. apply eq_sem, (M_correct PA_M ax_add_zero ltac:(firstorder) (empty_PA_env _)). Qed.

  Lemma add_rec x y :
    iσ x i⊕ y = iσ (x i⊕ y).
  Proof. apply eq_sem, (M_correct PA_M ax_add_rec ltac:(firstorder) (empty_PA_env _)). Qed.

  Lemma mul_zero x :
    izero i⊗ x = izero.
  Proof. apply eq_sem, (M_correct PA_M ax_mul_zero ltac:(firstorder) (empty_PA_env _)). Qed.

  Lemma mul_rec x y :
    iσ x i⊗ y = y i⊕ (x i⊗ y).
  Proof. apply eq_sem, (M_correct PA_M ax_mul_rec ltac:(firstorder) (empty_PA_env _)). Qed.


  (** Convert from nat to this model *)

  Fixpoint to_domain n : M_domain PA_M := match n with
    | 0 => izero
    | S n => iσ (to_domain n)
  end.

  Lemma to_domain_add x y :
    to_domain (x + y) = to_domain x i⊕ to_domain y.
  Proof.
    revert y. induction x; intros; cbn.
    - symmetry. apply add_zero.
    - rewrite add_rec. now repeat f_equal.
  Qed.

  Lemma to_domain_mul x y :
    to_domain (x * y) = to_domain x i⊗ to_domain y.
  Proof.
    revert y. induction x; intros; cbn.
    - symmetry. apply mul_zero.
    - rewrite mul_rec. rewrite to_domain_add. now repeat f_equal.
  Qed.

  Lemma to_domain_injective x x' :
    to_domain x = to_domain x' -> x = x'.
  Proof.
    revert x'. induction x; destruct x'.
    - reflexivity.
    - now intros H%zero_succ.
    - intros H. symmetry in H. now apply zero_succ in H.
    - intros H%succ_inj. now rewrite (IHx x').
  Qed.

End Model.



(** ** Standard Model *)

Section StandardModel.

  Definition std_interp_f (f : syms) : vec nat (ar_syms f) -> nat :=
    match f with
      | Zero => fun _ => 0
      | Succ => fun v => S (Vector.hd v)
      | Plus => fun v => Vector.hd v + Vector.hd (Vector.tl v)
      | Mult => fun v => Vector.hd v * Vector.hd (Vector.tl v)
    end.

  Definition std_interp_P (P : preds) : vec nat (ar_preds P) -> Prop :=
    match P with
      | Eq => fun v => Vector.hd v = Vector.hd (Vector.tl v)
    end.

  Instance I_nat : interp nat := {| i_f := std_interp_f ; i_P := std_interp_P |}.

  Definition Standard_Model : Model := {|
    M_domain := nat ;
    M_interp := I_nat
  |}.

  (* Automatically turns into relational interpretation via coercion *)
  Definition Standard_Model_p : Model_p := {|
    M_p_domain := nat ;
    M_p_interp := I_nat
  |}.

  Lemma std_model_correct : 
    forall phi, PA phi -> Standard_Model ⊨ phi.
  Proof.
    intros phi H. repeat try destruct H as [<-|H]; hnf; cbn; try congruence.
    intros rho P H IH n. induction n; auto. easy.
  Qed.

  Lemma std_model_p_correct : 
    forall phi, PA phi -> Standard_Model_p ⊨p phi.
  Proof.
    intros phi H rho. repeat destruct H as [<-|H]; cbn.
    - intros d. now exists [d;d].
    - intros ? ? [v [[-> [-> _]] ?]]. repeat depelim v. now exists [h0;h].
    - intros d [v [[[] [[v' [[]]] []]]]]. repeat depelim v. repeat depelim v'. lia.
    - intros ? ? [v1 [[[v2 [[->]]] [[v3 [[->] ]] ?]] ?]]. repeat depelim v1. repeat depelim v2. repeat depelim v3.
      cbn in *. exists [h1;h2]. cbn. split. easy. lia.
    - intros d. exists [d;d]. repeat split; cbn. exists [0;d]. repeat split; trivial. exact [].
    - intros d1 d2. exists [S d2 + d1; S (d2 + d1)]. repeat split.
      + exists [S d2;d1]. repeat split. now exists [d2].
      + exists [d2 + d1]. repeat split. now exists [d2;d1].
    - intros d. exists [0;0]. repeat split. 2: exact []. exists [0;d]. repeat split. exact [].
    - intros d1 d2. exists [S d1 * d2; d2 + (d1 * d2)]. repeat split.
      + exists [S d1;d2]. repeat split. now exists [d1].
      + exists [d2;d1 * d2]. repeat split. now exists [d1;d2].
    - intros P [v1 [[[_ [_ H1]] _] H2]] H3 d. repeat depelim v1; cbn in *. 
      rewrite <- H1 in H2. induction d as [|d [v2 [[-> _] IH]]].
      + now exists [0].
      + repeat depelim v2. exists [S h0]. repeat split. destruct (H3 h0) as [v3 [[[v4 [[-> _] ?]] ?] ?]]. now exists [h0].
        repeat depelim v3. repeat depelim v4. cbn in *. congruence.
    - now exfalso.
  Qed.

  Definition Standard_PA_Model : Model_of PA := {|
    M_model := Standard_Model ;
    M_correct := std_model_correct ;
  |}.

  Definition Standard_PA_Model_p : Model_p_of PA := {|
    M_p_model := Standard_Model_p ;
    M_p_correct := std_model_p_correct ;
  |}.

End StandardModel.



(** ** Signature Embedding *)

(** We can embed the PA signature into the formula and translate to
    an arbitrary signature. *)

Section EmbedSignature.

  Definition Σf := PA_funcs_signature.
  Definition Σp := PA_preds_signature.
  Context {Σf' : funcs_signature}.
  Context {Σp' : preds_signature}.
  Context {D : Type}.
  Context {I : @interp Σf Σp D}.
  Context {I' : @interp Σf' Σp' D}.

  (* We assume that the PA functions and predicates are inside the
     environment at

        xO = Position of zero
        xS = Position of succ
        xA = Position of add
        xA + 1 = Position of mul

     Replace function and predicate symbols with the corresponding
     variable and shift the existing variables. 
  *)

  Fixpoint embed_term xO xS xA (t : @term Σf) : @term Σf' := match t with
    | var_indi x => var_indi x
    | func (sym Zero) v => func (@var_func _ xO 0) (Vector.map (embed_term xO xS xA) v)
    | func (sym Succ) v => func (@var_func _ xS 1) (Vector.map (embed_term xO xS xA) v)
    | func (sym Plus) v => func (@var_func _ xA 2) (Vector.map (embed_term xO xS xA) v)
    | func (sym Mult) v => func (@var_func _ (S xA) 2) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x 0) v => if Compare_dec.le_lt_dec xO x then func (@var_func _ (S x) 0) (Vector.map (embed_term xO xS xA) v) else func (@var_func _ x 0) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x 1) v => if Compare_dec.le_lt_dec xS x then func (@var_func _ (S x) 1) (Vector.map (embed_term xO xS xA) v) else func (@var_func _ x 1) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x 2) v => if Compare_dec.le_lt_dec xA x then func (@var_func _ (S (S x)) 2) (Vector.map (embed_term xO xS xA) v) else func (@var_func _ x 2) (Vector.map (embed_term xO xS xA) v)
    | func (@var_func _ x ar) v => func (@var_func _ x ar) (Vector.map (embed_term xO xS xA) v)
  end.

  Fixpoint embed_form xO xS xA xEq (phi : @form Σf Σp _) : @form Σf' Σp' _ := match phi with
    | fal => fal
    | atom (pred Eq) v => atom (@var_pred _ xEq 2) (Vector.map (embed_term xO xS xA) v)
    | atom (@var_pred _ x 2) v => if Compare_dec.le_lt_dec xEq x then atom (@var_pred _ (S x) 2) (Vector.map (embed_term xO xS xA) v) else atom (@var_pred _ x 2) (Vector.map (embed_term xO xS xA) v)
    | atom (@var_pred _ x ar) v => atom (@var_pred _ x ar) (Vector.map (embed_term xO xS xA) v)
    | bin op phi psi => bin op (embed_form xO xS xA xEq phi) (embed_form xO xS xA xEq psi)
    | quant_indi op phi => quant_indi op (embed_form xO xS xA xEq phi)
    | quant_func op 0 phi => quant_func op 0 (embed_form (S xO) xS xA xEq phi)
    | quant_func op 1 phi => quant_func op 1 (embed_form xO (S xS) xA xEq phi)
    | quant_func op 2 phi => quant_func op 2 (embed_form xO xS (S xA) xEq phi)
    | quant_func op ar phi => quant_func op ar (embed_form xO xS xA xEq phi)
    | quant_pred op 2 phi => quant_pred op 2 (embed_form xO xS xA (S xEq) phi)
    | quant_pred op ar phi => quant_pred op ar (embed_form xO xS xA xEq phi)
  end.

  Definition pred n := match n with 0 => 0 | S n => n end.

  (* Predicate that states that rho' contains the PA signature inserted at
      positions xO, xS, xA and xEq, and matches up with rho. *)
  Definition env_contains_PA (rho rho' : env D) xO xS xA xEq :=
    (forall n, get_indi rho n = get_indi rho' n) /\
    (forall n ar, get_func rho' n ar = match ar with 
        | 0 => match Compare_dec.lt_eq_lt_dec n xO with inleft (left _) => get_func rho n 0 | inleft (right _) => @i_f _ _ D I Zero | inright _ => get_func rho (pred n) 0 end
        | 1 => match Compare_dec.lt_eq_lt_dec n xS with inleft (left _) => get_func rho n 1 | inleft (right _) => @i_f _ _ D I Succ | inright _ => get_func rho (pred n) 1 end
        | 2 => if Nat.eq_dec n xA then @i_f _ _ D I Plus else match Compare_dec.lt_eq_lt_dec n (S xA) with inleft (left _) => get_func rho n 2 | inleft (right _) => @i_f _ _ D I Mult | inright _ => get_func rho (pred (pred n)) 2 end
        | ar => get_func rho n ar
      end) /\
    (forall n ar, get_pred rho' n ar = match ar with
        | 2 => match Compare_dec.lt_eq_lt_dec n xEq with inleft (left _) => get_pred rho n 2 | inleft (right _) => @i_P _ _ D I Eq | inright _ => get_pred rho (pred n) 2 end
        | ar => get_pred rho n ar
      end).

  Local Arguments Nat.eq_dec : simpl never.
  Local Arguments Compare_dec.lt_eq_lt_dec : simpl never.

  Ltac solve_env E :=
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia; cbn; try rewrite E;
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia;
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia; cbn; try rewrite E;
    try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
    try destruct Nat.eq_dec; try lia.

  Lemma env_contains_PA_scons_i rho rho' xO xS xA xEq d :
    env_contains_PA rho rho' xO xS xA xEq -> env_contains_PA ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ ⟨d .: get_indi rho', get_func rho', get_pred rho'⟩ xO xS xA xEq.
  Proof.
    intros E. split. 2: apply E. intros []. reflexivity. apply E.
  Qed.

  Lemma env_contains_PA_scons_f {rho rho' xO xS xA xEq ar} (f : vec D ar -> D) :
    env_contains_PA rho rho' xO xS xA xEq ->
    match ar with
      | 0 => env_contains_PA ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ (S xO) xS xA xEq
      | 1 => env_contains_PA ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ xO (S xS) xA xEq
      | 2 => env_contains_PA ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ xO xS (S xA) xEq
      | ar => env_contains_PA ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ ⟨get_indi rho', f .: get_func rho', get_pred rho'⟩ xO xS xA xEq
    end.
  Proof.
    intros E. unfold scons, scons_env_func, scons_ar. destruct ar as [|[|[]]];
    split; try apply E; split; try apply E; destruct E as [_ [E2 _]];
    intros [|[|[]]] [|[|[]]]; solve_env E2; reflexivity.
  Qed.

  Lemma env_contains_PA_scons_p {rho rho' xO xS xA xEq ar} (P : vec D ar -> Prop) :
    env_contains_PA rho rho' xO xS xA xEq ->
    match ar with
      | 2 => env_contains_PA ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ ⟨get_indi rho', get_func rho', P .: get_pred rho'⟩ xO xS xA (S xEq)
      | _ => env_contains_PA ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ ⟨get_indi rho', get_func rho', P .: get_pred rho'⟩ xO xS xA xEq
    end.
  Proof.
    intros E. unfold scons, scons_env_func, scons_ar. destruct ar as [|[|[]]];
    split; try apply E; split; try apply E; destruct E as [_ [_ E3]];
    intros [|[|[]]] [|[|[]]]; solve_env E3; reflexivity.
  Qed.

  Lemma embed_term_correct rho rho' xO xS xA xEq t :
    env_contains_PA rho rho' xO xS xA xEq -> @eval Σf Σp D I rho t = @eval Σf' Σp' D I' rho' (embed_term xO xS xA t).
  Proof.
    intros E. induction t; cbn.
    - apply E.
    - destruct E as [_ [E2 _]]. apply map_ext_forall in IH. destruct ar as [|[|[]]];
      try destruct Compare_dec.le_lt_dec; cbn; rewrite E2;
      try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
      try destruct Nat.eq_dec; try lia; now rewrite map_map, IH.
    - destruct E as [_ [E2 _]]. apply map_ext_forall in IH. destruct f; cbn in *; 
      rewrite E2; destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
      try destruct Nat.eq_dec; try lia; now rewrite map_map, IH.
  Qed.

  Lemma embed_form_correct rho rho' xO xS xA xEq phi :
    env_contains_PA rho rho' xO xS xA xEq -> @sat Σf Σp D I rho phi <-> @sat Σf' Σp' D I' rho' (embed_form xO xS xA xEq phi).
  Proof.
    revert rho rho' xO xS xA xEq. induction phi; intros rho rho' xO xS xA xEq E; cbn.
    - reflexivity.
    - assert (map (@eval Σf Σp D I rho) v = map (fun t => @eval Σf' Σp' D I' rho' (embed_term xO xS xA t)) v) as Hv'.
      { clear p. induction v. reflexivity. cbn; f_equal. 
        apply (embed_term_correct _ _ _ _ _ _ _ E). apply IHv. }
      destruct E as [_ [_ E3]]. destruct p; cbn.
      + destruct ar as [|[|[]]];
        try destruct Compare_dec.le_lt_dec; cbn; rewrite E3;
        try destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia;
        now rewrite map_map, Hv'.
      + destruct P; cbn in *. rewrite E3.
        destruct Compare_dec.lt_eq_lt_dec as [[|]|]; try lia.
        now rewrite map_map, Hv'.
    - specialize (IHphi1 rho rho' xO xS xA xEq E);
      specialize (IHphi2 rho rho' xO xS xA xEq E).
      destruct b; tauto.
    - destruct q.
      + split; intros H d; eapply IHphi. 2,4: apply (H d). all: now apply env_contains_PA_scons_i.
      + split; intros [d H]; exists d; eapply IHphi. 2,4: apply H. all: now apply env_contains_PA_scons_i.
    - destruct q; destruct n as [|[|[]]]; split.
      1-8: intros H f; eapply IHphi; try apply (H f); try apply H; now apply (env_contains_PA_scons_f f).
      all: intros [f H]; exists f; eapply IHphi; try apply (H f); try apply H; now apply (env_contains_PA_scons_f f).
    - destruct q; destruct n as [|[|[]]]; split.
      1-8: intros H P; eapply IHphi; try apply (H P); try apply H; now apply (env_contains_PA_scons_p P).
      all: intros [P H]; exists P; eapply IHphi; try apply (H P); try apply H; now apply (env_contains_PA_scons_p P).
  Qed.

End EmbedSignature.



Section EmbedSignatureFuncfree.

  Context {Σf' : funcs_signature}.
  Context {Σp' : preds_signature}.
  Context {D : Type}.
  Context {I : @interp_p Σf Σp D}.
  Context {I' : @interp Σf' Σp' D}.

  Definition sshift k : nat -> term :=
    fun n => match n with 0 => $0 | S n => $(1 + k + n) end.

  Fixpoint embed_term_funcfree (t : @term Σf) : @form Σf' Σp' _ := match t with
    | var_indi x => ∀p(1) atom (var_pred 0) ([var_indi 0]) --> atom (var_pred 0) ([var_indi (S x)])
    | func (sym Zero) v => atom (var_pred 0) ([var_indi 0])
    | func (sym Succ) v => let v' := Vector.map embed_term_funcfree v in 
                              ∃i (Vector.hd v')[sshift 1]i 
                                ∧ atom (var_pred 0) ([i$1 ; i$0])
    | func (sym Plus) v => let v' := Vector.map embed_term_funcfree v in 
                              ∃i (Vector.hd v')[sshift 1]i 
                                ∧ ∃i (Vector.hd (Vector.tl v'))[sshift 2]i
                                    ∧ atom (var_pred 0) ([i$2 ; i$1 ; i$0])
    | func (sym Mult) v => let v' := Vector.map embed_term_funcfree v in 
                              ∃i (Vector.hd v')[sshift 1]i 
                                ∧ ∃i (Vector.hd (Vector.tl v'))[sshift 2]i
                                    ∧ atom (var_pred 1) ([i$2 ; i$1 ; i$0])
    | func (var_func _) _ => atom (var_pred 0) (Vector.nil _)
  end.

  Fixpoint embed_form_funcfree (phi : @form Σf Σp _) : @form Σf' Σp' _ := match phi with
    | fal => fal
    | atom (SOL.pred Eq) v => ∃i embed_term_funcfree (Vector.hd v)
                              ∧ ∃i (embed_term_funcfree (Vector.hd (Vector.tl v)))[sshift 1]i
                                  ∧ atom (var_pred 1) ([i$1 ; i$0])
    | atom (var_pred _) _ => atom (var_pred 0) (Vector.nil _)
    | bin op phi psi => bin op (embed_form_funcfree phi) (embed_form_funcfree  psi)
    | quant_indi op phi => quant_indi op (embed_form_funcfree phi)
    | quant_func op ar phi => quant_func op ar (embed_form_funcfree phi)
    | quant_pred op ar phi => quant_pred op ar (embed_form_funcfree phi)
  end.


  Lemma embed_term_funcfree_funcfree t :
    funcfree (embed_term_funcfree t).
  Proof.
    induction t; try easy. destruct f; repeat depelim v; cbn in *; repeat split;
    apply funcfree_subst_i; try apply IH; now intros [].
  Qed.

  Lemma sat_sshift1' rho_i rho_f rho_p x y (phi : @form Σf' Σp' _) :
    funcfree phi -> ⟨⟨y .: x .: rho_i, rho_f, rho_p⟩⟩ ⊨p phi[sshift 1]i <-> ⟨⟨y .: rho_i, rho_f, rho_p⟩⟩ ⊨p phi.
  Proof.
    intros F. setoid_rewrite sat_p_comp_i; trivial. erewrite sat_p_ext.
    split; eauto. intros n. split. 2: easy. now destruct n. intros []; eexists; reflexivity.
  Qed.

  Lemma sat_sshift2' rho_i rho_f rho_p x y z (phi : @form Σf' Σp' _) :
    funcfree phi -> ⟨⟨z .: y .: x .: rho_i, rho_f, rho_p⟩⟩ ⊨p phi[sshift 2]i <-> ⟨⟨z .: rho_i, rho_f, rho_p⟩⟩ ⊨p phi.
  Proof.
    intros F. setoid_rewrite sat_p_comp_i; trivial. erewrite sat_p_ext.
    split; eauto. intros n. split. 2: easy. now destruct n. intros []; eexists; reflexivity.
  Qed.

  Lemma sat_sshift1 rho_i rho_f rho_p x y (phi : @form Σf' Σp' _) :
    funcfree phi -> ⟨y .: x .: rho_i, rho_f, rho_p⟩ ⊨ phi[sshift 1]i <-> ⟨y .: rho_i, rho_f, rho_p⟩ ⊨ phi.
  Proof.
    intros F. setoid_rewrite sat_comp_i; trivial. erewrite sat_ext.
    split; eauto. intros n. split. 2: easy. now destruct n.
  Qed.

  Lemma sat_sshift2 rho_i rho_f rho_p z x y (phi : @form Σf' Σp' _) :
    funcfree phi -> ⟨z .: y .: x .: rho_i, rho_f, rho_p⟩ ⊨ phi[sshift 2]i <-> ⟨z .: rho_i, rho_f, rho_p⟩ ⊨ phi.
  Proof.
    intros F. setoid_rewrite sat_comp_i; trivial. erewrite sat_ext.
    split; eauto. intros n. split. 2: easy. now destruct n.
  Qed.

  Definition P_zero := fun v => proj1_sig (@i_f_p _ _ D I Zero) (Vector.tl v) (Vector.hd v).
  Definition P_succ := fun v => proj1_sig (@i_f_p _ _ D I Succ) (Vector.tl v) (Vector.hd v).
  Definition P_plus := fun v => proj1_sig (@i_f_p _ _ D I Plus) (Vector.tl v) (Vector.hd v).
  Definition P_mult := fun v => proj1_sig (@i_f_p _ _ D I Mult) (Vector.tl v) (Vector.hd v).
  Definition P_eq := fun v => @i_P_p _ _ D I Eq v.

  Lemma embed_term_funcfree_correct rho rho_f rho_p t :
    first_order_term t -> forall d, @eval_p Σf Σp D I rho t d <-> sat Σf' Σp' D I' ⟨d .: get_indi_p rho, rho_f, P_zero .: P_succ .: P_plus .: P_mult .: P_eq .: rho_p⟩ (embed_term_funcfree t).
  Proof.
    intros F. induction t; intros d; cbn.
    - split. now intros ->. intros H. now apply (H (fun v => Vector.hd v = d)).
    - now exfalso.
    - destruct f; repeat depelim v; cbn in *.
      + split.
        * intros [v' [? ?]]. now repeat depelim v'.
        * intros H. now exists ([]).
      + split.
        * intros [v' [[? ?] ?]]. repeat depelim v'; cbn in *. exists h0. split.
          apply sat_sshift1. apply embed_term_funcfree_funcfree. now apply IH. easy.
        * intros [d1 H]. exists ([d1]). repeat split. apply IH; try easy. 
          eapply sat_sshift1. apply embed_term_funcfree_funcfree. apply H. easy.
      + split.
        * intros [v' [[? ?] ?]]. repeat depelim v'; cbn in *.
          exists h1. split. apply sat_sshift1. apply embed_term_funcfree_funcfree. now apply IH.
          exists h2. split. apply sat_sshift2. apply embed_term_funcfree_funcfree. now apply IH. easy.
        * intros [d1 [H1 [d2 [H2 ?]]]]. exists ([d1 ; d2]). repeat split; try easy; apply IH; try easy. 
          eapply sat_sshift1. apply embed_term_funcfree_funcfree. apply H1.
          eapply sat_sshift2. apply embed_term_funcfree_funcfree. apply H2.
      + split.
        * intros [v' [[? ?] ?]]. repeat depelim v'; cbn in *.
          exists h1. split. apply sat_sshift1. apply embed_term_funcfree_funcfree. now apply IH.
          exists h2. split. apply sat_sshift2. apply embed_term_funcfree_funcfree. now apply IH. easy.
        * intros [d1 [H1 [d2 [H2 ?]]]]. exists ([d1 ; d2]). repeat split; try easy; apply IH; try easy. 
          eapply sat_sshift1. apply embed_term_funcfree_funcfree. apply H1.
          eapply sat_sshift2. apply embed_term_funcfree_funcfree. apply H2.
  Qed.

  Lemma embed_form_funcfree_correct rho rho_f rho_p phi :
    first_order phi -> rho ⊨p phi <-> ⟨get_indi_p rho, rho_f, P_zero .: P_succ .: P_plus .: P_mult .: P_eq .: rho_p⟩ ⊨ embed_form_funcfree phi.
  Proof.
    induction phi in rho |-*; cbn; intros F.
    - reflexivity.
    - destruct p. now exfalso. destruct P. repeat depelim v; cbn in *. split.
      + intros [v' [[? [? ?]] ?]]. repeat depelim v'; cbn in *. 
        exists h1. split. now apply embed_term_funcfree_correct.
        exists h2. split. apply sat_sshift1. apply embed_term_funcfree_funcfree. 
        now apply embed_term_funcfree_correct. easy.
      + intros [d1 [H1 [d2 [H2 ?]]]]. exists ([d1 ; d2]). repeat split; try easy.
        all: eapply embed_term_funcfree_correct; try easy. apply H1.
        eapply sat_sshift1. apply embed_term_funcfree_funcfree. apply H2.
    - destruct F as [F1 F2]. specialize (IHphi1 rho F1); specialize (IHphi2 rho F2).
      destruct b; tauto.
    - destruct q; split; cbn.
      + intros H d. specialize (H d). apply IHphi in H. apply H. easy.
      + intros H d. apply IHphi. easy. apply H.
      + intros [d H]. exists d. apply IHphi in H. apply H. easy.
      + intros [d H]. exists d. apply IHphi. easy. apply H.
    - now exfalso.
    - now exfalso.
  Qed.

End EmbedSignatureFuncfree.





(** Now we can translate satisfiability and validity for arbitrary models
    over arbitrary signatures to PA models. *)

Section PAValidSatTranslation.

  Context `{Σf' : funcs_signature}.
  Context `{Σp' : preds_signature}.

  (* Encode axioms into formula *)
  Definition PA_form :=
    ax_eq_refl ∧ ax_eq_symm ∧ ax_zero_succ ∧ ax_succ_inj ∧ ax_add_zero ∧ ax_add_rec ∧ ax_mul_zero ∧ ax_mul_rec ∧ ax_ind.

  Lemma PA_Model_sat_PA_form (M_PA : Model_of PA) :
    M_PA ⊨ PA_form.
  Proof.
    repeat split; apply (M_correct M_PA); repeat (try (left; reflexivity); try right).
  Qed.

  Lemma PA_model_valid_iff_model_valid (phi : @form PA_funcs_signature PA_preds_signature _) :
    (forall M_PA : Model_of PA, M_PA ⊨ phi) <-> (forall M' : @Model Σf' Σp', M' ⊨ (∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (embed_form 0 0 0 0 (PA_form --> phi)))).
  Proof.
    split.
    - intros H M' rho fO fS fM fA pE.
      pose (I := @B_I PA_funcs_signature PA_preds_signature _ 
                    (fun f => match f with Zero => fO | Succ => fS | Plus => fA | Mult => fM end)
                    (fun P => match P with Eq => pE end )).
      pose (M := {| M_domain := M_domain M' ; M_interp := I |}).
      eapply (embed_form_correct rho).
      + cbn. split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
      + intros H_PA. assert (forall psi, PA psi -> M ⊨ psi) as M_correct. 
        { intros psi H3. repeat try destruct H3 as [<-|H3]; intros rho'; try easy; apply H_PA. }
        apply (H {| M_model := M ; M_correct := M_correct |}).
    - intros H M rho. 
      pose (I' := {| i_f _ _ := @i_f _ _ _ (M_interp M) Zero ([]) ; i_P _ _ := True |} ).
      pose (M' := {| M_domain := M_domain M ; M_interp := I' |}).
      pose (zero' := @i_f _ _ _ (M_interp M) Zero);  pose (succ := @i_f _ _ _ (M_interp M) Succ); pose (plus := @i_f _ _ _ (M_interp M) Plus);  pose (mult := @i_f _ _ _ (M_interp M) Mult); pose (equal := @i_P _ _ _ (M_interp M) Eq).
      specialize (H M' rho zero' succ mult plus equal).
      eapply embed_form_correct in H. apply H. apply PA_Model_sat_PA_form. clear H. cbn. 
      split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
  Qed.

  Lemma PA_model_sat_iff_model_sat (phi : @form PA_funcs_signature PA_preds_signature _) :
    (exists (M_PA : Model_of PA) rho, (M_PA, rho) ⊨ phi) <-> (exists (M' : @Model Σf' Σp') rho, (M', rho) ⊨ (∃f(0) ∃f(1) ∃f(2) ∃f(2) ∃p(2) (embed_form 0 0 0 0 (PA_form ∧ phi)))).
  Proof.
    split.
    - intros [M [rho H]].
      pose (I' := @B_I Σf' Σp' _ (fun f _ => @i_f _ _ _ (M_interp M) Zero ([])) (fun P _ => True )).
      pose (M' := {| M_domain := M_domain M ; M_interp := I' |}).
      exists M', rho.
      exists (@i_f _ _ _ (M_interp M) Zero), (@i_f _ _ _ (M_interp M) Succ), (@i_f _ _ _ (M_interp M) Mult), (@i_f _ _ _ (M_interp M) Plus), (@i_P _ _ _ (M_interp M) Eq).
      eapply (embed_form_correct rho).
      + cbn. split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
      + split. repeat try split; apply (M_correct M); clear; firstorder. apply H.
    - intros [M' [rho [fO [fS [fM [fA [pE H]]]]]]]; cbn -[embed_form] in H.
      pose (I := @B_I PA_funcs_signature PA_preds_signature _ 
                    (fun f => match f with Zero => fO | Succ => fS | Plus => fA | Mult => fM end)
                    (fun P => match P with Eq => pE end )).
      assert (forall psi, PA psi -> {| M_domain := M_domain M' ; M_interp := I |} ⊨ psi) as M_correct. 
      { intros psi H1 rho'. repeat try destruct H1 as [<-|H1]; intros; try easy; apply H. }
      pose (M := {| M_model := {| M_domain := M_domain M' ; M_interp := I |} ; M_correct := M_correct |}).
      exists M, rho. eapply (embed_form_correct rho) in H. apply H.
      split. 2: split. now intros n. now intros [|[|[]]] [|[|[]]]. now intros [] [|[|[]]].
  Qed.

  Definition embed_PA phi := ∀f(0) ∀f(1) ∀f(2) ∀f(2) ∀p(2) (@embed_form Σf' Σp' 0 0 0 0 (PA_form --> phi)).

  Lemma PA_sat_iff_empty_theory_sat (phi : @form PA_funcs_signature PA_preds_signature _) :
    PA ⊨ phi <-> (fun _ => False) ⊨ embed_PA phi.
  Proof.
    split.
    - intros H M. now apply PA_model_valid_iff_model_valid.
    - intros H M. apply PA_model_valid_iff_model_valid. intros M'.
      apply (H {| M_model := M' ; M_correct := (fun _ (f : False) => match f with end) |}).
  Qed.

End PAValidSatTranslation.



Section PAValidSatTranslation_Funcfree.

  Context `{Σf' : funcs_signature}.
  Context `{Σp' : preds_signature}.


  (* Encode axioms into formula *)
  Definition PA_form_embedded :=
    @embed_form_funcfree Σf' Σp' (ax_eq_refl ∧ ax_eq_symm ∧ ax_zero_succ ∧ ax_succ_inj ∧ ax_add_zero ∧ ax_add_rec ∧ ax_mul_zero ∧ ax_mul_rec)
    ∧ ∀p(1) (∃i p$1 ([$0]) ∧ p$0 ([$0])) --> (∀i p$0 ([$0]) --> (∃i p$0 ([$0 ; $1]) ∧ p$0 ([$0]))) --> ∀i p$0 ([$0]).

  Definition total_functional0 x := (∃i p$x ([$0])) ∧ (∀i ∀i p$x ([$1]) --> p$x ([$0]) --> ∀p(1) p$0 ([$1]) --> p$0 ([$0])).
  Definition total_functional1 x := (∀i ∃i p$x ([$0 ; $1])) ∧ (∀i ∀i ∀i p$x ([$1 ; $2]) --> p$x ([$0 ; $2]) --> ∀p(1) p$0 ([$1]) --> p$0 ([$0])).
  Definition total_functional2 x := (∀i ∀i ∃i p$x ([$0 ; $1 ; $2])) ∧ (∀i ∀i ∀i ∀i p$x ([$1 ; $2 ; $3]) --> p$x ([$0 ; $2 ; $3]) --> ∀p(1) p$0 ([$1]) --> p$0 ([$0])).

  Definition all_total_functional := total_functional0 0 ∧ total_functional1 0 ∧ total_functional2 0 ∧ total_functional2 1.

  Lemma total_functional0_correct (M : Model) rho x :
    functional (fun v d => get_pred rho x 1 (Vector.cons _ d _ v)) /\ total (fun v d => get_pred rho x 1 (Vector.cons _ d _ v)) -> (M, rho) ⊨ (total_functional0 x).
  Proof.
    intros [HF HT]. cbn. split.
    - intros. apply HT.
    - intros d1 d2 ? ?. now rewrite (HF ([]) d1 d2).
  Qed.

  Lemma total_functional1_correct (M : Model) rho x :
    functional (fun v d => get_pred rho x 2 (Vector.cons _ d _ v)) /\ total (fun v d => get_pred rho x 2 (Vector.cons _ d _ v)) -> (M, rho) ⊨ (total_functional1 x).
  Proof.
    intros [HF HT]. cbn. split.
    - intros. apply HT.
    - intros a d1 d2 ? ?. now rewrite (HF ([a]) d1 d2).
  Qed.

  Lemma total_functional2_correct (M : Model) rho x :
    functional (fun v d => get_pred rho x 3 (Vector.cons _ d _ v)) /\ total (fun v d => get_pred rho x 3 (Vector.cons _ d _ v)) -> (M, rho) ⊨ (total_functional2 x).
  Proof.
    intros [HF HT]. cbn. split.
    - intros. apply HT.
    - intros a1 a2 d1 d2 ? ?. now rewrite (HF ([a2 ; a1]) d1 d2).
  Qed.

  Lemma PA_model_valid_iff_model_valid_funcfree (phi : @form PA_funcs_signature PA_preds_signature _) :
    first_order phi -> (forall M_PA : Model_p_of PA, M_PA ⊨p phi) <-> (forall M' : Model, M' ⊨ (∀p(2) ∀p(3) ∀p(3) ∀p(2) ∀p(1) all_total_functional --> PA_form_embedded --> (embed_form_funcfree phi))).
  Proof.
    intros FO. split.
    - intros H M' rho PE PM P_A PS PO H1 H_PA. cbn [get_indi get_func get_pred] in *.
      assert (functional (fun v d => PO (Vector.cons d v)) /\ total (fun v d => PO (Vector.cons d v))) as HPO.
      { destruct H1 as [[[[HF HT] _] _] _]. split. intros v y y' H2 H3. depelim v. now apply (HT y y' H2 H3 (fun v => y = Vector.hd v)). intros v. depelim v. apply HF. }
      assert (functional (fun v d => PS (Vector.cons d v)) /\ total (fun v d => PS (Vector.cons d v))) as HPS.
      { destruct H1 as [[[_ [HF HT]] _] _]. split. intros v y y' H2 H3. repeat depelim v. now apply (HT h y y' H2 H3 (fun v => y = Vector.hd v)). intros v. repeat depelim v. apply HF. }
      assert (functional (fun v d => P_A (Vector.cons d v)) /\ total (fun v d => P_A (Vector.cons d v))) as HPA.
      { destruct H1 as [[[_ _] [HF HT]] _]. split. intros v y y' H2 H3. repeat depelim v. now apply (HT h0 h y y' H2 H3 (fun v => y = Vector.hd v)). intros v. repeat depelim v. apply HF. }
      assert (functional (fun v d => PM (Vector.cons d v)) /\ total (fun v d => PM (Vector.cons d v))) as HPM.
      { destruct H1 as [[[_ _] _] [HF HT]]. split. intros v y y' H2 H3. repeat depelim v. now apply (HT h0 h y y' H2 H3 (fun v => y = Vector.hd v)). intros v. repeat depelim v. apply HF. }
      Existing Instance PA_funcs_signature.
      Existing Instance PA_preds_signature.
      pose (I := {| i_f_p f := match f with Zero => exist _ (fun v d => PO (Vector.cons d v)) HPO | Succ => exist _ (fun v d => PS (Vector.cons d v)) HPS | Plus => exist _ (fun v d => P_A (Vector.cons d v)) HPA | Mult => exist _ (fun v d => PM (Vector.cons d v)) HPM end ;
                    i_P_p P := match P with Eq => PE end |}).
      pose (M := {| M_p_domain := M_domain M' ; M_p_interp := I |}).
      destruct rho as [rho_i rho_f rho_p]. cbn [get_indi get_func get_pred] in *.
      eapply sat_ext.
      2: apply (embed_form_funcfree_correct ⟨⟨rho_i, fun _ _ => default_func_p _ (rho_i 0), rho_p⟩⟩); trivial.
      + intros n. split. reflexivity. intros ar. split. reflexivity.
        destruct n as [|[|[]]]; destruct ar as [|[|[]]]; cbn -[PeanoNat.Nat.eq_dec];
        repeat (try rewrite nat_eq_dec_same; try destruct Nat.eq_dec as [e|]; try lia; try destruct e); try reflexivity.
        all: now repeat depelim v.
      + assert (forall psi, PA psi -> M ⊨p psi) as M_correct. 
        { destruct H_PA as [H_PA1 H_PA2]. eapply sat_ext in H_PA1. eapply (embed_form_funcfree_correct ⟨⟨rho_i, fun _ _ => default_func_p _ (rho_i 0), rho_p⟩⟩) in H_PA1.
          * intros psi H2 rho. repeat destruct H2 as [<-|H2]; try easy; try apply H_PA1.
            cbn. cbn in H_PA2. intros P [v1 [[[v2 [? ?]] ?] ?]] H_IH d. 
            repeat depelim v1. repeat depelim v2. exists ([d]). repeat split.
            apply H_PA2. now exists h. intros d' ?. destruct (H_IH d') as [v3 [[[v4 [[-> ?] ?]] ?] ?]].
            now exists ([d']). repeat depelim v3. repeat depelim v4. now exists h1.
          * easy.
          * intros n. split. reflexivity. intros ar. split. reflexivity.
            destruct n as [|[|[]]]; destruct ar as [|[|[]]]; cbn -[PeanoNat.Nat.eq_dec];
            repeat (try rewrite nat_eq_dec_same; try destruct Nat.eq_dec as [e|]; try lia; try destruct e); try reflexivity.
            all: now repeat depelim v. }
        apply (H {| M_p_model := M ; M_p_correct := M_correct |}).
    - intros H M rho.
      Existing Instance Σf'. Existing Instance Σp'.
      pose (I' := {| i_f _ _ := get_indi_p rho 0 ; i_P _ _ := True |} ).
      pose (M' := {| M_domain := M_p_domain M ; M_interp := I' |}).
      pose (zero' := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Zero) (tl v) (hd v)); pose (succ := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Succ) (tl v) (hd v)); pose (plus := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Plus) (tl v) (hd v)); pose (mult := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Mult) (tl v) (hd v)); pose (equal := @i_P_p _ _ _ (M_p_interp M) Eq).
      pose (rho' := ⟨get_indi_p rho, fun _ _ _ => get_indi_p rho 0, fun _ _ _ => True⟩).
      specialize (H M' rho' equal mult plus succ zero'); change ((M', ⟨get_indi rho', get_func rho', zero' .: succ .: plus .: mult .: equal .: get_pred rho'⟩) ⊨ (all_total_functional --> PA_form_embedded --> embed_form_funcfree phi)) in H.
      eapply embed_form_funcfree_correct in H. apply H. easy.
      + change ((M', ⟨get_indi rho', get_func rho', zero' .: succ .: plus .: mult .: equal .: get_pred rho'⟩) ⊨ (all_total_functional)).
        split. split. split.
        * apply total_functional0_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Zero).
        * apply total_functional1_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Succ).
        * apply total_functional2_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Plus).
        * apply total_functional2_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Mult).
      + split.
        * eapply embed_form_funcfree_correct. easy. repeat split; apply (M_p_correct M); clear; firstorder.
        * cbn. intros P [d0 [? ?]] IH d. edestruct (M_p_correct M ax_ind ltac:(clear;firstorder) rho P) as [v H3].
          -- exists [d0]. cbn. repeat split; trivial. now exists [].
          -- cbn. intros d1 [v' [[-> ?] ?]]. repeat depelim v'. destruct (IH h) as [dS [? ?]]; trivial.
             exists [dS]. repeat split; trivial. now exists [h].
          -- cbn in H3. instantiate (1 := hd ([d])) in H3. repeat depelim v. cbn in H3.
             now destruct H3 as [[-> ?] ?].
  Qed.

  Lemma PA_model_sat_iff_model_sat_funcfree (phi : @form PA_funcs_signature PA_preds_signature _) :
    first_order phi -> (exists (M_PA : Model_p_of PA) rho, (M_PA, rho) ⊨p phi) <-> (exists (M' : Model) rho, (M', rho) ⊨ (∃p(2) ∃p(3) ∃p(3) ∃p(2) ∃p(1) all_total_functional ∧ PA_form_embedded ∧ (embed_form_funcfree phi))).
  Proof.
    intros FO. split.
    - intros [M [rho H]].
      pose (I' := {| i_f _ _ := get_indi_p rho 0 ; i_P _ _ := True |} ).
      pose (M' := {| M_domain := M_p_domain M ; M_interp := I' |}).
      pose (rho' := ⟨get_indi_p rho, fun _ _ _ => get_indi_p rho 0, fun _ _ _ => True⟩).
      exists M', rho'.
      pose (zero' := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Zero) (tl v) (hd v)); pose (succ := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Succ) (tl v) (hd v)); pose (plus := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Plus) (tl v) (hd v)); pose (mult := fun v => proj1_sig (@i_f_p _ _ _ (M_p_interp M) Mult) (tl v) (hd v)); pose (equal := @i_P_p _ _ _ (M_p_interp M) Eq).
      exists equal, mult, plus, succ, zero'; change ((M', ⟨get_indi rho', get_func rho', zero' .: succ .: plus .: mult .: equal .: get_pred rho'⟩) ⊨ ((all_total_functional ∧ PA_form_embedded) ∧ embed_form_funcfree phi)).
      split. split.
      + split. split. split.
        * apply total_functional0_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Zero).
        * apply total_functional1_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Succ).
        * apply total_functional2_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Plus).
        * apply total_functional2_correct; now destruct (@i_f_p _ _ _ (M_p_interp M) Mult).
      + split.
        * eapply embed_form_funcfree_correct. easy. repeat split; apply (M_p_correct M); clear; firstorder.
        * cbn. intros P [d0 [? ?]] IH d. edestruct (M_p_correct M ax_ind ltac:(clear;firstorder) rho P) as [v H3].
          -- exists [d0]. cbn. repeat split; trivial. now exists [].
          -- cbn. intros d1 [v' [[-> ?] ?]]. repeat depelim v'. destruct (IH h) as [dS [? ?]]; trivial.
             exists [dS]. repeat split; trivial. now exists [h].
          -- cbn in H3. instantiate (1 := hd ([d])) in H3. repeat depelim v. cbn in H3.
             now destruct H3 as [[-> ?] ?].
      + now eapply embed_form_funcfree_correct.
    - intros [M' [rho [PE [PM [P_A [PS [PO H]]]]]]]. cbn [get_indi get_func get_pred] in *.
      destruct H as [[HTF H_PA] H].
      assert (functional (fun v d => PO (Vector.cons d v)) /\ total (fun v d => PO (Vector.cons d v))) as HPO.
      { destruct HTF as [[[[HF HT] _] _] _]. split. intros v y y' H2 H3. depelim v. now apply (HT y y' H2 H3 (fun v => y = Vector.hd v)). intros v. depelim v. apply HF. }
      assert (functional (fun v d => PS (Vector.cons d v)) /\ total (fun v d => PS (Vector.cons d v))) as HPS.
      { destruct HTF as [[[_ [HF HT]] _] _]. split. intros v y y' H2 H3. repeat depelim v. now apply (HT h y y' H2 H3 (fun v => y = Vector.hd v)). intros v. repeat depelim v. apply HF. }
      assert (functional (fun v d => P_A (Vector.cons d v)) /\ total (fun v d => P_A (Vector.cons d v))) as HPA.
      { destruct HTF as [[[_ _] [HF HT]] _]. split. intros v y y' H2 H3. repeat depelim v. now apply (HT h0 h y y' H2 H3 (fun v => y = Vector.hd v)). intros v. repeat depelim v. apply HF. }
      assert (functional (fun v d => PM (Vector.cons d v)) /\ total (fun v d => PM (Vector.cons d v))) as HPM.
      { destruct HTF as [[[_ _] _] [HF HT]]. split. intros v y y' H2 H3. repeat depelim v. now apply (HT h0 h y y' H2 H3 (fun v => y = Vector.hd v)). intros v. repeat depelim v. apply HF. }
      Existing Instance PA_funcs_signature.
      Existing Instance PA_preds_signature.
      pose (I := {| i_f_p f := match f with Zero => exist _ (fun v d => PO (Vector.cons d v)) HPO | Succ => exist _ (fun v d => PS (Vector.cons d v)) HPS | Plus => exist _ (fun v d => P_A (Vector.cons d v)) HPA | Mult => exist _ (fun v d => PM (Vector.cons d v)) HPM end ;
                    i_P_p P := match P with Eq => PE end |}).
      pose (M := {| M_p_domain := M_domain M' ; M_p_interp := I |}).
      destruct rho as [rho_i rho_f rho_p]. cbn [get_indi get_func get_pred] in *.
      assert (forall psi, PA psi -> M ⊨p psi) as M_correct.
      { destruct H_PA as [H_PA1 H_PA2]. eapply sat_ext in H_PA1. eapply (embed_form_funcfree_correct ⟨⟨rho_i, fun _ _ => default_func_p _ (rho_i 0), rho_p⟩⟩) in H_PA1.
        * intros psi H2 rho. repeat destruct H2 as [<-|H2]; try easy; try apply H_PA1.
          cbn. cbn in H_PA2. intros P [v1 [[[v2 [? ?]] ?] ?]] H_IH d. 
          repeat depelim v1. repeat depelim v2. exists ([d]). repeat split.
          apply H_PA2. now exists h. intros d' ?. destruct (H_IH d') as [v3 [[[v4 [[-> ?] ?]] ?] ?]].
          now exists ([d']). repeat depelim v3. repeat depelim v4. now exists h1.
        * easy.
        * intros n. split. reflexivity. intros ar. split. reflexivity.
          destruct n as [|[|[]]]; destruct ar as [|[|[]]]; cbn -[PeanoNat.Nat.eq_dec];
          repeat (try rewrite nat_eq_dec_same; try destruct Nat.eq_dec as [e|]; try lia; try destruct e); try reflexivity.
          all: now repeat depelim v. }
      exists {| M_p_model := M ; M_p_correct := M_correct |}.
      eapply sat_ext in H.
      eapply (embed_form_funcfree_correct ⟨⟨rho_i, fun _ _ => default_func_p _ (rho_i 0), rho_p⟩⟩) in H; trivial.
      + eexists. apply H.
      + intros n. split. reflexivity. intros ar. split. reflexivity.
        destruct n as [|[|[]]]; destruct ar as [|[|[]]]; cbn -[PeanoNat.Nat.eq_dec];
        repeat (try rewrite nat_eq_dec_same; try destruct Nat.eq_dec as [e|]; try lia; try destruct e); try reflexivity.
        all: now repeat depelim v.
  Qed.

  Definition embed_PA_funcfree phi := (∀p(2) ∀p(3) ∀p(3) ∀p(2) ∀p(1) all_total_functional --> PA_form_embedded --> (embed_form_funcfree phi)).

  Lemma PA_sat_iff_empty_theory_sat_funcfree (phi : @form PA_funcs_signature PA_preds_signature _) :
    first_order phi -> PA ⊨p phi <-> (fun _ => False) ⊨ embed_PA_funcfree phi.
  Proof.
    intros FO. split.
    - intros H M. now apply PA_model_valid_iff_model_valid_funcfree.
    - intros H M. apply PA_model_valid_iff_model_valid_funcfree. easy. intros M'.
      apply (H {| M_model := M' ; M_correct := (fun _ (f : False) => match f with end) |}).
  Qed.

End PAValidSatTranslation_Funcfree.




(** ** Categoricity *)

Section Categoricity.

  Variable M1 : Model_of PA.
  Variable M2 : Model_of PA.

  (** Abbreviations *)
  Notation D1 := (M_domain (M_model M1)).
  Notation D2 := (M_domain (M_model M2)).
  Notation I1 := (M_interp (M_model M1)).
  Notation I2 := (M_interp (M_model M2)).
  Notation eq1_sem := (eq_sem M1).
  Notation eq2_sem := (eq_sem M2).

  Notation "'O1'" := (@i_f _ _ D1 I1 Zero ([])).
  Notation "'O2'" := (@i_f _ _ D2 I2 Zero ([])).
  Notation "'S1' x" := (@i_f _ _ D1 I1 Succ ([x])) (at level 37).
  Notation "'S2' x" := (@i_f _ _ D2  I2 Succ ([x])) (at level 37).
  Notation "x 'i⊕1' y" := (@i_f _ _ D1 I1 Plus ([x ; y])) (at level 39).
  Notation "x 'i⊕2' y" := (@i_f _ _ D2 I2 Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗1' y" := (@i_f _ _ D1 I1 Mult ([x ; y])) (at level 38).
  Notation "x 'i⊗2' y" := (@i_f _ _ D2 I2 Mult ([x ; y])) (at level 38).
  Notation "x '=1=' y" := (@i_P _ _ D1 I1 Eq ([x ; y])) (at level 40).
  Notation "x '=2=' y" := (@i_P _ _ D2 I2 Eq ([x ; y])) (at level 40).


  (** Definition of isomorphism *)
  Inductive F : D1 -> D2 -> Prop :=
    | F_O : F O1 O2
    | F_S : forall x y, F x y -> F (S1 x) (S2 y).


  Lemma F_inv1 x :
    F (S1 x) O2 -> False.
  Proof.
    intros H. inversion H.
    + now apply (zero_succ M1 x).
    + now apply (zero_succ M2 y).
  Qed.

  Lemma F_inv2 y :
    F O1 (S2 y) -> False.
  Proof.
    intros H. inversion H.
    + now apply (zero_succ M2 y).
    + now apply (zero_succ M1 x).
  Qed.

  Lemma F_inv3 y :
    F O1 y -> y = O2.
  Proof.
    destruct (case_analysis M2 y) as [->|[y' ->]].
    - easy.
    - now intros H%F_inv2.
  Qed.

  Lemma F_inv4 x :
    F x O2 -> x = O1.
  Proof.
    destruct (case_analysis M1 x) as [->|[x' ->]].
    - easy.
    - now intros H%F_inv1.
  Qed.

  Lemma F_inv5 :
    forall x y, F (S1 x) y -> exists y', y = S2 y'.
  Proof.
    intros x y. destruct (case_analysis M2 y) as [->|[y' ->]].
    - now intros H%F_inv1.
    - intros _. now exists y'.
  Qed.

  Lemma F_inv6 :
    forall x y, F x (S2 y) -> exists x', x = S1 x'.
  Proof.
    intros x y. destruct (case_analysis M1 x) as [->|[x' ->]].
    - now intros H%F_inv2.
    - intros _. now exists x'.
  Qed.

  Lemma F_inv7 x y :
    F (S1 x) (S2 y) -> F x y.
  Proof.
    intros H. inversion H.
    + exfalso. now apply (zero_succ M1 x).
    + apply (succ_inj M1) in H0 as ->.
      apply (succ_inj M2) in H1 as ->.
      exact H2.
  Qed.


  Lemma F_total :
    forall x, exists y, F x y.
  Proof.
    apply (induction M1).
    - exists O2. exact F_O.
    - intros x [y IH]. exists (S2 y). now apply F_S.
  Qed.

  Lemma F_surjective :
    forall y, exists x, F x y.
  Proof.
    apply (induction M2).
    - exists O1. exact F_O.
    - intros y [x IH]. exists (S1 x). now apply F_S.
  Qed.

  Lemma F_functional :
    forall x y y', F x y -> F x y' -> y = y'.
  Proof.
    apply (induction M1 (fun x => forall y y', F x y -> F x y' -> y = y')).
    - intros y y' H1 H2. now rewrite (F_inv3 y), (F_inv3 y').
    - intros x IH y y' H1 H2. 
      destruct (F_inv5 x y H1) as [z ->], (F_inv5 x y' H2) as [z' ->].
      apply F_inv7 in H1; apply F_inv7 in H2. now rewrite (IH z z').
  Qed.

  Lemma F_injective :
    forall x x' y, F x y -> F x' y -> x = x'.
  Proof.
    intros x x' y. revert y x x'. 
    apply (induction M2 (fun y => forall x x', F x y -> F x' y -> x = x')).
    - intros x x'' H1 H2. now rewrite (F_inv4 x), (F_inv4 x'').
    - intros y IH x x' H1 H2. 
      destruct (F_inv6 x y H1) as [z ->], (F_inv6 x' y H2) as [z' ->].
      apply F_inv7 in H1; apply F_inv7 in H2. now rewrite (IH z z').
  Qed.


  Lemma F_add :
    forall x x' y y', F x y -> F x' y' -> F (x i⊕1 x') (y i⊕2 y').
  Proof.
    apply (induction M1 (fun x => forall x' y y', F x y -> F x' y' -> F (x i⊕1 x') (y i⊕2 y'))).
    - intros x' y y' H1 H2. rewrite (F_inv3 y H1).
      now rewrite (add_zero M1), (add_zero M2).
    - intros x'' IH x' y y' H1 H2. destruct (F_inv5 x'' y H1) as [y'' ->].
      rewrite (add_rec M1), (add_rec M2).
      apply F_S, IH. now apply F_inv7. exact H2.
  Qed.

  Lemma F_mul :
    forall x x' y y', F x y -> F x' y' -> F (x i⊗1 x') (y i⊗2 y').
  Proof.
    apply (induction M1 (fun x => forall x' y y', F x y -> F x' y' -> F (x i⊗1 x') (y i⊗2 y'))).
    - intros x' y y' H1 H2. rewrite (F_inv3 y H1).
      rewrite (mul_zero M1), (mul_zero M2).
      exact F_O.
    - intros x'' IH x' y y' H1 H2. destruct (F_inv5 x'' y H1) as [y'' ->].
      rewrite (mul_rec M1), (mul_rec M2).
      apply F_add. exact H2. apply IH. now apply F_inv7. exact H2.
  Qed.

  Lemma F_eq :
    forall x x' y y', F x y -> F x' y' -> (x =1= x' <-> y =2= y').
  Proof.
    apply (induction M1 (fun x => forall x' y y', F x y -> F x' y' -> (x =1= x' <-> y =2= y'))).
    - intros x' y y' H1 H2. split. 
      + intros H3%eq1_sem. rewrite <- H3 in H2. rewrite (F_inv3 y H1). 
        rewrite (F_inv3 y' H2). now apply eq2_sem.
      + intros H3%eq2_sem. rewrite <- H3 in H2. rewrite (F_inv3 y H1) in H2. 
      rewrite (F_inv4 x' H2). now apply eq1_sem.
    - intros x IH x' y y' H1 H2. split.
      + intros H3%eq1_sem. rewrite <- H3 in H2.
        destruct (F_inv5 x y H1) as [z ->]. destruct (F_inv5 x y' H2) as [z' ->].
        enough (z =2= z') as ->%eq2_sem by now apply eq2_sem.
        apply (IH x). now apply F_inv7. now apply F_inv7. now apply eq1_sem.
      + intros H3%eq2_sem. rewrite <- H3 in H2.
        destruct (F_inv5 x y H1) as [z ->]. destruct (F_inv6 x' z H2) as [x'' ->].
        enough (x =1= x'') as ->%eq1_sem by now apply eq1_sem.
        apply (IH x'' z z). now apply F_inv7. now apply F_inv7. now apply eq2_sem.
  Qed.



  (** F describes an isomorphism between D1 and D2. *)

  Class Iso T1 T2 := { iso : T1 -> T2 -> Prop }.
  Notation "rho ≈ sigma" := (iso rho sigma) (at level 30).

  Instance Iso_indi : Iso D1 D2 := {| 
    iso := F 
  |}.
  Instance Iso_vec ar : Iso (vec D1 ar) (vec D2 ar) := {| 
    iso v1 v2 := @VectorLib.Forall2 _ _ F ar v1 v2
  |}.
  Instance Iso_func {ar} : Iso (vec D1 ar -> D1) (vec D2 ar -> D2) := {| 
    iso f1 f2 := forall v1 v2, v1 ≈ v2 -> F (f1 v1) (f2 v2)
  |}.
  Instance Iso_pred {ar} : Iso (vec D1 ar -> Prop) (vec D2 ar -> Prop) := {| 
    iso P1 P2 := forall v1 v2, v1 ≈ v2 -> (P1 v1 <-> P2 v2)
  |}.
  Instance Iso_func_p {ar} : Iso (func_p D1 ar) (func_p D2 ar) := {| 
    iso f1 f2 := forall v1 v2, v1 ≈ v2 -> forall x y, (proj1_sig f1 v1 x : Prop) -> (proj1_sig f2 v2 y : Prop) -> F x y
  |}.

  Instance Iso_env : Iso (env D1) (env D2) := {| 
    iso rho1 rho2 := forall n, 
         get_indi rho1 n ≈ get_indi rho2 n
       /\ forall ar, get_func rho1 n ar ≈ get_func rho2 n ar
                  /\ get_pred rho1 n ar ≈ get_pred rho2 n ar
  |}.
  Instance Iso_env_p : Iso (env_p D1) (env_p D2) := {| 
    iso rho1 rho2 := forall n, 
         get_indi_p rho1 n ≈ get_indi_p rho2 n
       /\ forall ar, get_func_p rho1 n ar ≈ get_func_p rho2 n ar
                  /\ get_pred_p rho1 n ar ≈ get_pred_p rho2 n ar 
  |}.


  Lemma iso_env_i rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p x y :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈ ⟨rho2_i, rho2_f, rho2_p⟩ -> x ≈ y -> ⟨x .: rho1_i, rho1_f, rho1_p⟩ ≈ ⟨y .: rho2_i, rho2_f, rho2_p⟩.
  Proof.
    intros H1 H2. split. destruct n; firstorder. apply H1.
  Qed.

  Lemma iso_env_f rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (f1 : vec D1 ar -> D1) f2 :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈ ⟨rho2_i, rho2_f, rho2_p⟩ -> f1 ≈ f2 -> ⟨rho1_i, f1 .: rho1_f, rho1_p⟩ ≈ ⟨rho2_i, f2 .: rho2_f, rho2_p⟩.
  Proof.
    intros H1 H2. split. apply H1. intros ar'. split. 2: apply H1.
    destruct n; cbn; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|].
    apply H2. all: apply H1.
  Qed.

  Lemma iso_env_p rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (P1 : vec D1 ar -> Prop) P2 :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈ ⟨rho2_i, rho2_f, rho2_p⟩ -> P1 ≈ P2 -> ⟨rho1_i, rho1_f, P1 .: rho1_p⟩ ≈ ⟨rho2_i, rho2_f, P2 .: rho2_p⟩.
  Proof.
    intros H1 H2. split. apply H1. intros ar'. split. apply H1.
    destruct n; cbn; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|].
    apply H2. all: apply H1.
  Qed.

  Lemma iso_env_p_i rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p x y :
    ⟨⟨rho1_i, rho1_f, rho1_p⟩⟩ ≈ ⟨⟨rho2_i, rho2_f, rho2_p⟩⟩ -> x ≈ y -> ⟨⟨x .: rho1_i, rho1_f, rho1_p⟩⟩ ≈ ⟨⟨y .: rho2_i, rho2_f, rho2_p⟩⟩.
  Proof.
    intros H1 H2. split. destruct n; firstorder. apply H1.
  Qed.

  Lemma iso_env_p_f rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (f1 : func_p D1 ar) f2 :
    ⟨⟨rho1_i, rho1_f, rho1_p⟩⟩ ≈ ⟨⟨rho2_i, rho2_f, rho2_p⟩⟩ -> f1 ≈ f2 -> ⟨⟨rho1_i, f1 .: rho1_f, rho1_p⟩⟩ ≈ ⟨⟨rho2_i, f2 .: rho2_f, rho2_p⟩⟩.
  Proof.
    intros H1 H2. split. apply H1. intros ar'. split. 2: apply H1.
    destruct n; cbn; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|]. 
    apply H2. all: apply H1.
  Qed.

  Lemma iso_env_p_p rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (P1 : vec D1 ar -> Prop) P2 :
    ⟨⟨rho1_i, rho1_f, rho1_p⟩⟩ ≈ ⟨⟨rho2_i, rho2_f, rho2_p⟩⟩ -> P1 ≈ P2 -> ⟨⟨rho1_i, rho1_f, P1 .: rho1_p⟩⟩ ≈ ⟨⟨rho2_i, rho2_f, P2 .: rho2_p⟩⟩.
  Proof.
    intros H1 H2. split. apply H1. intros ar'. split. apply H1.
    destruct n; cbn; destruct (PeanoNat.Nat.eq_dec ar ar') as [->|].
    apply H2. all: apply H1.
  Qed.

  Lemma iso_vec_eq1 ar (v1 v1' : vec D1 ar) v2 :
    v1 ≈ v2 -> v1' ≈ v2 -> v1 = v1'.
  Proof.
    intros H1 H2. induction v1; dependent elimination v1'. 
    reflexivity. f_equal. eapply F_injective. apply H1. apply H2.
    eapply IHv1. apply H1. apply H2.
  Qed.

  Lemma iso_vec_eq2 ar (v1 : vec D1 ar) v2 v2' :
    v1 ≈ v2 -> v1 ≈ v2' -> v2 = v2'.
  Proof.
    intros H1 H2. induction v2; dependent elimination v2'; dependent elimination v1. 
    reflexivity. f_equal. eapply F_functional. apply H1. apply H2.
    eapply IHv2. apply H1. apply H2.
  Qed.


  (** Alternative characterization of f1 ≈ f2 *)
  Lemma iso_func_p_char ar (f1 : func_p D1 ar) f2 :
    f1 ≈ f2 <-> forall x y, F x y -> forall v1 v2, v1 ≈ v2 -> (proj1_sig f1 v1 x <-> proj1_sig f2 v2 y).
  Proof.
    destruct f1 as [f1 [f1_functional f1_total]];
    destruct f2 as [f2 [f2_functional f2_total]]; cbn.
    split.
    - intros H x y H1 v1 v2 H2. split.
      + intros H3. destruct (f2_total v2) as [y' H4].
        enough (y = y') by congruence. eapply F_functional.
        apply H1. eapply H. apply H2. easy. easy.
      + intros H3. destruct (f1_total v1) as [x' H4].
        enough (x = x') by congruence. eapply F_injective.
        apply H1. eapply H. apply H2. easy. easy.
    - intros H v1 v2 H1 x y H2 H3. destruct (F_total x) as [y' H4].
      enough (y = y') by congruence. eapply f2_functional.
      apply H3. eapply H. apply H4. apply H1. exact H2.
  Qed.



  (** We can translate predicates along this isomorphism *)

  Lemma P1_to_P2 ar (P1 : vec D1 ar -> Prop) :
    { P2 | P1 ≈ P2 }.
  Proof.
    exists (fun v => forall v', VectorLib.Forall2 F v' v -> P1 v').
    intros v1 v2 H1. split.
    - intros H2 v' H3. induction v'; dependent elimination v1.
      + exact H2.
      + assert (h = h0) as ->. { apply eq1_sem. eapply F_eq. apply H3. apply H1. now apply eq2_sem. }
        assert (v' = t0) as ->. { eapply IHv'. apply H1. reflexivity. apply H3. } 
        exact H2.
    - firstorder.
  Qed.

  Lemma P2_to_P1 ar (P2 : vec D2 ar -> Prop) :
    { P1 | P1 ≈ P2 }.
  Proof.
    exists (fun v => forall v', VectorLib.Forall2 F v v' -> P2 v').
    intros v1 v2 H1. split.
    - firstorder.
    - intros H2 v' H3. induction v'; dependent elimination v2.
      + exact H2.
      + dependent elimination v1.
        assert (h = h0) as ->. { apply eq2_sem. eapply F_eq. apply H3. apply H1. now apply eq1_sem. }
        assert (v' = t0) as ->. { eapply IHv'. apply H1. reflexivity. apply H3. } 
        exact H2.
  Qed.


  (** Vectors and functions can not be computationally translated 
      because of the elim restriction. But we can prove existential
      versions. *)

  Lemma v1_to_v2_ex ar (v1 : vec D1 ar) :
    exists v2, v1 ≈ v2.
  Proof.
    induction v1.
    - now exists [].
    - destruct IHv1 as [v2 IH]. destruct (F_total h) as [y H]. 
      now exists (y::v2).
  Qed.

  Lemma v2_to_v1_ex ar (v2 : vec D2 ar) :
    exists v1, v1 ≈ v2.
  Proof.
    induction v2.
    - now exists [].
    - destruct IHv2 as [v1 IH]. destruct (F_surjective h) as [x H]. 
      now exists (x::v1).
  Qed.


  (** The isomorphism also respects evaluation of terms under
      isomorphic environments *)

  Lemma F_term rho1 rho2 t :
    rho1 ≈ rho2 -> F (eval D1 rho1 t) (eval D2 rho2 t).
  Proof.
    revert t. apply (term_ind (fun t => rho1 ≈ rho2 -> F (eval D1 rho1 t) (eval D2 rho2 t))); intros.
    - apply H.
    - apply H, Forall2_Forall. induction v. easy.
      split. now apply IH. apply IHv, IH.
    - destruct f; repeat depelim v; cbn in *.
      + exact F_O.
      + apply F_S. now apply IH.
      + apply F_add; now apply IH.
      + apply F_mul; now apply IH.
  Qed.


  (** A similar result holds for satisfiablility of formulas, but
      as we are not able to computationally translate functions along 
      the isomorphism, we must restrict to formulas without function
      quantificaion.
      To make our lives easier for the incompleteness proof, we 
      restrict even further to only first-order formulas *)

  Definition iso_env_funcfree (rho1 : env D1) rho2 := forall n, get_indi rho1 n ≈ get_indi rho2 n /\ forall ar, get_pred rho1 n ar ≈ get_pred rho2 n ar.
  Notation "rho ≈FF sigma" := (iso_env_funcfree rho sigma) (at level 30).

  Lemma iso_env_funcfree_i rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p x y :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈FF ⟨rho2_i, rho2_f, rho2_p⟩ -> x ≈ y -> ⟨x .: rho1_i, rho1_f, rho1_p⟩ ≈FF ⟨y .: rho2_i, rho2_f, rho2_p⟩.
  Proof.
    intros H1 H2 n. split. destruct n; firstorder. apply H1.
  Qed.

  Lemma iso_env_funcfree_p rho1_i rho1_f rho1_p rho2_i rho2_f rho2_p ar (P1 : vec D1 ar -> Prop) P2 :
    ⟨rho1_i, rho1_f, rho1_p⟩ ≈FF ⟨rho2_i, rho2_f, rho2_p⟩ -> P1 ≈ P2 -> ⟨rho1_i, rho1_f, P1 .: rho1_p⟩ ≈FF ⟨rho2_i, rho2_f, P2 .: rho2_p⟩.
  Proof.
    intros H1 H2 n. split. apply H1. intros ar'. destruct n; cbn;
    destruct Nat.eq_dec as [->|]. apply H2. all: apply H1.
  Qed.

  Lemma F_term_funcfree rho1 rho2 t :
    rho1 ≈FF rho2 -> funcfreeTerm t -> F (eval D1 rho1 t) (eval D2 rho2 t).
  Proof.
    induction t; intros.
    - apply H.
    - easy.
    - destruct f; repeat depelim v; cbn in *.
      + exact F_O.
      + apply F_S. now apply IH.
      + apply F_add; now apply IH.
      + apply F_mul; now apply IH.
  Qed.

  Theorem sat_iff_funcfree rho1 rho2 phi : 
    rho1 ≈FF rho2 -> funcfree phi -> rho1 ⊨ phi <-> rho2 ⊨ phi.
  Proof.
    revert phi rho1 rho2. induction phi; intros rho1 rho2 H F; cbn.
    - easy.
    - destruct p; cbn.
      + apply H. induction v; cbn. easy. split. apply F_term_funcfree. apply H. 
        apply F. apply IHv, F. 
      + destruct P; repeat depelim v; cbn in *. now apply F_eq; apply F_term_funcfree.
    - destruct F as [F1 F2]. 
      specialize (IHphi1 rho1 rho2 H F1); specialize (IHphi2 rho1 rho2 H F2).
      destruct b; tauto.
    - destruct q; split.
      + intros H1 y. destruct (F_surjective y).
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
      + intros H1 x. destruct (F_total x).
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
      + intros [x H1]. destruct (F_total x) as [y]. exists y.
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
      + intros [y H1]. destruct (F_surjective y) as [x]. exists x.
        eapply IHphi. 2: easy. 2: apply H1. apply iso_env_funcfree_i; eauto.
    - easy.
    - destruct q; split.
      + intros H1 P2. destruct (P2_to_P1 _ P2) as [P1 H2].
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
      + intros H1 P1. destruct (P1_to_P2 _ P1) as [P2 H2].
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
      + intros [P1 H1]. destruct (P1_to_P2 _ P1) as [P2 H2]. exists P2.
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
      + intros [P2 H1]. destruct (P2_to_P1 _ P2) as [P1 H2]. exists P1.
        eapply IHphi. 3: apply H1. apply iso_env_funcfree_p; eauto. easy.
  Qed.


  (** First-order version with bounded enviroment isomorphism.
      We use this later to refute compactness. *)

  Lemma F_term_firstorder_bounded rho1 rho2 t :
    first_order_term t -> (forall n, ~ bounded_indi_term n t -> F (get_indi rho1 n) (get_indi rho2 n))
    -> F (eval D1 rho1 t) (eval D2 rho2 t).
  Proof.
    intros FO H. induction t; cbn.
    - apply H. cbn. lia.
    - easy.
    - destruct f; repeat depelim v; cbn in *.
      + exact F_O.
      + apply F_S. apply IH. easy. intros. now apply H.
      + apply F_add; apply IH; try easy; intros; now apply H.
      + apply F_mul; apply IH; try easy; intros; now apply H.
  Qed.

  Theorem sat_iff_firstorder_bounded rho1 rho2 phi : 
    first_order phi -> (forall n, ~ bounded_indi n phi -> F (get_indi rho1 n) (get_indi rho2 n))
    -> rho1 ⊨ phi <-> rho2 ⊨ phi.
  Proof.
    revert phi rho1 rho2. induction phi; intros rho1 rho2 F H; cbn.
    - easy.
    - destruct p; cbn. easy.  destruct P; repeat depelim v; cbn in *.
      apply F_eq; apply F_term_firstorder_bounded; try easy; intros n H1;
      apply H; intros H2; now apply H1.
    - destruct F as [F1 F2]. 
      assert (forall n : nat, ~ bounded_indi n phi1 -> F (get_indi rho1 n) (get_indi rho2 n)) as H1 by (clear -H; firstorder).
      assert (forall n : nat, ~ bounded_indi n phi2 -> F (get_indi rho1 n) (get_indi rho2 n)) as H2 by (clear -H; firstorder).
      specialize (IHphi1 rho1 rho2 F1 H1); specialize (IHphi2 rho1 rho2 F2 H2).
      destruct b; tauto.
    - destruct q; split.
      + intros H1 y. destruct (F_surjective y). eapply IHphi. easy. 2: apply H1. intros [] ?; eauto.
      + intros H1 x. destruct (F_total x). eapply IHphi. easy. 2: apply H1. intros [] ?; eauto.
      + intros [x H1]. destruct (F_total x) as [y]. exists y. eapply IHphi. easy. 2: apply H1. intros [] ?; eauto.
      + intros [y H1]. destruct (F_surjective y) as [x]. exists x. eapply IHphi. easy. 2: apply H1. intros [] ?; eauto.
    - easy.
    - easy.
  Qed.


  (** Alternatively, we get the full result if we switch to semantics
      where functions are interpreted as total, functional predicates.
      Then the propositional isomorphism suffices. *)
  
  Lemma f1_to_f2_p ar (f1 : func_p D1 ar) :
    exists f2, f1 ≈ f2.
  Proof.
    destruct f1 as [f1 [f1_functional f1_total]].
    pose (f2 v y := forall v' x, VectorLib.Forall2 F v' v -> F x y -> f1 v' x).
    assert (functional f2) as f2_functional. {
      intros v2 y y' H1 H2.
      destruct (v2_to_v1_ex ar v2) as [v1 H].
      destruct (F_surjective y) as [x H3]; destruct (F_surjective y') as [x' H4].
      eapply eq2_sem, (F_eq _ _ _ _ H3 H4), eq1_sem, f1_functional.
      apply (H1 v1 x H H3). apply (H2 v1 x' H H4).
    }
    assert (total f2) as f2_total. {
      intros v2. destruct (v2_to_v1_ex ar v2) as [v1 H].
      destruct (f1_total v1) as [x H1].
      destruct (F_total x) as [y H2].
      exists y. intros v1' x' H3 H4.
      rewrite <- (iso_vec_eq1 _ v1 v1' v2 H H3).
      enough (x' = x) by congruence. now apply (F_injective x' x y).
    }
    exists (exist _ f2 (conj f2_functional f2_total)).
    apply iso_func_p_char. cbn.
    intros x y H1 v1 v2 H2. split; intros H3.
    - intros v1' x' H4 H5. rewrite <- (iso_vec_eq1 _ v1 v1' v2 H2 H4).
      enough (x' = x) by congruence. now apply (F_injective x' x y).
    - now apply H3.
  Qed.

  Lemma f2_to_f1_p ar (f2 : func_p D2 ar) :
    exists f1, f1 ≈ f2.
  Proof.
    destruct f2 as [f2 [f2_functional f2_total]].
    pose (f1 v x := forall v' y, VectorLib.Forall2 F v v' -> F x y -> f2 v' y).
    assert (functional f1) as f1_functional. {
      intros v1 x x' H1 H2.
      destruct (v1_to_v2_ex ar v1) as [v2 H].
      destruct (F_total x) as [y H3]; destruct (F_total x') as [y' H4].
      eapply eq1_sem, (F_eq _ _ _ _ H3 H4), eq2_sem, f2_functional.
      apply (H1 v2 y H H3). apply (H2 v2 y' H H4).
    }
    assert (total f1) as f1_total. {
      intros v1. destruct (v1_to_v2_ex ar v1) as [v2 H].
      destruct (f2_total v2) as [y H1].
      destruct (F_surjective y) as [x H2].
      exists x. intros v2' y' H3 H4.
      rewrite <- (iso_vec_eq2 _ v1 v2 v2' H H3).
      enough (y' = y) by congruence. now apply (F_functional x y' y).
    }
    exists (exist _ f1 (conj f1_functional f1_total)).
    apply iso_func_p_char. cbn.
    intros x y H1 v1 v2 H2. split; intros H3.
    - now apply H3.
    - intros v2' y' H4 H5. rewrite <- (iso_vec_eq2 _ v1 v2 v2' H2 H4).
      enough (y' = y) by congruence. now apply (F_functional x y' y).
  Qed.

  Lemma F_term_p rho1 rho2 t x y :
    rho1 ≈ rho2 -> eval_p D1 rho1 t x -> eval_p D2 rho2 t y -> F x y.
  Proof.
    revert t x y. apply (term_ind (fun t => forall x y, rho1 ≈ rho2 -> eval_p D1 rho1 t x -> eval_p D2 rho2 t y -> F x y)).
    - intros n x y H <- <-. apply H.
    - intros ar n v IH x y H [v1' [H1 H2]] [v2' [H3 H4]].
      eapply H. 2: apply H2. 2: apply H4. clear H2 H4.
      induction v1'; dependent elimination v; dependent elimination v2'; cbn.
      easy. split; cbn in H1, H3, IH. now apply IH. now apply (IHv1' t0).
    - intros f v IH x y H. destruct f; repeat depelim v; 
      intros [v1' [H1 <-]] [v2' [H2 <-]]; repeat depelim v1'; repeat depelim v2'.
      + exact F_O.
      + apply F_S. apply IH. easy. apply H1. apply H2.
      + destruct IH as [IH1 [IH2 _]]. apply F_add. 
        apply IH1. apply H. apply H1. apply H2.
        apply IH2. apply H. apply H1. apply H2.
      + destruct IH as [IH1 [IH2 _]]. apply F_mul.
        apply IH1. apply H. apply H1. apply H2.
        apply IH2. apply H. apply H1. apply H2.
  Qed.

  Lemma eval_p_iff rho1 rho2 t x y :
    rho1 ≈ rho2 -> F x y -> (eval_p D1 rho1 t x <-> eval_p D2 rho2 t y).
  Proof.
    revert t x y. apply (term_ind (fun t => forall x y, rho1 ≈ rho2 -> F x y -> (eval_p D1 rho1 t x <-> eval_p D2 rho2 t y))).
    - intros n x y H H1. cbn. split.
      + intros <-. eapply eq2_sem, F_eq. apply H. apply H1. now apply eq1_sem.
      + intros <-. eapply eq1_sem, F_eq. apply H. apply H1. now apply eq2_sem.
    - intros ar n v IH x y H H1. split.
      + intros [v1' [H3 H4]].
        destruct (v1_to_v2_ex _ v1') as [v2' H5]. exists v2'. split.
        * clear H4. induction v; dependent elimination v1'; dependent elimination v2'.
          easy. split. eapply IH. apply H. apply H5. apply H3.
          eapply IHv. apply IH. apply H3. apply H5.
        * eapply iso_func_p_char. apply H. apply H1. apply H5. exact H4.
      + intros [v2' [H3 H4]].
        destruct (v2_to_v1_ex _ v2') as [v1' H5]. exists v1'. split.
        * clear H4. induction v; dependent elimination v1'; dependent elimination v2'.
          easy. split. eapply IH. apply H. apply H5. apply H3.
          eapply IHv. apply IH. apply H3. apply H5.
        * eapply iso_func_p_char. apply H. apply H1. apply H5. exact H4.
    - intros f v IH x y H1 H2. destruct f; repeat depelim v; split; 
      intros [v' [H3 <-]]; repeat depelim v'.
      + rewrite (F_inv3 y H2). exists []. split; easy.
      + rewrite (F_inv4 x H2). exists []. split; easy.
      + destruct (F_inv5 _ y H2) as [y' ->]. exists [y']. repeat split.
        eapply IH. apply H1. eapply F_inv7. apply H2. apply H3.
      + destruct (F_inv6 x _ H2) as [x' ->]. exists [x']. repeat split.
        eapply IH. apply H1. eapply F_inv7. apply H2. apply H3.
      + destruct (F_total h1) as [y1 H4]. destruct (F_total h2) as [y2 H5].
        exists [y1 ; y2]. repeat split.
        * eapply IH. apply H1. apply H4. apply H3.
        * eapply IH. apply H1. apply H5. apply H3.
        * symmetry. eapply F_functional. apply H2. now apply F_add.
      + destruct (F_surjective h1) as [x1 H4]. destruct (F_surjective h2) as [x2 H5].
        exists [x1 ; x2]. repeat split.
        * eapply IH. apply H1. apply H4. apply H3.
        * eapply IH. apply H1. apply H5. apply H3.
        * symmetry. eapply F_injective. apply H2. now apply F_add.
      + destruct (F_total h1) as [y1 H4]. destruct (F_total h2) as [y2 H5].
        exists [y1 ; y2]. repeat split.
        * eapply IH. apply H1. apply H4. apply H3.
        * eapply IH. apply H1. apply H5. apply H3.
        * symmetry. eapply F_functional. apply H2. now apply F_mul.
      + destruct (F_surjective h1) as [x1 H4]. destruct (F_surjective h2) as [x2 H5].
        exists [x1 ; x2]. repeat split.
        * eapply IH. apply H1. apply H4. apply H3.
        * eapply IH. apply H1. apply H5. apply H3.
        * symmetry. eapply F_injective. apply H2. now apply F_mul.
  Qed.

  Theorem sat_p_iff rho1 rho2 phi : 
    rho1 ≈ rho2 -> rho1 ⊨p phi <-> rho2 ⊨p phi.
  Proof.
    revert phi rho1 rho2. induction phi; intros; cbn.
    - easy.
    - destruct p; split.
      + intros [v1' [H1 H2]]. destruct (v1_to_v2_ex _ v1') as [v2' H3].
        exists v2'. split.
        * clear H2. induction v; dependent elimination v1'; dependent elimination v2'.
          easy. split. 
          -- eapply eval_p_iff. apply H. apply H3. apply H1.
          -- eapply IHv. 2: apply H3. apply H1.
        * eapply H. apply H3. exact H2.
      + intros [v2' [H1 H2]]. destruct (v2_to_v1_ex _ v2') as [v1' H3].
        exists v1'. split.
        * clear H2. induction v; dependent elimination v1'; dependent elimination v2'.
          easy. split. 
          -- eapply eval_p_iff. apply H. apply H3. apply H1.
          -- eapply IHv. 2: apply H3. apply H1.
        * eapply H. apply H3. exact H2.
      + destruct P. intros [v1' [H1 H2]]. destruct (v1_to_v2_ex _ v1') as [v2' H3].
        exists v2'. repeat depelim v; repeat depelim v1'; repeat depelim v2'. split.
        * repeat split.
          -- eapply eval_p_iff. apply H. apply H3. apply H1.
          -- eapply eval_p_iff. apply H. apply H3. apply H1.
        * eapply F_eq. apply H3. apply H3. apply H2.
      + destruct P. intros [v2' [H1 H2]]. destruct (v2_to_v1_ex _ v2') as [v1' H3].
        exists v1'. repeat depelim v; repeat depelim v1'; repeat depelim v2'. split.
        * repeat split.
          -- eapply eval_p_iff. apply H. apply H3. apply H1.
          -- eapply eval_p_iff. apply H. apply H3. apply H1.
        * eapply F_eq. apply H3. apply H3. apply H2.
    - specialize (IHphi1 rho1 rho2 H); specialize (IHphi2 rho1 rho2 H).
      destruct b; tauto.
    - destruct q; split.
      + intros H1 y. destruct (F_surjective y).
        eapply IHphi. 2: apply H1. apply iso_env_p_i; eauto.
      + intros H1 x. destruct (F_total x).
        eapply IHphi. 2: apply H1. apply iso_env_p_i; eauto.
      + intros [x H1]. destruct (F_total x) as [y]. exists y.
        eapply IHphi. 2: apply H1. apply iso_env_p_i; eauto.
      + intros [y H1]. destruct (F_surjective y) as [x]. exists x.
        eapply IHphi. 2: apply H1. apply iso_env_p_i; eauto.
    - destruct q; split.
      + intros H1 f2 H2 H3.
        destruct (f2_to_f1_p n (exist _ f2 (conj H2 H3))) as [[f [Hf1 Hf2]] H0].
        eapply IHphi. 2: apply (H1 f Hf1 Hf2). apply iso_env_p_f; cbn; eauto.
      + intros H1 f1 H2 H3. 
        destruct (f1_to_f2_p n (exist _ f1 (conj H2 H3))) as [[f [Hf1 Hf2]] H0].
        eapply IHphi. 2: apply (H1 f Hf1 Hf2). apply iso_env_p_f; cbn; eauto.
      + intros [f1 [H1 [H2 H3]]].
        destruct (f1_to_f2_p n (exist _ f1 (conj H1 H2))) as [[f2 [H4 H5]]].
        exists f2, H4, H5. eapply IHphi. 2: apply H3. apply iso_env_p_f; auto.
      + intros [f2 [H1 [H2 H3]]].
        destruct (f2_to_f1_p n (exist _ f2 (conj H1 H2))) as [[f1 [H4 H5]]].
        exists f1, H4, H5. eapply IHphi. 2: apply H3. apply iso_env_p_f; auto.
    - destruct q; split.
      + intros H1 P2. destruct (P2_to_P1 n P2).
        eapply IHphi. 2: apply H1. apply iso_env_p_p; eauto.
      + intros H1 P1. destruct (P1_to_P2 n P1).
        eapply IHphi. 2: apply H1. apply iso_env_p_p; eauto.
      + intros [P1 H1]. destruct (P1_to_P2 n P1) as [P2].
        exists P2. eapply IHphi. 2: apply H1. apply iso_env_p_p; eauto.
      + intros [P2 H1]. destruct (P2_to_P1 n P2) as [P1 H2].
        exists P1. eapply IHphi. 2: apply H1. apply iso_env_p_p; eauto.
  Qed.



  (** To get the same result for the normal Tarski Semantics
      with functions, we need to assume that F is computational. *)

  Section ComputationalF.

    Hypothesis F_total_comp : forall x, { y | F x y }.
    Hypothesis F_surjective_comp : forall y, { x | F x y }.


    (** Now we can transport vectors and functions *)

    Lemma v1_to_v2 ar (v1 : vec D1 ar) :
      { v2 | Forall2 F v1 v2 }.
    Proof.
      induction v1.
      - now exists [].
      - destruct IHv1 as [v2 IH]. destruct (F_total_comp h) as [x H]. 
        now exists (x::v2).
    Qed.

    Lemma v2_to_v1 ar (v2 : vec D2 ar) :
      { v1 | Forall2 F v1 v2 }.
    Proof.
      induction v2.
      - now exists [].
      - destruct IHv2 as [v1 IH]. destruct (F_surjective_comp h) as [x H]. 
        now exists (x::v1).
    Qed.

    Lemma f1_to_f2 ar (f1 : vec D1 ar -> D1) :
      { f2 | f1 ≈ f2 }.
    Proof.
      exists (fun v2 => proj1_sig (F_total_comp (f1 (proj1_sig (v2_to_v1 _ v2))))).
      intros v1 v2 H1.
      destruct (v2_to_v1 ar v2) as [v1' H2]; cbn.
      destruct (F_total_comp (f1 v1')) as [x H3]; cbn.
      enough (v1 = v1') by congruence. 
      clear H3 f1. induction v1; dependent elimination v1'; dependent elimination v2.
      - reflexivity.
      - f_equal.
        + eapply eq1_sem, F_eq. apply H1. apply H2. now apply eq2_sem.
        + eapply IHv1. apply H1. apply H2.
    Qed.

    Lemma f2_to_f1 ar (f2 : vec D2 ar -> D2) :
      { f1 | f1 ≈ f2 }.
    Proof.
      exists (fun v1 => proj1_sig (F_surjective_comp (f2 (proj1_sig (v1_to_v2 _ v1))))).
      intros v1 v2 H1.
      destruct (v1_to_v2 ar v1) as [v2' H2]; cbn.
      destruct (F_surjective_comp (f2 v2')) as [y H3]; cbn.
      enough (v2 = v2') by congruence. 
      clear H3 f2. induction v2; dependent elimination v2'; dependent elimination v1.
      - reflexivity.
      - f_equal.
        + eapply eq2_sem, F_eq. apply H1. apply H2. now apply eq1_sem.
        + eapply IHv2. apply H1. apply H2.
    Qed. 


    Theorem sat_iff rho1 rho2 phi : 
      rho1 ≈ rho2 -> rho1 ⊨ phi <-> rho2 ⊨ phi.
    Proof.
      revert phi rho1 rho2. induction phi; intros; cbn.
      - easy.
      - destruct p.
        + apply H. apply Forall2_Forall. induction v; cbn.
          easy. split. now apply F_term. exact IHv.
        + destruct P; repeat depelim v; cbn.
          apply F_eq; apply F_term; exact H.
      - specialize (IHphi1 rho1 rho2 H); specialize (IHphi2 rho1 rho2 H).
        destruct b; tauto.
      - destruct q; split.
        + intros H1 y. destruct (F_surjective y).
          eapply IHphi. 2: apply H1. apply iso_env_i; eauto.
        + intros H1 x. destruct (F_total x).
          eapply IHphi. 2: apply H1. apply iso_env_i; eauto.
        + intros [x H1]. destruct (F_total x) as [y]. exists y.
          eapply IHphi. 2: apply H1. apply iso_env_i; eauto.
        + intros [y H1]. destruct (F_surjective y) as [x]. exists x.
          eapply IHphi. 2: apply H1. apply iso_env_i; eauto.
      - destruct q; split.
        + intros H1 f2. destruct (f2_to_f1 n f2).
          eapply IHphi. 2: apply H1. apply iso_env_f; eauto.
        + intros H1 f1. destruct (f1_to_f2 n f1).
          eapply IHphi. 2: apply H1. apply iso_env_f; eauto.
        + intros [f1 H1]. edestruct (f1_to_f2 n f1) as [f2].
          exists f2. eapply IHphi. 2: apply H1. apply iso_env_f; eauto.
        + intros [f2 H1]. edestruct (f2_to_f1 n f2) as [f1].
          exists f1. eapply IHphi. 2: apply H1. apply iso_env_f; eauto.
      - destruct q; split.
        + intros H1 P2. destruct (P2_to_P1 n P2).
          eapply IHphi. 2: apply H1. apply iso_env_p; eauto.
        + intros H1 P1. edestruct (P1_to_P2 n P1).
          eapply IHphi. 2: apply H1. apply iso_env_p; eauto.
        + intros [P1 H1]. edestruct (P1_to_P2 n P1) as [P2].
          exists P2. eapply IHphi. 2: apply H1. apply iso_env_p; eauto.
        + intros [P2 H1]. edestruct (P2_to_P1 n P2) as [P1 H2].
          exists P1. eapply IHphi. 2: apply H1. apply iso_env_p; eauto.
    Qed.

  End ComputationalF.



  (** If one side has a computational induction principle, we can
      translate from this side. *)

  Section ComputationalD1.

    Hypothesis rec1 : forall P : D1 -> Type, P O1 -> (forall x, P x -> P (S1 x)) -> forall x, P x.

    Lemma F_total_comp x : 
      { y | F x y }.
    Proof.
      revert x. apply rec1.
      - exists O2. exact F_O.
      - intros x [y IH]. exists (S2 y). now apply F_S.
    Qed.

    Lemma env1_to_env2_FO rho1 :
      { rho2 | rho1 ≈FF rho2 }.
    Proof.
      exists ⟨fun n => proj1_sig (F_total_comp (get_indi rho1 n)), 
              fun n ar v => O2, 
              fun n ar v => proj1_sig (P1_to_P2 _ (get_pred rho1 n ar)) v ⟩.
      intros n. split. destruct n; cbn; now destruct F_total_comp.
      intros ar v1 v2 H. cbn. destruct P1_to_P2 as [? H1]. now apply H1.
    Qed.

  End ComputationalD1.

  Section ComputationalD2.

    Hypothesis rec2 : forall P : D2 -> Type, P O2 -> (forall x, P x -> P (S2 x)) -> forall x, P x.

    Lemma F_surjective_comp y : 
      { x | F x y }.
    Proof.
      revert y. apply rec2.
      - exists O1. exact F_O.
      - intros y [x IH]. exists (S1 x). now apply F_S.
    Qed.

    Lemma env2_to_env1_FO rho2 :
      { rho1 | rho1 ≈FF rho2 }.
    Proof.
      exists ⟨fun n => proj1_sig (F_surjective_comp (get_indi rho2 n)), 
              fun n ar v => O1, 
              fun n ar v => proj1_sig (P2_to_P1 _ (get_pred rho2 n ar)) v ⟩.
      intros n. split. destruct n; cbn; now destruct F_surjective_comp.
      intros ar v1 v2 H. cbn. destruct P2_to_P1 as [? H1]. now apply H1.
    Qed.

  End ComputationalD2.


End Categoricity.



(** Consequence of categoricity we will use for incompleteness:
    If a closed formula holds in one model, it holds in all models. *)

Theorem PA_models_agree phi (M : Model_of PA) (rho : env (M_domain M)) :
  funcfree phi -> bounded_indi 0 phi -> (forall ar, bounded_pred ar 0 phi) -> sat _ rho phi -> forall M' : Model_of PA, M' ⊨ phi.
Proof.
  intros F Bi Bp H M' rho'.
  eapply sat_ext_closed_funcfree with (sigma := empty_PA_env _); try assumption.
  eapply sat_ext_closed_funcfree with (sigma := empty_PA_env _) in H; try assumption.
  eapply sat_iff_funcfree. 3: apply H.
  intros n. split. apply F_O. cbn. reflexivity. assumption.
Qed.

Theorem PA_models_agree_FO phi (M : Model_of PA) (rho : env (M_domain M)) :
  first_order phi -> bounded_indi 0 phi -> sat _ rho phi -> forall M' : Model_of PA, M' ⊨ phi.
Proof.
  intros F B H M' rho'.
  eapply sat_ext_closed_FO with (sigma := empty_PA_env _); try assumption.
  eapply sat_ext_closed_FO with (sigma := empty_PA_env _) in H; try assumption.
  eapply sat_iff_funcfree. 3: apply H.
  intros n. split. apply F_O. cbn. reflexivity. now apply firstorder_funcfree.
Qed.


(** Another interesting way of putting it using LEM: *)

Section LEM.

  Variable LEM : forall P, P \/ ~ P.

  Lemma PA_models_agree_LEM phi :
    funcfree phi -> bounded_indi 0 phi -> (forall ar, bounded_pred ar 0 phi) -> (forall M : Model_of PA, M ⊨ phi) \/ (forall M : Model_of PA, M ⊨ ¬ phi).
  Proof.
    intros FO B1 B2.
    destruct (LEM (Standard_PA_Model ⊨ phi)) as [H|H].
    - left. now apply PA_models_agree with (M := Standard_PA_Model) (rho := empty_PA_env _).
    - right. apply PA_models_agree with (M := Standard_PA_Model) (rho := empty_PA_env _); try easy. 
      intros H1. apply H. now apply PA_models_agree with (M := Standard_PA_Model) (rho := empty_PA_env _).
  Qed.

End LEM.



(** ** Failure of Upward Löwenheim-Skolem *)

Section LoewenheimSkolem.

  Definition countably_infinite (X : Type) := exists R : X -> nat -> Prop,
       (forall x, exists n, R x n)  (* Total *)
    /\ (forall n, exists x, R x n)  (* Surjective *)
    /\ (forall x n n', R x n -> R x n' -> n = n')  (* Functional *)
    /\ (forall x x' n, R x n -> R x' n -> x = x')  (* Injective *) .

  Theorem Upwards_Loewenheim_Skolem_Failure :
    forall M : Model_of PA, countably_infinite (M_domain M).
  Proof.
    intros M. exists (F M Standard_PA_Model). repeat split.
    - apply (F_total M Standard_PA_Model).
    - apply (F_surjective M Standard_PA_Model).
    - apply (F_functional M Standard_PA_Model).
    - apply (F_injective M Standard_PA_Model).
  Qed.

End LoewenheimSkolem.



(** ** Failure of Compactness *)

Require Import ListLib.

Section Compactness.

  Fixpoint num n := match n with 0 => zero | S n => σ (num n) end.

  Definition not_equal n := $0 == num n --> ⊥.

  Definition T phi := PA phi \/ exists n, phi = not_equal n.

  Lemma num_injective n1 n2 :
    num n1 = num n2 -> n1 = n2.
  Proof.
    revert n2. induction n1; intros [] H; try now inversion H.
    erewrite IHn1. reflexivity. now inversion H.
  Qed.

  Lemma num_standard_model n rho :
    eval (M_domain Standard_PA_Model) rho (num n) = n.
  Proof.
    induction n; cbn in *; congruence.
  Qed.

  Lemma not_equal_injective n1 n2 :
    not_equal n1 = not_equal n2 -> n1 = n2.
  Proof.
    revert n2. induction n1; intros [] H; try now inversion H.
    erewrite IHn1. reflexivity. inversion H. now apply num_injective in H1 as ->.
  Qed.

  Lemma not_equal_bounded n :
    bounded_indi 1 (not_equal n).
  Proof.
    induction n; cbn. lia. repeat split. lia. clear IHn. now induction n.
  Qed.


  (** T is decidable *)

  Lemma num_dec t:
    { n | t = num n } + ({ n | t = num n } -> False).
  Proof with try (right; intros [[] H]; now inversion H).
    induction t using term_rect... destruct f... all: repeat depelim v; cbn in *.
    - left. now exists 0.
    - destruct IH as [[IH|IH] _].
      + left. destruct IH as [n ->]. now exists (S n).
      + right. intros [[] H]; cbn in H. now inversion H. apply IH. exists n.
        now inversion H.
  Qed.

  Lemma not_equal_dec phi :
    { n | phi = not_equal n } + ({ n | phi = not_equal n } -> False).
  Proof with try (right; intros [[] H]; now inversion H).
    destruct phi... destruct b... destruct phi1... destruct phi2... 
    destruct p... destruct P. repeat depelim v. destruct h... destruct n...
    destruct (num_dec h0) as [[n1 ->]|H1]...
    - left. now exists n1.
    - right. intros [n H]. apply H1. exists n. now inversion H.
  Qed.

  Lemma T_decidable :
    decidable T.
  Proof.
    apply decidable_if. intros phi. apply or_dec. apply in_dec, form_eq_dec.
    destruct (not_equal_dec phi) as [[n ->]|H]. left. now exists n.
    right. intros [n ->]. apply H. now exists n.
  Qed.


  (** T does not fulfill compactness *)

  Lemma find_greatest_in_list A :
    (forall phi, List.In phi A -> T phi) -> exists k, forall n, List.In (not_equal n) A -> k > n.
  Proof.
    intros HA. induction A as [|phi A IHA]; cbn. now exists 0. destruct IHA as [k IHA].
    auto. destruct (HA phi) as [|[n ->]]; trivial.
    - exists k. intros n [->|]. 
      + cbn in H. unfold ax_eq_refl, ax_eq_symm, ax_zero_succ, ax_succ_inj, ax_add_zero, ax_add_rec, ax_mul_zero, ax_mul_rec, ax_ind in H.
        repeat (try destruct H as [|H]); try easy; destruct n; cbn in *; try congruence.
      + now apply IHA.
    - exists (max k (S n)). intros m [|].
      + apply not_equal_injective in H as ->. lia.
      + specialize (IHA _ H). lia.
  Qed.

  Lemma model_for_finite_subset A :
    (forall phi, List.In phi A -> T phi) -> exists (M : Model) rho, forall phi, List.In phi A -> (M, rho) ⊨ phi.
  Proof.
    intros HA. destruct (find_greatest_in_list A HA) as [k Hk].
    exists Standard_PA_Model, ⟨ fun _ => k, fun _ _ _ => 0, fun _ _ _ => True ⟩. 
    intros phi H. pose (H' := H). apply HA in H' as [|[n ->]].
    - now apply std_model_correct.
    - cbn. rewrite num_standard_model. intros ->. specialize (Hk n H). lia.
  Qed.

  Lemma no_model_for_T :
    ~ exists (M : Model) rho, forall phi, T phi -> (M, rho) ⊨ phi.
  Proof.
    intros [M [rho H]].
    assert (forall phi, PA phi -> M ⊨ phi) as M_PA_sat.
    { intros phi H1 rho'. specialize (H phi (or_introl H1)). 
      repeat destruct H1 as [<-|H1]; eauto. easy. }
    pose (M_PA := {| M_model := M ; M_correct := M_PA_sat |}).
    destruct (F_surjective Standard_PA_Model M_PA (get_indi rho 0)) as [n Hn].
    specialize (H (not_equal n)).
    change ((M, rho) ⊨ (not_equal n)) with ((M_PA, rho) ⊨ (not_equal n)) in H.
    eapply sat_iff_firstorder_bounded with (rho1 := ⟨ fun _ => n, fun _ _ _ => 0, fun _ _ _ => True ⟩) in H.
    - apply H. cbn. now rewrite num_standard_model.
    - repeat split. clear. now induction n.
    - intros [] H1; cbn. apply Hn. exfalso. apply H1. eapply bounded_indi_up.
      2: apply not_equal_bounded. lia.
    - right. now exists n.
  Qed.

  Theorem Compactness_Failure :
    ~ ((exists (M : Model) rho, forall phi, T phi -> (M, rho) ⊨ phi) <-> (forall A, (forall phi, List.In phi A -> T phi) -> exists (M : Model) rho, forall phi, List.In phi A -> (M, rho) ⊨ phi)).
  Proof.
    intros H. apply no_model_for_T, H, model_for_finite_subset.
  Qed.

End Compactness.



(** ** Infinitary Incompleteness *)

Section InfinitaryIncompleteness.

  Variable prv : list form -> form -> Prop.
  Definition tprv (T : form -> Prop) phi := exists A, (forall psi, List.In psi A -> T psi) /\ prv A phi.
  Notation "T ⊢ phi" := (prv T phi) (at level 20).
  Notation "T ⊩ phi" := (tprv T phi) (at level 20).

  Definition valid' (T : form -> Prop) phi :=
    forall M rho, (forall a, T a -> (M, rho) ⊨ a) -> (M, rho) ⊨ phi.

  Hypothesis sound : forall T phi, T ⊩ phi -> validT T phi.
  Hypothesis complete : forall T phi, decidable T -> validT T phi -> T ⊩ phi.

  Definition LEM := forall P, P \/ ~ P.

  (** Compatibility between different valdity formulations *)
  Lemma model_to_valid (T : form -> Prop) phi :
    (forall M rho, (forall a, T a -> (M, rho) ⊨ a) -> (M, rho) ⊨ phi) -> validT T phi.
  Proof.
    intros H D I rho. apply (H {| M_domain := D ; M_interp := I |} rho).
  Qed.

  (** We can avoid the use of LEM since we want to show a negation *)
  Lemma xm_neg P :
    (P \/ ~ P -> False) -> False. 
  Proof.
    tauto.
  Qed.

  Theorem InfinitaryIncompleteness :
    False.
  Proof.
    eapply xm_neg. intros X.
    apply Compactness_Failure. split.
    - intros [M [rho H1]] A H2. exists M, rho. intros phi H3. apply H1, H2, H3.
    - intros H1. enough (~ T ⊩ ⊥) as HT.
      { destruct X as [X|H]. apply X. exfalso. apply HT.
        apply complete, model_to_valid. apply T_decidable. intros M rho H2. apply H. now exists M, rho. }
      intros [A [H2 H3]]. assert ((fun phi => List.In phi A) ⊩ ⊥) as H4%sound by now exists A.
      destruct (H1 A) as [M [rho H5]]; trivial. eapply H4. apply H5.
  Qed.

End InfinitaryIncompleteness.






Notation "'izero'" := (@i_f _ _ (M_domain _) (M_interp _) Zero ([])).
Notation "'iσ' x" := (@i_f _ _ (M_domain _) (M_interp _) Succ ([x])) (at level 37).
Notation "x 'i⊕' y" := (@i_f _ _ (M_domain _) (M_interp _) Plus ([x ; y])) (at level 39).
Notation "x 'i⊗' y" := (@i_f _ _ (M_domain _) (M_interp _) Mult ([x ; y])) (at level 38).
Notation "x 'i==' y" := (@i_P _ _ (M_domain _) (M_interp _) Eq ([x ; y])) (at level 40).

Notation "rho ≈ sigma" := (@iso _ _ _ rho sigma) (at level 30).
Notation "rho ≈FF sigma" := (@iso_env_funcfree _ _ rho sigma) (at level 30).
