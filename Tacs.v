(****************************************************************
   
   Tactics
   
 ****************************************************************)

Ltac genc term := generalize term; clear term.

Ltac dest_wp :=
  intros [t1 [t2 [c [Hperm_c1 [Heq_c2 Hperm_w]]]]].

Ltac intro_dest_wp :=
  intros c1 w1 c2 w2; dest_wp.

Ltac eq_subst :=
  match goal with
    |  |- _ = _ -> _ => intro; subst
  end.

Ltac inject_subst :=
  match goal with
    | H: _ = _ |- _ => 
      injection H; repeat eq_subst; clear H
  end.

Ltac inject_subst' eq :=
  injection eq; repeat eq_subst; clear eq.

Set Implicit Arguments.

(* special induction principles *)
Require Import List.
Theorem double_list_induction: forall (A B: Set),
  forall P: list A -> list B -> Prop,
    (forall l1: list A, P l1 nil) ->
    (forall l2: list B, P nil l2) ->
    (forall (a: A)(l1: list A)(b: B)(l2: list B),
      P l1 l2 -> P (a::l1) (b::l2)) ->
    forall (l1: list A)(l2: list B), P l1 l2.
Proof.
  intros A' B P Hl1nil Hnill2 Hcons.
  intro l1; elim l1;
    [apply Hnill2 | clear l1; intros a l1 IHl1].
  intro l2; case l2;
    [apply Hl1nil | clear l2; intros b l2; apply Hcons; apply IHl1].
Qed.


Require Import Huffman.Permutation.
Require Import Huffman.Ordered.

Section lemmas.
  Variable (A: Set).
  
  Lemma perm_case:
    forall a b (l l1 l2: list A),
      permutation l (a::l1) ->
      permutation l (b::l2) ->
      (exists l',
        permutation l (a::b::l'))\/a=b.
  Proof.
    intros a b l l1 l2 Hperm1 Hperm2.
    generalize
      (permutation_trans _ _ _ _
        (permutation_sym _ _ _ Hperm1) Hperm2).
    intro Hperm; apply permutation_cons_ex in Hperm.
    destruct Hperm as [l3 [l4 [Heq Hperm]]].
    genc Hperm; genc Heq.
    case l3; clear l3; simpl.
    intros; injection Heq; intros; subst b l4; clear Heq.
    right; reflexivity.
    intros c l3 Heq; injection Heq; intros; subst c; clear Heq.
    left; exists (l3++l4).
    apply (permutation_trans _ _ _ _ Hperm1).
    apply permutation_skip; assumption.
  Qed.

  Lemma perm_2_1:
    forall a b (l l1 l2: list A),
      a <> b ->
      permutation l (a::l1) ->
      permutation l (b::l2) ->
      exists l',
        permutation l (a::b::l').
  Proof.
    intros.
    generalize (perm_case H0 H1).
    intros [Hperm | Heq].
    assumption.
    elim H; assumption.
  Qed.

  
  Lemma NoDup_neq:
    forall l: list A,
    (forall t1 t2 l',
      permutation l (t1::t2::l') -> t1<>t2) ->
    NoDup l.
  Proof.
    intro l; elim l; clear l.
    intros; apply NoDup_nil.
    intros; apply NoDup_cons.
    genc H0; genc H; case l; clear l.
    simpl; tauto.
    simpl; intros b l; intros.
    intros [Heq | HIn]; subst.
    elim (H0 a a l (permutation_refl _ _)); reflexivity.
    cut (exists l', permutation l (a::l')).
    intros [l' Hperm].
    cut (permutation (a::b::l) (a::a::b::l')).
    intro Hperm'.
    elim (H0 a a (b::l') Hperm'); reflexivity.
    apply permutation_skip.
    apply permutation_trans with (b::a::l').
    apply permutation_skip; assumption.
    apply permutation_swap.
    clear H H0.
    genc HIn; genc a; elim l.
    simpl; intros; contradiction.
    simpl; intros b' l' IH a [Heq | HIn]; subst.
    exists l'; apply permutation_refl.
    destruct (IH _ HIn) as [l'' Hperm].
    exists (b'::l'').
    apply permutation_trans with (b'::a::l'').
    apply permutation_skip; assumption.
    apply permutation_swap.
    apply H.
    intros; eapply H0.
    apply permutation_trans with (a::t1::t2::l').
    apply permutation_skip; assumption.
    apply permutation_trans with (t1::a::t2::l').
    apply permutation_swap.
    apply permutation_skip; apply permutation_swap.
  Qed.


  Lemma cons_to_app:
    forall x (l: list A),
      x::l = (x::nil)++l.
  Proof.
    simpl; reflexivity.
  Qed.

  Lemma perm_app_in:
    forall (t: A) l l1 l2,
      permutation (t::l) (l1++l2) ->
      In t l1\/In t l2.
  Proof.
    intros t l l1; genc l; genc t.
    elim l1; clear l1; simpl.
    intros; right.
    apply (permutation_in _ _ _ _ H); simpl; left; reflexivity.
    intros a l1 IH t l l2 Hperm.
    apply permutation_cons_ex in Hperm.
    destruct Hperm as [l3 [l4 [Heq Hperm]]].
    genc Hperm; genc Heq.
    case l3; clear l3; simpl.
    intros; injection Heq; intros; subst t l4; clear Heq.
    left; left; reflexivity.
    intros t' l3; intros; injection Heq; intros; subst t'; clear Heq.
    cut (permutation (t::l3++l4) (l1++l2)).
    intro Hperm'.
    destruct (IH _ _ _ Hperm').
    left; right; assumption.
    right; assumption.
    rewrite H.
    rewrite (app_comm_cons l3).
    rewrite (cons_to_app t l4).
    rewrite app_assoc.
    apply permutation_app_comp; auto.
    rewrite (cons_to_app t l3); auto.
  Qed.

  Lemma in_to_perm:
    forall x (l: list A),
      In x l -> exists l', permutation l (x::l').
  Proof.
    intros x l HIn.
    apply in_split in HIn.
    destruct HIn as [l1 [l2 Heq]];
      subst l; exists (l1++l2).
    rewrite cons_to_app.
    rewrite app_comm_cons.
    rewrite app_assoc.
    apply permutation_app_comp; auto.
    rewrite (cons_to_app x l1); auto.
  Qed.
End lemmas.

Section OrderedLemmas.
  Variable (A: Set)(f: A -> nat)(order: A -> A -> Prop).
  Hypothesis
    (order_refl: forall x, order x x)
    (order_trans: forall x y z, order x y -> order y z -> order x z)
    (order_dec: forall x y, {order x y}+{order y x}).

  Lemma ordered_in_ordered:
    forall x l,
      ordered order l ->
      (forall y, In y l -> order x y) ->
      ordered order (x::l).
  Proof.
    intros x l Hord; generalize x; clear x.
    elim Hord; clear Hord l.
    intros; apply ordered_one.
    simpl; intros x z IH.
    apply ordered_cons.
    apply IH; left; reflexivity.
    apply ordered_one.
    intros a b l Horder Hord IH x HIn_order.
    repeat apply ordered_cons.
    apply HIn_order; simpl; left; reflexivity.
    assumption.
    assumption.
  Qed.

  Lemma ordered_app_cons:
    forall a l1 l2,
      ordered order (l1++a::l2) -> ordered order (l1++l2).
  Proof.
    intros a l1; generalize a; clear a.
    elim l1; clear l1.
    simpl; apply ordered_inv.
    simpl; intros a l1 IH b l2 Hord.
    inversion Hord; subst a0.
    elim (app_cons_not_nil _ _ _ H1).
    generalize H0 Hord IH; clear H0 Hord IH.
    case l1; clear l1.
    simpl.
    intro.
    injection H0; intros; subst b0 l; clear H0.
    apply (ordered_skip _ _ order_trans) with b;
      apply ordered_cons; assumption.
    intros c l1 Heq; injection Heq; intros; subst b0 l; clear Heq.
    simpl.
    apply ordered_cons; [assumption | apply (IH b _ H2)].
  Qed.    


  Lemma ordered_app_l:
    forall l1 l2,
      ordered order (l1++l2) -> ordered order l1.
  Proof.
    intros l1 l2; generalize l1; clear l1.
    elim l2; clear l2.
    intro l1; rewrite app_nil_r; tauto.
    intros a l2 IH l1 Hord. 
    apply ordered_app_cons in Hord; apply (IH _ Hord).
  Qed.

  Lemma ordered_app_r:
    forall l1 l2,
      ordered order (l1++l2) -> ordered order l2.
  Proof.
    intro l1; elim l1; clear l1; simpl.
    tauto.
    intros a l1 IH l2 Hord.
    apply IH.
    apply ordered_inv in Hord.
    assumption.
  Qed.
    
  Lemma ordered_head:
    forall x l l',
      ordered order l ->
      l = x::l' ->
      forall y, In y l -> order x y.
  Proof.
    intros x l l' Hord;
      generalize x l';
        clear x l'.
    elim Hord; clear Hord l.
    intros; contradiction.
    simpl.
    intros a x l' Heq y [Heq' | F];
      [injection Heq; intros; subst; subst | contradiction].
    apply order_refl.
    intros a b l Horder Hordered IH x l' Heq.
    simpl.
    intros y [Heq' | [Heq' | HIn]]; subst;
      injection Heq; intros; subst.
    apply order_refl.
    assumption.
    apply (order_trans Horder).
    apply IH with l;
      [reflexivity | simpl; right; assumption].
  Qed.

  Lemma ordered_app_head_l:
    forall x l l1 l2,
      ordered order (l1++l2) ->
      x::l = l1++l2 ->
      forall y, In y l1 -> order x y.
  Proof.
    intros x l l1;
      generalize x l;
        clear x l.
    elim l1; clear l1.
    simpl; intros; contradiction.
    intros a1 l1 IH x l l2 Hordered Heq.
    injection Heq; intros; subst x l; clear Heq.
    simpl in H1; destruct H1 as [Heq | HIn].
    subst y; apply order_refl.
    induction l1.
    contradiction.
    simpl in IH.
    apply order_trans with a.
    inversion Hordered; assumption.
    simpl in Hordered.
    apply ordered_inv in Hordered.
    apply (IH _ _ _ Hordered (eq_refl _)).
    simpl in HIn; assumption.
  Qed.    

  Lemma ordered_app_head_r:
    forall x l l1 l2,
      ordered order (l1++l2) ->
      x::l = l1++l2 ->
      forall y, In y l2 -> order x y.
  Proof.
    intros x l l1 l2;
      generalize x l l1;
        clear x l l1.
    elim l2; clear l2.
    simpl; intros; contradiction.
    intros a2 l2 IH x l l1 Hordered Heq.
    rewrite (cons_to_app a2 _) in Hordered.
    rewrite (cons_to_app a2 _) in Heq.
    rewrite app_assoc in Hordered.
    rewrite app_assoc in Heq.
    generalize (IH _ _ _ Hordered Heq).
    intro H.
    simpl; intros y [Heq' | HIn]; subst.
    apply (ordered_app_head_l _ _ Hordered Heq).
    rewrite in_app_iff; right; simpl; left; reflexivity.
    apply H; assumption.
  Qed.

  Lemma ordered_app_order_aux:
    forall a l1 l2,
      ordered order (l1++a::l2) ->
      forall x, In x l1 -> order x a.
  Proof.
    intros a l1; generalize a; clear a.
    elim l1; clear l1.
    simpl; intros; contradiction.
    simpl.
    intros a1 l1 IH a l2 Hordered x [Heq | HIn].
    subst.
    apply (ordered_trans _ _ order_trans x _ _ Hordered).
    apply in_app_iff; right; simpl; left; reflexivity.
    generalize HIn; clear HIn.
    apply ordered_inv in Hordered.
    apply (IH _ _ Hordered).
  Qed.    

  Lemma ordered_insert:
    forall a l,
      ordered order l ->
      exists l1, exists l2,
        l = (l1++l2)/\
        ordered order (l1++a::l2).
  Proof.
    intros a l Hord; generalize a; clear a.
    elim Hord; clear Hord l.
    intro a; exists nil, nil; repeat split; simpl.
    apply ordered_one.
    intros a b;
      case (order_dec a b); intro Hord.
    exists (a::nil), nil; repeat split; simpl.
    apply ordered_cons; [assumption | apply ordered_one].
    exists nil, (a::nil); repeat split; simpl.
    apply ordered_cons; [assumption | apply ordered_one].
    intros a b l Horder Hordered IH c.
    destruct (IH c) as [l1 [l2 [Heq Hordered']]].
    clear IH.
    generalize Heq Hordered'.
    clear Heq Hordered'.
    case l1; clear l1; simpl.
    intros; subst.
    case (order_dec a c); intro Hord.
    exists (a::nil), (b::l); simpl; split.
    reflexivity.
    apply ordered_cons; assumption.
    exists nil, (a::b::l); simpl; split.
    reflexivity.
    repeat apply ordered_cons; assumption.
    intros b' l1; intros; injection Heq; intros; subst b' l.
    exists (a::b::l1), l2; simpl; split.
    reflexivity.
    apply ordered_cons; assumption.
  Qed.


  Lemma ordered_perm_ex:
    forall l,
      exists l', permutation l l'/\ordered order l'.
  Proof.
    intro l; elim l; clear l.
    exists nil; split.
    apply permutation_nil.
    apply ordered_nil.
    intros a l [l' [Hperm Hord]].
    destruct (ordered_insert a Hord) as [l1 [l2 [Heq Hord']]].
    subst.
    exists (l1++a::l2); split.
    apply permutation_trans with (a::l1++l2).
    apply permutation_skip; assumption.
    rewrite (cons_to_app a l2); rewrite app_assoc.
    rewrite app_comm_cons.
    apply permutation_app_comp.
    rewrite (cons_to_app a l1); apply permutation_app_swap.
    apply permutation_refl.
    assumption.
  Qed.
End OrderedLemmas.

    

Section NoDup.
  Variable A: Set.
  Lemma NoDup_inv:
    forall (a: A) l,
      NoDup (a::l) -> NoDup l.
  Proof.
    intros a l Hnd; inversion Hnd; subst; assumption.
  Qed.
      
  Lemma NoDup_perm:
    forall (l1 l2: list A),
      permutation l1 l2 ->
      NoDup l1 -> NoDup l2.
  Proof.
    intros l1 l2 Hperm; elim Hperm; clear Hperm l1 l2.
    tauto.
    intros.
    apply NoDup_cons.
    inversion H1; subst.
    intro HIn; apply H4.
    apply permutation_sym in H.
    apply (permutation_in _ _ _ _ H); assumption.
    apply NoDup_inv in H1.
    apply H0; assumption.
    intros a b l Hnd;
      repeat apply NoDup_cons.
    inversion Hnd; subst.
    inversion H2; subst.
    simpl; intro HIn.
    destruct HIn as [Heq | HIn]; subst.
    apply H1; simpl; left; reflexivity.
    apply H3; assumption.
    inversion Hnd; subst.
    intro HIn; apply H1; simpl; right; assumption.
    repeat apply NoDup_inv in Hnd; assumption.
    intros; tauto.
  Qed.

  Lemma NoDup_app_inv_l:
    forall l1 l2: list A,
      NoDup (l1++l2) -> NoDup l1.
  Proof.
    intro l1; elim l1; clear l1.
    simpl; intros; apply NoDup_nil.
    simpl; intros; apply NoDup_cons.
    inversion H0; subst.
    intro HIn; apply H3; apply in_app_iff;
      left; assumption.
    apply (H l2); apply NoDup_inv in H0; assumption.
  Qed.

  Lemma NoDup_app_inv_r:
    forall l1 l2: list A,
      NoDup (l1++l2) -> NoDup l2.
  Proof.
    intro l1; elim l1; clear l1.
    simpl; tauto.
    simpl; intros.
    apply H; apply NoDup_inv in H0; assumption.
  Qed.
End NoDup.
