(****************************************************************

   Wrapper.v

 ****************************************************************)


(* Standard Libraries *)
Require Import List.
Require Import Relations.

(* By L.Thery *)
Require Import Huffman.Permutation.
Require Import Huffman.BTree.
Require Import Huffman.WeightTree.
Require Import Huffman.Cover.

(* append by me *)
Require Import SiblProp.Tacs.
Require Import SiblProp.BTree_appendix.

Set Implicit Arguments.


Section Wrapper.
  Variables (A: Set)(f: A -> nat).
  Hypothesis eq_A_dec: forall a b: A, {a=b}+{a<>b}.
  Notation "[ X ]" := (leaf X).
  Infix "/-\" := (@node A) (at level 60, no associativity).

  Definition wrapper_prop (c1 w1 c2 w2: list (btree A)) :=
    exists t1, exists t2, exists c,
      permutation c1 (t1::t2::c)/\
      c2 = (t1/-\t2::c)/\
      permutation w1 (t1/-\t2::w2).

  Ltac dest_wp :=
    intros [t1 [t2 [c [Hperm_c1 [Heq_c2 Hperm_w]]]]].

  Ltac intro_dest_wp :=
    intros c1 w1 c2 w2; dest_wp.

  Definition all_distinct (l: list (btree A)) :=
    forall x, In x l -> distinct_leaves x.

  Lemma wrapper_prop_c_ad:
    forall c1 w1 c2 w2, wrapper_prop c1 w1 c2 w2 ->
      all_distinct c2 ->
      all_distinct c1.
  Proof.
    intro_dest_wp; subst.
    unfold all_distinct; simpl; intros Had.
    intros x HIn; apply (permutation_in _ _ _ _ Hperm_c1) in HIn.
    simpl in HIn; destruct HIn as [Heq | [Heq | HIn]]; subst.
     generalize (Had _ (or_introl _ (eq_refl _))).
     intro Hdl; apply distinct_leaves_l in Hdl; assumption.

     generalize (Had _ (or_introl _ (eq_refl _))).
     intro Hdl; apply distinct_leaves_r in Hdl; assumption.

     apply Had; right; assumption.
  Qed.    
    

  Lemma wrapper_prop_w_incl:
    forall c1 w1 c2 w2,
      wrapper_prop c1 w1 c2 w2 ->
      incl w2 w1.
  Proof.
    intro_dest_wp.
    intros x HIn.
    apply (permutation_in _ _ _ _ (permutation_sym _ _ _ Hperm_w));
      simpl; right; assumption.
  Qed.

  (* Wrapper *)
  Inductive wrapper: list (btree A) -> list (btree A) -> btree A -> Prop :=
  | wrapper_one:
    forall t, wrapper (t::nil) nil t
  | wrapper_node:
    forall c1 w1 c2 w2,
      wrapper_prop c1 w1 c2 w2 ->
      forall t,
        wrapper c2 w2 t ->
        wrapper c1 w1 t.

  Ltac ind_wr :=
    intros c w t Hw; elim Hw; clear Hw c w t.

  Lemma wrapper_cover:
    forall c w t,
      wrapper c w t -> cover c t.
  Proof.
    ind_wr.
     apply cover_one.
     
     intro_dest_wp; subst.
     intros; eapply cover_node; eassumption.
  Qed.

  Lemma wrapper_exists:
    forall c t, cover c t ->
      exists w, wrapper c w t.
  Proof.
    intros c t Hc; elim Hc; clear Hc c t.
     intro t; exists nil; apply wrapper_one.

     intros l1 l2 t1 t2 t Hperm Hc [w Hcwb].
     exists (t1/-\t2::w).
     eapply wrapper_node; try eassumption.
     unfold wrapper_prop.
     exists t1, t2, l2; repeat split;
       try eassumption; auto.
  Qed.

  Lemma wrapper_perm:
    forall c w t,
      wrapper c w t ->
      forall c' w',
        permutation c c' ->
        permutation w w' ->
        wrapper c' w' t.
  Proof.
    ind_wr.
     intros.
     apply permutation_one_inv in H; subst.
     apply permutation_sym in H0;
       apply permutation_nil_inv in H0; subst;
         apply wrapper_one.

     intro_dest_wp; subst; intros.
     eapply wrapper_node.
      exists t1, t2, c; repeat split.
       apply permutation_trans with (c1); auto.
       apply permutation_sym; assumption.

       apply permutation_trans with (w1); auto.
        apply permutation_sym; assumption.
        
        eassumption.
      apply H0; auto.
  Qed.
  
 
  Lemma wrapper_all_node:
    forall c w t, wrapper c w t ->
      all_node w.
  Proof.
    unfold all_node.
    ind_wr.
     simpl; intros; contradiction.

     intro_dest_wp; subst; intros.
     apply (permutation_in _ _ _ _ Hperm_w) in H1;
       simpl in H1; destruct H1 as [Heq | HIn];
         subst; simpl; auto.
  Qed.
 
  Lemma wrapper_child_reached_cover:
    forall c w t, wrapper c w t ->
      forall tl tr, In (node tl tr) w ->
        (exists tc, In tc c/\sum_order f tc tl)/\
        (exists tc, In tc c/\sum_order f tc tr).
  Proof.
    ind_wr.
    simpl; intros; contradiction.
    intro_dest_wp; subst; intros.
    apply (permutation_in _ _ _ _ Hperm_w) in H1.
    simpl in H1; destruct H1 as [Heq | HIn]; [inject_subst |].
    apply permutation_sym in Hperm_c1.
    split;
      eexists; split;
        try unfold sum_order; trivial;
          eapply (permutation_in _ _ _ _ Hperm_c1); simpl;
            tauto.
    destruct (H0 _ _ HIn) as [[tcl [HInl Hlel]] [tcr [HInr Hler]]].
    apply permutation_sym in Hperm_c1.
    split.
    simpl in HInl; destruct HInl as [Heq | HInl]; subst.
    exists t2; split;
      [apply (permutation_in _ _ _ _ Hperm_c1); simpl;
        right; left; reflexivity |
          apply sum_order_trans with (t1/-\t2);
            [apply sum_order_node_r | assumption]].
    exists tcl; split;
      [apply (permutation_in _ _ _ _ Hperm_c1); simpl;
        right; right; assumption | assumption].
    simpl in HInr; destruct HInr as [Heq | HInr]; subst.
    exists t2; split;
      [apply (permutation_in _ _ _ _ Hperm_c1); simpl;
        right; left; reflexivity |
          apply sum_order_trans with (t1/-\t2);
            [apply sum_order_node_r | assumption]].
    exists tcr; split;
      [apply (permutation_in _ _ _ _ Hperm_c1); simpl;
        right; right; assumption | assumption].
  Qed.
  
  Lemma wrapper_child_in:
    forall c w t, wrapper c w t ->
      forall tl tr,
        In (tl/-\tr) w ->
        ((In tl c/\In tr c)\/
          (In tl w/\In tr w)\/
          (In tl w/\In tr c)\/
          (In tl c/\In tr w)).
  Proof.
    ind_wr.
    simpl; intros; contradiction.
    intro_dest_wp; subst; intros.
    apply (permutation_in _ _ _ _ Hperm_w) in H1;
      simpl in H1; destruct H1 as [Heq | HIn];
        [inject_subst |].
    left; split; apply permutation_sym in Hperm_c1;
      apply (permutation_in _ _ _ _ Hperm_c1); simpl;
        [| right]; left; reflexivity.
    simpl in H0.
    destruct (H0 _ _ HIn)
      as [[[Heq_l | HIn_l] [Heq_r | HIn_r]]
        | [[HIn_l HIn_r]
          | [[HIn_l [Heq_r | HIn_r]]
            | [[Heq_l | HIn_l] HIn_r]]]]; subst;
      [right; left | right; right; left | right; right; right | left
        | right; left | right; left | right; right; left | right; left |
          right; right; right]; split;
      try 
        (apply permutation_sym in Hperm_w;
          apply (permutation_in _ _ _ _ Hperm_w); simpl;
            try (left; reflexivity);
              try (right; assumption));
        try 
          (apply permutation_sym in Hperm_c1;
            apply (permutation_in _ _ _ _ Hperm_c1); simpl;
              try (left; reflexivity);
                try (right; left; reflexivity);
                  try (right; right; assumption)).
  Qed.


  Lemma wrapper_nil_inv:
    forall c t, wrapper c nil t -> c = t::nil.
  Proof.
    intros c' t Hw; inversion Hw; subst.
    reflexivity.
    genc H; dest_wp; subst.
    apply permutation_length in Hperm_w;
      simpl in H0; discriminate.
  Qed.

  Lemma wrapper_nil_aux:
    forall c w t,
      wrapper c w t ->
      c = t::nil ->
      w = nil.
  Proof.
    ind_wr.
    reflexivity.
    intro_dest_wp; intros; subst.
    apply permutation_length in Hperm_c1; discriminate.
  Qed.

  Lemma wrapper_nil:
    forall w t,
      wrapper (t::nil) w t ->
      w = nil.
  Proof.
    intros w t Hw;
      apply (wrapper_nil_aux Hw (eq_refl _)).
  Qed.


  Lemma wrapper_leaf_inv_aux:
    forall c w t, wrapper c w t ->
      forall a,
        t = [a] ->
        c = [a]::nil/\w=nil.
  Proof.
    ind_wr.
    intros; subst; split; reflexivity.
    intro_dest_wp; subst; intros.
    apply H0 in H1.
    destruct H1; discriminate.
  Qed.


  Lemma wrapper_leaf_inv:
    forall c w a,
      wrapper c w [a] -> c=[a]::nil/\w=nil.
  Proof.
    intros; eapply wrapper_leaf_inv_aux;
      [eassumption | reflexivity].
  Qed.


  Lemma wrapper_cover_In_inb:
    forall c w t, wrapper c w t ->
      forall t', In t' c -> inb t' t.
  Proof.
    intros c w t Hw; apply wrapper_cover in Hw.
    intro.
    apply (cover_in_inb _ _ _ _ Hw).
  Qed.

  Lemma wrapper_wrapper_in_inb:
    forall c w t, wrapper c w t ->
      forall t', In t' w -> inb t' t.
  Proof.
    ind_wr.
    simpl; intros; contradiction.
    intro_dest_wp; subst.
    intros.
    apply (permutation_in _ _ _ _ Hperm_w) in H1.
    simpl in H1; destruct H1 as [Heq | HIn]; subst.
    generalize (wrapper_cover_In_inb H); simpl; intros HIib.
    apply HIib; left; reflexivity.
    apply H0; assumption.
  Qed.


  Lemma wrapper_distinct_cover:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      all_distinct c.
  Proof.
    ind_wr.
    simpl; intros t Hdl x [Heq | F];
      [subst x; assumption | contradiction].
    intros; eapply wrapper_prop_c_ad; try eassumption; try tauto.
  Qed.
    


  Lemma wrapper_NoDup_cover_aux:
    forall c w t,
      wrapper c w t ->
      forall t1 t2,
        In t1 c -> In t2 c ->
        inb t1 t2\/inb t2 t1\/
        (exists tl, exists tr,
          inb (tl/-\tr) t/\
          ((inb t1 tl/\inb t2 tr)\/(inb t2 tl/\inb t1 tr))).
  Proof.
    intros c w t Hw.


    generalize (wrapper_cover_In_inb Hw).
    intros HIi t1 t2 HIn_1 HIn_2.

    apply HIi in HIn_1.
    apply HIi in HIn_2.

    clear Hw HIi.

    generalize (inb_inb_inb HIn_1 HIn_2).
    intros
      [[Heq_1 Heq_2]
      | [[tl [tr [Hinb [[Hinb_l Hinb_r]
        | [Hinb_l Hinb_r]]]]] | [Hinb | Hinb]]]; subst.
    left; assumption.
    right; right; exists tl, tr; split;
      [assumption | left; split; assumption].
    right; right; exists tl, tr; split;
      [assumption | right; split; assumption].
    left; assumption.
    right; left; assumption.
  Qed.

  Lemma wrapper_NoDup_cover_aux_1:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall t1 t2,
        In t1 c -> In t2 c ->
        forall x y,
          inb x t1 -> inb y t2 ->
          x<>y\/inb t1 t2\/inb t2 t1.
  Proof.
    intros c w t Hw.


    generalize (wrapper_cover_In_inb Hw).
    intros HIi Hdl t1 t2 HIn_1 HIn_2 x y Hinb_x Hinb_y.
    
    generalize (wrapper_NoDup_cover_aux Hw _ _ HIn_1 HIn_2).
    intros [Hinb | [Hinb | [tl [tr [Hinb [[Hinb_l Hinb_r] | [Hinb_l Hinb_r]]]]]]].
    right; left; assumption.
    right; right; assumption.
    left; intro Heq; subst y.
    generalize (Hdl x _  _ Hinb); intro H; apply H.
    eapply inb_trans.
    eexact Hinb_x.
    assumption.
    eapply inb_trans.
    eexact Hinb_y.
    assumption.
    left; intro Heq; subst y.
    generalize (Hdl x _  _ Hinb); intro H; apply H.
    eapply inb_trans.
    eexact Hinb_y.
    assumption.
    eapply inb_trans.
    eexact Hinb_x.
    assumption.
  Qed.



  Lemma wrapper_distinc_cover_2:
    forall c w t,
      wrapper c w t ->
      forall t1 t2,
        In t1 c -> In t2 c ->
        ~inb t1 t2 -> ~inb t2 t1 ->
        (exists x, inb x t1/\inb x t2) ->
        ~distinct_leaves t.
  Proof.
    intros.
    generalize (wrapper_NoDup_cover_aux H _ _ H0 H1).
    intros [Hinb | [Hinb | [tl [tr [Hinb [[Hinb_l Hinb_r] | [Hinb_l Hinb_r]]]]]]].
    elim H2; assumption.
    elim H3; assumption.
    destruct H4 as [x [Hinb_1 Hinb_2]].
    intro Hdl; eapply Hdl in Hinb.
    apply Hinb.
    eapply inb_trans.
    eexact Hinb_1.
    assumption.
    eapply inb_trans; eassumption.
    destruct H4 as [x [Hinb_1 Hinb_2]].
    intro Hdl; eapply Hdl in Hinb.
    apply Hinb.
    eapply inb_trans.
    eexact Hinb_2.
    assumption.
    eapply inb_trans.
    eexact Hinb_1.
    assumption.
  Qed.


  Lemma wrapper_min_child_in_cover:
    forall c w t,
      wrapper c w t ->
      all_well_sibl f w ->
      (*
      strict_parent f w ->
      *)
      strict_parent f t ->
      forall t1 t2 w',
        permutation w (t1/-\t2::w') ->
        (forall x, In x w' -> node_le f (t1/-\t2) x) ->
        In t1 c/\In t2 c.
  Proof.
    intros.
    cut (In (t1/-\t2) w).
    intro HIn.
    generalize (wrapper_child_in H _ _ HIn).
    generalize (wrapper_all_node H); intro Han.
    intros [[HIn_1 HIn_2] | [[HIn_1 HIn_2] | [[HIn_1 HIn_2] | [HIn_1 HIn_2]]]].
    repeat split; try assumption.
    

    generalize (Han _ HIn_1); intro Hin_1;
      apply is_node_exists in Hin_1;
        destruct Hin_1 as [tl1 [tr1 Heq]]; subst.
    generalize (wrapper_wrapper_in_inb H _ HIn_1); intro Hinb.
    generalize (H1 _ _ Hinb); simpl; intro Hlt_1.
    apply (permutation_in _ _ _ _ H2) in HIn_1.
    simpl in HIn_1; destruct HIn_1 as [Heq | HIn_1].
    elim (not_node_l Heq).
    generalize (H3 _ HIn_1); simpl; unfold sum_order; simpl; intros Hle_1.
    generalize (le_lt_trans _ _ _ Hle_1 Hlt_1); intro Hlt_21.
    generalize (Han _ HIn_2); intro Hin_2;
      apply is_node_exists in Hin_2;
        destruct Hin_2 as [tl2 [tr2 Heq]]; subst.
    generalize (wrapper_wrapper_in_inb H _ HIn_2); intro Hinb'.
    generalize (H1 _ _ Hinb'); simpl; intro Hlt_2.
    apply (permutation_in _ _ _ _ H2) in HIn_2.
    simpl in HIn_2; destruct HIn_2 as [Heq | HIn_2].
    elim (not_node_r Heq).
    generalize (H3 _ HIn_2); simpl; unfold sum_order; simpl; intros Hle_2.
    generalize (le_lt_trans _ _ _ Hle_2 Hlt_2); intro Hlt_22.
    elim (lt_irrefl _ Hlt_22).
    
    generalize (Han _ HIn_1); intro Hin_1;
      apply is_node_exists in Hin_1;
        destruct Hin_1 as [tl1 [tr1 Heq]]; subst.
    generalize (H0 _ HIn); simpl;
      unfold sum_order; simpl; intro Hle.
    generalize (wrapper_wrapper_in_inb H _ HIn_1); intro Hinb.
    generalize (H1 _ _ Hinb); simpl; intro Hlt_1.
    apply (permutation_in _ _ _ _ H2) in HIn_1.
    simpl in HIn_1; destruct HIn_1 as [Heq | HIn_1].
    elim (not_node_l Heq).
    generalize (H3 _ HIn_1); simpl; unfold sum_order; simpl; intros Hle_1.
    generalize (le_lt_trans _ _ _ Hle_1 Hlt_1); intro Hlt_21.
    generalize (lt_le_trans _ _ _ Hlt_21 Hle); intro Hlt_22.
    elim (lt_irrefl _ Hlt_22).


    generalize (Han _ HIn_2); intro Hin_2;
      apply is_node_exists in Hin_2;
        destruct Hin_2 as [tl2 [tr2 Heq]]; subst.
    generalize (wrapper_wrapper_in_inb H _ HIn_2); intro Hinb.
    generalize (H1 _ _ Hinb); simpl; intro Hlt_2.
    apply (permutation_in _ _ _ _ H2) in HIn_2.
    simpl in HIn_2; destruct HIn_2 as [Heq | HIn_2].
    elim (not_node_r Heq).
    generalize (H3 _ HIn_2); simpl; unfold sum_order; simpl; intros Hle_2.
    generalize (le_lt_trans _ _ _ Hle_2 Hlt_2); intro Hlt_22.
    elim (lt_irrefl _ Hlt_22).
    apply
      (permutation_in _ _ _ _ (permutation_sym _ _ _ H2));
      simpl; left; reflexivity.
  Qed.


  Lemma wrapper_no_twin:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall t1 t2,
        In (t1/-\t2) w ->
        t1<>t2.
  Proof.
    intros.
    generalize (wrapper_wrapper_in_inb H _ H1);
      intros Hinb Heq; subst t2.
    elim (H0 _ _ _ Hinb (inleaf _ _) (inleaf _ _)).
  Qed.    


  Lemma wrapper_cover_distinct:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall t1 t2 c',
        permutation c (t1::t2::c') ->
        forall t1' t2',
          inb t1' t1 -> inb t2' t2 ->
          t1' <> t2'.
  Proof.
    ind_wr.
    intros.
    apply permutation_length in H0; discriminate.

    intro_dest_wp; subst.
    intros t Hw IH Hdl t3 t4 c' Hperm.

    intros t1' t2' Hinb_1' Hinb_2' Heq; subst.
    generalize (wrapper_cover_In_inb Hw); simpl; intros HIib.
    generalize (HIib _ (or_introl _ (eq_refl _))); intro Hinb.
    
    cut (In t3 c1/\In t4 c1).
    intros [HIn_3 HIn_4].
    apply (permutation_in _ _ _ _ Hperm_c1) in HIn_3.
    simpl in HIn_3; destruct HIn_3 as [Heq | [Heq | HIn_3]]; try subst t3.
    (* .t3 = t1 *)
    apply (permutation_in _ _ _ _ Hperm_c1) in HIn_4.
    simpl in HIn_4; destruct HIn_4 as [Heq | [Heq | HIn_4]]; try subst t4.
    (* ..t4 = t1 *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_inv in Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t2 = t1 *)
    intros; inject_subst.
    apply (Hdl t2 _ _ Hinb); apply inleaf.
    (* ...Dup t1 *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    cut (In t1 c).
    intro HIn.
    generalize (HIib _ (or_intror _ HIn)); intro Hinb_1.
    elim
      (IH Hdl (t1/-\t2) t1 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm') t1 t1
      (innodeL _ _ t1 t2 (inleaf _ t1)) (inleaf _ t1));
      reflexivity.
    apply permutation_sym in Hperm';
      apply (permutation_in _ _ _ _ Hperm');
        simpl; left; reflexivity.
    (* ..t4 = t2 *)
    elim (Hdl t2' t1 t2 Hinb Hinb_1' Hinb_2').
    (* .. t4 in c *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_inv in Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t4 = t2 *)
    intros; inject_subst.
    elim (Hdl t2' t1 t2 Hinb Hinb_1' Hinb_2').
    (* ...Dup t1 *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    elim
      (IH Hdl (t1/-\t2) t4 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeL _ _ t1 t2  Hinb_1') Hinb_2');
      reflexivity.

    (* .t3 = t2 *)
    apply (permutation_in _ _ _ _ Hperm_c1) in HIn_4.
    simpl in HIn_4; destruct HIn_4 as [Heq | [Heq | HIn_4]]; try subst t4.
    (* ..t4 = t1 *)
    elim (Hdl t2' t1 t2 Hinb Hinb_2' Hinb_1').
    (* ..t4 = t2 *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ (permutation_swap _ _ _ c) Hperm_c1);
      clear Hperm_c1; intro Hperm_c1.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_inv in Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t2 = t1 *)
    intros; inject_subst.
    apply (Hdl t1 _ _ Hinb); apply inleaf.
    (* ...Dup t1 *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    cut (In t2 c).
    intro HIn.
    generalize (HIib _ (or_intror _ HIn)); intro Hinb_2.
    elim
      (IH Hdl (t1/-\t2) t2 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm') t2 t2
      (innodeR _ _ t1 t2 (inleaf _ _)) (inleaf _ _));
      reflexivity.
    apply permutation_sym in Hperm';
      apply (permutation_in _ _ _ _ Hperm');
        simpl; left; reflexivity.
    (* .. t4 in c *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ (permutation_swap _ _ _ c) Hperm_c1);
      clear Hperm_c1; intro Hperm_c1.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_inv in Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t4 = t1 *)
    intros; inject_subst.
    elim (Hdl t2' t1 t2 Hinb Hinb_2' Hinb_1').
    (* ...Dup t1 *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    elim
      (IH Hdl (t1/-\t2) t4 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeR _ _ t1 t2  Hinb_1') Hinb_2');
      reflexivity.

    (* .t3 in c *)
    apply (permutation_in _ _ _ _ Hperm_c1) in HIn_4.
    simpl in HIn_4; destruct HIn_4 as [Heq | [Heq | HIn_4]]; try subst t4.
    (* ..t4 = t1 *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ (permutation_swap _ _ _ c') 
      (permutation_sym _ _ _ Hperm));
      clear Hperm; intro Hperm; apply permutation_sym in Hperm.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_inv in Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t3 = t2 *)
    intros; inject_subst.
    elim (Hdl t2' t1 t2 Hinb Hinb_2' Hinb_1').
    (* ...Dup t1 *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    elim
      (IH Hdl (t1/-\t2) t3 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeL _ _ t1 t2  Hinb_2') Hinb_1');
      reflexivity.
    (* ..t4 = t2 *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ (permutation_swap _ _ _ c) Hperm_c1);
      clear Hperm_c1; intro Hperm_c1.
    generalize (permutation_trans _ _ _ _ (permutation_swap _ _ _ c') 
      (permutation_sym _ _ _ Hperm));
      clear Hperm; intro Hperm; apply permutation_sym in Hperm.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_inv in Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t3 = t1 *)
    intros; injection Heq; intros; subst t3 l2; clear Heq.
    elim (Hdl t2' t1 t2 Hinb Hinb_1' Hinb_2').
    (* ...Dup t1 *)
    intros t' l1; intros; injection Heq; intros; subst t'; clear Heq.
    elim
      (IH Hdl (t1/-\t2) t3 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeR _ _ t1 t2  Hinb_2') Hinb_1');
      reflexivity.
    (* ..t4 in c *)
    apply permutation_sym in Hperm_c1.
    generalize (permutation_trans _ _ _ _ Hperm_c1 Hperm); intro Hperm'.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ...t3 = t1 *)
    intros; inject_subst.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    (* ....t4 = t2 *)
    intros; inject_subst.
    elim (Hdl t2' t1 t2 Hinb Hinb_1' Hinb_2').
    (* ....other *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    elim
      (IH Hdl (t1/-\t2) t4 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeL _ _ t1 t2  Hinb_1') Hinb_2');
      reflexivity.
    (* ...ooo *)
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    genc Hperm'; genc H.
    case l1; clear l1; simpl.
    intros; inject_subst.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l1 [l2 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l1; clear l1; simpl.
    intros; inject_subst.
    elim (Hdl t2' t4 t2 Hinb Hinb_2' Hinb_1').
    intros t' l1; intros; apply eq_sym in Heq; inject_subst.
    elim
      (IH Hdl (t4/-\t2) t3 (l1++l2) (permutation_skip _ (t4/-\t2) _ _ Hperm')
        t2' t2' (innodeL _ _ t4 t2  Hinb_2') Hinb_1');
      reflexivity.
    intros t' l1; intros; inject_subst.
    apply permutation_cons_ex in Hperm'.
    destruct Hperm' as [l3 [l4 [Heq Hperm']]].
    genc Hperm'; genc Heq.
    case l3; clear l3; simpl.
    intros; inject_subst.
    elim
      (IH Hdl (t1/-\t2) t4 (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeR _ _ t1 t2  Hinb_1') Hinb_2');
      reflexivity.
    intros t' l3; intros; inject_subst.
    genc Hperm'; genc H.
    case l3; clear l3; simpl.
    intros; inject_subst.
    elim
      (IH Hdl (t1/-\t2) t' (l1++l2) (permutation_skip _ (t1/-\t2) _ _ Hperm')
        t2' t2' (innodeR _ _ t1 t2  Hinb_2') Hinb_1');
      reflexivity.
    intros; inject_subst.
    cut (permutation (t1/-\t2::c) (t'::b::t1/-\t2::l++l4)).
    intro Hperm''.
    elim
      (IH Hdl t' b (t1/-\t2::l++l4) Hperm'' t2' t2' Hinb_1' Hinb_2');
      reflexivity.
    apply permutation_trans with (t1/-\t2::t'::b::l++l4); auto.
    apply permutation_trans with (t'::t1/-\t2::b::l++l4); auto.
    apply permutation_sym in Hperm.
    split; apply (permutation_in _ _ _ _ Hperm); simpl;
      [| right]; left; reflexivity.
  Qed.
    

  Lemma wrapper_cover_NoDup_aux:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall t1 t2 c',
        permutation c (t1::t2::c') ->
        t1 <> t2.
  Proof.
    intros.
    generalize (wrapper_cover_distinct H H0 H1).
    intros.
    apply H2; apply inleaf.
  Qed.

    
  Lemma wrapper_cover_NoDup:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      NoDup c.
  Proof.
    intros.
    generalize (wrapper_cover_NoDup_aux H H0).
    intros.
    apply (NoDup_neq H1).
  Qed.


  Lemma wrapper_in_t:
    forall c w t,
      wrapper c w t ->
      w <> nil ->
      In t w.
  Proof.
    ind_wr.
    intros t Hneq; elim Hneq; reflexivity.
    intros c1 w1 c2 w2; generalize c1 w1 c2; clear c1 w1 c2;
      case w2; clear w2.
    intros c1 w1 c2; dest_wp.
    apply permutation_sym in Hperm_w.
    apply permutation_one_inv in Hperm_w; subst.
    intros t Hw; apply wrapper_nil_inv in Hw.
    injection Hw; intros; subst; simpl; left; reflexivity.
    intros.
    cut (b::l<>nil).
    intro.
    apply H1 in H3; genc H3.
    apply (wrapper_prop_w_incl H).
    intro; discriminate.
  Qed.

  Lemma wrapper_cover_inb_not_in_wrapper:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall x, In x c ->
        forall y, inb y x -> ~In y w.
  Proof.
    ind_wr.
    simpl; tauto.
    intros.
    generalize c1 w1 c2 w2 H t H0 H1 H2 x H3 y H4 (wrapper_node H H0).
    clear c1 w1 c2 w2 H t H0 H1 H2 x H3 y H4.
    intro_dest_wp; subst.
    intros t Hw IH Hdl x HIn_c1 y Hinb Hw_1 HIn_w1.
    apply (permutation_in _ _ _ _  Hperm_w) in HIn_w1.
    simpl in HIn_w1; destruct HIn_w1 as [Heq | HIn_w2]; subst.
    apply (permutation_in _ _ _ _ Hperm_c1) in HIn_c1.
    simpl in HIn_c1.
    destruct HIn_c1 as [Heq | [Heq | HIn_c]]; try subst x.
    elim (not_inb_node_l Hinb).
    elim (not_inb_node_r Hinb).
    apply in_to_perm in HIn_c.
    destruct HIn_c as [c' Hperm].
    cut (permutation c1 (t1::x::t2::c')).
    intro Hperm'.
    cut (inb t1 x).
    intro Hinb'.
    apply
      (wrapper_cover_distinct Hw_1 Hdl Hperm'
        (inleaf _ _) Hinb'); reflexivity.
    apply inb_trans with (t1/-\t2);
      [apply innodeL; apply inleaf | assumption].
    apply permutation_trans with (t1::t2::c); auto.
    apply permutation_skip.
    apply permutation_trans with (t2::x::c'); auto.

    simpl in *.
    apply (permutation_in _ _ _ _ Hperm_c1) in HIn_c1.
    simpl in HIn_c1.
    destruct HIn_c1 as [Heq | [Heq | HIn_c]]; try subst x.
    apply (innodeL _ _ _ t2) in Hinb.
    genc HIn_w2; genc Hinb; genc y.
    apply (IH Hdl _ (or_introl _ (eq_refl _))).
    apply (innodeR _ _ t1 _) in Hinb.
    genc HIn_w2; genc Hinb; genc y.
    apply (IH Hdl _ (or_introl _ (eq_refl _))).
    genc HIn_w2; genc Hinb; genc y.
    apply (IH Hdl _ (or_intror _ HIn_c)).
  Qed.



  Lemma wrapper_cover_not_in_wrapper:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall x, In x c ->
        ~In x w.
  Proof.
    intros c w t Hw Hdl x HIn_c.
    apply (wrapper_cover_inb_not_in_wrapper Hw Hdl HIn_c (inleaf _ _)).
  Qed.

  Lemma wrapper_wrapper_not_in_cover:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      forall x, In x w ->
        ~In x c.
  Proof.
    intros c w t Hw Hdl x HIn_w HIn_c.
    apply (wrapper_cover_not_in_wrapper Hw Hdl _ HIn_c HIn_w).
  Qed.

   Lemma wrapper_all_NoDup:
    forall c w t,
      wrapper c w t ->
      distinct_leaves t ->
      NoDup (c++w).
   Proof.
     ind_wr.
     simpl; intros.
     apply NoDup_cons.
     simpl; tauto.
     apply NoDup_nil.
     intro_dest_wp; subst.
     intros t Hw IH Hdl.
     cut (permutation (c1++w1) (t1::t2::t1/-\t2::c++w2)).
     intro Hperm.
     apply (NoDup_perm (permutation_sym _ _ _ Hperm)).
     repeat apply NoDup_cons.
     simpl; intros [Heq | [Heq | HIn]].
     subst t2.
     generalize (wrapper_cover_In_inb Hw); intro HIib.
     simpl in HIib.
     elim
       (Hdl _ _ _
         (HIib _ (or_introl _ (eq_refl _))) (inleaf _ _) (inleaf _ _)).
     elim (not_node_l Heq).
     apply in_app_iff in HIn.
     destruct HIn as [HIn | HIn].
     apply in_to_perm in HIn.
     destruct HIn as [c' Hperm'].
     generalize (wrapper_cover_In_inb Hw); simpl; intro HIib.
     apply
       (wrapper_cover_distinct Hw Hdl 
         (permutation_skip _ (t1/-\t2) _ _ Hperm')
         (innodeL _ _ _ t2 (inleaf _ _)) (inleaf _ _));
       reflexivity.
     generalize (wrapper_cover_inb_not_in_wrapper Hw Hdl);
       simpl; intro Hini.
     elim (Hini _ (or_introl _ (eq_refl _)) _
       (innodeL _ _ _ t2 (inleaf _ _)) HIn).
     simpl; intros [Heq | HIn].
     elim (not_node_r Heq).
     apply in_app_iff in HIn.
     destruct HIn as [HIn | HIn].
     apply in_to_perm in HIn.
     destruct HIn as [c' Hperm'].
     generalize (wrapper_cover_In_inb Hw); simpl; intro HIib.
     apply
       (wrapper_cover_distinct Hw Hdl 
         (permutation_skip _ (t1/-\t2) _ _ Hperm')
         (innodeR _ _ t1 _ (inleaf _ _)) (inleaf _ _));
       reflexivity.
     generalize (wrapper_cover_inb_not_in_wrapper Hw Hdl);
       simpl; intro Hini.
     elim (Hini _ (or_introl _ (eq_refl _)) _
       (innodeR _ _ t1 _ (inleaf _ _)) HIn).
     intro HIn.
     apply in_app_iff in HIn.
     destruct HIn as [HIn | HIn].
     apply in_to_perm in HIn.
     destruct HIn as [c' Hperm'].
     generalize (wrapper_cover_In_inb Hw); simpl; intro HIib.
     apply
       (wrapper_cover_distinct Hw Hdl 
         (permutation_skip _ (t1/-\t2) _ _ Hperm')
         (inleaf _ _) (inleaf _ _));
       reflexivity.
     generalize (wrapper_cover_not_in_wrapper Hw Hdl);
       simpl; intro Hni.
     elim (Hni _ (or_introl _ (eq_refl _)) HIn).
     apply IH in Hdl.
     simpl in Hdl.
     apply NoDup_inv in Hdl; assumption.
     apply permutation_trans with (c1++t1/-\t2::w2); auto.
     apply permutation_trans with ((t1::t2::c)++(t1/-\t2::w2)); auto.
     simpl; repeat apply permutation_skip.
     rewrite cons_to_app.
     rewrite app_comm_cons.
     rewrite app_assoc.
     apply permutation_app_comp;
       [rewrite cons_to_app; apply permutation_app_swap
         | apply permutation_refl].
   Qed.


   Lemma wrapper_wrapper_NoDup:
     forall c w t,
       wrapper c w t ->
       distinct_leaves t ->
       NoDup w.
   Proof.
     intros c w t Hw Hdl;
       apply (NoDup_app_inv_r _ _ (wrapper_all_NoDup Hw Hdl)).
   Qed.  


   Lemma wrapper_t_in_cover_init:
     forall c w t,
       wrapper c w t ->
       distinct_leaves t ->
       In t c ->
       c = t::nil.
   Proof.
     ind_wr.
     reflexivity.
     intro_dest_wp; subst; simpl;
       intros t Hw IH Hdl HIn_c1.
     apply (permutation_in _ _ _ _ Hperm_c1) in HIn_c1;
       simpl in HIn_c1; destruct HIn_c1 as [Heq | [Heq | HIn_c]];
         try subst t1; try subst t2.
     generalize (wrapper_cover_In_inb Hw); simpl; intro Hiib.
     generalize
       (Hiib _ (or_introl _(eq_refl _))).
     intro Hinb.
     elim (not_inb_node_l Hinb).
     generalize (wrapper_cover_In_inb Hw); simpl; intro Hiib.
     generalize
       (Hiib _ (or_introl _(eq_refl _))).
     intro Hinb.
     elim (not_inb_node_r Hinb).
     generalize (wrapper_cover_distinct Hw); simpl; intro Hcd.
     apply in_to_perm in HIn_c.
     destruct HIn_c as [c' Hperm].
     cut (permutation (t1/-\t2::c) (t1/-\t2::t::c')).
     intro Hperm'.
     generalize (wrapper_cover_In_inb Hw _ (or_introl _ (eq_refl _)));
       intro Hinb'.
     elim (Hcd Hdl _ _ _ Hperm' _ _ (inleaf _ _) Hinb'); reflexivity.
     apply permutation_skip; assumption.
   Qed.
     
   Lemma wrapper_cover_parent_in_wrapper:
     forall c w (t: btree A),
       wrapper c w t ->
       distinct_leaves t ->
       forall t',
         In t' c ->
         t' = t\/
         (exists tl, exists tr,
           In (tl/-\tr) w/\(t'=tl\/t'=tr)).
   Proof.
     ind_wr.
     simpl; intros t Hdl t' [Heq | F];
       [left; subst; reflexivity | contradiction].
     intro_dest_wp; subst; intros t Hw IH Hdl t' HIn_c1.
     right.
     apply (permutation_in _ _ _ _ Hperm_c1) in HIn_c1;
       simpl in HIn_c1; destruct HIn_c1 as [Heq | [Heq | HIn_c]];
         try subst t'.
     exists t1, t2; split.
     apply
       (permutation_in _ _ _ _
         (permutation_sym _ _ _ Hperm_w));
       simpl; left; reflexivity.
     left; reflexivity.
     exists t1, t2; split.
     apply
       (permutation_in _ _ _ _
         (permutation_sym _ _ _ Hperm_w));
       simpl; left; reflexivity.
     right; reflexivity.
     simpl in IH.
     destruct (IH Hdl _ (or_intror _ HIn_c))
       as [Heq | [tl [tr [HIn_w2 [Heq_l | Heq_r]]]]];
         subst t'.
     generalize (wrapper_t_in_cover_init Hw Hdl (or_intror _ HIn_c));
       intros; inject_subst.
     simpl in HIn_c; contradiction.
     exists tl, tr; split;
       [apply
         (permutation_in _ _ _ _ 
           (permutation_sym _ _ _ Hperm_w));
         simpl; right; assumption | left; reflexivity].
     exists tl, tr; split;
       [apply
         (permutation_in _ _ _ _ 
           (permutation_sym _ _ _ Hperm_w));
         simpl; right; assumption | right; reflexivity].
   Qed.



   Lemma wrapper_inv:
     forall c w (t: btree A),
       wrapper c w t ->
       distinct_leaves t ->
       forall t1 t2 c' w',
         permutation c (t1::t2::c') ->
         permutation w (t1/-\t2::w') ->
         wrapper (t1/-\t2::c') w' t.
   Proof.
     ind_wr.
     
     (* base case *)
     intros.
     apply permutation_length in H0; discriminate.

     (* induction *)
     intros c1 w1 c2 w2 Hwp t Hw.
     generalize (wrapper_node Hwp Hw); intro Hw_1.
     generalize c1 w1 c2 w2 Hwp t Hw Hw_1.
     clear c1 w1 c2 w2 Hwp t Hw Hw_1.

     intro_dest_wp; subst.
     intros t Hw Hw_1 IH Hdl t3 t4 c' w' Hperm_c' Hperm_w'.

     generalize
       (permutation_trans _ _ _ _
         (permutation_sym _ _ _ Hperm_c1) Hperm_c');
       intro Hperm.

     apply permutation_cons_ex in Hperm;
       destruct Hperm as [l1 [l2 [Heq Hperm]]];
         genc Hperm; genc Heq.
     case l1; clear l1; simpl.
     (* .t3 = t1 *)
     intros; inject_subst.
     apply permutation_cons_ex in Hperm;
       destruct Hperm as [l1 [l2 [Heq Hperm]]];
         genc Hperm; genc Heq.
     case l1; clear l1; simpl.
     (* ..t4 = t2 *)
     intros; inject_subst.
     apply permutation_sym in Hperm_c1;
       apply (permutation_trans _ _ _ _ Hperm_c1) in Hperm_c';
         repeat apply permutation_inv in Hperm_c'.
     apply permutation_sym in Hperm_w;
       apply (permutation_trans _ _ _ _ Hperm_w) in Hperm_w';
         apply permutation_inv in Hperm_w'.
     apply
       (wrapper_perm Hw
         (permutation_skip _ _ _ _ Hperm_c') Hperm_w').
     (* ..other *)
     intros; apply eq_sym in Heq; inject_subst.
     cut (In (t1/-\t4) w1).
     intro HIn_w1.

     rewrite <-
       (distinct_distinct_r Hdl
         (wrapper_cover_In_inb Hw _ (or_introl _ (eq_refl _)))
         (wrapper_wrapper_in_inb Hw_1 _ HIn_w1)) in *.
     cut (permutation c1 (t2::t2::t1::l++l2)).
     intro Hperm'.
     elim (wrapper_cover_NoDup_aux Hw_1 Hdl Hperm'); reflexivity.
     apply (permutation_trans _ _ _ _ Hperm_c1).
     apply (permutation_trans _ _ _ _ (permutation_swap _ _ _ _)).
     apply permutation_skip.
     apply (permutation_trans _ _ _ _ (permutation_skip _ _ _ _ Hperm)).
     apply permutation_swap.
     apply (permutation_in _ _ _ _ (permutation_sym _ _ _ Hperm_w'));
       simpl; left; reflexivity.

     (* . *)
     intros; apply eq_sym in Heq; inject_subst.
     genc Hperm; genc H.
     case l; clear l; simpl.
     (* ..t4 = t1 *)
     intros; apply eq_sym in H; inject_subst.
     cut (In (t1/-\t2) w1/\In (t3/-\t1) w1).
     intros [HIn HIn'].
     elim
       (distinct_not_rev_l Hdl
         (wrapper_wrapper_in_inb Hw_1 _ HIn)
         (wrapper_wrapper_in_inb Hw_1 _ HIn')).
     split;
       [eapply
         (permutation_in _ _ _ _
           (permutation_sym _ _ _ Hperm_w))
         | apply
           (permutation_in _ _ _ _
             (permutation_sym _ _ _ Hperm_w'))];
       simpl; left; reflexivity.
     (* .. *)
     intros; inject_subst.
     apply permutation_cons_ex in Hperm.
     destruct Hperm as [l3 [l4 [Heq Hperm]]].
     genc Hperm; genc Heq.
     case l3; clear l3; simpl.
     (* ...t3 = t2 *)
     intros; inject_subst.
     cut (In (t1/-\t2) w1/\In (t2/-\t4) w1).
     intros [HIn HIn'].
     elim
       (distinct_not_rev_r Hdl
         (wrapper_wrapper_in_inb Hw_1 _ HIn)
         (wrapper_wrapper_in_inb Hw_1 _ HIn')).
     split;
       [apply
         (permutation_in _ _ _ _
           (permutation_sym _ _ _ Hperm_w))
         | apply
           (permutation_in _ _ _ _
             (permutation_sym _ _ _ Hperm_w'))];
       simpl; left; reflexivity.
     (* ... *)
     intros; apply eq_sym in Heq; inject_subst.
     genc Hperm; genc H.
     case l0; clear l0; simpl.
     (* ....t4 = t2 *)
     intros; inject_subst.
     cut (In (t3/-\t4) w1).
     intro HIn_w1.
     rewrite <-
       (distinct_distinct_l Hdl
         (wrapper_cover_In_inb Hw _ (or_introl _ (eq_refl _)))
         (wrapper_wrapper_in_inb Hw_1 _ HIn_w1)) in *.
     cut (permutation c1 (t1::t1::t4::l++l2)).
     intro Hperm'.
     elim (wrapper_cover_NoDup_aux Hw_1 Hdl Hperm'); reflexivity.
     apply (permutation_trans _ _ _ _ Hperm_c1).
     apply permutation_skip.
     apply (permutation_trans _ _ _ _ (permutation_skip _ _ _ _ Hperm)).
     apply permutation_swap.
     apply (permutation_in _ _ _ _ (permutation_sym _ _ _ Hperm_w'));
       simpl; left ;reflexivity.
     (* .... *)
     intros; inject_subst.

     destruct
       (permutation_cons_ex _ _ _ _
         (permutation_trans _ _ _ _
           (permutation_sym _ _ _ Hperm_w') Hperm_w))
       as [k1 [k2 [Heq Hperm']]].
     genc Hperm'; genc Heq.
     case k1; clear k1; simpl.
     (* .....t1/-\t2 = t3/-\t4 *)
     intros; apply eq_sym in Heq; inject_subst.
     cut (permutation c1 (t1::t1::t2::t2::l0++l4)).
     intro Hperm''.
     elim (wrapper_cover_NoDup_aux Hw_1 Hdl Hperm''); reflexivity.
     apply (permutation_trans _ _ _ _ Hperm_c1).
     apply permutation_skip.
     apply (permutation_trans _ _ _ _ (permutation_skip _ _ _ _ Hperm)).
     apply permutation_swap.
     (* ..... *)
     intros t' k1; intros; inject_subst.
     eapply wrapper_node.
     unfold wrapper_prop.
     exists t1, t2, (t3/-\t4::l0++l4); repeat split.
     apply permutation_trans with (t3/-\t4::t1::t2::l0++l4).
     apply permutation_skip.
     apply (permutation_trans _ _ _ _ (permutation_app_swap _ _ _)).
     simpl; apply permutation_skip.
     apply (permutation_trans _ _ _ _ (permutation_app_swap _ _ _)).
     rewrite <- H0.
     rewrite app_comm_cons; rewrite (cons_to_app t2 l4);
       rewrite app_assoc;
         apply permutation_app_comp.
     rewrite (cons_to_app t2 l0);
       apply permutation_app_swap.
     apply permutation_refl.
     apply (permutation_trans _ _ _ _ (permutation_swap _ _ _ _)).
     apply permutation_skip; apply permutation_swap.
     eexact Hperm'.
     
     generalize
       (permutation_trans _ _ _ _
         (permutation_sym _ _ _ Hperm_w) Hperm_w');
       intro Hperm_w''.
     
     eapply wrapper_perm.
     apply (IH Hdl).
     apply
       (permutation_trans _ _ _ _
         (permutation_skip _ _ _ _ Hperm)).
     apply (permutation_trans _ _ _ _ (permutation_swap _ _ _ _)).
     apply permutation_skip; apply permutation_swap.
     
     apply permutation_trans with (t3/-\t4::k1++k2).
     rewrite app_comm_cons.
     rewrite (cons_to_app (t3/-\t4) k2).
     rewrite app_assoc.
     apply permutation_app_comp; auto.
     apply (permutation_trans _ _ _ _ (permutation_app_swap _ _ _)); simpl; auto.
     apply permutation_refl.
     apply permutation_swap.
     apply permutation_refl.
   Qed.
End Wrapper.




