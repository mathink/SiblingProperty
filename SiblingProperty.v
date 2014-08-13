(****************************************************************

   Huffmanitive.v

 ****************************************************************)

(* Standard Libraries *)
Require Import List.
Require Import Relations.

(* By L.Thery *)
Require Import Huffman.BTree.
Require Import Huffman.WeightTree.
Require Import Huffman.Cover.
Require Import Huffman.Build.


(* append by me *)
Require Import SiblProp.Tacs.
Require Import SiblProp.BTree_appendix.
Require Import SiblProp.Wrapper.

Set Implicit Arguments.


Section SiblProp.
  Variables (A: Set)(f: A -> nat).
  Hypothesis eq_A_dec: forall a b: A, {a=b}+{a<>b}.
  Notation "[ X ]" := (leaf X).
  Infix "/-\" := node (at level 60, no associativity).


  Definition gsp t c w :=
    wrapper c w t/\ordered_siblist f w.
  
  Definition sibling_property (t: btree A) :=
    exists w,
      gsp t (leaves t) w.
End SiblProp.


Section HuffmanTree.
  Variables (A: Set)(f: A -> nat).
  Hypothesis eq_A_dec: forall a b: A, {a=b}+{a<>b}.
  Notation "[ X ]" := (leaf X).
  Infix "/-\" := node (at level 60, no associativity).

  (* Huffmanized Step Property *)
  Definition wone_step (ml1 pl1 ml2 pl2: list (btree A)) :=
    exists t1, exists t2, exists ml,
      ordered (sum_order f) (t1::t2::ml)/\
      permutation ml1 (t1::t2::ml)/\
      permutation ml2 (node t1 t2::ml)/\
      pl1 = (t1/-\t2::pl2).

  Ltac dest_hp :=
    let t1 := fresh "ht1" in
      let t2 := fresh "ht2" in
        let l := fresh "hml" in
      intros [ht1 [ht2 [html
        [Hord [Hperm1 [Hperm2 Heq_pl]]]]]].

  Ltac intro_dest_hp :=
    intros ml1 pl1 ml2 pl2; dest_hp.


  (* Some Properties of wone_step *)
  Section HuffProp.
    Variables ml1 pl1 ml2 pl2: list (btree A).
    Hypothesis hp: wone_step ml1 pl1 ml2 pl2.

    Ltac hp_dest := genc hp; dest_hp.
      

    Lemma wone_step_pl_all_well_sibl:
      all_well_sibl f pl2 -> all_well_sibl f pl1.
    Proof.
      hp_dest; subst; unfold all_well_sibl.
      simpl; intros IH x [Heq | HIn]; subst.
      inversion Hord; subst.
      unfold sum_order in H1.
      simpl; unfold sum_order; assumption.
      apply IH; assumption.
    Qed.

    Lemma wone_step_pl_all_node:
      all_node pl2 -> all_node pl1.
    Proof.
      hp_dest; subst.
      unfold all_node; simpl; intros H x [Heq | HIn];
        subst.
      simpl; tauto.
      apply H; assumption.
    Qed.


    Definition ml_pl_wrapper (ml pl: list (btree A)) :=
      forall tl tr,
        In (tl/-\tr) pl ->
        ((In tl ml/\In tr ml)\/In tl pl\/In tr pl).

    Lemma wone_step_ml_pl_wrapper:
      ml_pl_wrapper ml2 pl2 -> ml_pl_wrapper ml1 pl1.
    Proof.
      hp_dest; subst; unfold ml_pl_wrapper; simpl.
      intros Hgpw tl tr [Heq | HIn];      
        [inject_subst; left; split;
          apply permutation_sym in Hperm1;
            apply (permutation_in _ _ _ _ Hperm1); simpl;
              [| right]; left; reflexivity |].
      destruct (Hgpw _ _ HIn)
        as [[HIn_l HIn_r] | [HIn_l | HIn_r]].
      apply (permutation_in _ _ _ _ Hperm2) in HIn_l.
      simpl in HIn_l; destruct HIn_l as [Heq_l | HIn_l]; subst.
      right; left; left; reflexivity.
      apply (permutation_in _ _ _ _ Hperm2) in HIn_r.
      simpl in HIn_r; destruct HIn_r as [Heq_r | HIn_r]; subst.
      right; right; left; reflexivity.
      left; split; apply permutation_sym in Hperm1;
        apply (permutation_in _ _ _ _ Hperm1); simpl;
          right; right; assumption.
      right; left; right; assumption.
      right; right; right; assumption.
    Qed.


  End HuffProp.


  (*******)
  Lemma wone_step_one_step:
    forall ml1 pl1 ml2 pl2,
      wone_step ml1 pl1 ml2 pl2 ->
      one_step f ml1 ml2.
  Proof.
    unfold wone_step, one_step.
    intro_dest_hp.
    exists html, ht1, ht2; repeat split; try assumption.
  Qed.
  (*******)


  Inductive wbuild: list (btree A) -> list (btree A) -> btree A -> Prop :=
  | wbuild_one:
    forall t, wbuild (t::nil) nil t
  | wbuild_step:
    forall ml1 pl1 ml2 pl2,
      wone_step ml1 pl1 ml2 pl2 ->
      forall t,
        wbuild ml2 pl2 t -> wbuild ml1 pl1 t.



  (* Some Properties of Wbuild *)
  Section Wbuild.
    Variables (t: btree A)(ml pl: list (btree A)).
    Hypothesis Hwb: wbuild ml pl t.

    Ltac ind_huff := elim Hwb; clear Hwb ml pl t.

    Lemma wbuild_wrapper:
      wrapper ml pl t.
    Proof.
      ind_huff.
      apply wrapper_one.
      intros.
      genc H; dest_hp; subst.
      eapply wrapper_node.
      unfold wrapper_prop.
      exists ht1, ht2, html; repeat split.
      assumption.
      apply permutation_refl.
      eapply wrapper_perm; try eassumption.
      apply permutation_refl.
    Qed.

        
    
    Lemma wbuild_pl_all_well_sibl:
      all_well_sibl f pl.
    Proof.
      ind_huff.
      unfold all_well_sibl.
      simpl; intros; contradiction.
      intros.
      apply (wone_step_pl_all_well_sibl H H1).
    Qed.


    Lemma wbuild_pl_all_node:
      all_node pl.
    Proof.
      unfold all_node.
      ind_huff.
      simpl; intros; contradiction.
      intros.
      apply (wone_step_pl_all_node H H1 _ H2).
    Qed.


    Lemma wbuild_ml_pl_wrapper:
      ml_pl_wrapper ml pl.
    Proof.
      ind_huff; simpl.
      unfold ml_pl_wrapper; intros; contradiction.
      intros; eapply wone_step_ml_pl_wrapper; eassumption.
    Qed.
  End Wbuild.


  Lemma wbuild_pl_os:
    forall ml pl t,
      wbuild ml pl t -> ordered_siblist f pl.
  Proof.
    intros ml pl t Hwb; elim Hwb; clear Hwb ml pl t.
    intro; apply os_nil.
    intro_dest_hp; subst; intros t Hwb Hos.
    apply os_cons.
    assumption.
    simpl; tauto.
    inversion Hord; subst.
    simpl; unfold sum_order.
    unfold sum_order in H1; assumption.
    intros t' HIn.
    generalize (wbuild_pl_all_node Hwb).
    intro Han; generalize (Han _ HIn).
    intro Hin; apply is_node_exists in Hin;
      destruct Hin as [tl [tr Heq]]; subst.
    apply wbuild_wrapper in Hwb.
    destruct (wrapper_child_reached_cover f Hwb _ _ HIn) as
      [[tcl [HInl Hlel]] [tcr [HInr Hler]]].
    simpl.
    apply (permutation_in _ _ _ _ Hperm2) in HInl.
    simpl in HInl; destruct HInl as [Heq | HInl]; subst.
    unfold sum_order in Hlel; simpl in Hlel.
    unfold sum_order; eauto with arith.
    inversion Hord; subst a b l.
    cut (forall a b c : btree A, sum_order f a b -> sum_order f b c -> sum_order f a c).
    intro sum_order_trans'.
    generalize (ordered_trans _ (sum_order f) sum_order_trans' _ tcl _ H3 HInl).
    intro; apply sum_order_trans with tcl; assumption.
    apply sum_order_trans.
  Qed.

  Lemma wbuild_perm:
    forall ml pl t,
      wbuild ml pl t ->
      forall ml',
        permutation ml ml' ->
        wbuild ml' pl t.
  Proof.
    intros ml pl t Hwb; elim Hwb; clear Hwb ml pl t.
    intros t ml' Hperm.
    apply permutation_one_inv in Hperm; subst.
    apply wbuild_one.
    intro_dest_hp; subst.
    intros t Hwb IH ml' Hperm.
    genc Hwb; apply wbuild_step.
    exists ht1, ht2, html; repeat split; try assumption.
    apply permutation_sym in Hperm.
    apply (permutation_trans _ _ _ _ Hperm); assumption.
  Qed.



  (********)
  Lemma wbuild_build:
    forall ml pl t,
      wbuild ml pl t ->
      build f ml t.
  Proof.
    intros ml pl t Hwb; elim Hwb; clear ml pl t Hwb.
    apply build_one.
    intros ml1 pl1 ml2 pl2 Hhp t Hwb IH.
    apply wone_step_one_step in Hhp.
    apply (build_step _ f _ _ _ Hhp IH).
  Qed.
  (********)

  Lemma build_wbuild:
    forall ml t,
      build f ml t ->
      exists pl,
        wbuild ml pl t.
  Proof.
    intros ml t Hbuild; elim Hbuild; clear Hbuild ml t.
    intro t; exists nil; apply wbuild_one.
    intros t ml1 ml2 [ml [t1 [t2 [Hord [Hperm1 Hperm2]]]]].
    intros Hbuild [pl2 Hwb].
    exists (t1/-\t2::pl2).
    eapply wbuild_step.
    exists t1, t2, ml; repeat split; try eassumption.
    assumption.
  Qed.


  Theorem wbuild_gsiblprop:
    forall ml pl t,
      wbuild ml pl t ->
      gsp f t ml pl.
  Proof.
    intros ml pl t Hwb.
    split;
      [genc Hwb; apply wbuild_wrapper
        | genc Hwb; apply wbuild_pl_os].
  Qed.

  Theorem build_gsiblprop:
    forall ml t,
      build f ml t ->
      exists pl,
        gsp f t ml pl.
  Proof.
    intros ml t Hb.
    destruct (build_wbuild Hb) as [pl Hwb].
    exists pl; split;
      [genc Hwb; apply wbuild_wrapper
        | genc Hwb; apply wbuild_pl_os].
  Qed.


  Definition huffman_tree' (t: btree A) :=
    build f (leaves t) t.

  Definition huffman_tree (t: btree A) :=
    exists w,
      wbuild (leaves t) w t.

  Lemma build_equiv_huffman_tree:
    forall t,
      build f (leaves t) t <-> huffman_tree t.
  Proof.
    intro t; split.
    apply build_wbuild.
    intros [pl Hwb].
    apply (wbuild_build Hwb).
  Qed.



  Theorem huffman_tree_siblprop:
    forall t, huffman_tree t -> sibling_property f t.
  Proof.
    intros t [w Hwb];
      exists w; genc Hwb; apply wbuild_gsiblprop.
  Qed.


  Theorem huffman_tree'_siblprop:
    forall t, huffman_tree' t -> sibling_property f t.
  Proof.
    intros t Hb.
    destruct (build_wbuild Hb) as [w Hwb].
    exists w; genc Hwb; apply wbuild_gsiblprop.
  Qed.


  Theorem gsiblprop_build:
    forall ml pl t,
      distinct_leaves t ->
      strict_parent f t ->
      gsp f t ml pl ->
      build f ml t.
  Proof.
    intros ml pl t Hdl Hsp [Hw Hos].
    generalize ml t Hdl Hsp Hw.
    clear ml t Hdl Hsp Hw.
    elim Hos; clear Hos pl.

    intros.
    apply wrapper_nil_inv in Hw; subst; apply build_one.

    intros ph pl Hos IH Hin Hws Hnl ml t Hdl Hsp Hw.
    apply is_node_exists in Hin.
    destruct Hin as [tl [tr Heq]]; subst.
    generalize
      (wrapper_min_child_in_cover Hw
        (aws_cons Hws (os_all_well_sibl Hos))
        Hsp (permutation_refl _ _) Hnl);
      simpl; intros [HIn_l HIn_r].
    apply in_to_perm in HIn_l;
      destruct HIn_l as [mll Hperm_l].
    apply in_to_perm in HIn_r;
      destruct HIn_r as [mlr Hperm_r].
    generalize
      (perm_2_1 (wrapper_no_twin Hw Hdl (or_introl _ (eq_refl _))) Hperm_l Hperm_r);
      intros [ml' Hperm].
    generalize
      (wrapper_inv Hw Hdl Hperm
        (permutation_refl _ _));
      intro Hw'.
    generalize (IH _ _ Hdl Hsp Hw'); intro Hb.
    eapply build_step in Hb.
    apply permutation_sym in Hperm.
    apply (build_permutation _ _ _ _ _ Hb Hperm).
    destruct (ordered_perm_ex (sum_order f) (sum_order_dec f) ml') as [ml'' [Hperm' Hord']].
    exists ml'', tl, tr; repeat split.
    apply ordered_cons.
    simpl in Hws; assumption.
    apply ordered_in_ordered.
    assumption.
    intros y HIn.
    apply (permutation_in _ _ _ _ (permutation_sym _ _ _ Hperm')) in HIn.
    generalize (wrapper_cover_parent_in_wrapper Hw' Hdl _ (or_intror _ HIn)).
    intros [Heq | [tl' [tr' [HIn' [Heqy | Heqy]]]]]; subst.
    apply inb_sum_order.
    apply inb_trans with (tl/-\tr).
    apply innodeR; apply inleaf.
    apply (wrapper_cover_In_inb Hw'); simpl; left; reflexivity.
    generalize (Hnl _ HIn'); simpl; tauto.
    generalize (Hnl _ HIn'); simpl; intro Hord.
    apply sum_order_trans with tl'.
    assumption.
    apply (os_all_well_sibl Hos) in HIn'; simpl in HIn'; assumption.
    repeat apply permutation_skip; assumption.
    apply permutation_skip; assumption.
  Qed.


  Theorem gsiblprop_wbuild:
    forall ml pl t,
      distinct_leaves t ->
      strict_parent f t ->
      gsp f t ml pl ->
      wbuild ml pl t.
  Proof.
    intros ml pl t Hdl Hsp [Hw Hos].

    (*****)
    generalize ml t Hdl Hsp Hw.
    clear ml t Hdl Hsp Hw.
    elim Hos; clear Hos pl.

    intros.
    apply wrapper_nil_inv in Hw; subst; apply wbuild_one.

    intros ph pl Hos IH Hin Hws Hnl ml t Hdl Hsp Hw.
    apply is_node_exists in Hin.
    destruct Hin as [tl [tr Heq]]; subst.
    generalize
      (wrapper_min_child_in_cover Hw
        (aws_cons Hws (os_all_well_sibl Hos))
        Hsp (permutation_refl _ _) Hnl);
      simpl; intros [HIn_l HIn_r].
    apply in_to_perm in HIn_l;
      destruct HIn_l as [mll Hperm_l].
    apply in_to_perm in HIn_r;
      destruct HIn_r as [mlr Hperm_r].
    generalize
      (perm_2_1 (wrapper_no_twin Hw Hdl (or_introl _ (eq_refl _))) Hperm_l Hperm_r);
      intros [ml' Hperm].

    inversion Hw.
    unfold wrapper_prop in H; subst.

    generalize
      (wrapper_inv Hw Hdl Hperm
        (permutation_refl _ _));
      intro Hw'.
    generalize (IH _ _ Hdl Hsp Hw');
      intros Hwb.
    eapply wbuild_step in Hwb.
    apply permutation_sym in Hperm.
    apply (wbuild_perm Hwb Hperm).
    destruct (ordered_perm_ex (sum_order f) (sum_order_dec f) ml') as [ml'' [Hperm' Hord']].
    exists tl, tr, ml''; repeat split.
    apply ordered_cons.
    simpl in Hws; assumption.
    apply ordered_in_ordered.
    assumption.
    intros y HIn.
    apply (permutation_in _ _ _ _ (permutation_sym _ _ _ Hperm')) in HIn.
    generalize (wrapper_cover_parent_in_wrapper Hw' Hdl _ (or_intror _ HIn)).
    intros [Heq | [tl' [tr' [HIn' [Heqy | Heqy]]]]]; subst.
    apply inb_sum_order.
    apply inb_trans with (tl/-\tr).
    apply innodeR; apply inleaf.
    apply (wrapper_cover_In_inb Hw'); simpl; left; reflexivity.
    generalize (Hnl _ HIn'); simpl; tauto.
    generalize (Hnl _ HIn'); simpl; intro Hord.
    apply sum_order_trans with tl'.
    assumption.
    apply (os_all_well_sibl Hos) in HIn'; simpl in HIn'; assumption.
    repeat apply permutation_skip; assumption.
    apply permutation_skip; assumption.
  Qed.    


  Theorem siblprop_huffman_tree:
    forall t, 
      distinct_leaves t ->
      strict_parent f t ->
      sibling_property f t ->
      huffman_tree t.
  Proof.
    intros t Hdl Hsp [w Hgs].
    exists w;
      apply (gsiblprop_wbuild Hdl Hsp Hgs).
  Qed.

  Theorem siblprop_huffman_tree':
    forall t, 
      distinct_leaves t ->
      strict_parent f t ->
      sibling_property f t ->
      huffman_tree' t.
  Proof.
    intros t Hdl Hsp [w Hgs].
    apply (gsiblprop_build Hdl Hsp Hgs).
  Qed.


  Theorem build_equiv_gsiblprop:
    forall c t,
      distinct_leaves t ->
      strict_parent f t ->
      (build f c t <-> exists w, gsp f t c w).
  Proof.
    intros c t Hdl Hsp; split;
      [apply build_gsiblprop |
        intros [w Hgsp]; genc Hgsp;
          apply (gsiblprop_build Hdl Hsp)].
  Qed.


  Theorem wbuild_equiv_gsiblprop:
    forall c w t,
      distinct_leaves t ->
      strict_parent f t ->
      (wbuild c w t <-> gsp f t c w).
  Proof.
    intros c w t Hdl Hsp; split;
      [apply wbuild_gsiblprop |
        apply (gsiblprop_wbuild Hdl Hsp)].
  Qed.


  (** t is Huffman Treee <-> t satisfies SiblingProperty *)
  Theorem huffman_tree_equiv_sibling_property:
    forall t,
      distinct_leaves t ->
      strict_parent f t ->
      (huffman_tree t <-> sibling_property f t).
  Proof.
    intros t Hdl Hsp; split;
      [apply huffman_tree_siblprop
        | apply (siblprop_huffman_tree Hdl Hsp)].
  Qed.


  Theorem huffman_tree'_equiv_sibling_property:
    forall t,
      distinct_leaves t ->
      strict_parent f t ->
      (huffman_tree' t <-> sibling_property f t).
  Proof.
    intro t; apply build_equiv_gsiblprop.
  Qed.
End HuffmanTree.
