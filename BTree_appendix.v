(****************************************************************

   BTree_appendix.v

 ****************************************************************)

(* Standard Libraries *)
Require Import List.
Require Import Relations.


(* By L.Thery *)
Require Import Huffman.Permutation.
Require Import Huffman.BTree.
Require Import Huffman.WeightTree.

(* *)
Require Import SiblProp.Tacs.

Set Implicit Arguments.

Section BTree_appendix.
  Variables (A: Set)(f: A -> nat).
  Hypothesis eq_A_dec: forall a b: A, {a=b}+{a<>b}.
  Notation "[ X ]" := (leaf X).
  Infix "/-\" := node (at level 60, no associativity).
  Implicit Type t: btree A.
  
  Lemma nol_eq:
    forall t1 t2: btree A, t1 = t2 -> number_of_nodes t1 = number_of_nodes t2.
  Proof.
    intros; subst; reflexivity.
  Qed.
  
  Definition leaves (t: btree A) :=
    map (fun x : A => leaf x) (all_leaves t).

  Inductive child: btree A -> btree A -> Prop :=
  | childL: forall tl tr, child tl (tl/-\tr)
  | childR: forall tl tr, child tr (tl/-\tr).


  Inductive subtree: btree A -> btree A -> Prop :=
  | subtree_nodeL: forall tl tr, subtree tl (tl/-\tr)
  | subtree_nodeR: forall tl tr, subtree tr (tl/-\tr)
  | subtree_trans:
    forall t1 t2 t3, subtree t2 t1 -> subtree t3 t2 -> subtree t3 t1.

  Lemma subtree_trans_left:
    forall t tl tr, subtree (tl/-\tr) t -> subtree tl t.
  Proof.
    intros t tl tr Hsbt; inversion Hsbt; subst.
    apply subtree_trans with (tl/-\tr); apply subtree_nodeL.
    apply subtree_trans with (tl/-\tr); [apply subtree_nodeR | apply subtree_nodeL].
    apply subtree_trans with (t2);
      [assumption | apply subtree_trans with (tl/-\tr); [assumption | apply subtree_nodeL]].
  Qed.

  Lemma subtree_trans_right:
    forall t tl tr, subtree (tl/-\tr) t -> subtree tr t.
  Proof.
    intros t tl tr Hsbt; inversion Hsbt; subst.
    apply subtree_trans with (tl/-\tr); [apply subtree_nodeL | apply subtree_nodeR].
    apply subtree_trans with (tl/-\tr); apply subtree_nodeR.
    apply subtree_trans with (t2);
      [assumption | apply subtree_trans with (tl/-\tr); [assumption | apply subtree_nodeR]].
  Qed.

  Lemma subtree_node_aux:
    forall t t', subtree t' t ->
      forall tl tr, 
        t = (tl/-\tr) ->
        t'=tl\/t'=tr\/subtree t' tl\/subtree t' tr.
  Proof.
    intros t t' Hsbt; elim Hsbt; clear Hsbt t t'.
    intros.
    injection H; intros; subst.
    left; reflexivity.
    intros.
    injection H; intros; subst.
    right; left; reflexivity.
    intros; subst.
    inversion H1; subst.
    destruct (H0 tl tr (eq_refl _)) as [Heq | [Heq | [Hsbt | Hsbt]]]; subst.
    right; right; left; apply subtree_nodeL.
    right; right; right; apply subtree_nodeL.
    right; right; left.
    apply subtree_trans_left in Hsbt; assumption.
    right; right; right.
    apply subtree_trans_left in Hsbt; assumption.
    destruct (H0 tl tr (eq_refl _)) as [Heq | [Heq | [Hsbt | Hsbt]]]; subst.
    right; right; left; apply subtree_nodeR.
    right; right; right; apply subtree_nodeR.
    right; right; left.
    apply subtree_trans_right in Hsbt; assumption.
    right; right; right.
    apply subtree_trans_right in Hsbt; assumption.
    destruct (H0 tl tr (eq_refl _)) as [Heq | [Heq | [Hsbt | Hsbt]]]; subst.
    right; right; left; assumption.
    right; right; right; assumption.
    right; right; left;
      apply subtree_trans with (t0);
        [apply subtree_trans with (t2) | idtac]; assumption.
    right; right; right;
      apply subtree_trans with (t0);
        [apply subtree_trans with (t2) | idtac]; assumption.
  Qed.    

  Lemma subtree_node:
    forall t tl tr, subtree t (tl/-\tr) ->
      t=tl\/t=tr\/subtree t tl\/subtree t tr.
  Proof.
    intros.
    apply subtree_node_aux with (tl/-\tr);
      [assumption | reflexivity].
  Qed.

  Lemma inb_eq_subtree:
    forall t t',
      inb t' t ->
      t' = t\/subtree t' t.
  Proof.
    intros t t' Hinb; elim Hinb; clear Hinb t t'.
    left; reflexivity.
    intros t t1 t2 Hinb [Heq | Hsbt]; right;
      [subst t; apply subtree_nodeL |].
    apply subtree_trans with t1;
      [apply subtree_nodeL | assumption].
    intros t t1 t2 Hinb [Heq | Hsbt]; right;
      [subst t; apply subtree_nodeR |].
    apply subtree_trans with t2;
      [apply subtree_nodeR | assumption].
  Qed.

  Definition is_node (t: btree A) :=
    match t with
      | [_] => False
      | _/-\_ => True
    end.

  Lemma is_node_exists:
    forall t, is_node t -> exists tl, exists tr, t = tl/-\tr.
  Proof.
    intro t; case t; clear t; simpl;
      [intro; contradiction | idtac].
    intros tl tr T; exists tl, tr; reflexivity.
  Qed.

  Definition all_node (l: list (btree A)) :=
    forall x, In x l -> is_node x.

  Lemma all_node_perm:
    forall l1 l2,
      permutation l1 l2 ->
      all_node l1 -> all_node l2.
  Proof.
    intros l1 l2 Hperm; elim Hperm; clear Hperm l1 l2.
    tauto.
    unfold all_node.
    simpl; intros.
    destruct H2 as [Heq | HIn]; try subst x.
    apply H1; left; reflexivity.
    genc HIn; genc x; apply H0.
    intros x HIn; apply H1; right; assumption.
    unfold all_node; simpl; intros.
    destruct H0 as [Heq | [Heq | HIn]]; try subst x.
    apply H; right; left; reflexivity.
    apply H; left; reflexivity.
    apply H; right; right; assumption.
    intros; tauto.
  Qed.



  Fixpoint node_list (l: list (btree A)) :=
    match l with
      | nil => True
      | [a]::_ => False
      | _/-\_::t => node_list t
    end.

  Lemma distinct_leaves_child:
    forall t t',
      distinct_leaves t ->
      child t' t ->
      distinct_leaves t'.
  Proof.
    intros t t' Hdl Hchild; genc Hdl;
      case Hchild; clear Hchild t t';
        [apply distinct_leaves_l
         | apply distinct_leaves_r].
  Qed.

  Lemma distinct_node_neq:
    forall t1 t2: btree A,
      distinct_leaves (t1/-\t2) -> t1 <> t2.
  Proof.
    intros t1 t2 Hdl Heq; subst.
    eapply Hdl; apply inleaf.
  Qed.


  Lemma inb_node_node:
    forall t tl tr,
      inb (tl/-\tr) t -> is_node t.
  Proof.
    intros t tl tr Hinb; inversion Hinb; subst; simpl; tauto.
  Qed.

  Lemma inb_neq_node:
    forall t1 t2,
      inb t1 t2 -> t1 <> t2 -> is_node t2.
  Proof.
    intros t1 t2 Hinb; elim Hinb; clear Hinb t1 t2.
    intros t Hneq; elim Hneq; reflexivity.
    intros; simpl; tauto.
    intros; simpl; tauto.
  Qed.

  Lemma inb_inb_inb:
    forall t t1 t2: btree A,
      inb t1 t -> inb t2 t ->
      (t1 = t/\t2 = t)\/
      (exists tl, exists tr,
        inb (tl/-\tr) t/\
          ((inb t1 tl/\inb t2 tr)\/(inb t2 tl/\inb t1 tr)))\/
      inb t1 t2\/
      inb t2 t1.
  Proof.
    intros t t1 t2 Hinb_1; genc t2;
      elim Hinb_1; clear Hinb_1 t t1.
    intros t t2 Hinb_2; elim Hinb_2; clear Hinb_2 t t2.
    intro t; left; split; reflexivity.
    intros t t1 t2 Hinb_1.
    repeat right; apply innodeL; assumption.
    intros t t1 t2 Hinb_2.
    repeat right; apply innodeR; assumption.

    intros t t1 t2 Hinb_1 IH t3 Hinb_3.
    inversion Hinb_3; subst.
    right; right; left; apply innodeL; assumption.
    generalize (IH _ H1).
    intros [[H Heq] | [[tl [tr [Hinb [[Hinb_l Hinb_r] | [Hinb_l Hinb_r]]]]] | [Hinb | Hinb]]];
      subst.
    repeat right; apply inleaf.
    right; left; exists tl, tr; split.
    apply innodeL; assumption.
    left; split; assumption.
    right; left; exists tl, tr; split.
    apply innodeL; assumption.
    right; split; assumption.
    right; right; left; assumption.
    repeat right; assumption.
    right; left; exists t1, t2; split.
    apply inleaf.
    left; split; assumption.

    intros t t1 t2 Hinb_2 IH t3 Hinb_3.
    inversion Hinb_3; subst.
    right; right; left; apply innodeR; assumption.
    right; left; exists t1, t2; split.
    apply inleaf.
    right; split; assumption.
    generalize (IH _ H1).
    intros [[H Heq] | [[tl [tr [Hinb [[Hinb_l Hinb_r] | [Hinb_l Hinb_r]]]]] | [Hinb | Hinb]]];
      subst.
    repeat right; apply inleaf.
    right; left; exists tl, tr; split.
    apply innodeR; assumption.
    left; split; assumption.
    right; left; exists tl, tr; split.
    apply innodeR; assumption.
    right; split; assumption.
    right; right; left; assumption.
    repeat right; assumption.
  Qed.

    
  Lemma not_node_l:
    forall tl tr: btree A, tl/-\tr<>tl.
  Proof.
    intros tl; elim tl; clear tl.
    intros a tr Heq; discriminate.
    intros tll IHl tlr IHr tr Heq.
    injection Heq; intros.
    elim (IHl _ H0).
  Qed.

  Lemma not_node_r:
    forall tl tr: btree A, tl/-\tr<>tr.
  Proof.
    intros tl tr; genc tl; elim tr; clear tr.
    intros a tl Heq; discriminate.
    intros trl IHl trr IHr tl Heq.
    injection Heq; intros.
    elim (IHr _ H).
  Qed.

  Lemma not_child:
    forall t t',
      child t' t -> t<>t'.
  Proof.
    intros t t' Hchild; case Hchild; clear Hchild t t';
      [apply not_node_l | apply not_node_r].
  Qed.


  Lemma not_inb_node_l:
    forall tl tr: btree A,
      ~inb (tl/-\tr) tl.
  Proof.
    intros tl tr Hinb.
    elim
      (not_node_l
        (inb_antisym _ _ _ Hinb (innodeL _ _ _ _ (inleaf _ _)))).
  Qed.


  Lemma not_inb_node_r:
    forall tl tr: btree A,
      ~inb (tl/-\tr) tr.
  Proof.
    intros tl tr Hinb.
    elim
      (not_node_r
        (inb_antisym _ _ _ Hinb (innodeR _ _ _ _ (inleaf _ _)))).
  Qed.  


  Lemma distinct_leaves_inb_trans:
    forall t1 t2: btree A,
      distinct_leaves (t1/-\t2) ->
      forall t3 t4,
        inb t3 t1 -> inb t4 t2 ->
        distinct_leaves (t3/-\t4).
  Proof.
    unfold distinct_leaves.
    intros t1 t2 Hdl t3 t4 Hinb_31 Hinb_42 t t5 t6 Hinb_t Hinb_5 Hinb_6.
    inversion Hinb_t; subst.
    eapply Hdl.
    apply inleaf.
    eapply inb_trans.
    eexact Hinb_5.
    assumption.
    eapply inb_trans.
    eexact Hinb_6.
    assumption.
    generalize (inb_node_node H1); intro Hin;
      apply is_node_exists in Hin; destruct Hin as [tl3 [tr3 Heq]]; subst.
    apply (Hdl t t5 t6); try assumption.
    apply innodeL; eapply inb_trans; eassumption.
    generalize (inb_node_node H1); intro Hin;
      apply is_node_exists in Hin; destruct Hin as [tl3 [tr3 Heq]]; subst.
    apply (Hdl t t5 t6); try assumption.
    apply innodeR; eapply inb_trans; eassumption.
  Qed.


  Lemma distinct_leaves_inb:
    forall t: btree A,
      distinct_leaves t ->
      forall t', inb t' t ->
        distinct_leaves t'.
  Proof.
    intro t; elim t; clear t.
    intros a Hdl t' Hinb; inversion Hinb; subst; assumption.
    intros tl IHl tr IHr Hdl t' Hinb.
    inversion Hinb; subst.
    assumption.
    apply IHl; apply distinct_leaves_l in Hdl; assumption.
    apply IHr; apply distinct_leaves_r in Hdl; assumption.
  Qed.


   Lemma distinct_not_rev_l_aux:
     forall t,
       distinct_leaves t ->
       forall t',
         inb t' t ->
         forall tl tr,
           t' = tl/-\tr ->
           forall tr',
             ~inb (tr'/-\tl) t.
   Proof.
     intros t Hdl t' Hinb; genc Hdl;
       elim Hinb; clear Hinb t t'.
     intros t Hdl tl tr Heq tr' Hinb; subst.
     inversion Hinb; subst.
     elim (Hdl _ _ _ (inleaf _ _) (inleaf _ _) (inleaf _ _)).
     elim (not_inb_node_r H1).
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inleaf _ _)
         (inb_trans _ _ _ _
           (innodeR _ _ tr' _ (inleaf _ _)) H1)).
     intros t t1 t2 Hinb_1 IH Hdl tl tr Heq tr' Hinb_12; subst.
     inversion Hinb_12; subst.
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inb_trans _ _ _ _
           (innodeL _ _ _ tr (inleaf _ _)) Hinb_1)
         (inleaf _ _)).
     genc H1; generalize tr';
       eapply IH; [apply (distinct_leaves_l _ _ _ Hdl) | reflexivity].
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inb_trans _ _ _ _ (innodeL _ _ _ _ (inleaf _ _)) Hinb_1)
         (inb_trans _ _ _ _ (innodeR _ _ _ _ (inleaf _ _)) H1)).
     intros t t1 t2 Hinb_2 IH Hdl tl tr Heq tr' Hinb_12; subst.
     inversion Hinb_12; subst.
     elim (not_inb_node_l Hinb_2).
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inb_trans _ _ _ _ (innodeR _ _ _ _ (inleaf _ _)) H1)
         (inb_trans _ _ _ _ (innodeL _ _ _ _ (inleaf _ _)) Hinb_2)).
     genc H1; generalize tr';
       eapply IH; [apply (distinct_leaves_r _ _ _ Hdl) | reflexivity].
   Qed.
     
   Lemma distinct_not_rev_l:
     forall t,
       distinct_leaves t ->
       forall tl tr,
         inb (tl/-\tr) t ->
         forall tr',
           ~inb (tr'/-\tl) t.
   Proof.
     intros; eapply distinct_not_rev_l_aux;
       try eassumption.
     reflexivity.
   Qed.

   Lemma distinct_not_rev_r_aux:
     forall t,
       distinct_leaves t ->
       forall t',
         inb t' t ->
         forall tl tr,
           t' = tl/-\tr ->
           forall tl',
             ~inb (tr/-\tl') t.
   Proof.
     intros t Hdl t' Hinb; genc Hdl;
       elim Hinb; clear Hinb t t'.
     intros t Hdl tl tr Heq tl' Hinb; subst.
     inversion Hinb; subst.
     elim (Hdl _ _ _ (inleaf _ _) (inleaf _ _) (inleaf _ _)).
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inb_trans _ _ _ _
           (innodeL _ _ _ tl' (inleaf _ _)) H1)
         (inleaf _ _)).
     elim (not_inb_node_l H1).

     intros t t1 t2 Hinb_1 IH Hdl tl tr Heq tl' Hinb_12; subst.
     inversion Hinb_12; subst.
     elim (not_inb_node_r Hinb_1).
     genc H1; generalize tl';
       eapply IH; [apply (distinct_leaves_l _ _ _ Hdl) | reflexivity].
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inb_trans _ _ _ _ (innodeR _ _ _ _ (inleaf _ _)) Hinb_1)
         (inb_trans _ _ _ _ (innodeL _ _ _ _ (inleaf _ _)) H1)).
     intros t t1 t2 Hinb_2 IH Hdl tl tr Heq tl' Hinb_12; subst.
     inversion Hinb_12; subst.
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inleaf _ _)
         (inb_trans _ _ _ _
           (innodeR _ _ tl _ (inleaf _ _)) Hinb_2)).
     elim
       (Hdl _ _ _ (inleaf _ _)
         (inb_trans _ _ _ _ (innodeL _ _ _ _ (inleaf _ _)) H1)
         (inb_trans _ _ _ _ (innodeR _ _ _ _ (inleaf _ _)) Hinb_2)).
     genc H1; generalize tl';
       eapply IH; [apply (distinct_leaves_r _ _ _ Hdl) | reflexivity].
   Qed.
     
   Lemma distinct_not_rev_r:
     forall t,
       distinct_leaves t ->
       forall tl tr,
         inb (tl/-\tr) t ->
         forall tl',
           ~inb (tr/-\tl') t.
   Proof.
     intros; eapply distinct_not_rev_r_aux;
       try eassumption.
     reflexivity.
   Qed.


   Lemma distinct_not_rev:
     forall t,
       distinct_leaves t ->
       forall tl tr,
         inb (tl/-\tr) t -> ~inb (tr/-\tl) t.
   Proof.
     intros.
     apply (distinct_not_rev_l H H0).
   Qed.

(*   Lemma distinct_distinct_aux:
     forall t,
       distinct_leaves t ->
       forall t',
         inb t' t ->
         t' = t\/(subtree t' t).
   Proof.
     intros tl tr Hdl tl' tr' Hsbt; split; intro Heq; subst.
     inversion Hsbt.
     elim (not_node_l H1).
     

     forall t t',
       distinct_leaves t ->
       child t' t ->
       forall tl tr,
         inb (tl/-\tr) t' ->
         forall tl' tr',
           t = tl'/-\tr' ->
           tl <> tl' /\ tr <> tr'.
     PRoof.
*)
(*
   Definition strict_not (t t': btree A) :=
     match t, t' with
       | node tl tr, node tl' tr' => tl<>tl'/\tr<>tr'
       | _, _ => t <> t'
     end.

   Lemma subtree_strict_not:
     forall t t',
       subtree t' t -> strict_not t' t.
   Proof.
     intros t t' Hsbt; elim Hsbt; clear Hsbt t t'.
     simpl.

   Lemma distinct_distinct_aux:
     forall t,
       distinct_leaves t ->
       forall t',
         child t' t ->
         forall t'',
           inb t'' t' ->
           t'' = t'\/strict_not t'' t'.
   Proof.
     intros t Hdl t' Hchild;
       genc Hdl; case Hchild; clear Hchild t t'.
     intros tl tr Hdl t'' Hinb.
     apply distinct_leaves_l in Hdl.
     apply inb_eq_subtree in Hinb.
     genc Hdl; case
     
 
     intros tl tr Hdl t'' Hinb; elim Hinb.
     left; reflexivity.
     intros t t1 t2 Hinb' [Heq | Hsn];
       [right; subst | left].
     case t; simpl.
     intros a Heq; elim (not_node_l Heq).
     intros b b'; 

*)
   Lemma distinct_distinct_aux:
     forall t,
       distinct_leaves t ->
       forall t',
         inb t' t ->
         forall tl tr,
           t' = tl/-\tr ->
           forall t'',
             inb t'' t ->
             forall tl' tr',
               t'' = tl'/-\tr' ->
               (tl=tl'/\tr=tr')\/(tl<>tl'/\tr<>tr').
   Proof.
     intros t Hdl t' Hinb; genc Hdl;
       elim Hinb; clear t t' Hinb.
     intros t Hdl tl tr Heq; subst.
     intros t'' Hinb'; inversion Hinb'; subst.
     intros tl' tr' Heq; injection Heq; intros; subst tl' tr'.
     left; split; reflexivity.
     intros tl' tr' Heq; subst; right; split; intro Heq; subst.
     elim (not_inb_node_l H1).
     apply (inb_trans _ tr' _ _ (innodeR _ _ _ _ (inleaf _ _))) in H1.
     elim (Hdl _ _ _ (inleaf _ _) H1 (inleaf _ _)).
     intros tl' tr' Heq; subst; right; split; intro Heq; subst.
     apply (inb_trans _ tl' _ _ (innodeL _ _ _ _ (inleaf _ _))) in H1.
     elim (Hdl _ _ _ (inleaf _ _) (inleaf _ _) H1).
     elim (not_inb_node_r H1).

     (* .t1 *)
     intros t t1 t2 Hinb_1 IH Hdl tl tr Heq; subst t.
     intros t'' Hinb'; inversion Hinb'; subst.
     (* ..t''=t1/-\t2 *)
     intros tl' tr' Heq; injection Heq; intros; subst tl' tr'; clear Heq.
     right; split; intro Heq; subst.
     elim (not_inb_node_l Hinb_1).
     apply (inb_trans _ t2 _ _ (innodeR _ _ _ _ (inleaf _ _))) in Hinb_1.
     elim (Hdl _ _ _ (inleaf _ _) Hinb_1 (inleaf _ _)).
     (* ..inb t'' t1 *)
     intros tl' tr' Heq; subst.
     apply distinct_leaves_l in Hdl.
     apply (IH Hdl _ _ (eq_refl _) _ H1 _ _ (eq_refl _)).
     (* .. inb t'' t2 *)
     intros tl' tr' Heq; subst.
     right; split; intro Heq; subst.
     apply (inb_trans _ tl' _) in H1.
     apply (inb_trans _ tl' _) in Hinb_1.
     elim (Hdl _ _ _ (inleaf _ _) Hinb_1 H1).
     apply innodeL; apply inleaf.
     apply innodeL; apply inleaf.
     apply (inb_trans _ tr' _) in H1.
     apply (inb_trans _ tr' _) in Hinb_1.
     elim (Hdl _ _ _ (inleaf _ _) Hinb_1 H1).
     apply innodeR; apply inleaf.
     apply innodeR; apply inleaf.
    
     (* .t2 *)
     intros t t1 t2 Hinb_2 IH Hdl tl tr Heq; subst t.
     intros t'' Hinb'; inversion Hinb'; subst.
     (* ..t''=t1/-\t2 *)
     (*cut 
       (forall t t',
         distinct_leaves t ->
         child t' t ->
         forall tl tr,
           inb (tl/-\tr) t' ->
           forall tl' tr',
             t = tl'/-\tr' ->
             tl <> tl' /\ tr <> tr').
     intro H.
     right.
     apply (H (t1/-\t2) t2 Hdl (childR _ _) _ _ Hinb_2 _ _ H0).
     *)
     intros tl' tr' Heq; injection Heq; intros; subst tl' tr'; clear Heq.
     right; split; intro Heq; subst.
     apply (inb_trans _ t1 _ _ (innodeL _ _ _ _ (inleaf _ _))) in Hinb_2.
     elim (Hdl _ _ _ (inleaf _ _) (inleaf _ _) Hinb_2).
     elim (not_inb_node_r Hinb_2).
     (* ..inb t'' t1 *)
     intros tl' tr' Heq; subst.
     right; split; intro Heq; subst.
     apply (inb_trans _ tl' _) in H1.
     apply (inb_trans _ tl' _) in Hinb_2.
     elim (Hdl _ _ _ (inleaf _ _) H1 Hinb_2).
     apply innodeL; apply inleaf.
     apply innodeL; apply inleaf.
     apply (inb_trans _ tr' _) in H1.
     apply (inb_trans _ tr' _) in Hinb_2.
     elim (Hdl _ _ _ (inleaf _ _) H1 Hinb_2).
     apply innodeR; apply inleaf.
     apply innodeR; apply inleaf.
     (* ..inb t'' t2 *)
     intros tl' tr' Heq; subst.
     apply distinct_leaves_r in Hdl.
     apply (IH Hdl _ _ (eq_refl _) _ H1 _ _ (eq_refl _)).
   Qed.     

   Lemma distinct_distinct:
     forall t,
       distinct_leaves t ->
       forall tl tr,
         inb (tl/-\tr) t ->
         forall tl' tr',
           inb (tl'/-\tr') t ->
           (tl=tl'/\tr=tr')\/(tl<>tl'/\tr<>tr').
   Proof.
     intros; eapply distinct_distinct_aux;
       try reflexivity; try eassumption.
   Qed.

   Lemma distinct_distinct_r:
     forall t,
       distinct_leaves t ->
       forall tl tr,
         inb (tl/-\tr) t ->
           forall tr',
             inb (tl/-\tr') t ->
             tr = tr'.
   Proof.
     intros.
     generalize (distinct_distinct H H0 H1).
     intros [[Heql Heqr] | [Hneql Hneqr]];
       [assumption | elim Hneql; reflexivity].
   Qed.


   Lemma distinct_distinct_l:
     forall t,
       distinct_leaves t ->
       forall tl tr,
         inb (tl/-\tr) t ->
           forall tl',
             inb (tl'/-\tr) t ->
             tl = tl'.
   Proof.
     intros.
     generalize (distinct_distinct H H0 H1).
     intros [[Heql Heqr] | [Hneql Hneqr]];
       [assumption | elim Hneqr; reflexivity].
  Qed.


  Definition strict_parent (t: btree A) :=
    forall tl tr,
      inb (tl/-\tr) t ->
      sum_leaves f tl < sum_leaves f (tl/-\tr).


  (* Lemmas of sum_order *)
  Lemma sum_order_trans: transitive _ (sum_order f).
  Proof.
    unfold transitive, sum_order; simpl.
    intros; eauto with arith.
  Qed.

  Lemma sum_order_node_l:
    forall tl tr, sum_order f tl (tl/-\tr).
  Proof.
    intros tl tr; unfold sum_order; simpl; auto with arith.
  Qed.

  Lemma sum_order_node_r:
    forall tl tr, sum_order f tr (tl/-\tr).
  Proof.
    intros tl tr; unfold sum_order; simpl; auto with arith.
  Qed.

  Lemma inb_sum_order:
    forall t1 t2, inb t2 t1 -> sum_order f t2 t1.
  Proof.
    intros t1 t2 Hinb; elim Hinb; clear Hinb t1 t2.
    unfold sum_order; simpl; auto with arith.
    unfold sum_order; simpl; intros; auto with arith.
    unfold sum_order; simpl; intros.
    rewrite plus_comm; auto with arith.
  Qed.

  Lemma sum_order_dec:
    forall x y, {sum_order f x y}+{sum_order f y x}.
  Proof.
    unfold sum_order; intros x y;
      apply le_ge_dec.
  Qed.

  Definition node_le (t1 t2: btree A) :=
    match t1, t2 with
      | node _ t1r, node t2l _ => sum_order f t1r t2l
      | _, _ => True
    end.

  Definition well_sibl (t: btree A) :=
    match t with
      | [a] => True
      | tl/-\tr => sum_order f tl tr
    end.  


  Fixpoint well_siblist (l: list (btree A)) :=
    match l with
      | nil => True
      | h::t => well_sibl h/\well_siblist t
    end.


  Definition all_well_sibl (l: list (btree A)) :=
    forall x, In x l -> well_sibl x.


  Lemma well_siblist_all_well_sibl:
    forall l, well_siblist l <-> all_well_sibl l.
  Proof.
    unfold all_well_sibl.
    intro l; elim l; clear l; simpl.
    split.
    intros; contradiction.
    tauto.
    intros h t IH; split.
    intros [Hws Hwsl] x [Heq | HIn]; subst.
    assumption.
    genc HIn; genc x; apply IH; assumption.
    intros; split.
    apply H; left; reflexivity.
    apply IH; intros x HIn; apply H; right; assumption.
  Qed.

  Lemma aws_cons_aux:
    forall t l,
      well_sibl t ->
      well_siblist l ->
      well_siblist (t::l).
  Proof.
    intros; simpl; split; assumption.
  Qed.

  Lemma aws_cons:
    forall t l,
      well_sibl t ->
      all_well_sibl l ->
      all_well_sibl (t::l).
  Proof.
    intros.
    apply well_siblist_all_well_sibl.
    apply well_siblist_all_well_sibl in H0.
    apply aws_cons_aux; assumption.
  Qed.



  Inductive ordered_siblist: list (btree A) -> Prop :=
  | os_nil: ordered_siblist nil
  | os_cons:
    forall t l,
      ordered_siblist l ->
      is_node t -> well_sibl t ->
      (forall t', In t' l -> node_le t t') ->
      ordered_siblist (t::l).

  Lemma os_one:
    forall t, is_node t -> well_sibl t -> ordered_siblist (t::nil).
  Proof.
    intros t Hin Hws; apply os_cons; [apply os_nil | | |]; try assumption.
    simpl; intros; contradiction.
  Qed.

  Lemma os_rear:
    forall l,
      ordered_siblist l ->
      forall t,
        is_node t -> well_sibl t ->
        (forall t', In t' l -> node_le t' t) ->
        ordered_siblist (l++t::nil).
  Proof.
    intros l Hos; elim Hos; clear Hos l; simpl.
    intros; apply os_one; assumption.
    intros.
    apply os_cons; try assumption.
    apply H0; try assumption.
    intros t' HIn; apply H6; right; assumption.
    intros t' HIn; apply in_app_iff in HIn;
      simpl in HIn; destruct HIn as [HIn | [Heq | F]];
        subst; try contradiction.
    apply H3; assumption.
    apply H6; left; reflexivity.
  Qed.


  Lemma os_all_well_sibl:
    forall l, ordered_siblist l -> all_well_sibl l.
  Proof.
    unfold all_well_sibl.
    intros l Hos; elim Hos; clear Hos l.
    simpl; intros; contradiction.
    simpl; intros.
    destruct H4 as [Heq | HIn]; subst.
    assumption.
    apply H0; assumption.
  Qed.

  Lemma os_all_node:
    forall l, ordered_siblist l -> all_node l.
  Proof.
    unfold all_node.
    intros l Hos; elim Hos; clear Hos l.
    simpl; intros; contradiction.
    simpl; intros.
    destruct H4 as [Heq | HIn]; subst.
    assumption.
    apply H0; assumption.
  Qed.


  Lemma os_in_well_sibl_node:
    forall l,
      ordered_siblist l ->
      forall x, In x l ->
        exists tl, exists tr, x = tl/-\tr/\sum_order f tl tr.
  Proof.
    intros l Hos; elim Hos; clear Hos l.
    simpl; intros; contradiction.
    intros.
    simpl in H4; destruct H4 as [Heq | HIn]; subst.
    apply is_node_exists in H1;
      destruct H1 as [tl [tr Heq]]; subst.
    exists tl, tr; split; [reflexivity | simpl in H2; assumption].
    apply H0; assumption.
  Qed.
End BTree_appendix.

