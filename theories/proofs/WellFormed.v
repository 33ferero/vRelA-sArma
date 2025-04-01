From hahn Require Import Hahn.
From Coq Require Import IndefiniteDescription.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.
Require Import Misc.

Ltac unfold_src :=
    simpl in *;
    unfold src_rf, src_mo, src_rmw, src_po, src_events, src_rel  in *;
    repeat (match goal with
    | [H: context[match ?X with _ => _ end] |- _] => destruct X 
    | [H: context[ _ /\ _ ] |- _] => destruct H
    | [H: context[exists _, _] |- _] => destruct H 
    | [H: context[map_ev_back _ _ = map_ev_back _ _] |- _] => apply map_ev_back_eq in H
    end; subst).

Lemma src_mo_elements : dom_rel (mo src) ∪₁ codom_rel (mo src) ⊆₁ events src.
Proof.
    intros x_src H.
    destruct H as [H | H];
    destruct H as [y_src [x_dst [y_dst [rel_dst H]]]];
    unfold src_events;
    destruct (mo_in_ev DST_WF x_dst y_dst rel_dst) as [X_DST_EV Y_DST_EV];
    destruct H.
    - exists x_dst, X_DST_EV. auto.
    - exists y_dst, Y_DST_EV. auto.
Qed.

Lemma src_rmw_elements : dom_rel (rmw src) ∪₁ codom_rel (rmw src) ⊆₁ events src.
Proof.
    intros x_src H.
    destruct H as [H | H];
    destruct H as [y_src [x_dst [y_dst [rel_dst H]]]];
    unfold src_events;
    destruct (rmw_in_ev DST_WF x_dst y_dst rel_dst) as [X_DST_EV Y_DST_EV];
    destruct H.
    - exists x_dst, X_DST_EV. auto.
    - exists y_dst, Y_DST_EV. auto.
Qed.

Lemma src_rf_elements : dom_rel (rf src) ∪₁ codom_rel (rf src) ⊆₁ events src.
Proof.
    intros x_src H.
    destruct H as [H | H];
    destruct H as [y_src [x_dst [y_dst [rel_dst H]]]];
    unfold src_events;
    destruct (rf_in_ev DST_WF x_dst y_dst rel_dst) as [X_DST_EV Y_DST_EV];
    destruct H.
    - exists x_dst, X_DST_EV. auto.
    - exists y_dst, Y_DST_EV. auto.
Qed.

Lemma src_po_elements : dom_rel (po src) ∪₁ codom_rel (po src) ⊆₁ events src.
Proof.
    intros x_src H.
    destruct H as [H | H];
    destruct H as [y_src [x_dst [y_dst [rel_dst H]]]];
    unfold src_events;
    destruct (po_in_ev DST_WF x_dst y_dst rel_dst) as [X_DST_EV Y_DST_EV];
    destruct H.
    - exists x_dst, X_DST_EV. auto.
    - exists y_dst, Y_DST_EV. auto.
Qed.

Lemma src_po_trans : transitive (po src).
Proof.
    intros x y z PO_SRC1 PO_SRC2.
    destruct PO_SRC1 as [x_dst [y_dst [PO_DST1]]].
    destruct PO_SRC2 as [y_dst2 [z_dst [PO_DST2]]].
    unfold_src.
    assert (PO_DST3 : po dst x_dst z_dst).
    { apply (po_trans DST_WF) with (y := y_dst2); auto. }
    exists x_dst, z_dst, PO_DST3.
    basic_solver.
Qed.

Lemma src_mo_trans : transitive (mo src).
Proof.
    intros x y z MO_SRC1 MO_SRC2.
    destruct MO_SRC1 as [x_dst [y_dst [MO_DST1]]].
    destruct MO_SRC2 as [y_dst2 [z_dst [MO_DST2]]].
    unfold_src.
    assert (MO_DST3 : mo dst x_dst z_dst).
    { apply (mo_trans DST_WF) with (y := y_dst2); auto. }
    exists x_dst, z_dst, MO_DST3.
    basic_solver.
Qed.

Lemma src_po_irrefl : irreflexive (po src).
Proof.
    intros x H.
    destruct H as [x_dst [y_dst [PO H1]]]. 
    unfold_src.
    apply (po_irrefl DST_WF) in PO.
    contradiction PO.
Qed.

Lemma src_rf_same_loc : (rf src) ⊆ same_loc. 
Proof.
    intros x y H.
    destruct H as [x_dst [y_dst [RF]]]. 
    unfold_src.
    apply (rf_same_loc DST_WF) in RF.
    inversion RF.
    unfold map_ev_back, has_loc in *.
    basic_solver.
Qed.

Lemma src_mo_same_loc : (mo src) ⊆ same_loc. 
Proof.
    intros x y H.
    destruct H as [x_dst [y_dst [MO]]]. 
    unfold_src.
    apply (mo_same_loc DST_WF) in MO.
    inversion MO.
    unfold map_ev_back, has_loc in *.
    basic_solver.
Qed.
    
Lemma rf_implies_wr : forall ex (WF : well_formed ex) x y (RF : rf ex x y), ev_w x /\ ev_r y.
Proof.
    intros.
    assert (W: (⦗W⦘ ⨾ (rf ex) ⨾ ⦗R⦘) x y).
    { apply (rfD WF). apply RF. }
    assert (W_DST : ev_w x /\ ev_r y).
    { unfold HahnRelationsBasic.seq, eqv_rel in W. basic_solver. }
    auto.
Qed.

Lemma is_w_back : forall y_dst (Y_DST_EV : events dst y_dst) y_src (W_Y_DST : ev_w y_dst) (MAP : map_ev_back y_dst Y_DST_EV = y_src),
    ev_w y_src.
Proof.
    intros.
    unfold map_ev_back in *.
    destruct y_dst; try destruct s;
    try by (inversion W_Y_DST; inversion H0);
    subst; repeat econstructor.
Qed.

Lemma is_r_back : forall y_dst (Y_DST_EV : events dst y_dst) y_src (R_Y_DST : ev_r y_dst) (MAP : map_ev_back y_dst Y_DST_EV = y_src),
    ev_r y_src.
Proof.
    intros.
    unfold map_ev_back in *.
    destruct y_dst; try destruct s;
    try by (inversion R_Y_DST; inversion H0).
    basic_solver.
Qed.

Lemma src_rfD : (rf src) ≡ ⦗W⦘ ⨾ (rf src) ⨾ ⦗R⦘.
Proof.
    simpl. split.
    - intros x_src y_src [x_dst [y_dst [REL H]]].
      destruct (rf_in_ev DST_WF x_dst y_dst REL). 
      destruct H as [H1 H2].
      assert(ev_w x_dst /\ ev_r y_dst) as [W_DST R_DST].
      { apply (rf_implies_wr dst DST_WF x_dst y_dst REL). }
      exists x_src. repeat split.
      + apply (is_w_back x_dst e); auto.
      + exists y_src. repeat split.
        * subst. 
          apply
          (map_rf_back x_dst y_dst). 
          basic_solver.
        * apply (is_r_back y_dst e0); auto.
    - intros x_src y_src RF_REL.
      destruct RF_REL as [x_src2 [[X_EQ W_X_SRC] [y_src2 [RF_SRC [Y_EQ R_Y_SRC]]]]]. 
      subst. 
      apply RF_SRC.
Qed.

Lemma mo_implies_w : forall ex (WF : well_formed ex) x y (MO : mo ex x y), ev_w x /\ ev_w y.
Proof.
    intros.
    assert (W: (⦗W⦘ ⨾ (mo ex) ⨾ ⦗W⦘) x y).
    { apply (moD WF). apply MO. }
    assert (W_DST : ev_w x /\ ev_w y).
    { unfold HahnRelationsBasic.seq, eqv_rel in W. basic_solver. }
    auto.
Qed.

Lemma src_wf_moD : (mo src) ≡ ⦗W⦘ ⨾ (mo src) ⨾ ⦗W⦘.
Proof.
  simpl. split.
  - intros x_src y_src [x_dst [y_dst [REL H]]].
    destruct (mo_in_ev DST_WF x_dst y_dst REL). 
    destruct H as [H1 H2].
    assert(ev_w x_dst /\ ev_w y_dst) as [W_DST1 W_DST2].
    { apply (mo_implies_w dst DST_WF x_dst y_dst REL). }
    exists x_src. repeat split.
    + apply (is_w_back x_dst e); auto.
    + exists y_src. repeat split.
      * subst. 
        apply
        (map_mo_back x_dst y_dst). 
        basic_solver.
      * apply (is_w_back y_dst e0); auto.
  - intros x_src y_src MO_REL.
    destruct MO_REL as [x_src2 [[X_EQ W_X_SRC] [y_src2 [MO_SRC [Y_EQ R_Y_SRC]]]]]. 
    subst. 
    apply MO_SRC.
Qed.

Lemma src_unique_ids : forall x y, E src x -> E src y -> get_uid x = get_uid y -> x = y.
Proof.
    intros x_src y_src X_SRC_EV Y_SRC_EV EQ_UID.
    rewrite (forw_uid X_SRC_EV), (forw_uid Y_SRC_EV) in EQ_UID.
    pose proof (unique_ids DST_WF (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV) (forw_events X_SRC_EV) (forw_events Y_SRC_EV) EQ_UID).
    repeat apply_forw.
    basic_solver.
Qed.

Lemma src_functional_rft : functional (rf src)⁻¹.
Proof.
    intros x_src y_src z_src RFT_SRC1 RFT_SRC2.
    destruct RFT_SRC1 as [x_dst1 [y_dst [RF_DST1 X_Y_EQ]]].
    destruct RFT_SRC2 as [x_dst2 [z_dst [RF_DST2 X_Z_EQ]]].
    unfold_src.
    assert (x_dst1 = x_dst2).
    { apply ((rft_functional DST_WF) z_dst x_dst1 x_dst2); auto. }
    basic_solver.
Qed.

Lemma src_po_splittable : po src ≡ (immediate (po src))⁺.
Proof.
    split.    
    - intros x_src y_src PO.      
      unfold_src.
      rename x into x_dst, x0 into y_dst, x1 into PO.
      apply (po_splittable DST_WF), clos_trans_tn1_iff in PO.
      induction PO.
      + left. 
        destruct H as [H1 H2].
        split.
        * exists x_dst, y, H1.
          basic_solver. 
        * intros.
          unfold_src.
          specialize (H2 x).
          basic_solver.
      + assert (Y_DST_EV: events dst y).
        { apply po_imm_to_po in H. apply (po_in_ev DST_WF y z H). }
        rename e0 into Z_DST_EV.
        specialize (IHPO Y_DST_EV).
        assert (immediate (po src) (map_ev_back y Y_DST_EV) (map_ev_back z Z_DST_EV)).
        {
          simpl.
          unfold immediate, src_po, src_rel in *.
          destruct H.
          split.
          * exists y, z. exists H. basic_solver.
          * intros.
            destruct R1 as [? [? [?]] ].
            destruct R2 as [? [? [?]] ].
            destruct (po_in_ev DST_WF x x0 x1).
            destruct (po_in_ev DST_WF x2 x3 x4).
            destruct H1, H2.
            subst.
            apply map_ev_back_eq in H1, H2, H4.
            subst. specialize (H0 x0). basic_solver.
        }
        apply t_trans with (y := map_ev_back y Y_DST_EV).
        * auto.
        * left. apply H0.
    - intros x y PO. 
      apply clos_trans_immediate1 in PO; auto. 
      apply src_po_trans. 
Qed.

Lemma src_po_stid : po src ⊆ ((ev_init × ev) ∪ same_tid).
Proof.
    intros x_src y_src PO.
    destruct PO as [x_dst [y_dst [PO_DST ]]].
    unfold_src.
    apply (po_stid DST_WF) in PO_DST.
    destruct PO_DST as [INIT_EV | SAME_TID].
    - left. destruct INIT_EV.
        split.
        + inversion H. 
          unfold map_ev_back in *.
          basic_solver.
        + destruct y_dst; try destruct s;
          repeat econstructor.
    - right.
      unfold map_ev_back in *.
      inversion SAME_TID.
      basic_solver.
Qed.

Lemma forw_e_init_tid {x_src} {tid} (X_SRC_EV : events src x_src) (H : ((ev_init ∪₁ has_tid tid)) x_src) 
    : (E dst ∩₁ (ev_init ∪₁ has_tid tid)) (forw_ev X_SRC_EV).
Proof.
    split.
    - apply_forw; basic_solver.
    - destruct H as [X_INIT | X_SAME_TID].
      + left.
        apply_forw as [? [? ?]].  
        destruct x_src; 
        inversion X_INIT.
        unfold map_ev_back in *. 
        basic_solver.
      + right.
        apply_forw. 
        destruct x_src; unfold map_ev_back in *; basic_solver.
Qed.

Lemma src_po_total : forall (t : tid), is_total (events src ∩₁ (ev_init ∪₁ has_tid t)) (po src).
Proof.
    unfold is_total in *.
    intros tid x_src [X_SRC_EV HX] y_src [Y_SRC_EV HY] NEQ_X_Y_SRC.
    pose proof (forw_e_init_tid X_SRC_EV HX) as HX_DST.
    pose proof (forw_e_init_tid Y_SRC_EV HY) as HY_DST.
    assert (NEQ_X_Y_DST: forw_ev X_SRC_EV <> forw_ev Y_SRC_EV).
    {
        repeat apply_forw.
        subst.
        apply map_ev_back_neq in NEQ_X_Y_SRC.
        auto.
    }
    destruct (po_total DST_WF tid (forw_ev X_SRC_EV) HX_DST (forw_ev Y_SRC_EV) HY_DST NEQ_X_Y_DST).
    + left. 
      exists (forw_ev X_SRC_EV), (forw_ev Y_SRC_EV), H.
      repeat apply_forw.
      basic_solver.
    + right. 
      exists (forw_ev Y_SRC_EV), (forw_ev X_SRC_EV), H.
      repeat apply_forw.
      basic_solver.
Qed.

Definition src_well_formed : well_formed src :=
  {| 
    moD := src_wf_moD; 
    po_elements := src_po_elements; 
    rf_elements := src_rf_elements; 
    mo_elements := src_mo_elements; 
    rmw_elements := src_rmw_elements ;
    unique_ids := src_unique_ids ;
    rft_functional := src_functional_rft ;
    po_trans := src_po_trans ;
    rfD := src_rfD ;
    po_irrefl := src_po_irrefl ;
    rf_same_loc := src_rf_same_loc ; 
    mo_same_loc := src_mo_same_loc ; 
    po_splittable := src_po_splittable ;
    po_stid := src_po_stid ;
    po_total := src_po_total ;
    mo_trans := src_mo_trans
  |}.