From hahn Require Import Hahn.
From Coq Require Import IndefiniteDescription.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.
Require Import WellFormed.
Require Import Relations.

Record is_mapping (src : execution rel_acq_label) (dst : execution simpl_arm_label) :=
 {
    read_rule : forall a b loc val,
        rel_acq_r_eq tmov loc val a ->
        ev_skip b ->
        po_imm src a b ->
        exists a' b', po_imm dst a' b' /\ simpl_arm_r_eq tmov loc val a' /\ simpl_arm_f_eq rm b' ;

    write_rule : forall a b loc val,
        ev_skip a ->
        rel_acq_w_eq tmov loc val b ->
        po_imm src a b ->
        exists a' b', po_imm dst a' b' /\ simpl_arm_f_eq ww a' /\ simpl_arm_w_eq tmov loc val b' ;

    rmw_rule : forall a b loc val1 val2,
        rel_acq_r_eq trmw loc val1 a ->
        rel_acq_w_eq trmw loc val2 b ->
        rmw src a b ->
        exists a' b', rmw dst a' b' /\ simpl_arm_r_eq trmw loc val1 a' /\ simpl_arm_w_eq trmw loc val2 b'
 }.

 Lemma read_rule_proof 
    (x_src y_src : event rel_acq_label) loc val 
    (R_EQ_X_SRC : rel_acq_r_eq tmov loc val x_src) (SKIP_B : ev_skip y_src) 
    (PO_IMM_SRC : po_imm src x_src y_src) :
    exists x_dst y_dst, po_imm dst x_dst y_dst /\ simpl_arm_r_eq tmov loc val x_dst /\ simpl_arm_f_eq rm y_dst.
Proof.
    assert (X_SRC_EV : events src x_src).
    { apply (po_imm_in_ev src_well_formed x_src y_src PO_IMM_SRC). }
    assert (R_T_X_SRC : ev_r_t tmov x_src).
    { inversion R_EQ_X_SRC; basic_solver. }
    pose proof (DST_RESTR.(rd_fe_left dst) (forw_ev X_SRC_EV) (forw_events X_SRC_EV) (forw_ev_r_t X_SRC_EV R_T_X_SRC)) as [y_dst [PO_IMM F_RM_Y_DST]].
    exists (forw_ev X_SRC_EV), y_dst.
    split;[|split]; auto.
    apply_forw as [x_dst [X_DST_EV EQ_X]].
    unfold map_ev_back in *.
    inversion R_EQ_X_SRC.
    basic_solver.
Qed.

Lemma write_rule_proof
    (x_src y_src : event rel_acq_label) loc val
    (SKIP_A : ev_skip x_src) (W_EQ_Y_SRC : rel_acq_w_eq tmov loc val y_src)
    (PO_IMM_SRC : po_imm src x_src y_src) :
    exists x_dst y_dst, po_imm dst x_dst y_dst /\ simpl_arm_f_eq ww x_dst /\ simpl_arm_w_eq tmov loc val y_dst.
Proof.
    assert (Y_SRC_EV : events src y_src).
    { apply (po_imm_in_ev src_well_formed x_src y_src PO_IMM_SRC). }
    assert (W_T_Y_SRC : ev_w_t tmov y_src).
    { inversion W_EQ_Y_SRC. repeat constructor. }
    pose proof (DST_RESTR.(fe_wr_right dst) (forw_ev Y_SRC_EV) (forw_events Y_SRC_EV) (forw_ev_w_t Y_SRC_EV W_T_Y_SRC)) as [x_dst [PO_IMM F_WW_X_DST]].
    exists x_dst, (forw_ev Y_SRC_EV).
    split;[|split]; auto.
    apply_forw as [y_dst [Y_DST_EV EQ_Y]].
    unfold map_ev_back in *.
    inversion W_EQ_Y_SRC.
    basic_solver.
Qed.

Lemma rmw_rule_proof
    (x_src y_src : event rel_acq_label) loc val1 val2
    (R_EQ_X_SRC : rel_acq_r_eq trmw loc val1 x_src) (W_EQ_Y_SRC : rel_acq_w_eq trmw loc val2 y_src)
    (RMW_SRC : rmw src x_src y_src) :
    exists x_dst y_dst, rmw dst x_dst y_dst /\ simpl_arm_r_eq trmw loc val1 x_dst /\ simpl_arm_w_eq trmw loc val2 y_dst.
Proof.
    assert ( events src x_src /\events src y_src) as [X_SRC_EV Y_SRC_EV].
    { apply (rmw_in_ev src_well_formed x_src y_src RMW_SRC). }
    exists (forw_ev X_SRC_EV), (forw_ev Y_SRC_EV).
    apply (forw_rmw X_SRC_EV Y_SRC_EV ) in RMW_SRC.
    inversion R_EQ_X_SRC. inversion W_EQ_Y_SRC.
    repeat apply_forw.
    unfold map_ev_back in *.
    basic_solver.
Qed.

Definition mapping_proof : is_mapping src dst :=
    {| write_rule := write_rule_proof ;
       read_rule := read_rule_proof ;
       rmw_rule := rmw_rule_proof ;
    |}.
