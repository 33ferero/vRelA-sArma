From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.
Require Import Relations.
Require Import WellFormed.
Require Import Coq.Relations.Relation_Operators.
Require Import Misc.

Lemma rf_mo_fr_trans_same_loc {x y} (RF_MO_FR : (rf src ∪ mo src ∪ fr src)⁺ x y) : same_loc x y.
Proof.
  apply clos_trans_tn1 in RF_MO_FR.
  induction RF_MO_FR;
  destruct H as [[RF | MO] | FR];
  try (apply (mo_same_loc src_well_formed) in MO);
  try (apply (rf_same_loc src_well_formed) in RF);
  try (apply (fr_same_loc src_well_formed) in FR);
  try apply (same_loc_trans x y z);
  auto.
Qed.

(* Contradictions from incompatible set of assumptions *)
Lemma elim_rf_rf {x y z} (RF1 : rf src x y) (RF2 : rf src y z) : False.
Proof.
  pose proof (rfD src_well_formed) as RFD.
  apply RFD in RF1, RF2.
  destruct RF1 as [? [? [? [? [? R]]]]].
  destruct RF2 as [? [[? W]]].
  inversion R as [? ? ? R_LAB]. 
  inversion W as [? ? ? W_LAB|];
  inversion R_LAB; try inversion W_LAB;
  basic_solver.
Qed. 

Lemma elim_rf_mo {x y z} (RF : rf src x y) (MO : mo src y z) : False.
Proof.
  pose proof (rfD src_well_formed) as RFD.
  pose proof (moD src_well_formed) as MOD.
  apply RFD in RF.
  apply MOD in MO.
  destruct RF as [? [? [? [? [? R]]]]].
  destruct MO as [? [[? W] [? [? [? ]]]]]. subst.
  inversion R as [? ? ? R_LAB]. inversion W as [? ? ? W_LAB|];
  inversion R_LAB; try inversion W_LAB;
  basic_solver.
Qed.

Lemma elim_mo_fr {x y z} (MO : mo src x y) (FR : fr src y z) : False.
Proof.
  pose proof (moD src_well_formed) as MOD.
  pose proof (frD src_well_formed) as FRD.
  apply MOD in MO.
  apply FRD in FR.
  destruct MO as [? [? [? [? [? W]]]]].
  destruct FR as [? [[? R] [? [? [? ]]]]]. subst.
  inversion W as [? ? ? W_LAB |]; inversion R as [? ? ? R_LAB];
  try inversion W_LAB; inversion R_LAB;
  basic_solver.
Qed.

Lemma elim_fr_fr {x y z} (FR1 : fr src x y) (FR2 : fr src y z) : False.
Proof.
  pose proof (frD src_well_formed) as FRD.
  apply FRD in FR1, FR2.
  destruct FR1 as [? [? [? [? [? W]]]]].
  destruct FR2 as [? [[? R] [? [? [? ]]]]]. subst.
  inversion W as [? ? ? W_LAB|]; inversion R as [? ? ? R_LAB];
  try inversion W_LAB; inversion R_LAB;
  basic_solver.
Qed.

Lemma is_rw_r {x} (R : ev_r x) : RW x.
Proof. left. auto. Qed.

Lemma is_rw_w {x} (W : ev_w x) : RW x.
Proof. right. auto. Qed.

Lemma elim_fe_rw {x t} (FE : simpl_arm_f_eq t x) (RW : RW x) : False.
Proof.
  inversion RW as [R | W];
  try inversion R as [? ? ? R_LAB];
  try inversion W as [? ? ? W_LAB|];
  try inversion R_LAB; try inversion W_LAB;
  inversion FE as [? ? F_EQ];
  subst;
  inversion F_EQ.
Qed.

(* Splitting of relations into subcases *)
Lemma split_coh_rel {x} (COH_REL : coh_rel src x x) : (hb src x x /\ (rf src ∪ mo src ∪ fr src)＊ x x \/ (hb src ⨾ (rf src ∪ mo src ∪ fr src)⁺) x x).
Proof.
  destruct COH_REL as [m [HB_STAR RF_MO_S]].
  destruct (classic (m = x)) as [EQ | NEQ].
  - basic_solver.
  - right. exists m. split; auto.
    apply star_neq_trans; auto.
Qed.


Lemma extract_mo_fr {x} (H : (hb src ⨾ (rf src ∪ mo src ∪ fr src)⁺) x x) : exists y, hb src y y /\ (rf src ∪ mo src ∪ fr src)＊ y y \/ (hb src ⨾ (rf src ∪ mo src ∪ fr src)＊ ⨾ (mo src ∪ fr src)) y y.
Proof.
  destruct H as [y [HB_ALT RF_MO_FR]].
  apply ct_end in RF_MO_FR.
  destruct RF_MO_FR as [z [STAR REL]]. 
  apply clos_rt_rtn1_iff in STAR.
  destruct STAR.
  - destruct REL as [[RF | MO] | FR].
    + exists y. left. split. 
      * apply t_trans with (y := x); auto.
        left. right. 
        apply (equiv_sw_rf src_well_formed). auto.
      * apply rt_refl.
    + exists x. 
      right. 
      exists y. split; auto.
      exists y. split; auto.
      { apply rt_refl. }
      { left. auto. }
    + exists x. 
      right. 
      exists y. split; auto.
      exists y. split; auto.
      { apply rt_refl. }
      { right. auto. }
  - destruct H as [[RF | MO] | FR]; destruct REL as [[RF' | MO'] | FR'];
    try by (
        exists x; right;
        exists y; split; auto;
        exists z; split; auto;
        try apply clos_rt_rtn1_iff;
        try apply (Relation_Operators.rtn1_trans) with (y := y0); 
        basic_solver
    ).
    + contradiction (elim_rf_rf RF RF').
    + exists z. right.
      exists y. split; auto.
      * apply t_trans with (y := x); auto.
        left. right.
        apply (equiv_sw_rf src_well_formed). auto. 
      * exists y0. split; try basic_solver.
        apply clos_rt_rtn1_iff;
        basic_solver.
    + exists z. right.
      exists y. split; auto.
      * apply t_trans with (y := x); auto.
        left. right.
        apply (equiv_sw_rf src_well_formed). auto. 
      * exists y0. split; try basic_solver.
        apply clos_rt_rtn1_iff;
        basic_solver.
Qed.

(* Mapping sw to rfe in hb *)
Definition hb_alt (ex : execution rel_acq_label) := (ppo ex ∪ rfe ex)⁺.
Lemma hb_to_hb_alt {x y} (HB : hb src x y) : hb_alt src x y.
Proof.
  assert (RF_RW : dom_rel (rf src) ∪₁ codom_rel (rf src) ⊆₁ RW).
  { rewrite (rfD src_well_formed). basic_solver. }
  apply (inclusion_t_t (subset_ppo_external src rf RF_RW)).
  unfold hb in *.
  induction HB in x, y, HB |- *.
  - destruct H.
    + repeat left; auto.
    + left. right.
      apply (equiv_sw_rf src_well_formed). auto.
  - apply t_trans with (y := y); auto.
Qed.


(* Some aux for unfold proofs *)
Lemma ppo_rfe_extract {x y} (PPO_RFE : (ppo src ⨾ rfe src)⁺ x y) : exists z,  rfe src z y.
Proof.
  apply clos_trans_t1n in PPO_RFE.
  induction PPO_RFE.
  - destruct H as [z [PPO RFE]]. exists z. auto.
  - destruct IHPPO_RFE. exists x0. auto.
Qed.  

Lemma rfe_ppo_ppo_subs {x y z r} (PPO_RFE : (r ⨾ ppo src)⁺  x y) (PPO : ppo src y z) : (r ⨾ ppo src)⁺ x z.
Proof.
  apply clos_trans_t1n in PPO_RFE.
  induction PPO_RFE.
  - left. destruct H as [w [RFE PPO1]]. exists w. split; auto. apply (ppo_trans src_well_formed w y z); auto.
  - specialize (IHPPO_RFE PPO). apply clos_trans_t1n_iff. 
  apply clos_trans_t1n_iff in IHPPO_RFE.
  apply (Relation_Operators.t1n_trans _ _ x y z H IHPPO_RFE).
Qed.

(* Unfolding closures into all possible subcases *)
(* Unfold hb_alt *)
Definition hb_alt_split_rel :=  (ppo src ∪ rfe src ∪ (ppo src ⨾ rfe src)⁺ ∪ (rfe src ⨾ ppo src)⁺ ∪ (ppo src ⨾ rfe src)⁺ ⨾ ppo src ∪ (rfe src ⨾ ppo src)⁺ ⨾ rfe src).

Lemma split_hb_alt_stop' {x z} (REL : (hb_alt_split_rel ⨾ (ppo src ∪ rfe src)) x z) : hb_alt_split_rel x z.
Proof.
  destruct REL as [y [H1 H2]].
  destruct H1 as [[[[[PPO|RFE]|PPO_RFE]|RFE_PPO]|PPO_RFE_PPO]|RFE_PPO_RFE]; 
  destruct H2 as [PPO1|RFE1].
  - repeat left. apply (ppo_trans src_well_formed x y z); auto.
  - do 3 left. right. left. 
    exists y. split; auto.
  - do 2 left. right. left. 
    exists y. split; auto.
  - contradiction (elim_rf_rf (ex_to_rel RFE) (ex_to_rel RFE1)).
  - left. right. exists y. split; auto.
  - destruct (ppo_rfe_extract PPO_RFE) as [? RFE2]. 
    contradiction (elim_rf_rf (ex_to_rel RFE2) (ex_to_rel RFE1)).
  - do 2 left. right.
    apply (rfe_ppo_ppo_subs RFE_PPO PPO1).
  - right. 
    exists y. split; auto.
  - left. right.
    destruct PPO_RFE_PPO as [x' [PPO_RFE PPO2]].
    exists_solve x'.
    apply (ppo_trans src_well_formed x' y z); auto.
  - do 3 left. right. 
    destruct PPO_RFE_PPO as [x' [PPO_RFE PPO2]]. 
    assert (PPO_RFE' : (ppo src ⨾ rfe src) x' z). 
    { exists y. split; auto. }
    apply (clos_trans_tn1_iff). 
    apply (clos_trans_tn1_iff) in PPO_RFE.
    apply (Relation_Operators.tn1_trans _ _ _ _ _ PPO_RFE' PPO_RFE).
  - do 2 left. right. 
    destruct RFE_PPO_RFE as [x' [RFE_PPO RFE2]].
    assert (RFE_PPO' : (rfe src ⨾ ppo src) x' z). 
    { exists y. split; auto. }
    apply (clos_trans_tn1_iff). 
    apply (clos_trans_tn1_iff) in RFE_PPO.
    apply (Relation_Operators.tn1_trans _ _ _ _ _ RFE_PPO' RFE_PPO).
  - destruct RFE_PPO_RFE as [x' [RFE_PPO RFE2]].
    contradiction (elim_rf_rf (ex_to_rel RFE2) (ex_to_rel RFE1)).
Qed.

Lemma split_hb_alt_stop x y z (R1 : hb_alt_split_rel x y) (R2 : hb_alt src y z) : hb_alt_split_rel x z.
Proof.
  apply clos_trans_t1n in R2.
  induction R2 as [y | y z H2 IH].
  - apply split_hb_alt_stop'. 
    exists y. auto.
  - apply IHR2.
    apply split_hb_alt_stop'.
    exists y. auto.
Qed.

Lemma split_hb_alt {x y} (HB_ALT : hb_alt src x y) : hb_alt_split_rel x y.
Proof.
  apply clos_trans_t1n in HB_ALT.
  destruct HB_ALT as [y [PPO|RFE]| y z [PPO| RFE] [a [PPO1|RFE1] | a b [PPO1|RFE1] [c [PPO2|RFE2]| c d [PPO2|RFE2] HB_ALT]]].
  - repeat left. auto. 
  - do 4 left. right. auto.
  - repeat left. 
    apply (ppo_trans src_well_formed x y a); auto.
  - do 3 left. right. left. 
    exists y. split; auto.
  - repeat left. auto.
    apply (ppo_trans src_well_formed x y c); auto.
    apply (ppo_trans src_well_formed y a c); auto.
  - do 3 left. right. left.
    exists a. split; auto.
    apply (ppo_trans src_well_formed x y a); auto.
  - assert (ppo src x c).
    {
    apply (ppo_trans src_well_formed x y c); auto.
    apply (ppo_trans src_well_formed y a c); auto.
    }
    apply clos_trans_t1n_iff in HB_ALT.
    apply split_hb_alt_stop with (y := c); auto.
    repeat left. auto.
  - assert (ppo src x a).
    { apply (ppo_trans src_well_formed x y a); auto. }
    apply clos_trans_t1n_iff in HB_ALT.
    apply split_hb_alt_stop with (y := c); auto.
    do 3 left. right. left.
    exists a. split; auto.
  - left. right.
    exists a. split; auto.
    left. exists y. split; auto.
  - contradiction (elim_rf_rf (ex_to_rel RFE1) (ex_to_rel RFE2)).
  - assert (((ppo src ⨾ rfe src)⁺ ⨾ ppo src) x c).
    { 
      exists a. split; auto.
      left. exists y. split; auto. 
    }
    apply clos_trans_t1n_iff in HB_ALT.
    apply split_hb_alt_stop with (y := c); auto.
    do 1 left. right. auto.
  - contradiction (elim_rf_rf (ex_to_rel RFE1) (ex_to_rel RFE2)).
  - do 2 left. right. left.
    exists y. split; auto.
  - contradiction (elim_rf_rf (ex_to_rel RFE) (ex_to_rel RFE1)).
  - do 2 left. right. left.
    exists y. split; auto. 
    apply (ppo_trans src_well_formed y a c); auto.
  - right. 
    exists a. split; auto.
    left. exists y. split; auto.
  - assert ((rfe src ⨾ ppo src)⁺ x c).
    { 
      left. exists y. split; auto.
      apply (ppo_trans src_well_formed y a c); auto.
    }
    apply clos_trans_t1n_iff in HB_ALT.
    apply split_hb_alt_stop with (y := c); auto.
    do 2 left. right. auto.
  - assert (((rfe src ⨾ ppo src)⁺ ⨾ rfe src) x c).
    {
      exists a. split; auto.
      left. exists y. split; auto.
    }
    apply clos_trans_t1n_iff in HB_ALT.
    apply split_hb_alt_stop with (y := c); auto.
    right. auto.
  - contradiction (elim_rf_rf (ex_to_rel RFE) (ex_to_rel RFE1)).
  - contradiction (elim_rf_rf (ex_to_rel RFE) (ex_to_rel RFE1)).
  - contradiction (elim_rf_rf (ex_to_rel RFE) (ex_to_rel RFE1)).
  - contradiction (elim_rf_rf (ex_to_rel RFE) (ex_to_rel RFE1)).
Qed.

(* Unfolding (rf src ∪ mo src ∪ fr src)＊ ⨾ (mo src ∪ fr src))  *)

Definition coh_right_split_rel := (mo src ∪ (fr src) ∪ (fr src) ⨾ (mo src)).

Lemma split_coh_rel_right_stop x y z (R1 : (rf src ∪ mo src ∪ fr src)＊ x y) (R2 : coh_right_split_rel y z) : coh_right_split_rel x z.
Proof.
  unfold coh_right_split_rel in *.
  apply clos_rt_rtn1 in R1.
  induction R1.
  - auto.
  - apply IHR1. destruct H as [[RF | MO] | FR]; destruct R2 as [[MO' | FR'] | FR_MO].
    + contradiction (elim_rf_mo RF MO').
    + repeat left.
      apply (rf_fr_to_mo src_well_formed RF FR').
    + do 2 left.
      destruct FR_MO as [y' [FR MO]].
      apply (mo_trans src_well_formed y y' z); auto.
      apply (rf_fr_to_mo src_well_formed RF FR).
    + do 2 left.
      apply (mo_trans src_well_formed y z0 z); auto.
    + contradiction (elim_mo_fr MO FR').
    + destruct FR_MO as [y' [FR]].
      contradiction (elim_mo_fr MO FR).
    + right.
      exists z0; auto.
    + contradiction (elim_fr_fr FR FR').
    + destruct FR_MO as [y' [FR']].
      contradiction (elim_fr_fr FR FR').
Qed.


Lemma split_coh_rel_right {x y} (REL : ((rf src ∪ mo src ∪ fr src)＊ ⨾ (mo src ∪ fr src)) x y) : coh_right_split_rel x y.
Proof.
  destruct REL as [z [RF_MO_FR MO_FR]].
  apply clos_rt_rtn1_iff in RF_MO_FR.
  destruct RF_MO_FR.
  - destruct MO_FR as [MO | FR].
    + repeat left. auto.
    + left. right. auto.
  - destruct H as [[RF | MO] | FR]; destruct MO_FR as [MO' | FR']; try apply clos_rt_rtn1_iff in RF_MO_FR.
    + contradiction (elim_rf_mo RF MO').
    + assert (mo src y0 y).
      { apply (rf_fr_to_mo src_well_formed RF FR'); auto. }
      apply split_coh_rel_right_stop with (y := y0); try do 2 left; auto.
    + assert (mo src y0 y).
      { apply (mo_trans src_well_formed y0 z y); auto. }
      apply split_coh_rel_right_stop with (y := y0); try do 2 left; auto.
    + contradiction (elim_mo_fr MO FR').
    + assert ((fr src ⨾ mo src) y0 y).
      { exists z. auto.  }
      apply split_coh_rel_right_stop with (y := y0); try right; auto.
    + contradiction (elim_fr_fr FR FR').
Qed.

(* Mapping relations to ob *)
Lemma rfe_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (RFE : rfe src x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  do 3 left. right. apply forw_rfe. auto.
Qed.

(* ppos's where we have information about whether left/right side is a read *)

Lemma ppo_left_r_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO : ppo src x y) (X_R : ev_r x) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  apply (forw_ppo X_SRC_EV Y_SRC_EV) in PPO.
  destruct x eqn:X_EQ; try destruct r; try destruct m;
  try by (inversion X_R as [? ? ? R_LAB]; inversion R_LAB).
  - do 7 left. right.
    assert (R_X : ev_r x) by basic_solver.
    assert (TMOV_X :ev_r_t tmov x) by basic_solver.
    rewrite X_EQ in R_X, TMOV_X.
    assert (RW_Y : RW (forw_ev Y_SRC_EV)).
    { unfold ppo, eqv_rel, seq in PPO. basic_solver. }
    apply (forw_ev_r X_SRC_EV) in R_X. apply (forw_ev_r_t X_SRC_EV) in TMOV_X.
    pose proof (DST_RESTR.(rd_fe_left dst) (forw_ev X_SRC_EV) (forw_events X_SRC_EV) TMOV_X) as [b [PO_IMM FE]].
    pose proof (po_imm_to_po PO_IMM).
    exists_solve (forw_ev X_SRC_EV).
    do 2 exists_solve b.
    apply ppo_to_po in PPO.
    assert (X_NOT_INIT: ~ ev_init (forw_ev X_SRC_EV)).
    { 
      intros IS_INIT. 
      inversion IS_INIT as [? ? ? INIT_EQ].
      inversion R_X as [? ? ? ? EV_EQ].
      rewrite <- INIT_EQ in EV_EQ.
      inversion EV_EQ.
    }
    apply (po_split_left DST_WF) in PPO as [PO_IMM' | [m  [PO_M' PO_IMM']]].
    + pose proof (po_imm_refl_left DST_WF PO_IMM PO_IMM' X_NOT_INIT). subst.
      contradiction (elim_fe_rw FE RW_Y).
    + pose proof (po_imm_refl_left DST_WF PO_IMM' PO_IMM X_NOT_INIT). 
      subst. auto.
  - do 5 left. right.
    apply ppo_to_po in PPO.
    assert (ev_r_t trmw (forw_ev X_SRC_EV)).
    { apply (forw_ev_r_t X_SRC_EV). repeat econstructor. }
    exists_solve (forw_ev X_SRC_EV).
Qed.

Lemma ppo_right_w_rmw_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO : ppo src x y) (Y_W_RMW : ev_w_t trmw y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  do 4 left. right.
  apply ppo_to_po, (forw_po X_SRC_EV Y_SRC_EV) in PPO.
  apply (forw_ev_w_t Y_SRC_EV) in Y_W_RMW.
  exists_solve (forw_ev Y_SRC_EV).
Qed.

Lemma ppo_w_w_tmov_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO : ppo src x y) (X_W : ev_w x) (Y_W_TMOV : ev_w_t tmov y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  do 6 left. right.
  apply (forw_ppo X_SRC_EV Y_SRC_EV) in PPO.
  apply (forw_ev_w X_SRC_EV) in X_W.
  assert (Y_W : ev_w (forw_ev Y_SRC_EV)).
  { 
    apply (forw_ev_w Y_SRC_EV). 
    inversion Y_W_TMOV as [? ? ? W_LAB|]; try inversion W_LAB; 
    repeat econstructor. 
  }
  pose proof (DST_RESTR.(fe_wr_right dst) (forw_ev Y_SRC_EV) (forw_events Y_SRC_EV) (forw_ev_w_t Y_SRC_EV Y_W_TMOV)) as [f [PO_IMM FE]].
  pose proof (po_imm_to_po PO_IMM).
  assert (po dst (forw_ev X_SRC_EV) f).
  {
    apply ppo_to_po in PPO.
    apply (po_split_right DST_WF) in PPO as [PO_IMM' | [m'  [PO_M' PO_IMM']]].
    - pose proof (po_imm_refl_right DST_WF PO_IMM' PO_IMM). subst.
      contradiction (elim_fe_rw FE (is_rw_w X_W)).
    - pose proof (po_imm_refl_right DST_WF PO_IMM' PO_IMM). subst. 
      auto.
  }
  exists_solve (forw_ev X_SRC_EV).
  exists_solve f.
  exists_solve f.
  exists_solve (forw_ev Y_SRC_EV).
Qed.
      
Lemma ppo_right_w_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO : ppo src x y) (Y_W : ev_w y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  assert (RW_X : RW x).
  { unfold ppo, eqv_rel, seq in PPO. basic_solver. }
  destruct RW_X as [R | W].
  - apply ppo_left_r_to_ob; auto.
  - destruct y; try destruct r; try destruct m;
    try by (inversion Y_W as [? ? ? IS_W_LAB|]; inversion IS_W_LAB).
    + apply ppo_w_w_tmov_to_ob; auto;
      repeat econstructor.
    + apply ppo_right_w_rmw_to_ob; auto.
      repeat econstructor.
    + apply ppo_w_w_tmov_to_ob; auto.
      repeat econstructor.
Qed.

(* Combinations of rfe and ppo *)

Lemma ppo_rfe_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO_RFE : (ppo src ⨾ rfe src) x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof. 
  destruct PPO_RFE as [m [PPO RFE]].
  assert (M_W: ev_w m).
  {
    apply (rfeD src_well_formed) in RFE.
    unfold seq, eqv_rel in RFE. basic_solver.
  }
  assert (M_SRC_EV : events src m).
  { apply (rfe_in_ev src_well_formed m y). auto. }
  apply t_trans with (y := forw_ev M_SRC_EV); auto.
  - apply (ppo_right_w_to_ob X_SRC_EV M_SRC_EV PPO M_W).
  - apply (rfe_to_ob M_SRC_EV Y_SRC_EV RFE).
Qed.

Lemma rfe_ppo_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (RFE_PPO : (rfe src ⨾ ppo src) x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
    destruct RFE_PPO as [m [RFE PPO]].
    assert (M_R : ev_r m).
    {
        apply (rfeD src_well_formed) in RFE.
        unfold seq, eqv_rel in RFE. basic_solver.
    }
    assert (M_SRC_EV : events src m).
    { apply (rfe_in_ev src_well_formed x m RFE). }
    apply t_trans with (y := forw_ev M_SRC_EV); auto.
    - apply (rfe_to_ob X_SRC_EV M_SRC_EV RFE).
    - apply (ppo_left_r_to_ob M_SRC_EV Y_SRC_EV PPO M_R).
Qed.

Lemma ppo_rfe_trans_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO_RFE : (ppo src ⨾ rfe src)⁺ x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  apply clos_trans_t1n_iff in PPO_RFE.
  induction PPO_RFE.
  - apply (ppo_rfe_to_ob X_SRC_EV Y_SRC_EV) in H. auto.
  - rename Y_SRC_EV into Z_SRC_EV.
    assert (Y_SRC_EV : events src y).
    { destruct H as [a [PPO RFE]]. apply (rfe_in_ev src_well_formed a y RFE). }
    specialize (IHPPO_RFE Y_SRC_EV Z_SRC_EV).
    apply (ppo_rfe_to_ob X_SRC_EV Y_SRC_EV) in H.
    apply t_trans with (y := forw_ev Y_SRC_EV); auto.
Qed.

Lemma rfe_ppo_trans_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (RFE_PPO : (rfe src ⨾ ppo src)⁺ x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  apply clos_trans_t1n_iff in RFE_PPO.
  induction RFE_PPO.
  - apply (rfe_ppo_to_ob X_SRC_EV Y_SRC_EV) in H. auto.
  - rename Y_SRC_EV into Z_SRC_EV.
    assert (Y_SRC_EV : events src y).
    { destruct H as [a [RFE PPO]]. apply (ppo_in_ev src_well_formed a y PPO). }
    specialize (IHRFE_PPO Y_SRC_EV Z_SRC_EV).
    apply (rfe_ppo_to_ob X_SRC_EV Y_SRC_EV) in H.
    apply t_trans with (y := forw_ev Y_SRC_EV); auto.
Qed.

Lemma ppo_rfe_ppo_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO_RFE_PO : ((ppo src ⨾ rfe src)⁺ ⨾ ppo src) x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  destruct PPO_RFE_PO as [m [PPO_RFE PPO]].
  assert (M_SRC_EV : events src m).
  { apply (ppo_in_ev src_well_formed m y). auto. }
  assert (M_R : ev_r m).
  {
    apply clos_trans_t1n in PPO_RFE.
    induction PPO_RFE in m, x, PPO_RFE |-*.
    - destruct H as [a [_ RFE]].
      apply (rfeD src_well_formed) in RFE.
      unfold seq, eqv_rel in RFE. basic_solver.
    - apply IHPPO_RFE.
  }
  apply t_trans with (y := forw_ev M_SRC_EV).
  - apply (ppo_rfe_trans_to_ob X_SRC_EV M_SRC_EV PPO_RFE).
  - apply (ppo_left_r_to_ob M_SRC_EV Y_SRC_EV PPO M_R).
Qed.

Lemma rfe_ppo_rfe_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (RFE_PPO_RFE : ((rfe src ⨾ ppo src)⁺ ⨾ rfe src) x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
    destruct RFE_PPO_RFE as [m [RFE_PPO RFE]].
    assert (M_SRC_EV : events src m).
    { apply (rfe_in_ev src_well_formed m y). auto. }
    apply (rfe_ppo_trans_to_ob X_SRC_EV M_SRC_EV) in RFE_PPO.
    apply (rfe_to_ob M_SRC_EV Y_SRC_EV) in RFE.
    apply t_trans with (y := forw_ev M_SRC_EV); auto.
Qed.

(* Contradiction for sole ppo in hb *)

Lemma ppo_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (PPO : ppo src x y) (SAME_LOC : same_loc x y) (TRANS : (rf src ∪ mo src ∪ fr src)⁺ y x) (SC_PER_LOC : acyclic (po_loc_rf_mo_fr src)) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  apply (ppo_to_po) in PPO.
  assert (po_loc src x y) as PO_LOC.
  { split; basic_solver.  }
  assert ((po_loc_rf_mo_fr src)⁺ x x) as PO_LOC_RF_MO_FR.
  { 
    assert (po_loc src ⊆ po_loc_rf_mo_fr src) as PO_LOC_SUB.
    { intros. repeat left. auto. }
    assert ((rf src ∪ mo src ∪ fr src) ⊆ po_loc_rf_mo_fr src) as RF_MO_FR_SUB.
    { intros x1 y1 [[RF | MO] | FR]. do 2 left. right. auto. left. right. auto. right. auto. }
    apply PO_LOC_SUB, t_step in PO_LOC.
    apply clos_trans_mori in RF_MO_FR_SUB.
    apply RF_MO_FR_SUB in TRANS.
    apply t_trans with (y := y); auto.
  }
  exfalso. 
  apply (SC_PER_LOC x). 
  auto.
Qed.

Lemma hb_alt_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (HB_ALT : hb_alt src x y) (STAR : (rf src ∪ mo src ∪ fr src)＊ y x) (SC_PER_LOC : acyclic (po_loc_rf_mo_fr src)) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof. unfold hb_alt in *.
  apply split_hb_alt in HB_ALT. unfold hb_alt_split_rel, ob, bob in *.
  destruct HB_ALT as [[[[[PO|RFE]|PO_RFE]|RFE_PO]|PO_RFE_PO]|RFE_PO_RFE].
  - destruct (classic (x = y)) as [EQ | NEQ].
    + subst. apply (ppo_irreflexive src_well_formed) in PO. contradiction.
    + apply star_neq_trans in STAR; auto.
      pose proof (rf_mo_fr_trans_same_loc STAR) as SAME_LOC.
      apply (ppo_to_ob X_SRC_EV Y_SRC_EV PO (same_loc_sym _ _ SAME_LOC) STAR SC_PER_LOC).
  - apply rfe_to_ob; auto.
  - apply ppo_rfe_trans_to_ob. auto.
  - apply rfe_ppo_trans_to_ob. auto.
  - apply ppo_rfe_ppo_to_ob. auto.
  - apply rfe_ppo_rfe_to_ob. auto.
Qed.

(* Now for the left side, mo and fr extracted into moe \/ moi and fri \/ fre *)

Lemma mo_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (MO : mo src x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  apply external_internal in MO as [MOI | MOE].
  - apply (moiD src_well_formed) in MOI.
    destruct MOI as [x' [[? W_X] [y' [MOI [Y_EQ W_Y]]]]].
    destruct MOI as [MO PO].
    assert (ppo src x' y) as PPO.
    { unfold eqv_rel. exists x'. split; try basic_solver. }
    subst.
    apply (ppo_right_w_to_ob X_SRC_EV Y_SRC_EV PPO W_Y).
  - left. left. right.
    apply (forw_moe X_SRC_EV Y_SRC_EV).
    auto.
Qed.

Lemma fr_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (FR : fr src x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  apply external_internal in FR as [FRI | FRE].
  - apply (friD src_well_formed) in FRI.
    destruct FRI as [x' [[? W_X] [y' [FRI [Y_EQ W_Y]]]]].
    destruct FRI as [FR PO].
    assert (ppo src x' y) as PPO.
    { unfold eqv_rel. exists x'. split; try basic_solver. }
    subst.
    apply (ppo_left_r_to_ob X_SRC_EV Y_SRC_EV PPO W_X).
  - left. right.
    apply (forw_fre X_SRC_EV Y_SRC_EV).
    auto.
Qed.

Lemma coh_right_split_rel_to_ob {x y} (X_SRC_EV : events src x) (Y_SRC_EV : events src y) (COH_REL : coh_right_split_rel x y) : ob dst (forw_ev X_SRC_EV) (forw_ev Y_SRC_EV).
Proof.
  destruct COH_REL as [[MO | FR] | [m [FR MO]]].
  - apply mo_to_ob; auto.
  - apply fr_to_ob; auto.
  - assert (M_SRC_EV : events src m).
    { apply (fr_in_ev src_well_formed x m FR). }
    apply t_trans with (y := (forw_ev M_SRC_EV)).
    + apply fr_to_ob; auto.
    + apply mo_to_ob; auto.
Qed.

(* Final proof of the coh rel to hb mapping *)
  
Lemma coh_rel_to_ob {x} (X_SRC_EV : events src x)
  (COH_REL : coh_rel src x x) 
  (SC_PER_LOC : acyclic (po_loc_rf_mo_fr src)) : 
  exists y, ob dst y y.
Proof.
  apply split_coh_rel in COH_REL as [[HB STAR]| COH_REL].
  - exists (forw_ev X_SRC_EV). 
    apply (hb_alt_to_ob X_SRC_EV X_SRC_EV (hb_to_hb_alt HB) STAR SC_PER_LOC).
  - apply extract_mo_fr in COH_REL as [y [[HB STAR]|[z [HB RF_MO_FR]]] ].
    * assert (Y_SRC_EV: events src y).
      { apply (hb_in_ev src_well_formed y y HB). }
      exists (forw_ev Y_SRC_EV).
      apply (hb_alt_to_ob Y_SRC_EV Y_SRC_EV (hb_to_hb_alt HB) STAR SC_PER_LOC).
    * assert (events src y /\ events src z) as [Y_SRC_EV Z_SRC_EV].
      { apply (hb_in_ev src_well_formed y z HB). }
      exists (forw_ev Y_SRC_EV).
      apply t_trans with (y := forw_ev Z_SRC_EV).
      + assert ((rf src ∪ mo src ∪ fr src)＊ z y) as STAR.
        { 
          assert (mo src ∪ fr src ⊆ rf src ∪ mo src ∪ fr src).
          { intros x1 y1 [MO | FR]; basic_solver. }
          apply rt_unit.
          destruct RF_MO_FR as [m [? ?]]. exists m. 
          split; auto.
        }
        apply (hb_alt_to_ob Y_SRC_EV Z_SRC_EV (hb_to_hb_alt HB) STAR SC_PER_LOC).
      + apply split_coh_rel_right in RF_MO_FR.
        apply (coh_right_split_rel_to_ob Z_SRC_EV Y_SRC_EV RF_MO_FR).
Qed.