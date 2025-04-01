From hahn Require Import Hahn.
From Coq Require Import IndefiniteDescription.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.
Require Import WellFormed.
Require Import Misc.

Ltac forw_f_solver :=
    repeat apply_forw;
    repeat (
      match goal with
      | [H: context[match ?X with _ => _ end] |- _] => destruct X (* as [X_DST_EV Y_DST_EV]*)
      | [H: context[ _ /\ _ ] |- _] => destruct H (* as [X_EQ Y_EQ] *)
      | [H: context[exists _, _] |- _] => destruct H 
      | [H: context[map_ev_back _ _ = map_ev_back _ _] |- _] => apply map_ev_back_eq in H
      end;
      subst
    );
    auto.

Lemma forw_po {x} {y} 
  (X_EV_SRC : events src x) (Y_EV_SRC : events src y) 
  (PO_SRC : po src x y) 
  : po dst (forw_ev X_EV_SRC) (forw_ev Y_EV_SRC).
Proof.
    destruct PO_SRC as [x_dst [y_dst [PO_DST H]]].
    forw_f_solver.
Qed.

Lemma forw_mo {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (MO_SRC : mo src x y) 
  : mo dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    simpl in *.
    unfold src_rel in *.
    destruct MO_SRC as [x_dst [y_dst [MO_DST H]]].
    forw_f_solver.
Qed.

Lemma forw_rf {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (RF_SRC : rf src x y) 
  : rf dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    destruct RF_SRC as [x_dst [y_dst [RF_DST H]]].
    forw_f_solver.
Qed.

Lemma forw_rmw {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (RMW_SRC : rmw src x y) 
  : rmw dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    destruct RMW_SRC as [x_dst [y_dst [RMW_DST H]]].
    forw_f_solver.
Qed.

Lemma forw_fr {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (FR_SRC : fr src x y) 
  : fr dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    unfold fr, seq, transp.
    unfold src_rel in *. simpl in *. unfold src_rel in *.
    destruct FR_SRC as [z_src [[z_dst [x_dst [RF_DST H1]]] [z_dst2 [y_dst [MO_DST H2]]]]].
    exists z_dst.
    repeat forw_f_solver.
Qed.

Lemma forw_po_loc {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (PO_LOC_SRC : po_loc src x y) 
  : po_loc dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    destruct PO_LOC_SRC as [[x_src [y_src [PO_SRC H1]]] [l [PO_LOC_DST H]]].
    split. 
    - forw_f_solver.
    - forw_f_solver.
      unfold has_loc, map_ev_back, get_loc, same_loc in *.
      basic_solver.
Qed.
  
Lemma forw_po_loc_rf_mo_fr_f {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (PO_LOC_RF_MO_FR : po_loc_rf_mo_fr src x y) 
  : po_loc_rf_mo_fr dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    destruct PO_LOC_RF_MO_FR as [[[PO_LOC | RF ] | MO ] | FR].
    - repeat left. apply (forw_po_loc x_ev y_ev PO_LOC). 
    - left. left. right. apply (forw_rf x_ev y_ev RF).
    - left. right. apply (forw_mo x_ev y_ev MO).
    - right. apply (forw_fr x_ev y_ev FR).
Qed.

Lemma forw_po_loc_rf_mo_fr_trans {x} {y}
(x_ev : events src x) (y_ev : events src y)
(PO_LOC_RF_MO_FR : (po_loc_rf_mo_fr src)⁺ x y)
: (po_loc_rf_mo_fr dst)⁺ (forw_ev x_ev) (forw_ev y_ev).
Proof.
  induction PO_LOC_RF_MO_FR.
  - left. apply (forw_po_loc_rf_mo_fr_f x_ev y_ev H).
  - rename y_ev into z_ev.
    assert (y_ev: events src y).
    { apply (po_loc_rf_mo_fr_trans_in_ev src_well_formed x y PO_LOC_RF_MO_FR1). }
    specialize (IHPO_LOC_RF_MO_FR1 x_ev y_ev).
    specialize (IHPO_LOC_RF_MO_FR2 y_ev z_ev).
    apply transitive_ct with (y := forw_ev y_ev);
    auto.
Qed.

Lemma forw_rfe {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (RFE_SRC : rfe src x y) 
  : rfe dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    destruct RFE_SRC. split.
    - apply (forw_rf x_ev y_ev H).
    - intros H1. apply H0.
      repeat apply_forw.
      exists x0, x2.
      exists H1. 
      basic_solver.
Qed.

Lemma forw_moe {x} {y} 
  (x_ev : events src x) (y_ev : events src y) 
  (MOE_SRC : moe src x y) 
  : moe dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
    destruct MOE_SRC. split.
    - apply (forw_mo x_ev y_ev H).
    - intros H1. apply H0.
      repeat apply_forw.
      exists x0, x2.
      exists H1. 
      basic_solver.
Qed.

Ltac exists_solve x := exists x; repeat split; auto.

Lemma forw_ppo {x} {y} 
(x_ev : events src x) (y_ev : events src y) 
(PPO : ppo src x y) 
: (⦗RW⦘ ⨾ po dst ⨾ ⦗RW⦘) (forw_ev x_ev) (forw_ev y_ev).
Proof.
  destruct PPO as [? [[? [X_R|X_W]]  [t [PO [a [Y_R | Y_W ]]]]]];
  subst;
  apply (forw_po x_ev y_ev) in PO;
  try apply (forw_ev_r x_ev) in X_R;
  try apply (forw_ev_r y_ev) in Y_R;
  try apply (forw_ev_w x_ev) in X_W;
  try apply (forw_ev_w y_ev) in Y_W;
  exists_solve (forw_ev x_ev); exists_solve (forw_ev y_ev).  
Qed.

Lemma forw_fre {x} {y}
(x_ev : events src x) (y_ev : events src y)
(FRE : fre src x y)
: fre dst (forw_ev x_ev) (forw_ev y_ev).
Proof.
  destruct FRE. split.
  - apply (forw_fr x_ev y_ev H).
  - intros H1. apply H0.
    repeat apply_forw.
    exists x0, x2.
    exists H1. 
    basic_solver.
Qed.