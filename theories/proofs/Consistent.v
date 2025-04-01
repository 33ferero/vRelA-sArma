From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.
Require Import Relations.
Require Import Coq.Logic.JMeq.
Require Import WellFormed.
Require Import ObMap.
Require Import Coq.Relations.Relation_Operators.

Lemma src_atomic : (rmw src ∩ (fr src ⨾ mo src ) ⊆ ∅₂).
Proof.
    intros x y SRC_REL.
    destruct SRC_REL as [RMW [z [FR MO]]].
    assert (E src x /\ E src y /\ E src z) as [X_SRC_EV [Y_SRC_EV Z_SRC_EV]].
    { 
      split. apply (rmw_in_ev src_well_formed x y RMW). 
      split; apply (mo_in_ev src_well_formed z y MO). 
    }
    pose proof DST_CONS as [_ [_ DST_ATOM]].
    apply DST_ATOM with (x := forw_ev X_SRC_EV) (y := forw_ev Y_SRC_EV).
    split.
    - apply (forw_rmw X_SRC_EV Y_SRC_EV RMW).
    - exists (forw_ev Z_SRC_EV).
      split.
      * apply (forw_fr X_SRC_EV Z_SRC_EV FR).
      * apply (forw_mo Z_SRC_EV Y_SRC_EV MO).
Qed.

Lemma sc_per_loc : acyclic (po_loc_rf_mo_fr src).
Proof.
    intros x SRC_PO_LOC_RF_MO_FR.
    assert (X_SRC_EV: events src x).
    { apply (po_loc_rf_mo_fr_trans_in_ev src_well_formed x x SRC_PO_LOC_RF_MO_FR). }
    pose proof DST_CONS as [_ [DST_PO_LOC_RF_MO_FR_ACY _]].
    apply DST_PO_LOC_RF_MO_FR_ACY with (x := forw_ev X_SRC_EV).
    apply forw_po_loc_rf_mo_fr_trans with (x_ev := X_SRC_EV) (y_ev := X_SRC_EV).
    auto.
Qed.

Lemma coh : irreflexive (hb src ⨾ (rf src ∪ mo src ∪ fr src)＊).
Proof.
  intros x COH_REL.
  assert (X_SRC_EV : events src x).
  { apply (coh_rel_in_ev src_well_formed x x COH_REL). }
  pose proof DST_CONS as [OB_ACY].
  pose proof (coh_rel_to_ob X_SRC_EV COH_REL sc_per_loc) as [y].
  apply (OB_ACY y).
  auto.
Qed.

Lemma src_consistent : is_rel_acq_consistent src.
Proof.
  split; [|split].
    - apply coh.
    - apply sc_per_loc.
    - apply src_atomic.
Qed.
        
