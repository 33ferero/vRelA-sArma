From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import Mapping.
Require Import Consistent.
Require Import Behavior.
Require Import SrcDst.
Require Import WellFormed.

(* The destination and its hypotheses are defined in /proofs/util/SrcDst.v *)
Lemma mapping_correct : 
    exists src, well_formed src 
    /\ is_mapping src dst 
    /\ is_rel_acq_consistent src 
    /\ behavior src ≡ behavior dst.
Proof.
    exists src.
    split; [|split; [|split]].
    - apply src_well_formed.
    - apply mapping_proof.
    - apply src_consistent.
    - apply behavior_proof.
Qed.
