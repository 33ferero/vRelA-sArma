From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.
Require Import WellFormed.
Require Import Relations.
Require Import Misc.

Lemma subset_src_dst : behavior src ⊆ behavior dst.
Proof.
  intros loc val [x_src [X_SRC_EV [W_X [VAL_SRC_X [LOC_SRC_X MO_SRC_MAX]]]]].
  exists (forw_ev X_SRC_EV).
  repeat split; 
  try by (apply_forw as [? [?]]; unfold map_ev_back in *; basic_solver).
  + apply (forw_ev_w X_SRC_EV) in W_X. auto.
  + intros y_dst MO.
    assert (Y_DST_EV: E dst y_dst).
    { apply (mo_in_ev DST_WF (forw_ev X_SRC_EV) y_dst MO). }
    apply MO_SRC_MAX with (b := map_ev_back y_dst Y_DST_EV).
    unfold map_ev_back in *. 
    apply_forw as [x_dst [X_DST_EV]].
    exists x_dst, y_dst, MO.
    basic_solver.
Qed.

Lemma subset_dst_src : behavior dst ⊆ behavior src.
Proof.
  intros loc val [x_dst [X_DST_EV [W_X [VAL_DST_X [LOC_DST_X MO_DST_MAX]]]]].
  exists (map_ev_back x_dst X_DST_EV).
  repeat split.
  + exists x_dst, X_DST_EV. 
    reflexivity.
  + destruct x_dst; try destruct s; 
    inversion W_X as [? ? ? IS_W_LAB|]; try inversion IS_W_LAB;
    repeat econstructor.
  + unfold has_val in *. destruct x_dst; try destruct s; auto; basic_solver.
  + unfold has_loc in *. destruct x_dst; try destruct s; auto; basic_solver.
  + intros y_src MO.
    assert (Y_SRC_EV: E src y_src).
    { apply (mo_in_ev src_well_formed (map_ev_back x_dst X_DST_EV) y_src MO). }
    apply MO_DST_MAX with (b := forw_ev Y_SRC_EV).
    apply_forw as [y_dst [Y_DST_EV]].
    destruct MO as [x_dst2 [y_dst2 [MO_DST]]].
    destruct (mo_in_ev DST_WF x_dst2 y_dst2 MO_DST).
    repeat (match goal with
    | [H: context[ _ /\ _ ] |- _] => destruct H
    | [H: context[map_ev_back _ _ = map_ev_back _ _] |- _] => apply map_ev_back_eq in H
    end; subst).
    auto.
Qed.

Lemma behavior_proof : behavior src ≡ behavior dst.
Proof.
  split.
    - apply subset_src_dst.
    - apply subset_dst_src.
Qed. 
