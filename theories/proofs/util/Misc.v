From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.
Require Import SrcDst.

Lemma po_split_left {label : Type} {label_class : label_class label} 
  {ex x z} (WF : well_formed ex) (PO : po ex x z) : po_imm ex x z \/ exists y, (po ex y z /\ po_imm ex x y).
Proof.
  apply (po_splittable WF) in PO.
  apply clos_trans_t1n_iff in PO.
  induction PO.
  - left. auto.
  - right.
    destruct IHPO;
    exists y;
    split; auto.
    + apply po_imm_to_po.  auto.
    + apply clos_trans_t1n_iff in PO.
      apply (po_splittable WF) in PO. 
      auto.
Qed. 

Lemma po_split_right {label : Type} {label_class : label_class label} 
  {ex x z} (WF : well_formed ex) (PO : po ex x z) : po_imm ex x z \/ exists y, (po ex x y /\ po_imm ex y z).
Proof.
  apply (po_splittable WF) in PO.
  apply clos_trans_tn1_iff in PO.
  induction PO.
  - left. auto.
  - right.
    destruct IHPO;
    exists y;
    split; auto.
    + apply po_imm_to_po. auto.
    + apply clos_trans_tn1_iff in PO.
      apply (po_splittable WF) in PO. 
      auto.
Qed.

Lemma po_imm_refl_right {label : Type} {label_class : label_class label} 
  {ex x y z} (WF: well_formed ex)
  (PO_IMM1: po_imm ex x z) (PO_IMM2: po_imm ex y z) 
  : x = y.
Proof.
  assert (events ex x /\ events ex y /\ events ex z) as [X_SRC_EV [Y_SRC_EV Z_SRC_EV]].
  { repeat split; try apply (po_imm_in_ev WF _ _ PO_IMM1). apply (po_imm_in_ev WF _ _ PO_IMM2). }
  assert  (exists t, (E ex ∩₁ (ev_init ∪₁ has_tid t)) x /\ (E ex ∩₁ (ev_init ∪₁ has_tid t)) y /\ (E ex ∩₁ (ev_init ∪₁ has_tid t)) z) as [t [X [Y Z]]].
  {
    apply po_imm_to_po, (po_stid WF) in PO_IMM1, PO_IMM2.
    destruct PO_IMM1 as [[EV_INIT EV] | SAME_TID], PO_IMM2 as [[EV_INIT' EV'] | SAME_TID'], z;
    try (
      exists t; 
      try inversion SAME_TID; try inversion SAME_TID'; 
      unfold has_tid, get_tid, same_tid in *; 
      repeat split; basic_solver
    );
    exists 0;
    try inversion SAME_TID; try inversion SAME_TID'; 
    unfold has_tid, get_tid, same_tid in *; 
    repeat split; try left; basic_solver.
  }
  unfold po_imm in *.
  apply (total_immediate_unique (po_total WF t)) with (c := z);
  auto.
Qed.
  
Lemma total_immediate_unique':
  forall {A} {r: A -> A -> Prop} {P: A -> Prop}
         (Tot: is_total P r)
         a b c (pa: P a) (pb: P b) (pc: P c)
         (iac: immediate r a b)
         (ibc: immediate r a c),
    b = c.
Proof.
  ins; destruct (classic (b = c)) as [|N]; eauto.
  exfalso; unfold immediate in *; desf.
  eapply Tot in N; eauto; desf; eauto.
Qed.

Lemma po_imm_refl_left {label : Type} {label_class : label_class label} 
  {ex x y z} (WF: well_formed ex) (PO_IMM1: po_imm ex x y) (PO_IMM2: po_imm ex x z) 
  (X_NOT_INIT : ~ ev_init x)
  : y = z.
Proof.
  assert (events ex x /\ events ex y /\ events ex z) as [X_SRC_EV [Y_SRC_EV Z_SRC_EV]].
  { repeat split; try apply (po_imm_in_ev WF _ _ PO_IMM1). apply (po_imm_in_ev WF _ _ PO_IMM2). }
  assert  (exists t, (E ex ∩₁ (ev_init ∪₁ has_tid t)) x /\ (E ex ∩₁ (ev_init ∪₁ has_tid t)) y /\ (E ex ∩₁ (ev_init ∪₁ has_tid t)) z) as [t [X [Y Z]]].
  {
    apply po_imm_to_po, (po_stid WF) in PO_IMM1, PO_IMM2.
    destruct PO_IMM1 as [[EV_INIT EV] | SAME_TID], PO_IMM2 as [[EV_INIT' EV'] | SAME_TID'], x;
    try (contradiction (X_NOT_INIT EV_INIT));
    try (contradiction (X_NOT_INIT EV_INIT'));
    try (
      exists t; 
      try inversion SAME_TID; try inversion SAME_TID'; 
      unfold has_tid, get_tid, same_tid in *; 
      repeat split; basic_solver
    );
    exists 0;
    try inversion SAME_TID; try inversion SAME_TID'; 
    unfold has_tid, get_tid, same_tid in *; 
    repeat split; try left; basic_solver.
  }
  unfold po_imm in *.
  apply (total_immediate_unique' (po_total WF t)) with (a := x);
  auto.
Qed.

Lemma star_neq_trans {A} {r : relation A} {x y} (STAR : r＊ x y) (NEQ : x <> y) : (r⁺ x y).
Proof.
  apply clos_refl_transE in STAR.
  destruct STAR as [EQ | STAR].
  - exfalso. apply NEQ. auto.
  - auto.
Qed.

Lemma map_rf_back :  forall x_dst y_dst x_dst_ev y_dst_ev (RF : rf dst x_dst y_dst), rf src (map_ev_back x_dst x_dst_ev ) (map_ev_back y_dst y_dst_ev).
Proof.
    intros.
    simpl in *.
    unfold src_rf, src_rel.
    exists x_dst, y_dst, RF. 
    basic_solver.
Qed.

Lemma map_po_back :  forall x_dst y_dst x_dst_ev y_dst_ev (PO : po dst x_dst y_dst), po src (map_ev_back x_dst x_dst_ev ) (map_ev_back y_dst y_dst_ev).
Proof.
    intros.
    simpl in *.
    unfold src_po, src_rel.
    exists x_dst, y_dst, PO. 
    basic_solver.
Qed.

Lemma map_ev_back_eq x y (X_SRC_EV : events dst x) (Y_SRC_EV : events dst y) (MAP : map_ev_back x X_SRC_EV = map_ev_back y Y_SRC_EV) :  x = y.
Proof.
    pose proof (unique_ids DST_WF) as H.
    apply H; auto.
    unfold map_ev_back in MAP.
    repeat match goal with
    | [H: context [match ?X with _ => _ end] |- _] => destruct X
    end; 
    inversion MAP; auto.
Qed.

Lemma map_ev_back_neq x y (X_SRC_EV : events dst x) (Y_SRC_EV : events dst y) (MAP : map_ev_back x X_SRC_EV <> map_ev_back y Y_SRC_EV) : x <> y.
Proof.
    unfold not in *. intros.
    apply MAP.
    unfold map_ev_back in *.
    basic_solver.
Qed.

Lemma map_mo_back :  forall x_dst y_dst x_dst_ev y_dst_ev (MO : mo dst x_dst y_dst), mo src (map_ev_back x_dst x_dst_ev ) (map_ev_back y_dst y_dst_ev).
Proof.
    intros.
    simpl in *.
    unfold src_mo, src_rel.
    exists x_dst, y_dst, MO. 
    basic_solver.
Qed.

