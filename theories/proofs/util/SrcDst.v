From hahn Require Import Hahn.
From Coq Require Import IndefiniteDescription.
Require Import Event.
Require Import Execution.
Require Import RelAcq.
Require Import SimplArm.

(* Record that indicates simplArm execution was mapped from release-acquire *)
Record is_mapping_restricted (ex : execution simpl_arm_label) :=
    {
        rd_fe_left : forall a (A_EV : events ex a) (r : ev_r_t tmov a), exists b, po_imm ex a b /\ simpl_arm_f_eq rm b ;
        rf_fe_right : forall b (B_EV : events ex b) (f : simpl_arm_f_eq rm b), exists a, po_imm ex a b /\ ev_r_t tmov a ;

        fe_wr_left : forall a (A_EV : events ex a) (f : simpl_arm_f_eq ww a), exists b, po_imm ex a b /\ ev_w_t tmov b ;
        fe_wr_right : forall b (B_EV : events ex b) (w : ev_w_t tmov b), exists a, po_imm ex a b /\ simpl_arm_f_eq ww a 
    }.

(* Hypotheses for the main lemma *)
Parameter dst : execution simpl_arm_label.
Axiom DST_WF : well_formed dst.
Axiom DST_CONS : is_simpl_arm_consistent dst.
Axiom DST_RESTR : is_mapping_restricted dst.

Definition map_ev_back x (_ : events dst x) := 
    match x with
    | Ev u t (Rd m l v) => Ev u t (Racq m l v)
    | Ev u t (Wr m l v) => Ev u t (Wrel m l v)
    | Ev u t (Fe _) => EvSkip u t
    | EvSkip u t => EvSkip u t
    | EvInit u l v => EvInit u l v
    end.

(* Definition of source from dst *)
Definition src_events x_src := 
    exists x_dst x_dst_ev, map_ev_back x_dst x_dst_ev = x_src.

Definition src_rel rel (in_ev : forall x y, rel x y -> events dst x /\ events dst y) x_src y_src :=
    exists x_dst y_dst rel_x_y, let (x_dst_ev, y_dst_ev) := in_ev x_dst y_dst rel_x_y 
        in map_ev_back x_dst x_dst_ev = x_src /\ map_ev_back y_dst y_dst_ev = y_src.

Definition src_po := src_rel (po dst) (po_in_ev DST_WF).
Definition src_rf := src_rel (rf dst) (rf_in_ev DST_WF).
Definition src_mo := src_rel (mo dst) (mo_in_ev DST_WF).
Definition src_rmw := src_rel (rmw dst) (rmw_in_ev DST_WF).

Definition src : execution rel_acq_label :=
    {| events := src_events ;
       po := src_po ;
       rf := src_rf ;
       mo := src_mo ;
       rmw := src_rmw ;
    |}.

(* Forward mapping of common predicates *)
Definition forw_ev {x} (X_SRC_EV : events src x) : event simpl_arm_label.
Proof. 
    destruct (constructive_indefinite_description _ (X_SRC_EV)) as [X_DST].
    exact X_DST.
Defined.

Definition forw_events {x} (X_SRC_EV : events src x) : events dst (forw_ev X_SRC_EV).
Proof.
    unfold forw_ev.
    destruct constructive_indefinite_description as [x_dst [X_DST_EV]].
    exact X_DST_EV.
Defined.

Tactic Notation "apply_forw" "as"  simple_intropattern(H) :=
    unfold forw_ev in *;
    destruct constructive_indefinite_description as H.

Tactic Notation "apply_forw" :=
    unfold forw_ev in *;
    destruct constructive_indefinite_description as [? [? ?]].

Lemma forw_uid {x} (X_SRC_EV : events src x) : get_uid x = get_uid (forw_ev X_SRC_EV).
Proof.
    apply_forw as [x_dst [X_DST_EV]].
    rewrite <- H.
    unfold map_ev_back.
    basic_solver.
Qed.

Lemma forw_ev_r {x} (X_SRC_EV : events src x) (R_X_SRC : ev_r x) : ev_r (forw_ev X_SRC_EV).
Proof.
    apply_forw as [x_dst [X_DST_EV]].
    unfold map_ev_back in H.
    inversion R_X_SRC as [? ? ? IS_R_LAB].
    inversion IS_R_LAB.
    basic_solver.
Qed.

Lemma forw_ev_w {x} (X_SRC_EV : events src x) (W_X_SRC : ev_w x) : ev_w (forw_ev X_SRC_EV).
Proof.
    apply_forw as [x_dst [X_DST_EV]].
    unfold map_ev_back in H.
    inversion W_X_SRC as [? ? ? IS_W_LAB | ? ? TMOV].
    + inversion IS_W_LAB.
      subst.
      destruct x_dst eqn:X; try destruct s; 
      try basic_solver.
      repeat econstructor.
    + destruct x_dst eqn:X; try destruct s;
      try basic_solver.
      repeat econstructor.
Qed.

Lemma forw_rw {x} (X_SRC_EV : events src x) (RW_X_SRC : ev_r x \/ ev_w x) : RW (forw_ev X_SRC_EV).
Proof.
    destruct RW_X_SRC as [R | W].
    - left. apply forw_ev_r; auto.
    - right. apply forw_ev_w; auto.
Qed.

Lemma forw_ev_r_t {x m} (X_SRC_EV : events src x) (R_T_X_SRC : ev_r_t m x) : ev_r_t m (forw_ev X_SRC_EV).
Proof.
    apply_forw as [x_dst [X_DST_EV]].
    unfold map_ev_back in H.
    inversion R_T_X_SRC.
    inversion is_r.
    basic_solver.
Qed.

Lemma forw_ev_w_t {x m} (X_SRC_EV : events src x) (W_T_X_SRC : ev_w_t m x) : ev_w_t m (forw_ev X_SRC_EV).
Proof.
    apply_forw as [x_dst [X_DST_EV]].
    unfold map_ev_back in H.
    inversion W_T_X_SRC.
    inversion is_w.
    * destruct x_dst; try destruct s; subst;
      try basic_solver.
      inversion H0. inversion m0.
      subst. repeat econstructor.
    * destruct x_dst; try destruct s;
      try basic_solver.
      repeat econstructor.
      auto.
Qed.
