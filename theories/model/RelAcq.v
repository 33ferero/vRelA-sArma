From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.

(* Data type for release-acquire acceses *)
Inductive rel_acq_label :=
    | Racq (m : tag) (l : loc) (v : val)
    | Wrel (m : tag) (l : loc) (v : val).

(* Definitions for label_class instance *)
Inductive is_r_lab_impl : rel_acq_label -> Prop :=
| RacqLabR : forall m l v, is_r_lab_impl (Racq m l v).

Inductive is_w_lab_impl : rel_acq_label -> Prop :=
| WrelLabW : forall m l v, is_w_lab_impl (Wrel m l v).

Inductive is_f_lab_impl : rel_acq_label -> Prop :=.

Definition get_loc_impl a :=
    match a with
    | Racq _ l _ => Some l
    | Wrel _ l _ => Some l
    end.

Definition get_val_impl a :=
    match a with
    | Racq _ _ v => Some v
    | Wrel _ _ v => Some v
    end.

Definition get_mode_impl l :=
    match l with
    | Racq m _ _ => Some m
    | Wrel m _ _ => Some m
    end.

Instance rel_acq_label_class : label_class rel_acq_label :=
    {|
        is_r_lab := is_r_lab_impl ;
        is_w_lab := is_w_lab_impl ;
        is_f_lab := is_f_lab_impl ;
        get_mode := get_mode_impl ;
        get_loc := get_loc_impl ;
        get_val := get_val_impl ;
    |}.

(* Synchronizes with *)
Definition sw (ex : execution rel_acq_label ):= ⦗W⦘ ⨾ (rf ex) ⨾ ⦗R⦘.
(* Preserved program order *)
Definition ppo {label : Type} {_ : label_class label} (ex : execution label) := ⦗RW⦘ ⨾ po ex ⨾ ⦗RW⦘.
(* Happens before *)
Definition hb (ex : execution rel_acq_label) := (ppo ex ∪ sw ex)⁺.
(* Relation used in the coherence axiom, used so much might as well define it once *)
Definition coh_rel (ex : execution rel_acq_label) := (hb ex ⨾ (rf ex ∪ mo ex ∪ fr ex)＊).

(* Consistency property *)
Definition is_rel_acq_consistent (ex : execution rel_acq_label) :=
    irreflexive (coh_rel ex)
    /\ acyclic (po_loc_rf_mo_fr ex)
    /\ (rmw ex ∩ (fr ex ⨾ mo ex ) ⊆ ∅₂).

Inductive rel_acq_r_eq (t : tag) (l : loc) (v : val) : event rel_acq_label -> Prop :=
    | RacqEq : forall uid tid, rel_acq_r_eq t l v (Ev uid tid (Racq t l v)).

Inductive rel_acq_w_eq (t : tag) (l : loc) (v : val) : event rel_acq_label -> Prop :=
    | WrelEq : forall uid tid, rel_acq_w_eq t l v (Ev uid tid (Wrel t l v)).

Lemma equiv_sw_rf {ex} (WF: well_formed ex) : sw ex ≡ rf ex.
Proof.
    split.
    - intros x y SW.
      destruct SW as [? [[X_EQ] [? [RF [Y_EQ ]]]]].
      subst.
      auto.
    - intros x y RF.
      apply (rfD WF) in RF.
      auto.
Qed.


(* Lemmas about ppo, derived from po *)
Lemma ppo_trans {label : Type} {_ : label_class label} {ex : execution label} (WF : well_formed ex) : transitive (ppo ex).
Proof.
    pose proof (po_trans WF).
    intros x y z H1 H2.
    unfold ppo in *.
    destruct H1 as [? [[]  [? [? [? []]]]]];
    destruct H2 as [? [[]  [? [? [? []]]]]];
    subst;
    basic_solver.
Qed.

Lemma ppo_to_po {label : Type} {_ : label_class label} {ex : execution label} {x y} (PPO : ppo ex x y) : po ex x y.
Proof.
    destruct PPO as [? [[]  [? [? [? []]]]]];
    basic_solver.
Qed.

Lemma ppo_irreflexive {label : Type} {_ : label_class label} {ex : execution label} (WF : well_formed ex) : irreflexive (ppo ex).
Proof.
    intros x PPO.
    apply (po_irrefl WF x).
    apply ppo_to_po in PPO.
    auto.
Qed.

Lemma subset_ppo_external {label : Type} {_ : label_class label} ex (REL : execution label -> relation (event label)) (DOM : dom_rel (REL ex) ∪₁ codom_rel (REL ex) ⊆₁ RW) : ppo ex ∪ (REL ex) ⊆ ppo ex ∪ external REL ex.
Proof.
  intros x y H.
  destruct H.
  - left. auto.
  - apply external_internal in H; destruct H.
  + assert (H1 : RW x). apply DOM.
    left. exists y. auto. destruct H. auto.
    assert (H2 : RW y). apply DOM.
    right. exists x. auto. destruct H. auto.
    left. exists x; repeat split; auto. exists y; repeat split; auto.
    destruct H. auto.
  + right. auto.
Qed.

Lemma ppo_in_ev {label : Type} {_ : label_class label} {ex : execution label} (WF: well_formed ex) x y (PPO: ppo ex x y) : events ex x /\ events ex y.
Proof.
    destruct PPO as [? [X_EQ  [? [PO [? [ ]]]]]];
    destruct X_EQ;
    subst;
    apply (po_in_ev); auto.
Qed.

(* Lemmas about the coh relation *)
Lemma hb_in_ev {ex} (WF: well_formed ex) x y (HB: hb ex x y) : events ex x /\ events ex y.
Proof.
    induction HB.
    - destruct H as [PPO | SW].
        + apply (ppo_in_ev WF x y PPO).
        + apply (equiv_sw_rf WF) in SW.
          apply (rf_in_ev WF x y SW).
    - basic_solver.
Qed.

Lemma coh_rel_in_ev {ex} (WF: well_formed ex) x y (COH_REL: coh_rel ex x y) : E ex x.
Proof.
    unfold coh_rel in *.
    destruct COH_REL as [x1 [HB STAR]].
    apply (hb_in_ev WF x x1 HB).
Qed.