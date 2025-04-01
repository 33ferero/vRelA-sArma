From hahn Require Import Hahn.
Require Import Event.
Require Import Execution.

(* Tag kind, between writes, from read, or full *)
Inductive f_mode := ww | rm | full.

(* Data type for simplified arm acceses *)
Inductive simpl_arm_label :=
    | Rd (m : tag) (l : loc) (v : val)
    | Wr (m : tag) (l : loc) (v : val)
    | Fe (m : f_mode).
    
(* Definitions for label_class instance *)
Inductive is_r_lab_impl : simpl_arm_label -> Prop :=
    | RdLabR : forall m l v, is_r_lab_impl (Rd m l v).

Inductive is_w_lab_impl : simpl_arm_label -> Prop :=
    | WrLabW : forall m l v, is_w_lab_impl (Wr m l v).

Inductive is_f_lab_impl : simpl_arm_label -> Prop :=
    | FeLabF : forall m, is_f_lab_impl (Fe m).

Definition get_loc_impl l :=
    match l with
    | Rd _ l _ => Some l
    | Wr _ l _ => Some l
    | Fe _ => None
    end.

Definition get_val_impl v :=
    match v with
    | Rd _ _ v => Some v
    | Wr _ _ v => Some v
    | Fe _ => None
    end.

Definition get_mode_impl m :=
    match m with
    | Rd m _ _ => Some m
    | Wr m _ _ => Some m
    | Fe m => None
    end.

Instance simpl_arm_label_class : label_class simpl_arm_label :=
    {|
        is_r_lab := is_r_lab_impl ;
        is_w_lab := is_w_lab_impl ;
        is_f_lab := is_f_lab_impl ;
        get_mode := get_mode_impl ;
        get_loc := get_loc_impl ;
        get_val := get_val_impl ;
    |}.

Inductive simpl_arm_r_eq (t : tag) (l : loc) (v : val) : event simpl_arm_label -> Prop :=
    | RdEq : forall uid tid, simpl_arm_r_eq t l v (Ev uid tid (Rd t l v)).

Inductive simpl_arm_w_eq (t : tag) (l : loc) (v : val) : event simpl_arm_label -> Prop :=
    | WrEq : forall uid tid, simpl_arm_w_eq t l v (Ev uid tid (Wr t l v)).

Inductive simpl_arm_f_eq (m : f_mode) : event simpl_arm_label -> Prop :=
    | FeEq : forall uid tid, simpl_arm_f_eq m (Ev uid tid (Fe m)).


Notation "'F_rm'" := (fun e => simpl_arm_f_eq rm e).
Notation "'F_ww'" := (fun e => simpl_arm_f_eq ww e).
Notation "'F_full'" := (fun e => simpl_arm_f_eq full e).
(* Barrier-order-by relation *)
Definition bob (ex : execution simpl_arm_label) := 
    (po ex ⨾ ⦗F_full⦘ ⨾ po ex) 
    ∪ (⦗R⦘ ⨾ po ex ⨾ ⦗F_rm⦘ ⨾ po ex) 
    ∪ (⦗W⦘ ⨾ po ex ⨾ ⦗F_ww⦘ ⨾ po ex ⨾ ⦗W⦘)
    ∪ (⦗R_t trmw ⦘ ⨾ po ex)
    ∪ (po ex ⨾ ⦗W_t trmw⦘).
(* Ordered-by relation *)
Definition ob ex := (bob ex ∪ rfe ex ∪ moe ex ∪ fre ex)⁺.

(* Simplified arm consistency *)
Definition is_simpl_arm_consistent (ex : execution simpl_arm_label) :=
    irreflexive (ob ex)
    /\ acyclic (po_loc_rf_mo_fr ex)
    /\ (rmw ex ∩ (fr ex ⨾ mo ex ) ⊆ ∅₂).