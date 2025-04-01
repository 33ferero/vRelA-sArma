From hahn Require Import Hahn.
Require Import Event.

(* Execution is record of unary/binary relations *)
(* Each relation is a proof that it holds for the events in this execution *)
Record execution (label : Type) {label_class : label_class label} :=
    { events : event label -> Prop ;
      po : event label -> event label -> Prop ;
      rf : event label -> event label -> Prop ;
      mo : event label -> event label -> Prop ;
      rmw : event label -> event label -> Prop ;
    }.

Arguments events {label} {label_class}.
Arguments po {label} {label_class}.
Arguments rf {label} {label_class}.
Arguments mo {label} {label_class}.
Arguments rmw {label} {label_class}.

(* Some basic rules must hold in a execution for it to be valid *)
(* We only specify the ones we need for proofs *)
Record well_formed {label : Type} {label_class : label_class label} (ex : execution label)  :=
  { 
    unique_ids : forall x y, events ex x -> events ex y -> get_uid x = get_uid y -> x = y ;
    po_trans : transitive (po ex) ; 
    mo_trans : transitive (mo ex) ;
    po_irrefl : irreflexive (po ex) ;
    rfD : (rf ex) ≡ ⦗W⦘ ⨾ (rf ex) ⨾ ⦗R⦘ ;
    moD : (mo ex) ≡ ⦗W⦘ ⨾ (mo ex) ⨾ ⦗W⦘ ;
    rft_functional : functional (rf ex)⁻¹ ;
    rf_same_loc : (rf ex) ⊆ same_loc ;
    mo_same_loc : (mo ex) ⊆ same_loc ;
    po_elements : dom_rel (po ex) ∪₁ codom_rel (po ex) ⊆₁ events ex ;
    rf_elements : dom_rel (rf ex) ∪₁ codom_rel (rf ex) ⊆₁ events ex ;
    mo_elements : dom_rel (mo ex) ∪₁ codom_rel (mo ex) ⊆₁ events ex ;
    rmw_elements : dom_rel (rmw ex) ∪₁ codom_rel (rmw ex) ⊆₁ events ex ;
    po_splittable : po ex ≡ (immediate (po ex))⁺ ;
    po_stid : po ex ⊆ ((ev_init × ev) ∪ same_tid) ;
    po_total : forall (t : tid), is_total (events ex ∩₁ (ev_init ∪₁ has_tid t)) (po ex) ;
    }.

Arguments unique_ids {label} {label_class} {ex}.
Arguments po_trans {label} {label_class} {ex}.
Arguments mo_trans {label} {label_class} {ex}.
Arguments po_irrefl {label} {label_class} {ex}.
Arguments rfD {label} {label_class} {ex}.
Arguments moD {label} {label_class} {ex}.
Arguments rft_functional {label} {label_class} {ex}.
Arguments rf_same_loc {label} {label_class} {ex}.
Arguments mo_same_loc {label} {label_class} {ex}.
Arguments po_elements {label} {label_class} {ex}.
Arguments rf_elements {label} {label_class} {ex}.
Arguments mo_elements {label} {label_class} {ex}.
Arguments rmw_elements {label} {label_class} {ex}.
Arguments po_splittable {label} {label_class} {ex}.
Arguments po_stid {label} {label_class} {ex}.
Arguments po_total {label} {label_class} {ex}.

(* Definitions of derived events *)
Definition fr {label : Type} {_ : label_class label} ex := (rf ex)⁻¹ ⨾ (mo ex).

Definition po_loc {label : Type} {_ : label_class label} ex := po ex ∩ same_loc.
Definition po_imm {label : Type} {_ : label_class label} ex := immediate (po ex).

Definition internal {label : Type} {_ : label_class label} r ex := r ex ∩ po ex.
Definition external {label : Type} {_ : label_class label} r ex := r ex \ po ex.

Definition moe {label : Type} {_ : label_class label} := external (mo).
Definition fre {label : Type} {_ : label_class label} := external (fr).
Definition rfe {label : Type} {_ : label_class label} := external (rf).
Definition moi {label : Type} {_ : label_class label} := internal (mo).
Definition fri {label : Type} {_ : label_class label} := internal (fr).
Definition rfi {label : Type} {_ : label_class label} := internal (rf).

(* Behavior of an event is a relation on location/value pairs *)
(* It is the final values of all shared memory locations, i.e. the final event in the modification order *)
Definition behavior {label : Type} {_ : label_class label} ex l v :=
    exists ev, events ex ev 
      /\ W ev 
      /\ has_val v ev 
      /\ has_loc l ev 
      /\ max_elt (mo ex) ev.

(* This re;lation is used a lot so might as well define it once *)
Definition po_loc_rf_mo_fr {label : Type} {label_class : label_class label} 
  (ex : execution label) := (po_loc ex ∪ rf ex ∪ mo ex ∪ fr ex).

Lemma fr_same_loc {label : Type} {_ : label_class label} {ex} 
  (WF: well_formed ex) : (fr ex) ⊆ same_loc.
Proof.
  unfold fr. rewrite (rf_same_loc WF), (mo_same_loc WF).
  unfold transp, seq. simpl.
  intros x y H.
  destruct H. unfold same_loc in *. destruct H as [[l [X0 XA]] [l1 [X01 Y]]].
  assert (l = l1).
  { unfold has_loc in *. basic_solver. }
  subst. exists l1. split; auto.
Qed.

(* Taken from weakmemory/imm *)
Lemma re_dom {label : Type} {_ : label_class label} 
  ex (r : execution label -> relation (event label)) 
  d1 d2 (DOM: r ex ≡ ⦗d1⦘ ⨾ r ex ⨾ ⦗d2⦘) 
  : r ex \ po ex ⊆ ⦗d1⦘ ⨾ (r ex \ po ex) ⨾ ⦗d2⦘.
Proof using. rewrite DOM at 1; basic_solver. Qed.

(* Taken from weakmemory/imm *)
Lemma ri_dom {label : Type} {_ : label_class label} 
  ex (r : execution label -> relation (event label)) 
  d1 d2 (DOM: r ex ≡ ⦗d1⦘ ⨾ r ex ⨾ ⦗d2⦘) 
  : r ex ∩ po ex ⊆ ⦗d1⦘ ⨾ r ex ∩ po ex ⨾ ⦗d2⦘.
Proof using. rewrite DOM at 1; basic_solver. Qed.

(* Lemmas about what events can occur on the left and right of derived events *)
Lemma rfeD {label : Type} {_ : label_class label} {ex} 
  (WF : well_formed ex) : (rfe ex) ≡ ⦗W⦘ ⨾ (rfe ex) ⨾ ⦗R⦘ .
Proof using. split; [|basic_solver]. apply (re_dom ex rf W R (rfD WF)). Qed.

Lemma moiD {label : Type} {_ : label_class label} {ex} 
  (WF : well_formed ex) : (moi ex) ≡ ⦗W⦘ ⨾ (moi ex) ⨾ ⦗W⦘ .
Proof using. split; [|basic_solver]. apply (ri_dom ex mo W W (moD WF)). Qed.

Lemma frD {label : Type} {_ : label_class label} {ex} 
  (WF : well_formed ex) : (fr ex) ≡ ⦗R⦘ ⨾ (fr ex) ⨾ ⦗W⦘ .
Proof.
    unfold fr. split; [|basic_solver].
    intros x z FR.
    destruct FR as [y [RF MO]].
    apply (rfD WF) in RF.
    apply (moD WF) in MO.
    unfold eqv_rel, seq in *.
    destruct RF as [? [[?] [? [? [R_X]]]]].
    exists x. split; try basic_solver.
    exists z. split; try basic_solver.
Qed.

Lemma friD {label : Type} {_ : label_class label} {ex} 
  (WF : well_formed ex) : (fri ex) ≡ ⦗R⦘ ⨾ (fri ex) ⨾ ⦗W⦘ .
Proof using. split; [|basic_solver]. apply (ri_dom ex fr R W (frD WF)). Qed.

(* Proofs that a relation between events also mean they are in the execution *)
(* i.e. the `events` predicate holds *)
Lemma rel_in_ev {label : Type} {_ : label_class label} ex x y
  (rel : execution label -> relation (event label))
  (REL: rel ex x y)
  (H : dom_rel (rel ex) ∪₁ codom_rel (rel ex) ⊆₁ events ex)
   : events ex x /\ events ex y.
Proof.
  intros.
  split.
  - apply H. unfold set_union, codom_rel, dom_rel. left. exists y. apply REL.
  - apply H. unfold set_union. right. unfold codom_rel. exists x. apply REL.
Qed.

Lemma po_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (PO: po ex x y) : events ex x /\ events ex y.
Proof. apply (rel_in_ev ex x y (po) PO (po_elements WF)). Qed.

Lemma rf_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (RF: rf ex x y) : events ex x /\ events ex y.
Proof. apply (rel_in_ev ex x y (rf) RF (rf_elements WF)). Qed.

Lemma mo_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (MO: mo ex x y) : events ex x /\ events ex y.
Proof. apply (rel_in_ev ex x y (mo) MO (mo_elements WF)). Qed.

Lemma rmw_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (RMW: rmw ex x y) : events ex x /\ events ex y.
Proof. apply (rel_in_ev ex x y (rmw) RMW (rmw_elements WF)). Qed.

Lemma fr_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (FR: fr ex x y) : events ex x /\ events ex y.
Proof.
  intros.
  destruct FR as [z [RF MO]].
  apply rf_in_ev in RF; auto.
  apply mo_in_ev in MO; auto.
  destruct RF, MO.
  split; auto.
Qed.

Lemma po_loc_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (PO_LOC: po_loc ex x y) : events ex x /\ events ex y.
Proof. destruct PO_LOC. apply po_in_ev in H; auto. Qed.

Lemma po_imm_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (PO_IMM: po_imm ex x y) : events ex x /\ events ex y.
Proof. destruct PO_IMM. apply po_in_ev in H; auto. Qed.

Lemma po_loc_rf_mo_fr_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (PO_LOC_RF_MO_FR: po_loc_rf_mo_fr ex x y) : events ex x /\ events ex y.
Proof.
    destruct PO_LOC_RF_MO_FR as [[[PO_LOC | RF ] | MO ] | FR].
    - apply (po_loc_in_ev WF x y PO_LOC).
    - apply (rf_in_ev WF x y RF).
    - apply (mo_in_ev WF x y MO).
    - apply (fr_in_ev WF x y FR).
Qed.

Lemma po_loc_rf_mo_fr_trans_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (PO_LOC_RF_MO_FR: (po_loc_rf_mo_fr ex)⁺ x y) : events ex x /\ events ex y.
Proof.
    induction PO_LOC_RF_MO_FR.
    - apply (po_loc_rf_mo_fr_in_ev WF x y H).
    - basic_solver.
Qed.

Lemma rfe_in_ev {label : Type} {_ : label_class label} {ex}
  (WF: well_formed ex) x y (RFE: rfe ex x y) : events ex x /\ events ex y.
Proof. destruct RFE. apply rf_in_ev in H; auto. Qed.

(* Basic mapping proofs between different relations *)
Lemma rf_fr_to_mo {label : Type} {_ : label_class label} {ex x y z}
  (WF: well_formed ex) (RF: rf ex x y) (FR: fr ex y z) : mo ex x z.
Proof.
    assert (H1 : rf ex ⨾ (rf ex)⁻¹ ⊆ ⦗fun _ => True⦘). (*from Imm*)
    { apply functional_alt, WF. }
    assert (H : rf ex ⨾ fr ex ⊆ mo ex).
    { unfold fr. sin_rewrite H1; rels.  }
    apply H; auto.
    exists y; split; auto.
Qed.

Lemma po_imm_to_po {label : Type} {_ : label_class label} {ex x y} (PO_IMM : po_imm ex x y) : po ex x y.
Proof.
  unfold po_imm, immediate in *. 
  basic_solver.
Qed.

Lemma external_internal {label : Type} {_ : label_class label} {ex} 
  (REL : execution label -> relation (event label)) 
  : REL ex ≡ internal REL ex ∪ external REL ex.
Proof.
  unfold internal, external. 
  unfolder.
  split;
  intros;
  tauto.
Qed.

Lemma ex_to_rel {label : Type} {_ : label_class label} {ex x y} 
  {REL : execution label -> relation (event label)} (r : (external REL) ex x y) 
  : REL ex x y.
Proof.
  destruct r.
  auto.
Qed.  

Notation "'E'" := events.
