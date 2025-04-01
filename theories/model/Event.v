From hahn Require Import Hahn.

Definition loc := nat.
Definition val := nat.
Definition uid := nat.
Definition tid := nat.
Inductive tag := tmov | trmw.

(* Type class to be instatiated for both consistency models *)
Class label_class (A : Type) := {
  is_r_lab : A -> Prop ;
  is_w_lab : A -> Prop ;
  is_f_lab : A -> Prop ;
  
  get_mode : A -> option tag ;
  get_loc : A -> option loc ;
  get_val : A -> option val ;
}.

Inductive event (label : Type) {label_class : label_class label} :=
  (* Event consists of unique ID, thread ID, and access label *)
  | Ev : uid -> tid -> label -> event label 
  (* For mapping fences from SimplArm to RelAcq, does not do anything *)
  | EvSkip : uid -> tid -> event label
  (* Sequence of init events precede all threads before they fork *)
  | EvInit : uid -> loc -> val -> event label.

Arguments Ev {label} {label_class}.
Arguments EvSkip {label} {label_class}.
Arguments EvInit {label} {label_class}.

(* Event sets *)

(* Write events*)
Inductive ev_w {label : Type} {label_class : label_class label} : event label -> Prop :=
  | EvW : forall u t l (H : is_w_lab l), ev_w (Ev u t l)
  | EvInitW : forall u l v, ev_w (EvInit u l v).

(* Write events indexed by their tag *)
Inductive ev_w_t {label : Type} {label_classs : label_class label} (tg : tag) : event label -> Prop :=
  | EvWrTag : forall u t l (is_w : is_w_lab l) (m : get_mode l = Some tg), ev_w_t tg (Ev u t l)
  | EvInitTag : forall u l v, tg = tmov -> ev_w_t tg (EvInit u l v).

(* Read events*)
Inductive ev_r {label : Type} {label_class : label_class label} : event label -> Prop :=
  | EvR : forall u t l (H : is_r_lab l), ev_r (Ev u t l).

(* Read events indexed by their tag*)
Inductive ev_r_t  {label : Type} {label_classs : label_class label} (tg : tag) : event label -> Prop :=
  | EvRdTag : forall u t l (is_r : is_r_lab l) (m : get_mode l = Some tg),  ev_r_t tg (Ev u t l).

(* Fence events *)
Inductive ev_f {label : Type} {label_class : label_class label} : event label -> Prop :=
  | EvF : forall u t l (H : is_f_lab l), ev_f (Ev u t l).

(* Skip events *)
Inductive ev_skip {label : Type} {label_class : label_class label} : event label -> Prop :=
  | EvSkipDef : forall u t, ev_skip (EvSkip u t).

(* Init events *)
Inductive ev_init {label : Type} {label_class : label_class label} : event label -> Prop :=
  | EvInitDef : forall u l v, ev_init (EvInit u l v).

(* Set of all events *)
Inductive ev {label : Type} {label_class : label_class label} : event label -> Prop :=
  | EvDef : forall u t l, ev (Ev u t l)
  | EvSkipEv : forall u t, ev (EvSkip u t)
  | EvInitEv : forall u l v, ev (EvInit u l v).

(* General predicates for event values *)
(* These seem to be more convenient as fuctions for unfolding *)
Definition has_val {label : Type} {_ : label_class label} v e : Prop :=
  match e with
  | Ev _ _ l => get_val l = Some v
  | _ => False
  end.

Definition has_tid {label : Type} {_ : label_class label} t e : Prop :=
  match e with
  | Ev _ t' _ => t = t'
  | EvSkip _ t' => t = t'
  | _ => False
  end.

Definition has_loc {label : Type} {_ : label_class label} l e : Prop :=
  match e with
  | Ev _ _ l' => get_loc l' = Some l
  | _ => False
  end.

(* Helper functions *)
Definition get_uid {label : Type} {_ : label_class label} e : uid :=
  match e with
  | Ev u _ _ => u
  | EvSkip u _ => u
  | EvInit u _ _ => u
  end.

Definition get_tid {label : Type} {_ : label_class label} e : option tid :=
  match e with
  | Ev _ t _ => Some t
  | EvSkip _ t => Some t
  | _ => None
  end.

Definition same_loc {label : Type} {_ : label_class label} x y := exists l, has_loc l x /\ has_loc l y.
Definition same_tid {label : Type} {_ : label_class label} x y := get_tid x = get_tid y.

(* Notation to be used in model specification *)
Notation "'W'" := ev_w.
Notation "'R'" := ev_r.
Notation "'F'" := ev_f.

Notation "'W_t'" := ev_w_t.
Notation "'R_t'" := ev_r_t.

Notation "'RW'" := (fun x => ev_r x \/ ev_w x).

(* same_loc proofs *)
Lemma same_loc_trans {label : Type} {_ : label_class label} : transitive (same_loc).
Proof.
  intros a b c SAME_LOC1 SAME_LOC2.
  unfold same_loc, has_loc in *. 
  basic_solver.
Qed.

Lemma same_loc_sym {label : Type} {_ : label_class label} : symmetric (same_loc).
Proof.
  intros a b SAME_LOC.
  unfold same_loc, has_loc in *. 
  basic_solver.
Qed.