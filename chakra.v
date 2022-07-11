(** * Introduction

CHAKRA (Common Hierarchical Abstract Knowledge Representation for Anything) is a general-purpose framework for hierarchical knowledge representation. This file contains the formal specification of CHAKRA in Coq. It defines:

- The CHAKRA Data Model: functional signature of CHAKRA knowledge structures.
- The CHAKRA Description Language: syntax and semantics for describing CHAKRA knowledge structures.
- The CHAKRA Processing and Query Language: syntax and semantics for construction, retrieval and processing of CHARKA knowledge structures.

The CHAKRA processing and query language (CHPQL) is a simple programming language for working with CHAKRA knowledge structures. The syntax of expressions is defined by a formal grammar.  The semantics is defined by mapping expressions to native Coq programs with computational effects encapsulated by a continuation parsing monad.*) 

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.

(** * PreChakra *)

Class Functor (F:Type -> Type) :=
  { fmap {A B}: (A -> B) -> F A -> F B }.

Class Monad (F: Type -> Type) `{Functor F} :=
  { munit {A} : A -> F A;
    mjoin {A} : F (F A) -> F A }.

Definition ret {F:Type->Type} `{Monad F} {A} : A -> F A :=
  munit. 

Definition bind {F:Type->Type} `{Monad F} {A B} : F A -> (A -> F B) -> F B :=
  fun oa f => mjoin (fmap f oa).

Definition fish {F:Type->Type} `{Monad F} {A B C} : (A -> F B) -> (B -> F C) -> A -> F C :=
  fun f g a => bind (f a) g.


Instance list_funtor : Functor list :=
  { fmap := map }.


Instance list_monad : Monad list :=
  { munit {A} := fun a => cons a nil;
    mjoin {A} := fix MJOIN (lla:list (list A)) := match lla with
                                                | nil => nil
                                                | cons la lla' => app la (MJOIN lla')
                                                end }.


Instance op_functor : Functor option :=
  { fmap {A B}:= fun f oa => match oa with
                             | None => None
                             | Some a => Some (f a)
                             end }.


Instance op_monad : Monad option :=
  { munit {A} := Some;
    mjoin {A} := fun ooa => match ooa with
                           | None => None
                           | Some oa => oa
                           end }.

Class MFLIP (F G:Type -> Type) := mflip : forall {A}, F (G A) -> G (F A).

Fixpoint lo_to_ol {T} (lo: list (option T)) : option (list T) :=
  match lo with
  | nil => Some nil
  | cons x l => match x, (lo_to_ol l) with
                | Some x', Some l' => Some (cons x' l')
                | _,_ => None
                end
  end.


Instance flip_list_option : MFLIP list option := @lo_to_ol.

Definition Read (D A:Type) := D -> option A.

Definition State (D A:Type) := D -> prod D (option A).


Instance read_functor {D} : Functor (Read D) :=
  { fmap {A B} := fun f ra s => fmap f (ra s) }.


Instance read_monad {D} : Monad (Read D) :=
  { munit {A} := fun a s => ret a;
    mjoin {A} := fun rra s => match rra s with
               | None => None
               | Some f => f s
               end }.

Definition appto {A B} (a:A) (f:A->B) : B :=
  f a.

Definition apptoall {A B} (l:list (A->B)) (a:A) : list B :=
  map (appto a) l.


Instance flip_list_read {D} : MFLIP list (Read D) :=
  fun U (l:list (Read D U)) s => mflip (apptoall l s).

Definition rmap {D A B} (f:A->Read D B) (op:Read D (list A)) : Read D (list B) :=
  bind op (fun l => mflip (fmap f l)).


Instance state_functor {D} : Functor (State D) :=
  { fmap {A B} := fun f sa s => match sa s with
                                | (s', None) => (s', None)
                                | (s', Some a) => (s', Some (f a))
                                end }.


Instance state_monad {D} : Monad (State D) :=
  { munit {A} := fun a s => (s,Some a);
    mjoin {A} := fun ssa s => match ssa s with
                             | (s', None) => (s', None)
                             | (s', Some sa) => sa s'
                              end }.

(** Abstract logical constructs *)

Class LIFT A B := lift : A -> B.
Class EVAL A B C := eval : A -> B -> C.
Class CONJ A := conj : A -> A -> A.
Class DISJ A := disj : A -> A -> A.
Class NEG A := neg : A -> A.
Class IMP A := imp : A -> A -> A.
Class EX A B := ex : (A -> B) -> B.

Hint Unfold lift eval conj disj neg imp ex : core. 

(** Decidability *)

Definition Decision (P:Prop) := {P}+{~P}.

Class Decidable (P:Prop) := dec : Decision P.

Hint Unfold Decision Decidable : core.

(** Instances: *)


Instance liftoptiontoread {D A} : LIFT (option A) (Read D A) := fun o s => o.


Instance liftreadtostate {D A} : LIFT (Read D A) (State D A) := fun r s => (s, r s).


Instance liftoptiontostate {D A} : LIFT (option A) (State D A) := fun o s => (s, o).


Instance evaloption {A} : EVAL (option A) A Prop := fun oa a => Some a = oa.


Instance conjprop : CONJ Prop := and.


Instance disjprop : DISJ Prop := or.


Instance negprop : NEG Prop := not.


Instance impprop : IMP Prop := fun P Q => P -> Q.


Instance exprop {A} : EX A Prop := fun p => exists t, p t.

Hint Unfold evaloption conjprop disjprop negprop impprop exprop : core.

(** * Notation *)

Notation "x <- e1 ; e2" := (bind e1 (fun x => e2))
                             (right associativity, at level 60).

Notation " e1 ;; e2 " := (fish e1 e2)
                           (right associativity, at level 60).

Notation " x ~~ y " := (eval x y) (at level 55).

Notation " [ P ] " := (lift P) (at level 55).

Notation " A /\ B " := (conj A B) : type_scope.

Notation " A \/ B " := (disj A B) : type_scope.

Notation "~ x" := (neg x) : type_scope.

Notation "'Exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Exists' '/ ' x .. y , '/ ' p ']'")
    : type_scope.


Notation "'rw' H 'in' H'" := (eq_rect _ _ H' _ H)(at level 10, H' at level 10, format "'[' 'rw' H in '/' H' ']'").

(** * The CHARKA Data Model

The CHAKRA data model is specified as a collection of core abstract types and operations. The types capture the componenets of the model and the operations capture their interactions. The behaviour of the operations is specified by a collection of equational axioms over the operations.

The signature has five abstract types and two abstract type families:

- [ID] type of identifiers
- [C] type of constituents
- [H] type of hierarchies
- [A] type of attribute names
- [AT] family of attribute types
- [P] type of property names
- [PT] family of property types

[ID] is the type of identifiers. Elements [x:ID] are symbols used to uniquely identify extant entities. Computationally, identifiers are pointers to data structures that represent those entities.

[C] is the type of constituents. Elements [c:C] are data structures which aggregate information about extant entities. Constituents encapsulate attributes, properties and a list of particle indentifiers.

[H] is the type of hierarchies. Elements [s:H] are associative data structures which map identifiers to constieutns. They represent collections of entities and their hierarchical relationships.

[{a : A & AT a}] is the type of attribtues, constructed from the type [A] of attribute names and the type family [AT] of attribute types. Constituents are fitted with attribute name-value pairs [(a,v) : {a : A & AT a}], where the name [a : A] identifies an intrinsic quality of constituents, and the value [v : AT a] represents a point in the corresponding conceptual space [AT a] with which the constituent is identified.

[{p : P & PT a}] is the type of properties, constructed from the type [P] of property names and the type family [PT] of property types. Constituents are fitted with property name-value pairs [(p,v) : {p : P & PT a}], where the property name [p : P] represents the mode of classification, and the value [v : PT p] represents an extensional class to which the constituent belongs.

The signature has 10 core abstract operations: These are pure operations which define the functional behaviour and interaction of the types defined above.

The intended behaviour of the operations is specified with axioms, each defined as a universally quantified equations between terms constructed from the core CHAKRA operations. Any implementation of the CHAKRA signature should satisfy these equations.
-----
** Types: *)

Parameter ID : Set.
Parameter C : Set.
Parameter H : Set.
Parameter A : Set.
Parameter AT : A -> Set.
Parameter P : Set.
Parameter PT : P -> Set.

(** ** Operations *)

(** Equality checking: *)

Parameter ideq : ID -> ID -> bool.
Parameter aeq : A -> A -> bool.
Parameter peq : P -> P -> bool.

(** Constituent constructors: *)

Parameter agg : list ID -> C.
Parameter seta : forall a, AT a -> C -> C.
Parameter setp : forall p, PT p -> C -> C.

(** Constituent destructors: *)

Parameter pts : C -> list ID.
Parameter geta : forall a, C -> option (AT a).
Parameter getp : forall p, C -> option (PT p).

(** Hierarchy constructors: *)

Parameter emp : H.
Parameter ins : ID -> C -> H -> H.
Parameter rmv : ID -> H -> H.
Parameter pop : H -> H.

(** Hierarchy destructors: *)

Parameter fnd : ID -> H -> option C.
Parameter peek : H -> option (ID*C).

(** Membership checking: *)

Parameter isemp : H -> bool.
Parameter mem : ID -> H -> bool.

(** Mapping hierarchies to lists: *)

Parameter cts : H -> list (ID*C).
Parameter dom : H -> list ID.

(** ** Specification: *)

(** Spec for eqaulity operations: *)

Axiom ideq_spec : forall x y, true = ideq x y <-> x = y.
Axiom aeq_spec : forall a b, true = aeq a b <-> a = b.
  
(** Spec for [pts] *)

Axiom pts_agg : forall ps, pts (agg ps) = ps.
Axiom pts_seta : forall a v c, pts (seta a v c) = pts c.
Axiom pts_setp : forall p u c, pts (setp p u c) = pts c.

(** Spec for [geta] *)

Axiom geta_agg : forall a ps, geta a (agg ps) = None.
Axiom geta_seta_same : forall a b v c (e:a = b), geta b (seta a v c) = Some (rw e in v). 
Axiom geta_seta_other : forall a b v c, a <> b -> geta b (seta a v c) = geta b c.

(** Spec for [getp]: *)

Axiom getp_agg : forall p ps, getp p (agg ps) = None.
Axiom getp_setp_same : forall p q u c (e:p = q), getp q (setp p u c) = Some (rw e in u). 
Axiom getp_setp_other : forall p q u c, p <> q -> getp q (setp p u c) = getp q c.

(** Spec for [emp] *)

Axiom fnd_emp : forall x, fnd x emp = None.

(** Spec of [ins]: *)

Axiom fnd_ins_same : forall x y c s, x = y -> fnd x (ins y c s) = Some c.
Axiom fnd_ins_other : forall x y c s, x <> y -> fnd x (ins y c s) = fnd x s.

(** Spec for [rmv]: *)

Axiom rmv_emp : forall x, rmv x emp = emp.
Axiom fnd_rmv_same : forall x y s, x = y -> fnd x (rmv y s) = None.
Axiom fnd_rmv_other : forall x y s, x <> y -> fnd x (rmv y s) = fnd x s.

(** Spec for [pop]: *)

Axiom pop_emp : pop emp = emp.
Axiom pop_ins : forall x c s, pop (ins x c s) = rmv x s.

(** Spec for [peek]: *)

Axiom peek_emp : peek emp = None.
Axiom peek_ins : forall x c s, peek (ins x c s) = Some (x,c).

(** Spec for [mem]: *)

Axiom mem_1 : forall x s, mem x s = true <-> exists c, fnd x s = Some c.

(** Spec of [isemp]: *)

Axiom isemp_emp : forall s, isemp s = true <-> s = emp.

(** Spec for [cts]: *)

Axiom cts_emp : cts emp = nil.
Axiom cts_ins : forall x c s, cts (ins x c s) = (x,c) :: filter (fun p => ideq (fst p) x) (cts s).
Axiom cts_rmv : forall x s, cts (rmv x s) = filter (fun p => ideq (fst p) x) (cts s).
Axiom hd_cts : forall s, hd_error (cts s) = peek s.
Axiom tl_cts : forall s, tl (cts s) = cts (pop s).
Axiom cts_fnd : forall x c s, In (x,c) (cts s) <-> fnd x s = Some c.

(** Spec for [dom] *)
Axiom dom_fst_cts : forall s, dom s = map fst (cts s).

(** Decidable equality relations: *)


Instance id_dec : forall (x y: ID), Decidable (x=y).
(* begin details *)
intros.
remember (ideq x y). remember (ideq_spec x y). induction b.
- left. induction  i. exact (H0 Heqb).
- right. induction i. unfold not. intros. specialize (H1 H2). rewrite <- H1 in Heqb. inversion Heqb.
Defined.
(* end details *)


Instance id_list_dec : forall (l1 l2:list ID), Decidable (l1=l2).
(* begin details *)
refine (fix LD l1 l2 := match l1,l2 with
                        | nil, nil => left _
                        | cons x t, cons y u => match id_dec x y with 
                                                | left he => match LD t u with
                                                             | left te => left _
                                                             | right _ => right _
                                                             end             
                                                | right hne => right _
                                                end
                        | _, _ => right _
                        end).
- auto. 
- unfold not. intros. inversion H0.
- unfold not. intros. inversion H0.
- rewrite he. rewrite te. auto. 
- unfold not. intros. inversion H0. auto. 
- unfold not. intros. inversion H0. auto. 
Defined.
(* end details *)

(** Derivable facts: *)

Theorem dom_emp : dom emp = nil.
(* begin details *)
  remember (dom_fst_cts emp).
  remember cts_emp.
  rewrite e. rewrite e0.
  simpl. auto. 
Qed.
(* end details *)

(** * CHAKRA Standard Prelude

The core operations are used to define a set of more general operations for accessing and manipulating CHAKRA hierarchies. *)

(** Read Operations: *) 

Definition get_att (a:A) (x:ID) : Read H (AT a) :=
  (fnd x) ;; (geta a).

Definition get_prp (p:P) : ID -> Read H (PT p) :=
  fun x => (fnd x) ;; (getp p).

Definition get_parts : ID -> Read H (list ID) :=
  fun x s => o <- fnd x s ; ret (pts o).

Definition domain : Read H (list ID) :=
  fun s => ret (dom s).

(** State Operations *)
Definition insert (x:ID) (c:C) : State H unit :=
  fun s => let s' := ins x c s in (s', ret tt).

Definition aggregate (x:ID) (ps:list ID) : State H unit :=
  fun s => (ins x (agg ps) s, ret tt).

Definition set_att (a:A) (v:AT a) (x:ID) : State H unit :=
  fun s => match fnd x s with
           | None => (s,None)
           | Some o => (ins x (seta a v o) s, Some tt)
           end.

Definition set_prp (p:P) (v:PT p) (x:ID) : State H unit :=
  fun s => match fnd x s with
           | None => (s,None)
           | Some o => (ins x (setp p v o) s, Some tt)
           end.

Hint Unfold domain get_att get_prp get_parts insert aggregate set_att set_prp : core.

(** * The CHAKRA Description Language

The CHARKA description language (CHDL) is a simple logical language for expressing formal properties about knowledge structures and their constituents. The syntax of expressions is defined by a formal grammar. The semantics of expressions is defined in terms of Coq's underlying constructive logic.*)

Definition HProp := H -> Prop.
Definition CProp := ID -> HProp.
Definition LProp := list ID -> HProp.
Definition CRel := ID -> ID -> HProp.
Definition LRel := list ID -> list ID -> HProp.

Class DecidableHProp (h:HProp) := hdec: forall s:H, Decidable (h s).
Class DecidableCProp (c:CProp) := cdec: forall x:ID, DecidableHProp (c x).
Class DecidableLProp (r:LProp) := ldec: forall l:list ID, DecidableHProp (r l).
Class DecidableCRel (r:CRel) := rdec: forall x y, DecidableHProp (r x y).
Class DecidableLRel (m:LRel) := mdec: forall l1 l2, DecidableHProp (m l1 l2).

Hint Unfold DecidableHProp DecidableCProp DecidableLProp DecidableCRel DecidableLRel : core.

(** ** CHAKRA Props *)

(** Lifted propositions: *)

Definition HLift (P:Prop) : HProp :=
  fun _ => P.


Instance hliftp : LIFT Prop HProp := HLift.

Hint Unfold HLift hliftp : core.


Instance hlift_dec {P} `{Decidable P} : DecidableHProp ([P]). firstorder. Defined.

(** Evaluation of option values: *)

Definition HEvalOption {T} (o:option T) (v:T) : HProp :=
  fun _ => o ~~ v.


Instance hevaloption {T} : EVAL (option T) T HProp := HEvalOption.

Hint Unfold HEvalOption hevaloption : core.


Instance hevaloption_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, DecidableHProp (@hevaloption A c a).
(* begin details *)
autounfold in *. intros.
induction c.
- induction (eqd a0 a).
-- rewrite -> a1. auto.
-- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined. 
(* end details *)

(** Evaluation of Read operations: *)

Definition HEvalRead {T} (op:Read H T) (v:T) : HProp :=
  fun s => op s ~~ v.


Instance hevalread {T} : EVAL (Read H T) T HProp := HEvalRead.

Hint Unfold HEvalRead hevalread : core.


Instance hevalread_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, DecidableHProp (@hevalread A c a).
(* begin details *)
autounfold in *. intros.
induction (c s).
- induction (eqd a a0).
-- rewrite -> a1. auto.  
-- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined. 
(* end details *)

(** Evaluation of State operations: *)

Definition HEvalState T (op:State H T) (v:T) : HProp :=
  fun s => snd (op s) ~~ v.


Instance hevalstate T : EVAL (State H T) T HProp := HEvalState T.

Hint Unfold HEvalState hevalstate : core.


Instance hevalstate_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, DecidableHProp (@hevalstate A c a).
(* begin details *)
autounfold in *. intros.
induction (snd (c s)).
- induction (eqd a a0).
-- rewrite -> a1. auto.
-- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined. 
(* end details *)

(** Conjunction: *)

Definition HConj (h1 h2:HProp) : HProp :=
  fun s => h1 s /\ h2 s.


Instance hconj : CONJ HProp := HConj.

Hint Unfold HConj hconj : core.


Instance hconj_dec H1 H2 `{DecidableHProp H1} `{DecidableHProp H2} : DecidableHProp (H1 /\ H2). firstorder. Defined.

(** Disjunction *)

Definition HDisj (hp1 hp2:HProp) : HProp :=
  fun s => hp1 s \/ hp2 s.


Instance hdisj : DISJ HProp := HDisj.

Hint Unfold HDisj hdisj : core.


Instance hdisj_dec : forall hp1 hp2 `{DecidableHProp hp1} `{DecidableHProp hp2}, DecidableHProp (hp1 \/ hp2). firstorder. Defined.

(** Negation: *)

Definition HNeg (hp:HProp) : HProp :=
  fun s => ~ hp s.


Instance hneg : NEG HProp := HNeg.

Hint Unfold HNeg hneg : core.


Instance hneg_dec : forall hp `{DecidableHProp hp}, DecidableHProp (~ hp). firstorder. Defined. 

(** Existential quantification: *)

Definition HExists {T} (p:T->HProp) : HProp :=
  fun s => Exists t, p t s.


Instance hexists {T} : EX T HProp := HExists.

Hint Unfold HExists hexists : core. 

(** Total description *)

Definition HSpec (p:LProp) : HProp := Exists l, domain ~~ l /\ p l.

Hint Unfold HSpec : core.


Instance HSpec_dec {LP} `{DecidableLProp LP} : DecidableHProp (HSpec LP).
(* begin details *)
autounfold in *. intros.
remember (dom s).
induction (H0 l s).
- left. exists l. split. rewrite -> Heql. reflexivity. auto. 
- right. intros. induction H1. induction H1. inversion H1. rewrite -> H4 in H2. auto.
Defined.
(* end details *)
  
(** ** Constituent Specifications *)

(** Has Attribute: *)

Definition HasAtt (a:A) (v:AT a) : CProp :=
  fun x => (get_att a x) ~~ v.

Hint Unfold HasAtt : core.


Instance hasatt_dec {a:A} `{d:forall v v':AT a, Decidable (v=v')} (v:AT a) : DecidableCProp (HasAtt a v).
(* begin details *)
autounfold in *. intros. 
induction ((fnd x ;; geta a) s) as [v'|].
- induction (d v v').
  -- left. rewrite -> a0. auto.
  -- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined.
(* end details *)

(** Has Property: *)

Definition HasPrp (p:P) (v:PT p) : CProp :=
  fun x => (get_prp p x) ~~ v.

Hint Unfold HasPrp : core.


Instance hasprp_dec {p:P} `{d:forall v v':PT p, Decidable (v=v')} (v:PT p) : DecidableCProp (HasPrp p v).
(* begin details *)
autounfold in *. intros. 
induction ((fnd x ;; getp p) s) as [v'|].
- induction (d v v') as [e|].
  -- left. rewrite -> e. auto.
  -- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined.
(* end details *)

(** Has Particles: *)

Definition HasParts (l: list ID) : CProp :=
  fun x => (get_parts x) ~~ l.

Hint Unfold HasParts : core.


Instance hasparts_dec : forall (l:list ID), DecidableCProp (HasParts l).
(* begin details *)
autounfold in *. intros. 
induction (o <- fnd x s; ret (pts o)).
- induction (id_list_dec l a).
  -- left. rewrite a0. auto. 
  -- right. intros. inversion H0. exact (b H2).
- right. intros. inversion H0.
Defined. 
(* end details *)

(** Lifted Props: *)

Definition CLiftP (P:Prop) : CProp :=
  fun _ => [P]. 


Instance cliftp : LIFT Prop CProp := CLiftP.

Hint Unfold CLiftP cliftp : core.


Instance cliftp_dec : forall {P:Prop} `{Decidable P},  DecidableCProp (CLiftP P).
firstorder. Defined. 

(** Lifted HProps *)

Definition CLiftH (H:HProp) : CProp :=
  fun _ => H.


Instance clifth : LIFT HProp CProp := CLiftH. 

Hint Unfold CLiftH clifth : core.


Instance clift_dec : forall {X:HProp} `{DecidableHProp X}, DecidableCProp (CLiftH X).
firstorder. Defined. 

(** Conjunction: *)

Definition CConj (c1 c2 : CProp) : CProp :=
  fun x => c1 x /\ c2 x.


Instance cconj : CONJ CProp := CConj.

Hint Unfold CConj cconj : core.


Instance cconj_dec : forall (C1 C2:CProp) `{DecidableCProp C1} `{DecidableCProp C2}, DecidableCProp (CConj C1 C2).
(* begin details *)
autounfold in *.
refine (fun c1 c2 d1 d2 x s => _).
induction (d1 x s).
- induction (d2 x s).
  -- left. constructor; auto.  
  -- right. intros. inversion H0. exact (b H2).
- right. intros. inversion H0. exact (b H1).
Defined. 
(* end details *)

(** Existential quantification: *)

Definition CExists {T} (p:T->CProp) : CProp :=
  fun x => Exists t, p t x.


Instance cexists {T} : EX T CProp := CExists.

Hint Unfold CExists cexists : core. 

(** ** List Descriptions *)

(** Nil *)

Definition LNil : LProp :=
  fun l => [l = nil].

Hint Unfold LNil : core.


Instance lnil_dec : DecidableLProp (LNil).
(* begin details *)
autounfold in *.
refine (fun l s => match l with
                   | nil => left _
                   | cons h t => right _
                   end). 
- auto. 
- intros. inversion H0.
Defined.
(* end details *)

(** Cons *)

Definition LCons : ID -> CProp -> LProp -> LProp :=
  fun x c p l => (hd_error l) ~~ x /\ c x /\  p (tl l).

Hint Unfold LCons : core.


Instance lcons_dec : forall x c l `{DecidableCProp c} `{DecidableLProp l}, DecidableLProp (LCons x c l).
(* begin details *)
autounfold in *.
refine (fun x c r cd rd l s => match l with
                               | cons h t => match id_dec x h, cd x s, rd t s with
                                             | left xp, left cp, left rp => left _
                                             | _ , _ , _ => right _
                                             end
                               | nil => right _
                               end).
- simpl. intros. inversion H0. inversion H1. 
- split.
  -- rewrite xp. reflexivity. 
  -- simpl. auto. 
- simpl. intros. inversion H0. inversion H2. exact (f H4).
- simpl. intros. inversion H0. inversion H2. exact (f H3).
- simpl. intros. inversion H0. inversion H1. exact (n H4).
Defined. 
(* end details *)

(** All elements: *)

Inductive LAll : CProp -> LProp :=
| all_nil : forall c s, LAll c nil s
| all_cons : forall (c:CProp) x l s, c x s -> LAll c l s -> LAll c (cons x l) s.

Hint Constructors LAll : core.


Instance lall_dec : forall (cp:CProp) `{DecidableCProp cp}, DecidableLProp (LAll cp).
(* begin details *)
autounfold in *.
refine (fix LALLD cp cd l s := match l with
                                   | nil => left (all_nil cp s)
                                   | cons h t => match cd h s with
                                                 | left ch => match LALLD cp cd t s with
                                                              | left ct => left (all_cons cp h t s ch ct)
                                                              | right _ => right _
                                                              end
                                                 | right _ => right _
                                                 end
                               end).
- intros. inversion H0. exact (f H6).                                            
- intros. inversion H0. exact (f H4).
Defined.   
(* end details *)

(** Some element: *)

Inductive LSome : CProp -> LProp :=
| some_head : forall (c:CProp) x l s, c x s -> LSome c (cons x l) s
| some_tail : forall (c:CProp) x l s, LSome c l s -> LSome c (cons x l) s.

Hint Constructors LSome : core. 


Instance lsome_dec : forall (cp:CProp) `{DecidableCProp cp}, DecidableLProp (LSome cp).
(* begin details *)
autounfold in *.
refine (fix LSOMED cp cd l s := match l with
                                | nil => right _
                                | cons h t => match cd h s with
                                              | left ch => left _
                                              | right nch => match LSOMED cp cd t s with
                                                             | left ct => left _
                                                             | right nct => right _
                                                             end
                                              end
                                end).
- intros. inversion H0.
- exact (some_head cp h t s ch). 
- exact (some_tail cp h t s ct).
- intros. inversion H0.
  -- exact (nch H5).
  -- exact (nct H5).
Defined. 
(* end details *)

(** All ordered pairs *)

Inductive LAllOrdPairs : CRel -> LProp :=
| all_op_nil : forall (r:CRel) s, LAllOrdPairs r nil s
| all_op_cons : forall (r:CRel) x l s, LAll (r x) l s -> LAllOrdPairs r l s -> LAllOrdPairs r (cons x l) s.

Hint Constructors LAllOrdPairs : core.


Instance lallordpairs_dec : forall (cr:CRel) `{DecidableCRel cr}, DecidableLProp (LAllOrdPairs cr).
(* begin details *)
autounfold in *.
refine (fix LOPD r rd l s := match l with
                             | nil => left (all_op_nil r s)
                             | cons h t => match lall_dec (r h) t s with
                                           | left rh => match LOPD r rd t s with
                                                       | left rt => left _
                                                       | right nrt => right _
                                                       end
                                           | right nrh => right _
                                           end
                             end).
- exact (rd h).
- exact (all_op_cons r h t s rh rt).
- intros. inversion H0. exact (nrt H6).
- intros. inversion H0. exact (nrh H4).
Defined.
(* end details *)

(** Lifting props: *)

Definition LLiftP (P:Prop) : LProp :=
  fun _ => [P].


Instance lliftp : LIFT Prop LProp := LLiftP.

Hint Unfold LLiftP lliftp : core.


Instance lliftp_dec : forall (P:Prop) `{Decidable P}, DecidableLProp ([P]).
firstorder. Defined. 

(** Lifting HProps: *)

Definition LLiftH (H:HProp) : LProp :=
  fun _ => H. 


Instance llifth : LIFT HProp LProp := LLiftH.

Hint Unfold LLiftH llifth : core.


Instance llifth_dec : forall (hp:HProp) `{DecidableHProp hp}, DecidableLProp ([hp]).
firstorder. Defined. 

(** *** Conjunction *)

Definition LConj (s1 s2:LProp) : LProp :=
  fun l => s1 l /\ s2 l.                                               


Instance lconj : CONJ LProp := LConj.

Hint Unfold LConj lconj : core.


Instance lconj_dec : forall (r1 r2 : LProp) `{DecidableLProp r1} `{DecidableLProp r2}, DecidableLProp (r1 /\ r2).
(* begin details *)
autounfold in *.
refine (fun r1 r2 rd1 rd2 l s => match rd1 l s, rd2 l s with
                                 | left rp1, left rp2 => left _
                                 | _ , _ => right _
                                 end).
- auto. 
- intros. inversion H0. exact (f H2).
- intros. inversion H0. exact (f H1).
Defined. 
(* end details *)

(** *** Existential quantification: *)

Definition LExists {T} (s:T->LProp) : LProp :=
  fun l => Exists t, s t l.


Instance lexists {T} : EX T LProp := LExists.

Hint Unfold LExists lexists : core.

(** ** Constituent Relations *)

(** Attribtue relations *)

Definition AttRel (a1 a2:A) (p:AT a1 -> AT a2 -> Prop) : CRel :=
  fun x y => Exists v1, HasAtt a1 v1 x /\ Exists v2, HasAtt a2 v2 y /\ [p v1 v2].

Hint Unfold AttRel : core.


Instance attrel_dec : forall (a1 a2:A) (p:AT a1 -> AT a2 -> Prop) `{forall v v', Decidable (p v v')}, DecidableCRel (AttRel a1 a2 p).
(* begin details *)
autounfold in *.
intros. 
induction ((fnd x ;; geta a1) s).
- induction ((fnd y ;; geta a2) s).
  -- induction (H0 a a0).
     --- left. exists a. split.
         ---- auto.
         ---- exists a0. split.
              ----- auto. 
              ----- auto. 
     --- right. intros. inversion H1 as [t [eqat [v [va pp]]]]. inversion eqat. inversion va. rewrite H3 in pp. rewrite H4 in pp. exact (b pp).
  -- right. intros. inversion H1 as [t [ta [v [sn pp]]]]. inversion sn.
- right. intros. inversion H1 as [t [sn [v [sf pp]]]]. inversion sn.
Defined. 
(* end details *)

(** Particle relations *)

Definition PartRel : LRel -> CRel :=
  fun m x y => Exists l1, HasParts l1 x /\ Exists l2, HasParts l2 y /\ m l1 l2.

Hint Unfold PartRel : core.

(** Lifted Props: *)

Definition CRLiftP (P:Prop) : CRel :=
  fun _ _ => [P].


Instance crliftp : LIFT Prop CRel := CRLiftP.

Hint Unfold CRLiftP crliftp : core.


Instance crliftp_dec : forall P `{Decidable P}, DecidableCProp ([P]). firstorder. Defined. 

(** Lifted HProps: *)

Definition CRLiftH (H:HProp) : CRel :=
  fun _ _ => H.


Instance crlifth : LIFT HProp CRel := CRLiftH.

Hint Unfold CRLiftH crlifth : core.


Instance crlifth_dec : forall hp `{DecidableHProp hp}, DecidableCProp ([hp]). firstorder. Defined. 

(** Conjunction: *)

Definition CRConj (r1 r2:CRel) : CRel :=
  fun x y => r1 x y /\ r2 x y.


Instance crconj : CONJ CRel := CRConj.

Hint Unfold CRConj crconj : core.


Instance crconj_dec : forall cr1 cr2 `{DecidableCRel cr1} `{DecidableCRel cr2}, DecidableCRel (cr1 /\ cr2).
(* begin details *)
autounfold in *. refine (fun r1 r2 d1 d2 x y s => match d1 x y s, d2 x y s with
                                                  | left p1, left p2 => left _
                                                  | _ , _ => right _
                                                  end); firstorder.
Defined. 
(* end details *)

(** Existential quantification: *)

Definition CRExists {T} (p:T->CRel) : CRel :=
  fun x y => Exists t, p t x y. 


Instance crexists {T} : EX T CRel := CRExists.

(** ** List Relations *)

(** Pairwise relations *)

Inductive Pairwise (r:CRel) : LRel :=
| pw_nil : forall s, Pairwise r nil nil s
| pw_cons : forall x y l l' s, r x y s -> Pairwise r l l' s -> Pairwise r (cons x l) (cons y l') s.


Instance pairwise_dec {r:CRel} `{DecidableCRel r} : DecidableLRel (Pairwise r).
(* begin details *)
refine (fix F l1 l2 s := match l1, l2 with
                         | nil, nil => left (pw_nil r s)
                         | cons x l1', cons y l2' => match rdec x y s, F l1' l2' s with
                                                     | left P, left Q => left (pw_cons r x y l1' l2' s P Q)
                                                     | _ , _ => right _
                                                     end
                         | _,_ => right _ 
                         end).
unfold not. intros. inversion H1. 
unfold not. intros. inversion H1. 
unfold not. intros. inversion H1. auto.
unfold not. intros. inversion H1. auto. 
Defined.
(* end details *)

(** Lifted Props: *)

Definition LRLiftP (P:Prop) : LRel :=
  fun _ _ => [P].


Instance lrliftp : LIFT Prop LRel := LRLiftP.

(** Lifted HProps *)

Definition LRLiftH (H:HProp) : LRel :=
  fun _ _ => H.


Instance lrlifth : LIFT HProp LRel := LRLiftH.

(** Conjunction *)

Definition LRConj (r1 r2:LRel) : LRel :=
  fun l1 l2 => r1 l1 l2 /\ r2 l1 l2.


Instance lrconj : CONJ LRel := LRConj.

(** Existential quantification *)

Definition LRExists {T} (p:T -> LRel) : LRel :=
  fun l1 l2 => Exists t, p t l1 l2.


Instance lrexists {T} : EX T LRel := LRExists.

(** ** A Syntax for the HDDL *)

Inductive HPROP :=
| HLIFT : Prop -> HPROP
| EVALS {A} : OP A -> A -> HPROP
| HCONJ : HPROP -> HPROP -> HPROP
| HEXISTS {T} : (T -> HPROP) -> HPROP
| HSPEC : LPROP -> HPROP
| CAPP : CPROP -> ID -> HPROP
| CRAPP : CREL -> ID -> ID -> HPROP
| LAPP : LPROP -> list ID -> HPROP
| LRAPP : LREL -> list ID -> list ID -> HPROP 
with CPROP :=
| CLIFTP : Prop -> CPROP
| CLIFTH : HPROP -> CPROP
| CCONJ : CPROP -> CPROP -> CPROP
| CEXISTS {T} : (T -> CPROP) -> CPROP
| ATT : forall a, AT a -> (AT a -> Prop) -> CPROP
| PRT : list ID -> LPROP -> CPROP
with LPROP :=
| NIL : LPROP
| CONS : ID -> CPROP -> LPROP -> LPROP
| ALL : CPROP -> LPROP
| SOME : CPROP -> LPROP
| ALLOP : CREL -> LPROP
with CREL :=
| ATTREL : forall a1 a2:A, (AT a1 -> AT a2 -> Prop) -> CREL
| PRTREL : LREL -> CREL
with LREL :=
| PAIRWISE : CREL -> LREL
with OP : Type -> Type :=
| READOP {A} : READ A -> OP A
| OPTIONOP {A} : OPTION A -> OP A
with READ : Type -> Type :=
| GETATT : forall a, ID -> READ (AT a)
| GETPS : ID -> READ (list ID)
with OPTION : Type -> Type := 
| SIMPLEOPTION {A} : option A -> OPTION A.


