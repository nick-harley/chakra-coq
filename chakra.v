(** * Introduction

CHAKRA (Common Hierarchical Abstract Knowledge Representation for Anything) is a general-purpose framework for hierarchical knowledge representation. This file contains the formal specification of CHAKRA in Coq. It defines:

- The CHAKRA Data Model: functional signature of CHAKRA knowledge structures.
- The CHAKRA Description Language: syntax and semantics for describing CHAKRA knowledge structures.
- The CHAKRA Processing and Query Language: syntax and semantics for construction, retrieval and processing of CHARKA knowledge structures.

The CHAKRA processing and query language (CHPQL) is a simple programming language for working with CHAKRA knowledge structures. The syntax of expressions is defined by a formal grammar.  The semantics is defined by mapping expressions to native Coq programs with computational effects encapsulated by a continuation parsing monad.*) 

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.

(** * Boilerplate *)

(** Type classes: *)

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

Class Flippable (F G:Type->Type) := mflip : forall {A}, F (G A) -> G (F A).

Definition mmap {F G} `{Monad F} `{Monad G} `{Flippable G F} {A B} (f:A->F B) (t: F (G A)) : F (G B) :=
  bind t (fun g => mflip (fmap f g)).

(** List Monad: *)

Instance list_funtor : Functor list :=
  { fmap := map }.


Instance list_monad : Monad list :=
  { munit {A} := fun a => cons a nil;
    mjoin {A} := fix MJOIN (lla:list (list A)) := match lla with
                                                | nil => nil
                                                | cons la lla' => app la (MJOIN lla')
                                                  end }.

(** Option Monad: *)

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

(** Read monad: *)

Definition Read (D A:Type) := D -> option A.

Instance read_functor {D} : Functor (Read D) :=
  { fmap {A B} := fun f ra s => fmap f (ra s) }.

Instance read_monad {D} : Monad (Read D) :=
  { munit {A} := fun a s => ret a;
    mjoin {A} := fun rra s => match rra s with
               | None => None
               | Some f => f s
                              end }.

Definition rmap {D A B} := @mmap (Read D) list A B.

(** State monad: *)

Definition State (D A:Type) := D -> prod D (option A).

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

Definition smap {D A B} := @mmap (State D) list A B.

(** Flip list option: *)

Instance flip_list_option : Flippable list option :=
  fix FLO T (l:list (option T)) := match l with
                                   | nil => Some nil
                                   | cons h t => match h, FLO T t with
                                                 | Some x, Some l' => Some (cons x l')
                                                 | _ , _ => None
                                                 end
                                   end.

(** Flip list and Read: *)

Instance flip_list_read {D} : Flippable list (Read D) :=
  fix FLR U (l:list (Read D U)) s := match l with
                                     | nil => Some nil
                                     | cons r rs => let ol := FLR U rs s in
                                                    match r s, ol with
                                                    | Some u, Some l' => Some (cons u l')
                                                    | _ , _ => None
                                                    end
                                     end.

(** Flip list and state: *)

Instance flip_list_state {D} : Flippable list (State D) :=
  fix FLS U (l:list (State D U)) s := match l with
                                      | nil => (s, Some nil)
                                      | cons h ss => let (s', ol) := FLS U ss s in
                                                     match h s, ol with
                                                     | (_,Some u), Some l => (s',Some (cons u l))
                                                     | _ , _ => (s',None)
                                                     end
                                      end.

(** Abstract logical constructs: *)

Class LIFT A B := lift : A -> B.
Class EVAL A B C := eval : A -> B -> C.
Class CONJ A := conj : A -> A -> A.
Class DISJ A := disj : A -> A -> A.
Class NEG A := neg : A -> A.
Class IMP A := imp : A -> A -> A.
Class EX A B := ex : (A -> B) -> B.

Hint Unfold lift eval conj disj neg imp ex. 

(** Decidability *)

Definition Decision (P:Prop) := {P}+{~P}.

Class Decidable (P:Prop) := dec : Decision P.

Hint Unfold Decision Decidable.

(** Instances: *)

Instance liftoptionread {D A} : LIFT (option A) (Read D A) := fun o s => o.
Instance liftreadstate {D A} : LIFT (Read D A) (State D A) := fun r s => (s, r s).
Instance liftoptionstate {D A} : LIFT (option A) (State D A) := fun o s => (s, o).
Instance evaloption {A} : EVAL (option A) A Prop := fun oa a => Some a = oa.
Instance conjprop : CONJ Prop := and.
Instance disjprop : DISJ Prop := or.
Instance negprop : NEG Prop := not.
Instance impprop : IMP Prop := fun P Q => P -> Q.
Instance exprop {A} : EX A Prop := fun p => exists t, p t.

Hint Unfold evaloption conjprop disjprop negprop impprop exprop.

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
  
(** Spec for [pts]: *)

Axiom pts_agg : forall ps, pts (agg ps) = ps.
Axiom pts_seta : forall a v c, pts (seta a v c) = pts c.
Axiom pts_setp : forall p u c, pts (setp p u c) = pts c.

(** Spec for [geta]: *)

Axiom geta_agg : forall a ps, geta a (agg ps) = None.
Axiom geta_seta_same : forall a b v c (e:a = b), geta b (seta a v c) = Some (rw e in v). 
Axiom geta_seta_other : forall a b v c, a <> b -> geta b (seta a v c) = geta b c.

(** Spec for [getp]: *)

Axiom getp_agg : forall p ps, getp p (agg ps) = None.
Axiom getp_setp_same : forall p q u c (e:p = q), getp q (setp p u c) = Some (rw e in u). 
Axiom getp_setp_other : forall p q u c, p <> q -> getp q (setp p u c) = getp q c.

(** Spec for [emp]: *)

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

(** Spec for [dom]: *)

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

Hint Unfold domain get_att get_prp get_parts insert aggregate set_att set_prp.

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

Hint Unfold DecidableHProp DecidableCProp DecidableLProp DecidableCRel DecidableLRel.

(** ** CHAKRA Props *)

(** Lifted propositions: *)

Instance HLift : LIFT Prop HProp :=
  fun P _ => P.

Hint Unfold HLift.

Instance hlift_dec {P} `{Decidable P} : DecidableHProp ([P]).
(* begin details *)
firstorder.
Defined.
(* end details *)

(** Evaluation of option values: *)

Instance HEvalOption T : EVAL (option T) T HProp :=
  fun o v _ => o ~~ v.

Hint Unfold HEvalOption.

Instance hevaloption_dec T {eqd:forall (x y:T),Decidable(x=y)} : forall (c:option T) (v:T), DecidableHProp (c ~~ v).
(* begin details *)
autounfold in *. refine (fun o v _ => match o with
                                      | Some v' => match eqd v v' with
                                                   | left _ => left _
                                                   | right _ => right _
                                                   end
                                      | None => right _
                                      end).
- rewrite e. reflexivity.
- intros. inversion H0. exact (f H2).
- intros. inversion H0.
Defined. 
(* end details *)

(** Evaluation of Read operations: *)

Instance HEvalRead T : EVAL (Read H T) T HProp :=
  fun op v s => op s ~~ v.

Hint Unfold HEvalRead.

Instance hevalread_dec A {d:forall (x y:A),Decidable(x=y)} : forall (c:Read H A) (a:A), DecidableHProp (c ~~ a).
(* begin details *)
autounfold in *. refine (fun c a s => match c s with
                                      | Some v => match d a v with
                                                  | left _ => left _
                                                  | right _ => right _
                                                  end
                                      | None => right _
                                      end).
- rewrite e. reflexivity.
- intros. inversion H0. exact (f H2).
- intros. inversion H0.
Defined. 
(* end details *)

(** Evaluation of State operations: *)

Instance HEvalState T : EVAL (State H T) T HProp :=
  fun op v s => snd (op s) ~~ v.

Hint Unfold HEvalState.

Instance hevalstate_dec A {d:forall (x y:A),Decidable(x=y)} : forall (c:State H A) (a:A), DecidableHProp (c ~~ a).
(* begin details *)
autounfold in *. refine (fun c a s => match c s with
                                      | (_,Some v) => match d a v with
                                                      | left _ => left _
                                                      | right _ => right _
                                                      end
                                      | (_,None) => right _
                                      end).
- rewrite e. reflexivity.
- intros. inversion H0. exact (f H2).
- intros. inversion H0.
Defined. 
(* end details *)

(** Conjunction: *)

Instance HConj : CONJ HProp :=
  fun h1 h2 s => h1 s /\ h2 s.

Hint Unfold HConj.

Instance hconj_dec H1 H2 `{DecidableHProp H1} `{DecidableHProp H2} : DecidableHProp (H1 /\ H2).
(* begin details *)
firstorder.
Defined.
(* end details *)

(** Disjunction *)

Instance HDisj : DISJ HProp :=
  fun hp1 hp2 s => hp1 s \/ hp2 s.

Hint Unfold HDisj.

Instance hdisj_dec : forall hp1 hp2 `{DecidableHProp hp1} `{DecidableHProp hp2}, DecidableHProp (hp1 \/ hp2).
(* begin details *)
firstorder.
Defined.
(* end details *)

(** Negation: *)

Instance HNeg : NEG HProp :=
  fun hp s => ~ hp s.

Hint Unfold HNeg.

Instance hneg_dec : forall hp `{DecidableHProp hp}, DecidableHProp (~ hp).
(* begin details *)
firstorder.
Defined. 
(* end details *)

(** Implementation *)

Instance HImp : IMP HProp :=
  fun hp1 hp2 s => hp1 s -> hp2 s.

Hint Unfold HImp.

(** Existential quantification: *)

Instance HExists {T} : EX T HProp :=
  fun p s => Exists t, p t s.

Hint Unfold HExists. 

(** Total description *)

Definition HSpec (p:LProp) : HProp := Exists l, domain ~~ l /\ p l.

Hint Unfold HSpec.

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

Hint Unfold HasAtt.

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

Hint Unfold HasPrp.

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

Hint Unfold HasParts.

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

Instance CLiftP : LIFT Prop CProp :=
  fun P _ => [P]. 

Hint Unfold CLiftP.

Instance cliftp_dec : forall {P:Prop} `{Decidable P},  DecidableCProp (CLiftP P).
(* begin details *)
firstorder.
Defined.
(* end details *)

(** Lifted HProps: *)

Instance CLiftH : LIFT HProp CProp :=
  fun H _ => H.

Hint Unfold CLiftH.

Instance clift_dec : forall {X:HProp} `{DecidableHProp X}, DecidableCProp (CLiftH X).
(* begin details *)
firstorder.
Defined. 
(* end details *)

(** Conjunction: *)

Instance CConj : CONJ CProp :=
  fun c1 c2 x => c1 x /\ c2 x.

Hint Unfold CConj.

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

(** Disjunction: *)

Instance CDisj : DISJ CProp :=
  fun c1 c2 x => c1 x \/ c2 x.

Hint Unfold CDisj.

Instance cdisj_dec_left : forall (C1 C2:CProp) `{DecidableCProp C1} `{DecidableCProp C2}, DecidableCProp (C1 \/ C2).
(* begin details *)
autounfold in *. refine (fun c1 c2 d1 d2 x s => match d1 x s, d2 x s with
                                                | right nc1, right nc2 => right _
                                                | _ , _ => left _
                                                end); firstorder.
Defined.
(* end details *)

(** Negation *)

Instance CNeg : NEG CProp :=
  fun cp x => ~ cp x.

Hint Unfold CNeg.

Instance cneg_dec : forall cp `{DecidableCProp cp}, DecidableCProp (~ cp).
(* begin details *)
autounfold in *.
refine (fun c d x s => match d x s with
                       | left _ => right _
                       | right _ => left _
                       end); firstorder.
Defined.
(* end details *)

(** Implication: *)

Instance CImp : IMP CProp :=
  fun c1 c2 x s => c1 x s -> c2 x s.

Hint Unfold CImp.

(** Existential quantification: *)

Instance CExists {T} : EX T CProp :=
  fun p x => Exists t, p t x.

Hint Unfold CExists. 

(** ** List Descriptions *)

(** Nil *)

Definition LNil : LProp :=
  fun l => [l = nil].

Hint Unfold LNil.

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

Hint Unfold LCons.

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

Hint Constructors LAll.

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

Hint Constructors LSome. 

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

Hint Constructors LAllOrdPairs.

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

Instance LLiftP : LIFT Prop LProp :=
  fun P _ => [P].

Hint Unfold LLiftP.

Instance lliftp_dec : forall (P:Prop) `{Decidable P}, DecidableLProp ([P]).
(* begin details *)
firstorder.
Defined. 
(* end details *)

(** Lifting HProps: *)

Instance LLiftH : LIFT HProp LProp :=
  fun H _ => H. 

Hint Unfold LLiftH.

Instance llifth_dec : forall (hp:HProp) `{DecidableHProp hp}, DecidableLProp ([hp]).
(* begin details *)
firstorder.
Defined. 
(* end details *)

(** Conjunction *)

Instance LConj : CONJ LProp :=
  fun lp1 lp2 l => lp1 l /\ lp2 l.                                               

Hint Unfold LConj.

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

(** Disjunction *)

Instance LDisj : DISJ LProp :=
  fun lp lp' s => lp s \/ lp' s.

Hint Unfold LDisj.

Instance ldisj_dec : forall lp lp' `{DecidableLProp lp} `{DecidableLProp lp'}, DecidableLProp (lp \/ lp').
(* begin details *)
autounfold in *. refine (fun p q dp dq l s => match dp l s, dq l s with
                                                | right _ , right _ => right _
                                                | _ , _ => left _
                                                end); firstorder.
Defined. 
(* end details *)

(** Negation *)

Instance LNeg : NEG LProp := fun p l => ~ (p l). 

Hint Unfold LNeg.

Instance LNeg_dec : forall p `{DecidableLProp p}, DecidableLProp (LNeg p).
(* begin details *)
autounfold in *. refine (fun p d l s => match d l s with
                                        | left _ => right _
                                        | right _ => left _
                                        end); firstorder.
Defined.
(* end details *)

(** Implication *)

Instance LImp : IMP LProp := fun p q l => HImp (p l) (q l).

Hint Unfold LImp.

(** Existential quantification: *)

Instance LEx {T} : EX T LProp :=
  fun p l => Exists t, p t l.

Hint Unfold LEx.

(** ** Constituent Relations *)

(** Attribtue relations: *)

Definition AttRel (a1 a2:A) (p:AT a1 -> AT a2 -> Prop) : CRel :=
  fun x y => Exists v1, HasAtt a1 v1 x /\ Exists v2, HasAtt a2 v2 y /\ [p v1 v2].

Hint Unfold AttRel.

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

Hint Unfold PartRel.

(** Lifted Props: *)

Instance CRLiftP : LIFT Prop CRel :=
  fun P _ _ => [P].

Hint Unfold CRLiftP.

Instance crliftp_dec : forall P `{Decidable P}, DecidableCProp ([P]).
(* begin details *)
firstorder.
Defined.
(* end details *) 

(** Lifted HProps: *)

Instance CRLiftH : LIFT HProp CRel :=
  fun p _ _ => p.

Hint Unfold CRLiftH.

Instance crlifth_dec : forall hp `{DecidableHProp hp}, DecidableCProp ([hp]).
(* begin details *)
firstorder.
Defined.
(* end details *) 

(** Conjunction: *)

Instance CRConj : CONJ CRel :=
  fun r1 r2 x y => r1 x y /\ r2 x y.

Hint Unfold CRConj.

Instance crconj_dec : forall cr1 cr2 `{DecidableCRel cr1} `{DecidableCRel cr2}, DecidableCRel (cr1 /\ cr2).
(* begin details *)
autounfold in *. refine (fun r1 r2 d1 d2 x y s => match d1 x y s, d2 x y s with
                                                  | left p1, left p2 => left _
                                                  | _ , _ => right _
                                                  end); firstorder.
Defined. 
(* end details *)

(** Disjunction *)

Instance CRDisj : DISJ CRel := fun p q x y => p x y \/ q x y.

Hint Unfold CRDisj.

Instance CRDisj_dec : forall p q `{DecidableCRel p} `{DecidableCRel q}, DecidableCRel (p \/ q).
(* begin details *)
autounfold in *. refine (fun p q d1 d2 x y s => match d1 x y s, d2 x y s with
                                                | right _, right _ => right _
                                                | _ , _ => left _
                                                end); firstorder. 
Defined.
(* end details *)

(** Negation *)

Instance CRNeg : NEG CRel := fun p x y => ~ (p x y).

Hint Unfold CRNeg.

Instance CRNeg_dec : forall r `{DecidableCRel r}, DecidableCRel (~ r).
(* begin details *)
firstorder.
Defined.
(* end details *) 

(** Implication *)

Instance CRImp : IMP CRel := fun r r' x y => HImp (r x y) (r' x y). 

Hint Unfold CRImp.

(** Existential quantification: *)

Instance CRExists {T} : EX T CRel :=
  fun p x y => Exists t, p t x y.

Hint Unfold CRExists.

(** ** List Relations *)

(** Pairwise relations *)

Inductive Pairwise (r:CRel) : LRel :=
| pw_nil : forall s, Pairwise r nil nil s
| pw_cons : forall x y l l' s, r x y s -> Pairwise r l l' s -> Pairwise r (cons x l) (cons y l') s.

Hint Constructors Pairwise.

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

Instance LRLiftP : LIFT Prop LRel :=
  fun P _ _ => [P].

Hint Unfold LRLiftP.

Instance LRLiftP_dec : forall P `{Decidable P}, DecidableLRel ([P]).
(* begin details *)
firstorder.
Defined. 
(* end details *)

(** Lifted HProps *)

Instance LRLiftH : LIFT HProp LRel :=
  fun H _ _ => H.

Hint Unfold LRLiftH.

Instance LRListH_dec : forall H `{DecidableHProp H}, DecidableLRel ([H]).
(* begin details *)
firstorder.
Defined. 
(* end details *)

(** Conjunction: *)

Instance LRConj : CONJ LRel :=
  fun r1 r2 l1 l2 => r1 l1 l2 /\ r2 l1 l2.

Hint Unfold LRConj.

Instance LRConj_dec : forall p q `{DecidableLRel p} `{DecidableLRel q}, DecidableLRel (p /\ q).
(* begin details *)
autounfold in *. refine (fun p q d1 d2 l1 l2 s => match d1 l1 l2 s, d2 l1 l2 s with
                                                  | left _, left _ => left _
                                                  | _ , _ => right _
                                                  end); firstorder. 
Defined.
(* end details *)

(** Disjunction: *)

Instance LRDisj : DISJ LRel :=
  fun r1 r2 l l' => r1 l l' \/ r2 l l'.

Hint Unfold LRDisj.

Instance LRDisj_dec : forall p q `{DecidableLRel p} `{DecidableLRel q}, DecidableLRel (p \/ q).
(* begin details *)
autounfold in *. refine (fun p q d1 d2 l l' s => match d1 l l' s, d2 l l' s with
                                                 | right _, right _ => right _
                                                 | _ , _ => left _
                                                 end); firstorder.
Defined. 
(* end details *)

(** Negation *)

Instance LRNeg : NEG LRel :=
  fun p l => ~ (p l).

Hint Unfold LRNeg.

Instance LRNeg_dec : forall p `{DecidableLRel p}, DecidableLRel (~ p).
(* begin details *)
firstorder.
Defined.
(* end details *) 

(** Implication *)

Instance LRImp : IMP LRel:=
  fun p q l l' => HImp (p l l') (q l l').

Hint Unfold LRImp.

(** Existential quantification: *)

Instance LREx {T} : EX T LRel :=
  fun p l1 l2 => Exists t, p t l1 l2.

Hint Unfold LREx.

(** ** A Syntax for the HDDL *)

Inductive HPROP :=
| HLIFT : Prop -> HPROP
| EVALS {A} : OP A -> A -> HPROP
| HCONJ : HPROP -> HPROP -> HPROP
| HDISJ : HPROP -> HPROP -> HPROP
| HNEG : HPROP -> HPROP
| HIMP : HPROP -> HPROP -> HPROP
| HEX {T} : (T -> HPROP) -> HPROP
| HSPEC : LPROP -> HPROP
| CAPP : CPROP -> ID -> HPROP
| CRAPP : CREL -> ID -> ID -> HPROP
| LAPP : LPROP -> list ID -> HPROP
| LRAPP : LREL -> list ID -> list ID -> HPROP 
with CPROP :=
| ATT : forall a, AT a -> CPROP
| PRT : list ID -> CPROP
| CLIFTP : Prop -> CPROP
| CLIFTH : HPROP -> CPROP
| CCONJ : CPROP -> CPROP -> CPROP
| CDISJ : CPROP -> CPROP -> CPROP
| CNEG : CPROP -> CPROP
| CIMP : CPROP -> CPROP -> CPROP
| CEX {T} : (T -> CPROP) -> CPROP
with LPROP :=
| NIL : LPROP
| CONS : ID -> CPROP -> LPROP -> LPROP
| ALL : CPROP -> LPROP
| SOME : CPROP -> LPROP
| ALLOP : CREL -> LPROP
| LCONJ : LPROP -> LPROP -> LPROP
| LDISJ : LPROP -> LPROP -> LPROP
| LNEG : LPROP -> LPROP
| LIMP : LPROP -> LPROP -> LPROP
| LEX {T} : (T->LPROP) -> LPROP
with CREL :=
| ATTREL : forall a1 a2:A, (AT a1 -> AT a2 -> Prop) -> CREL
| PRTREL : LREL -> CREL
| CRCONJ : CREL -> CREL -> CREL
| CRDISJ : CREL -> CREL -> CREL
| CRNEG : CREL -> CREL
| CRIMP : CREL -> CREL -> CREL
| CREX {T} : (T->CREL) -> CREL
with LREL :=
| PAIRWISE : CREL -> LREL
| LRCONJ : LREL -> LREL -> LREL
| LRDISJ : LREL -> LREL -> LREL
| LRNEG : LREL -> LREL
| LRIMP : LREL -> LREL -> LREL
| LREX {T} : (T->LREL) -> LREL
with OP : Type -> Type :=
| GETATT : forall a, ID -> OP (AT a).

(** Semantic function: *)

Fixpoint hsem (h:HPROP) :=
  match h with
  | HLIFT P => HLift P
  | EVALS op v => (opsem op) ~~ v
  | HCONJ a b => hsem a /\ hsem b
  | HDISJ a b => hsem a \/ hsem b
  | HNEG a => ~ (hsem a)
  | HIMP a b => HImp (hsem a) (hsem b)
  | HEX p => Exists t, hsem (p t)
  | HSPEC p => HSpec (lsem p)
  | CAPP c x => csem c x 
  | LAPP p l => lsem p l
  | CRAPP r x y => crsem r x y 
  | LRAPP r l l' => lrsem r l l'
  end
with csem (c:CPROP) :=
       match c with
       | ATT a v => HasAtt a v
       | PRT l => HasParts l
       | CLIFTP P => CLiftP P
       | CLIFTH h => CLiftH (hsem h)
       | CCONJ a b => csem a /\ csem b
       | CDISJ a b => csem a \/ csem b
       | CNEG a => ~ (csem a)
       | CIMP a b => CImp (csem a) (csem b)
       | CEX p => Exists t, csem (p t)
       end
with lsem (l:LPROP) :=
       match  l with
       | NIL => LNil
       | CONS x c r => LCons x (csem c) (lsem r) 
       | ALL c => LAll (csem c)
       | SOME c => LSome (csem c)
       | ALLOP cr => LAllOrdPairs (crsem cr)
       | LCONJ l l' => (lsem l) /\ (lsem l')
       | LDISJ l l' => (lsem l) \/ (lsem l')
       | LNEG l => ~ (lsem l)
       | LIMP l l' => LImp (lsem l) (lsem l')
       | LEX p => Exists t, lsem (p t)
       end
with crsem (cr:CREL) :=
       match cr with
       | ATTREL a1 a2 p => AttRel a1 a2 p
       | PRTREL m => PartRel (lrsem m)
       | CRCONJ r r' => crsem r /\ crsem r'
       | CRDISJ r r' => crsem r \/ crsem r'
       | CRNEG r => ~ (crsem r)
       | CRIMP r r' => CRImp (crsem r) (crsem r')
       | CREX p => Exists t, crsem (p t)
       end
with lrsem (lr:LREL) :=
       match lr with
       | PAIRWISE r => Pairwise (crsem r)
       | LRCONJ x y => lrsem y /\ lrsem y
       | LRDISJ x y => lrsem x \/ lrsem y
       | LRNEG x => ~ (lrsem x)
       | LRIMP x y => LRImp (lrsem x) (lrsem y)
       | LREX p => Exists t, lrsem (p t)
       end
with opsem {T} (o:OP T) :=
       match o with
       | GETATT a x => fun s => (s, get_att a x s)
       end.
