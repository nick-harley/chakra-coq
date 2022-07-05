(** * Introduction

CHAKRA (Common Hierarchical Abstract Knowledge Representation for Anything) is a general-purpose framework for hierarchical knowledge representation. This file contains the formal specification of CHAKRA's core elements:

- Functional signature for a hierarchcial data model
- Syntax and semantics for a hierarchical data description language
- Syntax and semantics for a hierarchical data manipulation language

The hierarchical data model is specified as a collection of abstract types and operations. The types capture the componenets of the model and the operations capture their interactions. The behaviour of the operations is specified by a collection of equational axioms over the operations.

The DDL is defined in terms of Coq's underlying logic, [Prop]. The DML is defined in terms of the core CHARKA operations. The syntax of expressions in these languages is defined as formal grammars and represented as a mutually inductive types in Coq. The semantics of expressions is defined as a mappings from syntactic expressions to Coq terms. 

*) 

(* begin hide *)
Add LoadPath "/Users/nick/Dropbox/chakracoq/" as CH.
Require Export Utf8_core.
(* end hide *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import prechakra.

(** * Abstract Types

The CHAKRA data model defines four abstract types and 1 

- [ID]: Identifiers
- [C]: Constituents
- [H]: Hierarchies
- [A]: Attributes
- [P]: Properties 

[ID] is the type of constituent identifiers. Elements of the type [x:ID] are symbolic names which uniquely identifiy constituents.

[C] is the type of constituent objects. Elements of the type [c:C] are data structures which hold the represented entities particles, attribtues and properties.

[H] is the type of constituent hierarchies. Elements of the type [s:H] are data structures which map identifiers to constituents.

[A] is the type of attribtues. Elements of the type [a:A] are attribute names, or keys, which represent some intrinsic quality of a constituent. The type family [aty] associates with each attribtue [a] the type of its values [aty a]. Attribute key-value pairs are represented by the dependent sum type #&Sigma;#[a:A, aty a].

[P] is the type of constituent properties. Elements of the type [p:P] are labels which represent different kinds of extensional categories with which constituents can be identified. CHAKRA defines three properties of constituents: XXX. The type family [pty] maps each property to the type of its values. 
*)

Parameter ID : Set.
Parameter C : Set.
Parameter H : Set.
Parameter A : Set.
Inductive P : Set := MOD | LEV | DEF .

Parameter aty : A -> Set.
Parameter pty : P -> Set.

Class TYP T := ty : T -> Set.

#[global]
Instance ATTRTYP : TYP A := aty.

#[global]
Instance PROPTYP : TYP P := pty.

(** * Core

- [agg] takes a list of identifiers and returns a constituent whos particles are those ids.
- [pts] takes a constituent and returns its list of particles.
- [geta] and [seta] get and set the attributes of an object.
- [getp] and [setp] get and set the properties of an object.
- [emp] is the empty hierarchy.
- [ins] binds a constituent to an identifier in a given structure.
- [fnd] looks up an indentifier in a given structure. 
- [dom] returns the list of all identifiers bound in a hierarchy. 

*)

Parameter agg : list ID -> C.
Parameter pts : C -> list ID.

Parameter geta : forall a:A, C -> option (ty a).
Parameter seta : forall a:A, ty a -> C -> C.

Parameter getp : forall p:P, C -> option (ty p).
Parameter setp : forall p:P, ty p -> C -> C.

Parameter emp : H.
Parameter ins : ID -> C -> H -> H.
Parameter fnd : ID -> H -> option C.
Parameter dom : H -> list ID.

(** * Axioms

- [id_eq_dec] ensures equality between identifiers is decidable
- [a_eq_dec] ensures equality between identifiers is decidable
- [pts_agg] ensures that the 

*)

Axiom id_eq_dec : forall (x y:ID), Decision (x=y).
Axiom a_eq_dec : forall (a b:A), Decision (a=b).
Notation "'rw' H 'in' H'" := (eq_rect _ _ H' _ H)(at level 10, H' at level 10, format "'[' 'rw' H in '/' H' ']'").
Axiom pts_agg : forall ps, pts (agg ps) = ps.
Axiom pts_seta : forall a v c, pts (seta a v c) = pts c.
Axiom pts_setp : forall p v c, pts (setp p v c) = pts c.
Axiom geta_agg : forall a ps, geta a (agg ps) = None.
Axiom getp_agg : forall p ps, getp p (agg ps) = None.
Axiom geta_seta_same : forall a a' v c (e:a = a'), geta a' (seta a v c) = Some (rw e in v). 
Axiom getp_setp_same : forall p p' v c (e:p = p'), getp p' (setp p v c) = Some (rw e in v). 
Axiom geta_seta_other : forall a a' v c, a <> a' -> geta a' (seta a v c) = geta a' c.
Axiom getp_setp_other : forall p p' v c, p <> p' -> getp p' (setp p v c) = getp p' c.
Axiom fnd_emp : forall x, fnd x emp = None.
Axiom fnd_ins_same : forall x x' c s, x = x' -> fnd x (ins x' c s) = Some c.
Axiom fnd_ins_other : forall x x' c s, x <> x' -> fnd x (ins x' c s) = fnd x s.
Axiom dom_fnd : forall x s, In x (dom s) <-> fnd x s <> None. 

(** * Prelude *)

Definition get_att (a:A) : ID -> Read H (ty a) :=
  fun x => (fnd x) ;; (geta a).

Definition get_prp (p:P) : ID -> Read H (ty p) :=
  fun x => (fnd x) ;; (getp p).

Definition get_parts : ID -> Read H (list ID) :=
  fun x s => o <- fnd x s ; ret (pts o).

Definition domain : Read H (list ID) :=
  fun s => ret (dom s).

(** * Hierarchcial Data Description Language

CHAKRA includes a language for specifying precise logical properties of constituents and structures within hierarchies. The language consists of 5 kinds of expression, each of which can ultimately be interpreted in coq's underlying logic of [Prop]. *)

Definition HProp := H -> Prop.
Definition CProp := ID -> HProp.
Definition LProp := list ID -> HProp.
Definition CRel := ID -> ID -> HProp.
Definition LRel := list ID -> list ID -> HProp.

(** ** [HProp]

HProp is the type of unary predicates over constituent hierarchies. Applying an [p:HProp] to a structure [s:H] yields a proposition [H s] in coq's underlying logic. Definitions for basic [HProp]s are given as instances of the logical operational type classes [LIFT], [EVAL], [CONJ] and [EX]. An additional [HProp] constructor [hspec] is defined by applying an [LProp] (defined) below to the domain of a structure. *)

Definition HLift (P:Prop) : HProp :=
  fun _ => P.

Definition HEvalOption {T} (o:option T) (v:T) : HProp :=
  fun _ => o ~ v.

Definition HEvalRead {T} (op:Read H T) (v:T) : HProp :=
  fun s => op s ~ v.

Definition HEvalState {T} (op:State H T) (v:T) : HProp :=
  fun s => snd (op s) ~ v.

Definition HConj (h1 h2:HProp) : HProp :=
  fun s => h1 s /\ h2 s.

Definition HExists {T} (p:T->HProp) : HProp :=
  fun s => Exists t, p t s.

#[global]
Instance hliftp : LIFT Prop HProp := HLift.

#[global]
Instance hevaloption {T} : EVAL (option T) T HProp := HEvalOption.

#[global]
Instance hevalread {T} : EVAL (Read H T) T HProp := HEvalRead.

#[global]
Instance hevalstate {T} : EVAL (State H T) T HProp := HEvalState.

#[global]
Instance hconj : CONJ HProp := HConj.

#[global]
Instance hexists {T} : EX T HProp := HExists.

Definition HSpec (p:LProp) : HProp := Exists l, domain ~ l /\ p l.


(** ** [CProp]

[CProp] is the type of [HProp]-valued predicates over constituents. In other words, [CProp] is the type of relations between constituent identifiers [x:ID] and structures [s:H]. The basic [CProp] constructors are defined in terms of the values of attribtues, properties and particles a constituent can have. *)

Definition HasAtt (a:A) (v:ty a) : CProp :=
  fun x => (get_att a x) ~ v.

Definition HasPrp (p:P) (v:ty p) : CProp :=
  fun x => (get_prp p x) ~ v.
                                         
Definition HasParts (l: list ID) : CProp :=
  fun x => (get_parts x) ~ l.

Definition CLiftP (P:Prop) : CProp :=
  fun _ => [P]. 

Definition CLiftH (H:HProp) : CProp :=
  fun _ => H.

Definition CConj (c1 c2 : CProp) : CProp :=
  fun x => c1 x /\ c2 x.

Definition CExists {T} (p:T->CProp) : CProp :=
  fun x => Exists t, p t x.

#[global]
Instance cliftp : LIFT Prop CProp := CLiftP.

#[global]
Instance clifth : LIFT HProp CProp := CLiftH. 

#[global]
Instance cconj : CONJ CProp := CConj.

#[global]
Instance cexists {T} : EX T CProp := CExists.

(** ** [LProp]

[LProp] is the type of unary [HProp]-valued predicates over lists of identifiers. [LProp]s are used to define classes of configurations within a hierarchy. The CHAKRA HDDL includes 5 [LProp] constructors:

- [LNil l] represents the proposition that the list [l] is empty.
- [LCons x c p l] means that the head of [l] is equal to [x:ID] and satifies [c:CProp], and that the tail of the list satifies [p:LProp].
- [LAll c l] means that all elements of [l] satisfy [c:CProp].
- [LSome c l] means that at least one element of [l] satisfies [c:CProp].
- [LAllOrdPairs r l] means that at every pair [(x,y)] of elements of [l] such that [x] comes before [y] in [l], satisfy the relation [r:CRel]. This construct can be used to ascribe semantics to the ordering of lists in CHAKRA structures.
 *)

Definition LNil : LProp :=
  fun l => [l = nil].

Definition LCons : ID -> CProp -> LProp -> LProp :=
  fun x c p l => (hd_error l) ~ x /\ c x /\  p (tl l).

Inductive LAll : CProp -> LProp :=
| all_nil : forall c s, LAll c nil s
| all_cons : forall (c:CProp) x l s, c x s -> LAll c l s -> LAll c (cons x l) s.

Inductive LSome : CProp -> LProp :=
| some_head : forall (c:CProp) x l s, c x s -> LSome c (cons x l) s
| some_tail : forall (c:CProp) x l s, LSome c l s -> LSome c (cons x l) s.

Inductive LAllOrdPairs : CRel -> LProp :=
| all_op_nil : forall (r:CRel) s, LAllOrdPairs r nil s
| all_op_cons : forall (r:CRel) x l s, LAll (r x) l s -> LAllOrdPairs r l s -> LAllOrdPairs r (cons x l) s.

Definition LLiftP (P:Prop) : LProp :=
  fun _ => [P].

Definition LLiftH (H:HProp) : LProp :=
  fun _ => H.

Definition LConj (s1 s2:LProp) : LProp :=
  fun l => s1 l /\ s2 l.                                               

Definition LExists {T} (s:T->LProp) : LProp :=
  fun l => Exists t, s t l.

#[global]
Instance lliftp : LIFT Prop LProp := LLiftP.

#[global]
Instance llifth : LIFT HProp LProp := LLiftH.

#[global]
Instance lconj : CONJ LProp := LConj.

#[global]
Instance lexists {T} : EX T LProp := LExists.

(** ** [CRel]
 [CRel] is the type of [HProp]-valued relations over constituents. In other words, [CProp] is the type of ternary relations between two constituent identifiers and a structure. The CHAKRA HDDL includes two ways of constructing [CRel]s:
- [AttRel a1 a2 p x y] means that attribtue values [a1] for [x] and [a2] for [y] are related by [p:typ a1 -> typ a2 -> Prop].
- [PartRel m x y] means that the particles of [x] and [y] are related by [m:LRel].
 *)

Definition AttRel (a1 a2:A) (p:ty a1 -> ty a2 -> Prop) : CRel :=
  fun x y => Exists v1, HasAtt a1 v1 x /\ Exists v2, HasAtt a2 v2 y /\ [p v1 v2].

Definition PartRel : LRel -> CRel :=
  fun m x y => Exists l1, HasParts l1 x /\ Exists l2, HasParts l2 y /\ m l1 l2.

Definition CRLiftP (P:Prop) : CRel :=
  fun _ _ => [P].

Definition CRLiftH (H:HProp) : CRel :=
  fun _ _ => H.

Definition CRConj (r1 r2:CRel) : CRel :=
  fun x y => r1 x y /\ r2 x y.

Definition CRExists {T} (p:T->CRel) : CRel :=
  fun x y => Exists t, p t x y. 

#[global]
Instance crliftp : LIFT Prop CRel := CRLiftP.

#[global]
Instance crlifth : LIFT HProp CRel := CRLiftH.

#[global]
Instance crconj : CONJ CRel := CRConj.

#[global]
Instance crexists {T} : EX T CRel := CRExists.

(** ** [LRel]

[LRel] is the type of binary [HProp]-valued predicates over lists of constituent identifiers. [LRel] is used to express structural relationships beteen configurations of constituents in a hierarchy.
- [Pairwise c l1 l2] means that elements of [l1] and [l2] are pairwise relatd by [c:CRel].
 *)

Inductive Pairwise : CRel -> LRel :=
| pw_nil : forall r s, Pairwise r nil nil s
| pw_cons : forall (r:CRel) x l y l' s, r x y s -> Pairwise r l l' s -> Pairwise r (cons x l) (cons y l') s.

Definition LRLiftP (P:Prop) : LRel :=
  fun _ _ => [P].

Definition LRLiftH (H:HProp) : LRel :=
  fun _ _ => H.

Definition LRConj (r1 r2:LRel) : LRel :=
  fun l1 l2 => r1 l1 l2 /\ r2 l1 l2.

Definition LRExists {T} (p:T -> LRel) : LRel :=
  fun l1 l2 => Exists t, p t l1 l2.

#[global]
Instance lrliftp : LIFT Prop LRel := LRLiftP.

#[global]
Instance lrlifth : LIFT HProp LRel := LRLiftH.

#[global]
Instance lrconj : CONJ LRel := LRConj.

#[global]
Instance lrexists {T} : EX T LRel := LRExists.

(** ** A Syntax for the HDDL
 The abstract syntax of the logical language comprising the constructs defined above can reified as a mutually inductive definition: *)

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
| ATT : forall a, ty a -> (ty a -> Prop) -> CPROP
| PRT : list ID -> LPROP -> CPROP
with LPROP :=
| NIL : LPROP
| CONS : ID -> CPROP -> LPROP -> LPROP
| ALL : CPROP -> LPROP
| SOME : CPROP -> LPROP
| ALLOP : CREL -> LPROP
with CREL :=
| ATTREL : forall a1 a2:A, (ty a1 -> ty a2 -> Prop) -> CREL
| PRTREL : LREL -> CREL
with LREL :=
| PAIRWISE : CREL -> LREL
with OP : Type -> Type :=
| READOP {A} : READ A -> OP A
| OPTIONOP {A} : OPTION A -> OP A
with READ : Type -> Type :=
| GETATT : forall a, ID -> READ (ty a)
| GETPS : ID -> READ (list ID)
with OPTION : Type -> Type := 
| SIMPLEOPTION {A} : option A -> OPTION A.


(** ** Decidability *)

(** For each kind of expression we define what it means for an expression to be decidable. *)

Class HDecidable (h:HProp) := hdec: forall s:H, Decidable (h s).
Class CDecidable (c:CProp) := cdec: forall x:ID, HDecidable (c x).
Class LDecidable (r:LProp) := ldec: forall l:list ID, HDecidable (r l).
Class RDecidable (r:CRel) := rdec: forall x y, HDecidable (r x y).
Class MDecidable (m:LRel) := mdec: forall l1 l2, HDecidable (m l1 l2).

Instance lift_dec {P} `{Decidable P} : HDecidable ([P]).
firstorder. Defined.

Instance hconj_dec {H1 H2} `{HDecidable H1} `{HDecidable H2} : HDecidable (H1 /\ H2).
firstorder.
Defined.

Hint Unfold HDecidable.
Hint Unfold Decidable.
Hint Unfold Decision.
Hint Unfold hevaloption.
Hint Unfold hevalread.
Hint Unfold hevalstate.
Hint Unfold HEvalState. 
Hint Unfold HEvalRead.
Hint Unfold HEvalOption.
Hint Unfold eval.
Hint Unfold evaloption.

Instance hevaloption_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, HDecidable (@hevaloption A c a).
autounfold in *. intros.
induction c.
- induction (eqd a a0).
-- rewrite -> a1. firstorder. 
-- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined. 

Instance hevalread_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, HDecidable (@hevalread A c a).
autounfold in *. intros.
induction (c s).
- induction (eqd a a0).
-- rewrite -> a1. auto.  
-- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined. 

Instance hevalstate_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, HDecidable (@hevalstate A c a).
autounfold in *. intros.
induction (snd (c s)).
- induction (eqd a a0).
-- rewrite -> a1. auto.
-- right. intros. inversion H0. auto.
- right. intros. inversion H0.
Defined. 
