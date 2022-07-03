(** * Introduction
    CHAKRA is a framework for hierarchical knowledge representation. This file contains the formal specification of CHAKRA's hierarchical data model, heirarchical data description language, and data processing and query language. 
 *)

(** ** Built in types *)

(** CHAKRA uses several inductively defined concrete data types: [bool], [option] and [list]. [option] and [list] are polymorphic. Generic operations for working with these polymorhic types are taken from the coq standard library. For this we import the following: *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List. 

(** ** Functors and Monads
    For convenience, we define two type classes, [Functor] and [Monad], which capture common patterns of compositionality when working with polymorphic types. The operations [fmap], [unit] and [join] can be implemented for different type constructors and used generically, leaving it to the compiler to work out which concrete implementation to use via class inference.
*)

Class Functor (F:Type -> Type) :=
  { fmap {A B}: (A -> B) -> F A -> F B }.

Class Monad (F: Type -> Type) `{Functor F} :=
  { unit {A} : A -> F A;
    join {A} : F (F A) -> F A }.

(** These classes capture generic patterns which are common to both [list] and [option] types, as well as the [Read] and [State] types defined below. Using the basic [Funtor] and [Monad] operations we define [ret], [bind] and [fish]: *)

Definition ret {F:Type->Type} `{Monad F} {A} : A -> F A :=
  unit.

Definition bind {F:Type->Type} `{Monad F} {A B} : F A -> (A -> F B) -> F B :=
  fun oa f => join (fmap f oa).

Definition fish {F:Type->Type} `{Monad F} {A B C} : (A -> F B) -> (B -> F C) -> A -> F C :=
  fun f g a => bind (f a) g.

(** ** [list] and [option]

Instances of [Functor] and [Monad] are used to define [fmap], [unit] and [join] for the [list] and [option] types. *)

Instance list_funtor : Functor list :=
  { fmap := map }.

Instance list_monad : Monad list :=
  { unit {A} := fun a => cons a nil;
    join {A} := fix JOIN (lla:list (list A)) := match lla with
                                                | nil => nil
                                                | cons la lla' => app la (JOIN lla')
                                                end }.

Instance op_functor : Functor option :=
  { fmap {A B}:= fun f oa => match oa with
                             | None => None
                             | Some a => Some (f a)
                             end }.

Instance op_monad : Monad option :=
  { unit {A} := Some;
    join {A} := fun ooa => match ooa with
                           | None => None
                           | Some oa => oa
                           end }.


(** ** [Read] and [State] Monads

    In addition to [list] and [option], two other monadic type constructors are used in the specification of CHAKRA: [Read] and [State]. The type [Read D A := D -> option A] captures computations which attempt to read values of type [A] from data structures of type [D]. The type [State D A := D -> prod D (option A)] captures computations which return a value of type [A] but also modify the data structure in the process. Both [Read] and [State] are monadic in their second argument, the return type. *)

Definition Read (D A:Type) := D -> option A.

Definition State (D A:Type) := D -> prod D (option A).

Instance read_functor {D} : Functor (Read D) :=
  { fmap {A B} := fun f ra s => fmap f (ra s) }.

Instance read_monad {D} : Monad (Read D) :=
  { unit {A} := fun a s => ret a;
    join {A} := fun rra s => match rra s with
               | None => None
               | Some f => f s
               end }.


Instance state_functor {D} : Functor (State D) :=
  { fmap {A B} := fun f sa s => match sa s with
                                | (s', None) => (s', None)
                                | (s', Some a) => (s', Some (f a))
                                end }.

Instance state_monad {D} : Monad (State D) :=
  { unit {A} := fun a s => (s,Some a);
    join {A} := fun ssa s => match ssa s with
                             | (s', None) => (s', None)
                             | (s', Some sa) => sa s'
                             end }.

(** ** Logic
Type classes are used to define common kinds of logical operations (connectives) which can be applied to a variety of different types. [LIFT] takes an expression of a logic [A] and embedds it in a new kind of logical expression [B]. [EVAL] expresses the fact that some computation in [A] evaluates to a value in [B] in a logic [C]. [CONJ] is the binary conjunction connetive for a logic [A]. [EX] is this existential quantifier for a logic [B] which binds a variable of type [A]. *)

Class LIFT A B := lift : A -> B.
Class EVAL A B C := eval : A -> B -> C.
Class CONJ A := conj : A -> A -> A.
Class EX A B := ex : (A -> B) -> B.

Definition Decision (P:Prop) := {P}+{~P}.
Class Decidable (P:Prop) := dec : Decision P.

(** *** Prop
 [Prop] is the type of coq propositions. Class instances for [CONJ] [EX] and [EVAL (option A) A] can be defined using coqs underlying definitions of conjunction, existential quantification and equality.*)

#[global]
Instance pconj : CONJ Prop :=
  fun P Q => prod P Q.

#[global]
Instance pex {T} : EX T Prop :=
  fun P => exists t, P t.

#[global]
Instance pevaloption {A} : EVAL (option A) A Prop :=
  fun c a => eq c (Some a).


(** ** Notation *)

Notation "x <- e1 ; e2" := (bind e1 (fun x => e2))
                             (right associativity, at level 60).

Notation " e1 ;; e2 " := (fish e1 e2)
                           (right associativity, at level 60).

Notation " x ~ y " := (eval x y) (at level 55).

Notation " [ P ] " := (lift P) (at level 55).

Notation " A /\ B " := (conj A B) : type_scope.

Notation "'Exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Exists' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

(** * CHAKRA Data Model

The CHAKRA data model consists of eight abstract types, one abstract type family, and 14 abstract operations. These are explained in the following sections. In addition, we define the axioms which the operations must satisfy. 

** Types

    The conceptual structure of CHAKRA's heirarchcial data model are captured by eight abstract types: [U], [C], [H], [A], [L], [D], [I] and [E]. *)

Axiom U : Set.
Axiom C : Set.
Axiom H : Set.
Axiom A : Set.
Axiom typ : A -> Set.
Axiom L : Set.
Axiom D : Set.
Axiom E : Set.
Axiom I : Set.

(** *** Identifiers
 [U] is the type of universal constituent identifiers. Elements of this type [x:U] are symbolic names which uniquely identify the constituents of a knowledge base.*)

(** *** Constituent Objects
 [C] is the type of constituent objectcs. Elements of this type [o:C] are data structures which contain information about the entity represented by the constituent.*)


(** *** Hierarchical Knowledge Structures
[H] is the type of Hierarchical Knowledge structures. Elements of the type [h:H] are data strutures which associate constituent objects with unique identifiers. *)

(** *** Attribtues
 [A] is the type of Attribtues. Each attribtue [a:A] is associated with a type [typ a] which is the type of the values of that attribtue. *)


(** *** Properties
 Four additional types capture the different kinds of property with which constituent objects can be associated: *)

(** [L] is the type of hierarchical levels. Elements of this type [s:L] indicate the level of detail being represented by a constituent. [D] is the type of domains. Elements of this type represent the ontological domain to which a constituent belongs. [E] is the type of extrinsic definitions. Elements of this type represent extrinsic categories which constituents can belong to by fiat of the user. [I] is the type of intrinsic properties of constituents. Elements of this type represent properties which derivably true of a constituent. *)

(** ** Operations
 The CHAKRA interface consists of 14 abstract operations, 6 constructor operations and 8 destructor operations: *)

Axiom delimit : list U -> C.
Axiom setAtt : forall a, typ a -> C -> C.
Axiom setInt : I -> C -> C.
Axiom setExt : E -> C -> C.
Axiom setLvl : L -> C -> C.
Axiom setDom : D -> C -> C.
Axiom emp : H.
Axiom ins : U -> C -> H -> H.
Axiom getParts : C -> list U.
Axiom getAtt : forall a:A, C -> option (typ a).
Axiom getExt : C -> option E.
Axiom getInt : C -> option I.
Axiom getLvl : C -> option L.
Axiom getDom : C -> option D.
Axiom fnd : U -> H -> option C.
Axiom dom : H -> list U.

(** ** Axioms
The abstract operations must satisfy a number of axioms. These are expressed as equations between terms which must hold for any implementation of the interface. 
 *)

Axiom u_eq_dec : forall (x y:U), Decision (x=y).
Axiom a_eq_dec : forall (a b:A), Decision (a=b).
(* begin hide *)
Notation "'rw' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rw' H in '/' H' ']'").
(* end hide *)
Axiom parts_delim : forall ps, getParts (delimit ps) = ps.
Axiom parts_set : forall a v c, getParts (setAtt a v c) = getParts c.
Axiom get_delim : forall a ps, getAtt a (delimit ps) = None.
Axiom get_set_same : forall a a' v c (e:a = a'), getAtt a' (setAtt a v c) = Some (rw e in v). 
Axiom get_set_other : forall a a' v c, a <> a' -> getAtt a' (setAtt a v c) = getAtt a' c.
Axiom fnd_emp : forall x, fnd x emp = None.
Axiom fnd_ins_same : forall x x' c s, x = x' -> fnd x (ins x' c s) = Some c.
Axiom fnd_ins_other : forall x x' c s, x <> x' -> fnd x (ins x' c s) = fnd x s.
Axiom dom_fnd : forall x s, In x (dom s) <-> fnd x s <> None. 

(** ** Derived Operations
 Additional operations for accessing and manipulating constituents and hierarchical structures can be defined from the basic operations in the types [Read H] and [State H] *)

Definition get_att (a:A) : U -> Read H (typ a) :=
  fun x => (fnd x) ;; (getAtt a).

Definition get_parts : U -> Read H (list U) :=
  fun x s => o <- fnd x s ; ret (getParts o).

Definition get_ext : U -> Read H E :=
  fun x => fnd x ;; getExt.

Definition get_int : U -> Read H I :=
  fun x => fnd x ;; getInt.

Definition get_lvl : U -> Read H L :=
  fun x => fnd x ;; getLvl.

Definition get_dom : U -> Read H D :=
  fun x => fnd x ;; getDom.

Definition domain : Read H (list U) :=
  fun s => ret (dom s).

(** * Hierarchcial Data Description Language
CHAKRA includes a language for specifying precise logical properties of constituents and structures within hierarchies. The language consists of 5 kinds of expression, each of which can ultimately be interpreted in coq's underlying logic of [Prop]. *)

Definition HProp := H -> Prop.
Definition CProp := U -> HProp.
Definition LProp := list U -> HProp.
Definition CRel := U -> U -> HProp.
Definition LRel := list U -> list U -> HProp.

(** ** [HProp]
 HProp is the type of unary predicates over constituent hierarchies. Applying an [p:HProp] to a structure [s:H] yields a proposition [H s] in coq's underlying logic. Definitions for basic [HProp]s are given as instances of the logical operational type classes [LIFT], [EVAL], [CONJ] and [EX]. An additional [HProp] constructor [hspec] is defined by applying an [LProp] (defined) below to the domain of a structure. *)

#[global]
Instance hliftp : LIFT Prop HProp :=
  fun P _ => P.
#[global]
Instance hevalread {T} : EVAL (Read H T) T HProp :=
  fun c t s => c s ~ t.
#[global]
Instance hevalstate {T} : EVAL (State H T) T HProp :=
  fun c t s => snd (c s) ~ t.
#[global]
Instance hevaloption {T} : EVAL (option T) T HProp :=
  fun c v s => c ~ v.
#[global]
Instance hconj : CONJ HProp :=
  fun h1 h2 s => (h1 s) /\ (h2 s).
#[global]
Instance hex {T} : EX T HProp :=
  fun p s => Exists t, p t s. 
#[global]
Definition hspec : LProp -> HProp :=
  fun p => Exists l, domain ~ l /\ p l.

(** ** [CProp]
[CProp] is the type of [HProp]-valued predicates over constituents. In other words, [CProp] is the type of relations between constituent identifiers [x:U] and structures [s:H]. The basic [CProp] constructors are defined in terms of the values of attribtues, properties and particles a constituent can have. *)

Definition HasAtt (a:A) (v:typ a) : CProp :=
  fun x => (get_att a x) ~ v.

Definition HasParts (l: list U) : CProp :=
  fun x => (get_parts x) ~ l.

Definition AtLevel (l:L) : CProp :=
  fun x => (get_lvl x) ~ l.

Definition InDomain (d:D) : CProp :=
  fun x => (get_dom x) ~ d.

Definition HasExt (e:E) : CProp :=
  fun x => (get_ext x) ~ e.

#[global]
Instance cliftp : LIFT Prop CProp :=
  fun P _ => [P].
#[global]
Instance clifth : LIFT HProp CProp :=
  fun h _ => h.  
#[global]
Instance cconj : CONJ CProp :=
  fun Q R x => (Q x) /\ (R x).
#[global]
Instance cex {T} : EX T CProp :=
  fun p x => Exists t , p t x.

(** ** [LProp]
 [LProp] is the type of unary [HProp]-valued predicates over lists of identifiers. [LProp]s are used to define classes of configurations within a hierarchy. The CHAKRA HDDL includes 5 [LProp] constructors:
- [LNil l] represents the proposition that the list [l] is empty.
- [LCons x c p l] means that the head of [l] is equal to [x:U] and satifies [c:CProp], and that the tail of the list satifies [p:LProp].
- [LAll c l] means that all elements of [l] satisfy [c:CProp].
- [LSome c l] means that at least one element of [l] satisfies [c:CProp].
- [LAllOrdPairs r l] means that at every pair [(x,y)] of elements of [l] such that [x] comes before [y] in [l], satisfy the relation [r:CRel]. This construct can be used to ascribe semantics to the ordering of lists in CHAKRA structures.
 *)

Definition LNil : LProp :=
  fun l => [l = nil].

Definition LCons : U -> CProp -> LProp -> LProp :=
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

#[global]
Instance lliftp : LIFT Prop LProp :=
  fun P _ => [P].

#[global]
Instance llifth : LIFT HProp LProp :=
  fun h _ => h.

#[global]
Instance lconj : CONJ LProp :=
  fun p q l => p l /\ q l.

#[global]
Instance lex {T} : EX T LProp :=
  fun p l => Exists t, p t l.

(** ** [CRel]
 [CRel] is the type of [HProp]-valued relations over constituents. In other words, [CProp] is the type of ternary relations between two constituent identifiers and a structure. The CHAKRA HDDL includes two ways of constructing [CRel]s:
- [AttRel a1 a2 p x y] means that attribtue values [a1] for [x] and [a2] for [y] are related by [p:typ a1 -> typ a2 -> Prop].
- [PartRel m x y] means that the particles of [x] and [y] are related by [m:LRel].
 *)

Definition AttRel (a1 a2:A) (p:typ a1 -> typ a2 -> Prop) : CRel :=
  fun x y => Exists v1, HasAtt a1 v1 x /\ Exists v2, HasAtt a2 v2 y /\ [p v1 v2].

Definition PartRel : LRel -> CRel :=
  fun m x y => Exists l1, HasParts l1 x /\ Exists l2, HasParts l2 y /\ m l1 l2.

#[global]
Instance crliftp : LIFT Prop CRel :=
  fun P _ _ => [P].

#[global]
Instance crlifth : LIFT HProp CRel :=
  fun h _ _ => h.

#[global]
Instance crconj : CONJ CRel :=
  fun r1 r2 x y => r1 x y /\ r2 x y.

#[global]
Instance crex {T} : EX T CRel :=
  fun p x y => Exists t, p t x y.

(** ** [LRel]
 [LRel] is the type of binary [HProp]-valued predicates over lists of constituent identifiers. [LRel] is used to express structural relationships beteen configurations of constituents in a hierarchy.
- [Pairwise c l1 l2] means that elements of [l1] and [l2] are pairwise relatd by [c:CRel].
 *)

Inductive Pairwise : CRel -> LRel :=
| pw_nil : forall r s, Pairwise r nil nil s
| pw_cons : forall (r:CRel) x l y l' s, r x y s -> Pairwise r l l' s -> Pairwise r (cons x l) (cons y l') s.

#[global]
Instance lrliftp : LIFT Prop LRel :=
  fun P _ _ => [P].

#[global]
Instance lrlifth : LIFT HProp LRel :=
  fun h _ _ => h.

#[global]
Instance lrconj : CONJ LRel :=
  fun r1 r2 l1 l2 => r1 l1 l2 /\ r2 l1 l2.

#[global]
Instance lrex {T} : EX T LRel :=
  fun p l1 l2 => Exists t, p t l1 l2.

(** ** A Syntax for the HDDL
 The abstract syntax of the logical language comprising the constructs defined above can reified as a mutually inductive definition: *)

Inductive HPROP :=
| HLIFT : Prop -> HPROP
| EVALS {A} : OP A -> A -> HPROP
| HCONJ : HPROP -> HPROP -> HPROP
| HEXISTS {T} : (T -> HPROP) -> HPROP
| HSPEC : LPROP -> HPROP
| CAPP : CPROP -> U -> HPROP
| CRAPP : CREL -> U -> U -> HPROP
| LAPP : LPROP -> list U -> HPROP
| LRAPP : LREL -> list U -> list U -> HPROP 
with CPROP :=
| CLIFTP : Prop -> CPROP
| CLIFTH : HPROP -> CPROP
| CCONJ : CPROP -> CPROP -> CPROP
| CEXISTS {T} : (T -> CPROP) -> CPROP
| ATT : forall a, typ a -> (typ a -> Prop) -> CPROP
| PRT : list U -> LPROP -> CPROP
with LPROP :=
| NIL : LPROP
| CONS : U -> CPROP -> LPROP -> LPROP
| ALL : CPROP -> LPROP
| SOME : CPROP -> LPROP
| ALLOP : CREL -> LPROP
with CREL :=
| ATTREL : forall a1 a2:A, (typ a1 -> typ a2 -> Prop) -> CREL
| PRTREL : LREL -> CREL
with LREL :=
| PAIRWISE : CREL -> LREL
with OP : Type -> Type :=
| READOP {A} : READ A -> OP A
| OPTIONOP {A} : OPTION A -> OP A
with READ : Type -> Type :=
| GETATT : forall a, U -> READ (typ a)
| GETPS : U -> READ (list U)
with OPTION : Type -> Type := 
| SIMPLEOPTION {A} : option A -> OPTION A.



(** ** Decidability *)

(** For each kind of expression we define what it means for an expression to be decidable. *)

Class HDecidable (h:HProp) := hdec: forall s:H, Decidable (h s).
Class CDecidable (c:CProp) := cdec: forall x:U, HDecidable (c x).
Class LDecidable (r:LProp) := ldec: forall l:list U, HDecidable (r l).
Class RDecidable (r:CRel) := rdec: forall x y, HDecidable (r x y).
Class MDecidable (m:LRel) := mdec: forall l1 l2, HDecidable (m l1 l2).

Instance lift_dec {P} `{Decidable P} : HDecidable ([P]).
firstorder. Defined.

Instance hconj_dec {H1 H2} `{HDecidable H1} `{HDecidable H2} : HDecidable (H1 /\ H2).
firstorder.
Defined.

Instance hevaloption_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, HDecidable (@hevaloption A c a).
unfold HDecidable. unfold Decidable. unfold hevaloption. unfold eval. unfold pevaloption. intros.
induction c.
- induction (eqd a a0).
-- rewrite -> a1. firstorder. 
-- right. unfold not in *. intros. inversion H0. firstorder.
- right. autounfold in *. intros. inversion H0.
Defined. 

Instance hevalread_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, HDecidable (@hevalread A c a).
unfold HDecidable, Decidable, hevalread in *. intros.
induction (c s).
- induction (eqd a a0).
-- rewrite -> a1. firstorder. 
-- right. unfold not in *. unfold eval, pevaloption. intros. inversion H0. firstorder.
- right. autounfold in *. unfold eval, pevaloption in *. intros. inversion H0.
Defined. 

Instance hevalstate_dec A {eqd:forall (x y:A),Decidable(x=y)} : forall c a, HDecidable (@hevalstate A c a).
unfold HDecidable, Decidable, hevalstate in *. intros.
induction (snd (c s)).
- induction (eqd a a0).
-- rewrite -> a1. firstorder. 
-- right. unfold not in *. unfold eval, pevaloption. intros. inversion H0. firstorder.
- right. autounfold in *. unfold eval, pevaloption in *. intros. inversion H0.
Defined. 
