Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.

Class Functor (F:Type -> Type) :=
  { fmap {A B}: (A -> B) -> F A -> F B }.

Class Monad (F: Type -> Type) `{Functor F} :=
  { unit {A} : A -> F A;
    join {A} : F (F A) -> F A }.

Definition ret {F:Type->Type} `{Monad F} {A} : A -> F A :=
  unit. 

Definition bind {F:Type->Type} `{Monad F} {A B} : F A -> (A -> F B) -> F B :=
  fun oa f => join (fmap f oa).

Definition fish {F:Type->Type} `{Monad F} {A B C} : (A -> F B) -> (B -> F C) -> A -> F C :=
  fun f g a => bind (f a) g.

#[global]
Instance list_funtor : Functor list :=
  { fmap := map }.

#[global]
Instance list_monad : Monad list :=
  { unit {A} := fun a => cons a nil;
    join {A} := fix JOIN (lla:list (list A)) := match lla with
                                                | nil => nil
                                                | cons la lla' => app la (JOIN lla')
                                                end }.

#[global]
Instance op_functor : Functor option :=
  { fmap {A B}:= fun f oa => match oa with
                             | None => None
                             | Some a => Some (f a)
                             end }.

#[global]
Instance op_monad : Monad option :=
  { unit {A} := Some;
    join {A} := fun ooa => match ooa with
                           | None => None
                           | Some oa => oa
                           end }.

Definition Read (D A:Type) := D -> option A.

Definition State (D A:Type) := D -> prod D (option A).

#[global]
Instance read_functor {D} : Functor (Read D) :=
  { fmap {A B} := fun f ra s => fmap f (ra s) }.

#[global]
Instance read_monad {D} : Monad (Read D) :=
  { unit {A} := fun a s => ret a;
    join {A} := fun rra s => match rra s with
               | None => None
               | Some f => f s
               end }.

#[global]
Instance state_functor {D} : Functor (State D) :=
  { fmap {A B} := fun f sa s => match sa s with
                                | (s', None) => (s', None)
                                | (s', Some a) => (s', Some (f a))
                                end }.

#[global]
Instance state_monad {D} : Monad (State D) :=
  { unit {A} := fun a s => (s,Some a);
    join {A} := fun ssa s => match ssa s with
                             | (s', None) => (s', None)
                             | (s', Some sa) => sa s'
                             end }.

Class LIFT A B := lift : A -> B.

Class EVAL A B C := eval : A -> B -> C.

Class CONJ A := conj : A -> A -> A.

Class EX A B := ex : (A -> B) -> B.

Definition Decision (P:Prop) := {P}+{~P}.

Class Decidable (P:Prop) := dec : Decision P.

Instance evaloption {A} : EVAL (option A) A Prop := fun oa a => oa = Some a.
Instance conjprop : CONJ Prop := fun P Q => and P Q.
Instance exprop {A} : EX A Prop := fun p => exists t, p t.

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
