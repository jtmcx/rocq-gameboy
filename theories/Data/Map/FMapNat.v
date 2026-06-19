Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.Map.FMapPositive.

Set Implicit Arguments.
Set Strict Implicit.

(*|
An [nmap] is a [Map] with keys of type [N]. Defined as a small
wrapper around [pmap].
|*)

Section nmap.
Variable T : Type.

Variant nmap : Type :=
  NMap : option T -> pmap T -> nmap.

Definition nmap_empty : nmap := NMap None (pmap_empty T).

Definition nmap_lookup (k : N) (m : nmap) : option T :=
  match m, k with
  | (NMap x _), N0 => x
  | (NMap _ pm), Npos k' => pmap_lookup k' pm
  end.

Definition nmap_insert (k : N) (v : T) (m : nmap) : nmap :=
  match m, k with
  | (NMap _ pm), N0 => NMap (Some v) pm
  | (NMap x pm), Npos k' => NMap x (pmap_insert k' v pm)
  end.

Definition nmap_remove (k : N) (m : nmap) : nmap :=
  match m, k with
  | (NMap _ pm), N0 => NMap None pm
  | (NMap x pm), Npos k' => NMap x (pmap_remove k' pm)
  end.

Definition nmap_union (m1 m2 : nmap) : nmap :=
  match m1, m2 with
  | NMap None pm1, NMap x pm2 => NMap x (pmap_union pm1 pm2)
  | NMap (Some x) pm1, NMap _ pm2 => NMap (Some x) (pmap_union pm1 pm2)
  end.

Global Instance Map_nmap : Map N T nmap := {
  empty := nmap_empty;
  add := nmap_insert;
  remove := nmap_remove;
  lookup := nmap_lookup;
  union := nmap_union;
}.

End nmap.

Definition fmap_nmap T U (f : T -> U) (m : nmap T) : nmap U :=
  match m with
  | NMap x p => NMap (fmap f x) (fmap f p)
  end.

Global Instance Functor_nmap : Functor nmap := {
  fmap := fmap_nmap
}.
