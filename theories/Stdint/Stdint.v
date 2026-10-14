From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Local Open Scope bool_scope.

(*|
This module defines machine-width integers. It defines the types `i8`,
`i16`, `i32`, `i64`, `u8`, `u16`, `u32`, and `u16`. It takes heavy
inspiration from the [Integers] module Compcert. (TODO: for this reason,
this file should be licenses as LGPL v2.1!). The definitions in this file
roughly mirror the definitions in the [ocaml-stdint] library. Extracting
code after importing `StdintExtraction` will eventually generate OCaml
code that uses the ocaml-stdint library.

[Integers]: https://compcert.org/doc/html/compcert.lib.Integers.html
[ocaml-stdint]: https://ocaml.org/p/stdint/latest

Each integer type has its own notation scope (including number notations),
which make it easy to perform arbitrary modular arithmetic in Rocq:

```
Eval cbv in ((0x55 .^ 0xAA) + 0x42)%u8.
    = 0x41%u8 : Uint8.t
```
|*)

Module Type Width.
  Parameter width : positive.
End Width.

Module MakeInt(W : Width).
  Include W.
  Local Open Scope Z_scope.

  Definition modulus : Z := 2 ^ (Zpos width).
  Definition half_modulus : Z := modulus / 2.

  Definition in_signed_range : Z -> bool :=
    fun z => (-half_modulus <=? z) && (z <? half_modulus).

  Definition in_unsigned_range : Z -> bool :=
    fun z => (0 <=? z) && (z <? modulus).

  Record t := Int {
    value : Z;
    value_range : true = in_unsigned_range value;
  }.

  Definition unsigned x : Z := value x.

  Definition signed x : Z :=
    let u := unsigned x in 
    if half_modulus <=? u then u - modulus else u.

  Definition from_unsigned z : option t :=
    match sumbool_of_bool (in_unsigned_range z) with
    | left H => Some (Int z (eq_sym H))
    | right _ => None
    end.

  Definition from_signed z : option t :=
    if in_signed_range z
      then from_unsigned (z mod modulus)
      else None.

  Lemma modulus_positive :
    0 < modulus.
  Proof.
    unfold modulus. apply Z.pow_pos_nonneg; lia. 
  Qed.

  Lemma mod_modulus_in_unsigned_range : forall z,
    in_unsigned_range (z mod modulus) = true.
  Proof.
    intros.
    unfold in_unsigned_range.
    apply andb_true_intro.
    rewrite Z.leb_le, Z.ltb_lt.
    apply Z.mod_pos_bound.
    apply modulus_positive.
  Qed.

  Program Definition wrap : Z -> t :=
    fun z => match from_unsigned (z mod modulus) with
    | Some x => x
    | None   => _ (* impossible *)
    end.
  Next Obligation.
    unfold from_unsigned in *.
    destruct sumbool_of_bool.
    discriminate.
    rewrite mod_modulus_in_unsigned_range in e.
    discriminate.
  Qed.

  Definition add : t -> t -> t :=
    fun x y => wrap (unsigned x + unsigned y).

  Definition sub : t -> t -> t :=
    fun x y => wrap (unsigned x - unsigned y).

  Definition mul : t -> t -> t :=
    fun x y => wrap (unsigned x * unsigned y).

  Definition succ : t -> t :=
    fun x => wrap (Z.succ (unsigned x)).

  Definition pred : t -> t :=
    fun x => wrap (Z.pred (unsigned x)).

  Definition land : t -> t -> t :=
    fun x y => wrap (Z.land (unsigned x) (unsigned y)).

  Definition lor : t -> t -> t :=
    fun x y => wrap (Z.lor (unsigned x) (unsigned y)).

  Definition lxor : t -> t -> t :=
    fun x y => wrap (Z.lxor (unsigned x) (unsigned y)).

  Definition lnot : t -> t :=
    fun x => wrap (Z.lnot (unsigned x)).

  Definition shl : t -> t -> t :=
    fun x k => wrap (Z.shiftl (unsigned x) (unsigned k)).

  Definition eqb : t -> t -> bool :=
    fun x y => Z.eqb (unsigned x) (unsigned y).
End MakeInt.


Module MakeSigned(W : Width).
  Include MakeInt(W).

  Definition shr : t -> t -> t :=
    fun x k => wrap (Z.shiftr (signed x) (unsigned k)).

  Definition compare : t -> t -> comparison :=
    fun x y => Z.compare (signed x) (signed y).

  Definition ltb : t -> t -> bool :=
    fun x y => Z.ltb (signed x) (signed y).

  Definition leb : t -> t -> bool :=
    fun x y => Z.leb (signed x) (signed y).

  Definition geb : t -> t -> bool :=
    fun x y => Z.leb (signed y) (signed x).

  Definition gtb : t -> t -> bool :=
    fun x y => Z.ltb (signed y) (signed x).

  Definition lt : t -> t -> Prop :=
    fun x y => ltb x y = true.

  Definition le : t -> t -> Prop :=
    fun x y => leb x y = true.

  Definition ge : t -> t -> Prop :=
    fun x y => geb x y = true.

  Definition gt : t -> t -> Prop :=
    fun x y => gtb x y = true.

  Definition to_num : t -> Number.int :=
    fun b => Z.to_num_int (signed b).

  Definition to_hex : t -> Number.int :=
    fun b => Z.to_num_hex_int (signed b).

  Definition of_num : Number.int -> option t :=
    fun b => from_signed (Z.of_num_int b).

End MakeSigned.


Module MakeUnsigned(W : Width).
  Include MakeInt(W).

  Definition shr : t -> t -> t :=
    fun x k => wrap (Z.shiftr (unsigned x) (unsigned k)).

  Definition compare : t -> t -> comparison :=
    fun x y => Z.compare (unsigned x) (unsigned y).

  Definition ltb : t -> t -> bool :=
    fun x y => Z.ltb (unsigned x) (unsigned y).

  Definition leb : t -> t -> bool :=
    fun x y => Z.leb (unsigned x) (unsigned y).

  Definition geb : t -> t -> bool :=
    fun x y => Z.leb (unsigned y) (unsigned x).

  Definition gtb : t -> t -> bool :=
    fun x y => Z.ltb (unsigned y) (unsigned x).

  Definition lt : t -> t -> Prop :=
    fun x y => ltb x y = true.

  Definition le : t -> t -> Prop :=
    fun x y => leb x y = true.

  Definition ge : t -> t -> Prop :=
    fun x y => geb x y = true.

  Definition gt : t -> t -> Prop :=
    fun x y => gtb x y = true.

  Definition to_num : t -> Number.int :=
    fun b => Z.to_num_int (unsigned b).

  Definition to_hex : t -> Number.int :=
    fun b => Z.to_num_hex_int (unsigned b).

  Definition of_num : Number.int -> option t :=
    fun b => from_unsigned (Z.of_num_int b).

End MakeUnsigned.

Module Width8 <: Width.
  Definition width := 8%positive.
End Width8.

Module Width16 <: Width.
  Definition width := 16%positive.
End Width16.

Module Width32 <: Width.
  Definition width := 32%positive.
End Width32.

Module Width64 <: Width.
  Definition width := 64%positive.
End Width64.

Module Int8 := MakeSigned(Width8).
Module Int16 := MakeSigned(Width16).
Module Int32 := MakeSigned(Width32).
Module Int64 := MakeSigned(Width64).
Module Uint8 := MakeUnsigned(Width8).
Module Uint16 := MakeUnsigned(Width16).
Module Uint32 := MakeUnsigned(Width32).
Module Uint64 := MakeUnsigned(Width64).

Definition i8 : Type := Int8.t.
Definition i16 : Type := Int16.t.
Definition i32 : Type := Int32.t.
Definition i64 : Type := Int64.t.
Definition u8 : Type := Uint8.t.
Definition u16 : Type := Uint16.t.
Definition u32 : Type := Uint32.t.
Definition u64 : Type := Uint64.t.

Program Definition i8_to_i16 : i8 -> i16 :=
  fun x => Int16.wrap (Int8.signed x).

Program Definition i8_to_i32 : i8 -> i32 :=
  fun x => Int32.wrap (Int8.signed x).

Program Definition i8_to_i64 : i8 -> i64 :=
  fun x => Int64.wrap (Int8.signed x).

Program Definition i16_to_i8 : i16 -> i8 :=
  fun x => Int8.wrap (Int16.signed x).

Program Definition i16_to_i32 : i16 -> i32 :=
  fun x => Int32.wrap (Int16.signed x).

Program Definition i16_to_i64 : i16 -> i64 :=
  fun x => Int64.wrap (Int16.signed x).

Program Definition i32_to_i8 : i32 -> i8 :=
  fun x => Int8.wrap (Int32.signed x).

Program Definition i32_to_i16 : i32 -> i16 :=
  fun x => Int16.wrap (Int32.signed x).

Program Definition i32_to_i64 : i32 -> i64 :=
  fun x => Int64.wrap (Int32.signed x).

Program Definition i64_to_i8 : i64 -> i8 :=
  fun x => Int8.wrap (Int64.signed x).

Program Definition i64_to_i16 : i64 -> i16 :=
  fun x => Int16.wrap (Int64.signed x).

Program Definition i64_to_i32 : i64 -> i32 :=
  fun x => Int32.wrap (Int64.signed x).

Program Definition u8_to_u16 : u8 -> u16 :=
  fun x => Uint16.wrap (Uint8.unsigned x).

Program Definition u8_to_u32 : u8 -> u32 :=
  fun x => Uint32.wrap (Uint8.unsigned x).

Program Definition u8_to_u64 : u8 -> u64 :=
  fun x => Uint64.wrap (Uint8.unsigned x).

Program Definition u16_to_u8 : u16 -> u8 :=
  fun x => Uint8.wrap (Uint16.unsigned x).

Program Definition u16_to_u32 : u16 -> u32 :=
  fun x => Uint32.wrap (Uint16.unsigned x).

Program Definition u16_to_u64 : u16 -> u64 :=
  fun x => Uint64.wrap (Uint16.unsigned x).

Program Definition u32_to_u8 : u32 -> u8 :=
  fun x => Uint8.wrap (Uint32.unsigned x).

Program Definition u32_to_u16 : u32 -> u16 :=
  fun x => Uint16.wrap (Uint32.unsigned x).

Program Definition u32_to_u64 : u32 -> u64 :=
  fun x => Uint64.wrap (Uint32.unsigned x).

Program Definition u64_to_u8 : u64 -> u8 :=
  fun x => Uint8.wrap (Uint64.unsigned x).

Program Definition u64_to_u16 : u64 -> u16 :=
  fun x => Uint16.wrap (Uint64.unsigned x).

Program Definition u64_to_u32 : u64 -> u32 :=
  fun x => Uint32.wrap (Uint64.unsigned x).

Program Definition u8_to_i8 : u8 -> i8 :=
  fun '(Uint8.Int x H) => Int8.Int x H.

Program Definition u16_to_i16 : u16 -> i16 :=
  fun '(Uint16.Int x H) => Int16.Int x H.

Program Definition u32_to_i32 : u32 -> i32 :=
  fun '(Uint32.Int x H) => Int32.Int x H.

Program Definition u64_to_i64 : u64 -> i64 :=
  fun '(Uint64.Int x H) => Int64.Int x H.

Program Definition i8_to_u8 : i8 -> u8 :=
  fun '(Int8.Int x H) => Uint8.Int x H.

Program Definition i16_to_u16 : i16 -> u16 :=
  fun '(Int16.Int x H) => Uint16.Int x H.

Program Definition i32_to_u32 : i32 -> u32 :=
  fun '(Int32.Int x H) => Uint32.Int x H.

Program Definition i64_to_u64 : i64 -> u64 :=
  fun '(Int64.Int x H) => Uint64.Int x H.

(*|
## Notations

Unfortunately, we can't parameterize notations by scope, so we have to
define the same notations for each integer type.
|*)

Declare Scope i8_scope.
Delimit Scope i8_scope with i8.
Bind Scope i8_scope with i8.

Number Notation Int8.t Int8.of_num Int8.to_hex : i8_scope.

Notation "x + y"  := (Int8.add x y) : i8_scope.
Notation "x - y"  := (Int8.sub x y) : i8_scope.
Notation "x * y"  := (Int8.mul x y) : i8_scope.
Notation "x .& y" := (Int8.land x y) (at level 40) : i8_scope.
Notation "x .| y" := (Int8.lor x y) (at level 40) : i8_scope.
Notation "x .^ y" := (Int8.lxor x y) (at level 40) : i8_scope.
Notation ".~ x"   := (Int8.lnot x) (at level 35) : i8_scope.
Notation "x << y" := (Int8.shl x y) (at level 40) : i8_scope.
Notation "x >> y" := (Int8.shr x y) (at level 40) : i8_scope.
Notation "x < y"  := (Int8.lt x y) : i8_scope.
Notation "x <= y" := (Int8.le x y) : i8_scope.
Notation "x >= y" := (Int8.ge x y) : i8_scope.
Notation "x > y"  := (Int8.gt x y) : i8_scope.
Notation "x ?= y" := (Int8.compare x y) : i8_scope.
Notation "x <? y" := (Int8.ltb x y) : i8_scope.
Notation "x <=? y":= (Int8.leb x y) : i8_scope.
Notation "x =? y" := (Int8.eqb x y) : i8_scope.
Notation "x >=? y":= (Int8.geb x y) : i8_scope.
Notation "x >? y" := (Int8.gtb x y) : i8_scope.

Declare Scope u8_scope.
Delimit Scope u8_scope with u8.
Bind Scope u8_scope with u8.

Number Notation Uint8.t Uint8.of_num Uint8.to_hex : u8_scope.

Notation "x + y"  := (Uint8.add x y) : u8_scope.
Notation "x - y"  := (Uint8.sub x y) : u8_scope.
Notation "x * y"  := (Uint8.mul x y) : u8_scope.
Notation "x .& y" := (Uint8.land x y) (at level 40) : u8_scope.
Notation "x .| y" := (Uint8.lor x y) (at level 40) : u8_scope.
Notation "x .^ y" := (Uint8.lxor x y) (at level 40) : u8_scope.
Notation ".~ x"   := (Uint8.lnot x) (at level 35) : u8_scope.
Notation "x << y" := (Uint8.shl x y) (at level 40) : u8_scope.
Notation "x >> y" := (Uint8.shr x y) (at level 40) : u8_scope.
Notation "x < y"  := (Uint8.lt x y) : u8_scope.
Notation "x <= y" := (Uint8.le x y) : u8_scope.
Notation "x >= y" := (Uint8.ge x y) : u8_scope.
Notation "x > y"  := (Uint8.gt x y) : u8_scope.
Notation "x ?= y" := (Uint8.compare x y) : u8_scope.
Notation "x <? y" := (Uint8.ltb x y) : u8_scope.
Notation "x <=? y":= (Uint8.leb x y) : u8_scope.
Notation "x =? y" := (Uint8.eqb x y) : u8_scope.
Notation "x >=? y":= (Uint8.geb x y) : u8_scope.
Notation "x >? y" := (Uint8.gtb x y) : u8_scope.

Declare Scope i16_scope.
Delimit Scope i16_scope with i16.
Bind Scope i16_scope with i16.

Number Notation Int16.t Int16.of_num Int16.to_hex : i16_scope.

Notation "x + y"  := (Int16.add x y) : i16_scope.
Notation "x - y"  := (Int16.sub x y) : i16_scope.
Notation "x * y"  := (Int16.mul x y) : i16_scope.
Notation "x .& y" := (Int16.land x y) (at level 40) : i16_scope.
Notation "x .| y" := (Int16.lor x y) (at level 40) : i16_scope.
Notation "x .^ y" := (Int16.lxor x y) (at level 40) : i16_scope.
Notation ".~ x"   := (Int16.lnot x) (at level 35) : i16_scope.
Notation "x << y" := (Int16.shl x y) (at level 40) : i16_scope.
Notation "x >> y" := (Int16.shr x y) (at level 40) : i16_scope.
Notation "x < y"  := (Int16.lt x y) : i16_scope.
Notation "x <= y" := (Int16.le x y) : i16_scope.
Notation "x >= y" := (Int16.ge x y) : i16_scope.
Notation "x > y"  := (Int16.gt x y) : i16_scope.
Notation "x ?= y" := (Int16.compare x y) : i16_scope.
Notation "x <? y" := (Int16.ltb x y) : i16_scope.
Notation "x <=? y":= (Int16.leb x y) : i16_scope.
Notation "x =? y" := (Int16.eqb x y) : i16_scope.
Notation "x >=? y":= (Int16.geb x y) : i16_scope.
Notation "x >? y" := (Int16.gtb x y) : i16_scope.

Declare Scope u16_scope.
Delimit Scope u16_scope with u16.
Bind Scope u16_scope with u16.

Number Notation Uint16.t Uint16.of_num Uint16.to_hex : u16_scope.

Notation "x + y"  := (Uint16.add x y) : u16_scope.
Notation "x - y"  := (Uint16.sub x y) : u16_scope.
Notation "x * y"  := (Uint16.mul x y) : u16_scope.
Notation "x .& y" := (Uint16.land x y) (at level 40) : u16_scope.
Notation "x .| y" := (Uint16.lor x y) (at level 40) : u16_scope.
Notation "x .^ y" := (Uint16.lxor x y) (at level 40) : u16_scope.
Notation ".~ x"   := (Uint16.lnot x) (at level 35) : u16_scope.
Notation "x << y" := (Uint16.shl x y) (at level 40) : u16_scope.
Notation "x >> y" := (Uint16.shr x y) (at level 40) : u16_scope.
Notation "x < y"  := (Uint16.lt x y) : u16_scope.
Notation "x <= y" := (Uint16.le x y) : u16_scope.
Notation "x >= y" := (Uint16.ge x y) : u16_scope.
Notation "x > y"  := (Uint16.gt x y) : u16_scope.
Notation "x ?= y" := (Uint16.compare x y) : u16_scope.
Notation "x <? y" := (Uint16.ltb x y) : u16_scope.
Notation "x <=? y":= (Uint16.leb x y) : u16_scope.
Notation "x =? y" := (Uint16.eqb x y) : u16_scope.
Notation "x >=? y":= (Uint16.geb x y) : u16_scope.
Notation "x >? y" := (Uint16.gtb x y) : u16_scope.