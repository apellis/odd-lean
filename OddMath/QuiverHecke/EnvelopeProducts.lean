/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EnvelopeDividedPowers
import StringDiagrams.Super.KarOf

/-!
# Products of words in `K₀(Ḣ_{q,π})`

Brundan–Ellis, arXiv:1701.04133v2, (11.2): `K₀(Ḣ_{q,π})` is an algebra whose product is the
induction product, `[P(s)] [P(t)] = [P(st)]` on the projectives `P(t) = H 1_t` of words.

`K₀Ring` multiplies horizontal composites in diagrammatic order (`[G] · [F] = [F ≫ G]`), and
horizontal composition in `Ḣ_{q,π}` is the tensor product of `H`, which concatenates words. So
BE2's algebra is the opposite ring `KHop := (KH)ᵐᵒᵖ`, in which
`wordCls s * wordCls t = wordCls (s ++ t)` (`wordCls_mul`).

The classes in `K₀(HKar)` (`OddMath.QuiverHecke.EnvelopeDividedPowers`) map to `KH` along
`hKarToKH`, the map induced by the identity functor of the 1-morphism category; it sends
`[word t]` to the class of the word (`hKarToKH_word`).
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams MonoidalCategory

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- The identity functor from `HKar` to the 1-morphism category `HCat` (the two are
definitionally equal categories, with instances found along different paths). -/
def hKarToHCat : HKar (k := k) D Sc sy hc ⥤ HCat D Sc sy hc where
  obj P := P
  map f := f

instance : (hKarToHCat D Sc sy hc).Additive := ⟨rfl⟩

/-- `K₀(HKar) → K₀(Ḣ_{q,π})`. -/
def hKarToKH : K₀ (HKar (k := k) D Sc sy hc) →+ KH D Sc sy hc :=
  (K₀Ring.of _ _).comp (K₀.map (hKarToHCat D Sc sy hc))

/-- The class of a word in `K₀(Ḣ_{q,π})`. -/
def wordClass (t : List I) : KH D Sc sy hc :=
  K₀Ring.mk (GSKAR.of k (𝔄 := MonoidalTwo (HGr D Sc sy hc)) (a := MonoidalTwo.star _)
    (b := MonoidalTwo.star _) (hObj D Sc sy hc t))

theorem hKarToKH_word (t : List I) :
    hKarToKH D Sc sy hc (K₀.mk (word D Sc sy hc t)) = wordClass D Sc sy hc t := by
  rw [hKarToKH, AddMonoidHom.comp_apply, K₀.map_mk]
  rfl

/-- Horizontal composition of words in `MonoidalTwo HGr` is concatenation. -/
theorem hObj_comp (s t : List I) :
    CategoryStruct.comp (obj := MonoidalTwo (HGr D Sc sy hc)) (X := MonoidalTwo.star _)
      (Y := MonoidalTwo.star _) (Z := MonoidalTwo.star _) (hObj D Sc sy hc s)
      (hObj D Sc sy hc t) = hObj D Sc sy hc (s ++ t) := rfl

/-- Concatenation in `K₀Ring` order: `[t] · [s] = [s t]`. -/
theorem wordClass_mul_wordClass (s t : List I) :
    wordClass D Sc sy hc t * wordClass D Sc sy hc s = wordClass D Sc sy hc (s ++ t) := by
  have h := GSKAR.mk_of_mul_mk_of k (a := MonoidalTwo.star (HGr D Sc sy hc))
    (b := MonoidalTwo.star _) (c := MonoidalTwo.star _) (hObj D Sc sy hc s) (hObj D Sc sy hc t)
  rw [hObj_comp] at h
  exact h

/-- **BE2 (11.2).** `K₀(Ḣ_{q,π})` with BE2's multiplication, the induction product. -/
abbrev KHop := (KH D Sc sy hc)ᵐᵒᵖ

/-- The class `[P(t)]` of a word in `KHop`. -/
def wordCls (t : List I) : KHop D Sc sy hc := MulOpposite.op (wordClass D Sc sy hc t)

/-- **BE2 (11.2)**: the induction product of words is concatenation, `[P(s)] [P(t)] = [P(st)]`. -/
theorem wordCls_mul (s t : List I) :
    wordCls D Sc sy hc s * wordCls D Sc sy hc t = wordCls D Sc sy hc (s ++ t) := by
  rw [wordCls, wordCls, ← MulOpposite.op_mul, wordClass_mul_wordClass]
  rfl

end OddMath.QuiverHecke
