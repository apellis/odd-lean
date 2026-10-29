/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Quad
import OddMath.QuiverHecke.SwappedAssembly.Slides
import OddMath.QuiverHecke.SwappedAssembly.Braid
import OddMath.QuiverHecke.SwappedAssembly.Zigzag
import OddMath.QuiverHecke.SwappedAssembly.Inversion
import OddMath.QuiverHecke.SwappedAssembly.WindowZero
import OddMath.QuiverHecke.SwappedAssembly.Interchange

/-! # Assembly of the swapped action

The relation modules of `OddMath.QuiverHecke.SwappedAssembly` reduce each defining relation
of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5 and
(2.6), and the super interchange law, in the swapped layer representation
`P.layerRep Gs Ys gens` to entrywise identities for the generator images:

* (1.7): `CrossQuad` (`quadRelations`);
* (1.8): `CrossSlide` (`slideRelations`);
* (1.9): `CrossBraid` (`braidRelations`);
* (1.10): `CupCapZigzag` (`zigzagRelations`);
* (1.11)–(1.14): `SigmaPermutation` and `LeftwardData.IsInverse` (`inversionRelations`);
* (2.6): `DcupDcapWindowZero` (`windowZeroRelations`);
* the interchange law: `GeneratorsSupernatural` (`interchangeLaw`).

`SwappedRelationData c L` bundles these identities for the swapped generators
`P.swappedGens c L`; `SwappedRelationData.obligations` gives `SwappedObligations`, hence the
functor out of the presented 2-category and the upward module action at every rightmost weight
(`SwappedRelationData.upwardModuleAction`).

Main declarations: `ProbeReservoir.SwappedRelationData`,
`ProbeReservoir.SwappedRelationData.obligations`,
`ProbeReservoir.SwappedRelationData.upwardModuleAction`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- **The entrywise identities for the swapped generators** `P.swappedGens c L`, one for each
group of relations of Definition 1.5 and (2.6) and one for the interchange law. -/
structure SwappedRelationData (c : P.CrossCoeff) (L : P.LeftwardData) : Prop where
  /-- (1.7). -/
  quad : CrossQuad (P.swappedGens c L)
  /-- (1.8). -/
  slide : CrossSlide (P.swappedGens c L)
  /-- (1.9). -/
  braid : CrossBraid (P.swappedGens c L)
  /-- (1.10). -/
  zigzag : CupCapZigzag (P.swappedGens c L)
  /-- (1.11), (1.12): the distinct-colour sideways crossings have permutation matrices with
  invertible entries. -/
  sigma : ∀ i j ν, i ≠ j → P.SigmaPermutation c i j ν
  /-- (1.13), (1.14). -/
  leftward : L.IsInverse c
  /-- (2.6). -/
  windowZero : DcupDcapWindowZero (P.swappedGens c L)
  /-- The super interchange law. -/
  supernatural : GeneratorsSupernatural (P.swappedGens c L)

namespace SwappedRelationData

variable {c : P.CrossCoeff} {L : P.LeftwardData} (h : P.SwappedRelationData c L)
  (Gs Ys : ∀ s, P.H s)
include h

/-- **The obligations of the assembly hold** for the swapped layer representation. -/
theorem obligations : SwappedObligations Sc (P.layerRep Gs Ys (P.swappedGens c L)) where
  quad := quadRelations h.quad
  slide := slideRelations h.slide
  braid := braidRelations h.braid
  zigzag := zigzagRelations h.zigzag
  inversion := inversionRelations h.sigma h.leftward
  windowZero := windowZeroRelations Gs Ys h.windowZero
  interchange := interchangeLaw Gs Ys h.supernatural

/-- **The swapped upward module action** at rightmost weight `μ`. -/
def upwardModuleAction (μ : X) : UpwardModuleAction D Sc μ :=
  (h.obligations Gs Ys).upwardModuleAction μ

end SwappedRelationData

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
