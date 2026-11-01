/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.MixedBlockPost
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.ReservoirBlock

/-! # The braid relation (1.9) on `Eᵢ Eᵢ Eᵢ` for all pairs of paths

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at the colour pattern `iii`: a path of `Eᵢ Eᵢ Eᵢ` takes `a` probe summands and
`3 - a` reservoir summands, and its endpoint has probe content `s.1 + a αᵢ`. So two paths with
the same endpoints take the same number of probe summands, and lie in one of the four blocks
`PPP`, `{PPR, PRP, RPP}`, `{PRR, RPR, RRP}`, `RRR`. On each block (1.9) was checked
(`ppp_braid`, `block_braid`, `blockPost_braid`, `rrr_braid`); here the blocks are assembled.

## Main results

* `ProbeReservoir.braid_same`: the entries `braidLeft` and `braidRight` of the swapped
  generators agree on every pair of paths of `Eᵢ Eᵢ Eᵢ`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (ν : X) (i : I) (t : Sector I)

/-- (1.9) on the block `{PPR, PRP, RPP}`, for every pair of paths. -/
theorem block_braid_all (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hR : StepValid (true, i) false (nextSector (true, i) true (nextSector (true, i) true t)))
    (p q : SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, i) true t))))
    (Z : P.H (nextSector (true, i) false
      (nextSector (true, i) true (nextSector (true, i) true t)))) :
    braidLeft (P.swappedGens c L) i i i ν p q Z = braidRight (P.swappedGens c L) i i i ν p q Z := by
  obtain ⟨m, rfl⟩ := blockPath_surjective ν i t hR p
  obtain ⟨n, rfl⟩ := blockPath_surjective ν i t hR q
  exact block_braid ν i t hR Z c L hc h m n

/-- (1.9) on the block `{PRR, RPR, RRP}`, for every pair of paths. -/
theorem blockPost_braid_all (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hv : StepValid (true, i) false t)
    (hw : StepValid (true, i) false (nextSector (true, i) false t))
    (p q : SPath (wd D ν [up i, up i, up i]) t
      (nextSector (true, i) false (nextSector (true, i) false (nextSector (true, i) true t))))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) false
      (nextSector (true, i) true t)))) :
    braidLeft (P.swappedGens c L) i i i ν p q Z = braidRight (P.swappedGens c L) i i i ν p q Z := by
  obtain ⟨m, rfl⟩ := blockPathPost_surjective ν i t hv hw p
  obtain ⟨n, rfl⟩ := blockPathPost_surjective ν i t hv hw q
  exact blockPost_braid ν i t hv hw Z c L hc h m n

/-- **(1.9) for the colour pattern `iii`**: the entries `braidLeft` and `braidRight` of the
swapped generators agree on every pair of paths of `Eᵢ Eᵢ Eᵢ`. -/
theorem braid_same (hc : c.IsInverse) (h : P.CrossCoeffInputs) {s t : Sector I}
    (p q : SPath (wd D ν [up i, up i, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i i i ν p q Z = braidRight (P.swappedGens c L) i i i ν p q Z := by
  cases p with
  | cons _ σ₁ _ h₁ p =>
    cases p with
    | cons _ σ₂ _ h₂ p =>
      cases p with
      | cons _ σ₃ _ h₃ p =>
        cases p with
        | nil =>
          cases σ₁ <;> cases σ₂ <;> cases σ₃
          · obtain rfl := eq_rrrPath ν i s h₁ h₂ h₃ q
            exact rrr_braid ν i s h₁ h₂ h₃ c L Z
          · exact blockPost_braid_all c L ν i s hc h h₁ h₂ _ q Z
          · exact blockPost_braid_all c L ν i s hc h h₁ h₃ _ q Z
          · exact block_braid_all c L ν i s hc h h₁ _ q Z
          · exact blockPost_braid_all c L ν i s hc h h₂ h₃ _ q Z
          · exact block_braid_all c L ν i s hc h h₂ _ q Z
          · exact block_braid_all c L ν i s hc h h₃ _ q Z
          · obtain rfl := eq_pppPath ν i s q
            exact ppp_braid ν i s c L Z

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
