/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCapInverse

/-! # The left bubble entry at a probe-only sector

Brundan–Ellis, *Super Kac–Moody 2-categories*, (2.11), (2.13), (2.17), toward the
positive-height bubble identities of §8 (research issue #345).

At positive height `hᵢ(ν) > 0` the normalized left bubble is the closed diagram of
the dotted leftward cup with `n < hᵢ(ν)` dots followed by the rightward cap with
`N` dots (`SKM.inv_smul_bubLs_of_pos`). At a sector with no reservoir summand of
`Eᵢ` its entry in the swapped generators is the single product
`dcup n ≫ ε xᴺ` through the unique source path
(`compDiag_dcupL_epsL_swappedGens`). After any additive evaluation this product is
the padded cap-inverse column followed by the padded `N`-th cap row
(`map_dcup_epsEntry_eq_padded`), so the bubble entry is the column moment of the
leftward cap-window inverse of `PointwiseCapInverse`.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Classical

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance bubbleEntryPathFintype {w : List (Col I X)} {t s : Sector I} :
    Fintype (SPath w t s) :=
  Fintype.ofFinite _

/-- **The bubble entry at a probe-only sector.** Without a reservoir summand of
`Eᵢ` at `t`, the entry of `dcup n` followed by `ε xᴺ` between empty paths is the
product through the unique pure-probe path of `EᵢFᵢ`. -/
theorem compDiag_dcupL_epsL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I)
    (n N : ℕ) (ν : X) (hn : (n : ℤ) < D.h i ν) (t : Sector I) (Z : P.H t)
    (hu : ¬StepValid (up i) false t) :
    compDiag (P.swappedGens c L)
        (SKM.mkD D ν (SKM.dcupL i n ++ SKM.epsL i N)
          ((SKM.sChain_dcupL i n).append (SKM.sChain_epsL i N))) (.nil t) (.nil t) Z =
      L.dcup i n ν (.nil t) (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) Z ≫
        P.epsEntry c i N ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
          (.nil t) Z := by
  rw [← SKM.mkD_comp D ν _ _ (SKM.sChain_dcupL i n) (SKM.sChain_epsL i N), compDiag_comp]
  refine Eq.trans (Fintype.sum_eq_single
    (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
    (fun b hb => absurd (SPath.eq_centralUpDn_true i ν t hu b) hb)) ?_
  rw [compDiag_dcupL_swappedGens c L i n ν hn, compDiag_epsL_swappedGens]

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- **A column followed by a cap row, in the padded chart.** For any morphism `d`
into the pure-probe path image, the evaluated product `d ≫ ε xᴺ` is the padded
column `E (d ≫ ι⁻¹) ≫ κ⁻¹` followed by the padded cap row `centralPaddedCap true N`. -/
theorem map_dcup_epsEntry_eq_padded (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) {V : P.H t}
    (d : V ⟶ (P.pathFunctor (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)).obj Z)
    (N : ℕ) :
    E.map (d ≫ P.epsEntry c i N ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
        (.nil t) Z) =
      (E.map (d ≫ (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv) ≫
        (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).inv) ≫
        P.centralPaddedCap i t Z E true N := by
  rw [centralPaddedCap, dite_eq_left (show StepValid (up i) true t from trivial),
    P.epsEntry_centralFactor c i ν t Z ⟨true, trivial⟩ N]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
