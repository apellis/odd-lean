/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseBubbleEntry

/-! # The right bubble entry at a sector without probe `Fᵢ`

Brundan–Ellis, *Super Kac–Moody 2-categories*, (2.11), (2.13), (2.17), toward the
negative-height bubble identities of §8 (research issue #345).

At negative height `hᵢ(ν) < 0` the normalized right bubble is the closed diagram of
the dotted unit `xᴺ η` followed by the dotted rightward cap with `n < -hᵢ(ν)` dots.
At a sector with no probe summand of `Fᵢ` its entry in the swapped generators is the
single product `η xᴺ ≫ dcap n` through the unique pure-reservoir path of `FᵢEᵢ`
(`compDiag_etaL_dcapL_swappedGens`). After any additive evaluation this product is
the padded `N`-th unit row followed by the padded cup-inverse column
(`map_etaEntry_dcap_eq_padded`), so the bubble entry is the column moment of the
rightward cup-window inverse of `PointwiseCupInverse`.
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
local instance rightBubbleEntryPathFintype {w : List (Col I X)} {t s : Sector I} :
    Fintype (SPath w t s) :=
  Fintype.ofFinite _

/-- **The right bubble entry at a sector without probe `Fᵢ`.** Without a probe
summand of `Fᵢ` at `t`, the entry of `η xᴺ` followed by `dcap n` between empty paths
is the product through the unique pure-reservoir path of `FᵢEᵢ`. -/
theorem compDiag_etaL_dcapL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I)
    (N n : ℕ) (ν : X) (hn : (n : ℤ) < -D.h i ν) (t : Sector I) (Z : P.H t)
    (hd : ¬StepValid (dn i) true t) :
    compDiag (P.swappedGens c L)
        (SKM.mkD D ν (SKM.etaL i N ++ SKM.dcapL i n)
          ((SKM.sChain_etaL i N).append (SKM.sChain_dcapL i n))) (.nil t) (.nil t) Z =
      P.etaEntry c i N ν (.nil t) (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
          Z ≫
        L.dcap i n ν (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) (.nil t) Z := by
  rw [← SKM.mkD_comp D ν _ _ (SKM.sChain_etaL i N) (SKM.sChain_dcapL i n), compDiag_comp]
  refine Eq.trans (Fintype.sum_eq_single
    (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
    (fun b hb => absurd (SPath.eq_centralDnUp_false i ν t hd b) hb)) ?_
  rw [compDiag_etaL_swappedGens, compDiag_dcapL_swappedGens c L i n ν hn]

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- **A unit row followed by a column, in the padded chart.** For any morphism `d`
out of the pure-reservoir path image, the evaluated product `η xᴺ ≫ d` is the padded
unit row `centralPaddedUnit false N` followed by the padded column
`κ ≫ E (ι ≫ d)`. -/
theorem map_etaEntry_dcap_eq_padded (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t) (E : P.H t ⥤ C) {V : P.H t}
    (d : (P.pathFunctor (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)).obj Z ⟶ V)
    (N : ℕ) :
    E.map (P.etaEntry c i N ν (.nil t)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) Z ≫ d) =
      P.centralPaddedUnit i t Z E false N ≫
        ((P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).hom ≫
          E.map ((P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫ d)) := by
  rw [centralPaddedUnit, dite_eq_left (show StepValid (dn i) false t from trivial),
    P.etaEntry_centralFactor c i ν t Z ⟨false, trivial⟩ N]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
