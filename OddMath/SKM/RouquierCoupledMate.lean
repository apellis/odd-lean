import OddMath.SKM.RouquierCoupled
import OddMath.SKM.RouquierCurl

/-!
# Sector blocks of the coupled mate

The projection of the coupled mate from a source sector to a target sector is
the mate, for the two sector adjunctions, of the corresponding block of the
coupled crossing (`CoupledFactors.sector_mate_block`). In particular the
probe-to-reservoir projection is the sector mate of the rational block
`rationalPR` (`CoupledFactors.probe_mate_reservoir`), so the fused bubble
identification of the vacuum sectors is a statement about the probe and
reservoir factors and this single block, closed by their cups and caps.

The two transport lemmas `sectorIn_rouquierMate` and `rouquierMate_sectorOut`
only need the restriction of the counit and the projection of the unit; the
crossing is arbitrary (odd crossings allowed).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

section Transport
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}

/-- The mate with its output cup pulled into the left strand. -/
theorem rouquierMate_eq_cupped (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMate A₁ A₂ t = F₁ ◁ ((rightUnitor E₁).inv ≫ E₁ ◁ A₂.unit ≫
      (associator E₁ E₂ F₂).inv ≫ t ▷ F₂ ≫ (associator E₁ E₂ F₂).hom) ≫
        (associator F₁ E₁ (E₂ ≫ F₂)).inv ≫ A₁.counit ▷ (E₂ ≫ F₂) ≫
          (leftUnitor (E₂ ≫ F₂)).hom := by
  rw [rouquierMate, mate_suffix A₁, reassoc_of% (mate_prefix A₂)]
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]

/-- The mate with its input cap pulled into the right strand. -/
theorem rouquierMate_eq_capped (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMate A₁ A₂ t = (rightUnitor (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ A₂.unit ≫
      (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫ F₁ ◁ (associator E₁ E₂ F₂).inv ≫
        (associator F₁ (E₁ ≫ E₂) F₂).inv ≫
      (F₁ ◁ t ≫ (associator F₁ E₁ E₂).inv ≫ A₁.counit ▷ E₂ ≫ (leftUnitor E₂).hom) ▷ F₂ := by
  rw [rouquierMate]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), TwoSupercategory.whisker_assoc (R := k),
    Category.assoc, Iso.inv_hom_id_assoc]

/-- Restricting the mate to a source sector replaces the source adjunction by
the sector adjunction and the crossing by its restriction to the sector. -/
theorem sectorIn_rouquierMate (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) {iE : E ⟶ E₁} {pE : E₁ ⟶ E} {iF : F ⟶ F₁}
    (hiE : iE ∈ parity (R := k) _ _ 0) (hiF : iF ∈ parity (R := k) _ _ 0)
    (hc : iF ▷ E₁ ≫ A₁.counit = F ◁ pE ≫ A.counit) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    sectorIn iE iF ≫ rouquierMate A₁ A₂ t =
      rouquierMate A A₂ (iE ▷ E₂ ≫ t ≫ pE ▷ E₂) := by
  rw [rouquierMate_eq_cupped, rouquierMate_eq_cupped, sectorIn, Category.assoc,
    ← TwoSupercategory.whiskerLeft_comp'_assoc k,
    TwoSupercategory.whisker_exchange_of_even_left_assoc hiF,
    TwoSupercategory.associator_inv_naturality_left_assoc k,
    ← TwoSupercategory.comp_whiskerRight'_assoc k, hc,
    TwoSupercategory.comp_whiskerRight'_assoc k,
    ← TwoSupercategory.associator_inv_naturality_middle_assoc k,
    ← TwoSupercategory.whiskerLeft_comp'_assoc k]
  congr 2
  rw [TwoSupercategory.rightUnitor_inv_naturality_assoc k,
    TwoSupercategory.whisker_exchange_of_even_left_assoc hiE,
    TwoSupercategory.associator_inv_naturality_left_assoc k]
  simp only [Category.assoc, TwoSupercategory.comp_whiskerRight (R := k)]
  rw [TwoSupercategory.associator_naturality_left k]

/-- Projecting the mate to a target sector replaces the target adjunction by the
sector adjunction and the crossing by its corestriction to the sector. -/
theorem rouquierMate_sectorOut (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂) {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) {iE : E ⟶ E₂} {pE : E₂ ⟶ E} {pF : F₂ ⟶ F}
    (hpF : pF ∈ parity (R := k) _ _ 0)
    (hu : A₂.unit ≫ E₂ ◁ pF = A.unit ≫ iE ▷ F) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    rouquierMate A₁ A₂ t ≫ sectorOut pE pF =
      rouquierMate A₁ A (E₁ ◁ iE ≫ t ≫ E₁ ◁ pE) := by
  rw [rouquierMate_eq_capped, rouquierMate_eq_capped, sectorOut]
  simp only [Category.assoc]
  rw [← TwoSupercategory.comp_whiskerRight'_assoc k,
    TwoSupercategory.whisker_exchange_of_even_right _ hpF,
    ← TwoSupercategory.associator_inv_naturality_right_assoc k,
    ← TwoSupercategory.whiskerLeft_comp'_assoc k,
    ← TwoSupercategory.associator_inv_naturality_right k,
    TwoSupercategory.whiskerLeft_comp'_assoc k,
    ← TwoSupercategory.associator_naturality_right_assoc k,
    ← TwoSupercategory.whiskerLeft_comp'_assoc k, hu,
    TwoSupercategory.whiskerLeft_comp'_assoc k,
    TwoSupercategory.associator_naturality_right_assoc k,
    ← TwoSupercategory.whiskerLeft_comp'_assoc k F₁ (E₁ ◁ (iE ▷ F))
      (associator E₁ E₂ F).inv,
    TwoSupercategory.associator_inv_naturality_middle k,
    TwoSupercategory.whiskerLeft_comp'_assoc k,
    TwoSupercategory.associator_inv_naturality_middle_assoc k,
    ← TwoSupercategory.comp_whiskerRight' k]
  congr 6
  simp only [Category.assoc, TwoSupercategory.whiskerLeft_comp (R := k)]
  rw [← TwoSupercategory.leftUnitor_naturality k,
    TwoSupercategory.whisker_exchange_of_even_left_assoc A₁.counit_mem,
    ← TwoSupercategory.associator_inv_naturality_right_assoc k]

end Transport

namespace SectorDecomp
variable {a b : B} {M : a ⟶ b} {ι : Type} [Fintype ι] [DecidableEq ι] {O : ι → (a ⟶ b)}
  (D : SectorDecomp (k := k) M ι O)

omit [TwoSupercategory k B] in
/-- The diagonal block of a block matrix. -/
theorem inc_mat_proj (m : ∀ i j, O i ⟶ O j) (i : ι) :
    D.inc i ≫ D.mat m ≫ D.proj i = m i i := by
  rw [← Category.assoc, D.inc_mat, D.sum_proj]

end SectorDecomp

namespace CoupledFactors
variable {a b c : B} (C : CoupledFactors (k := k) a b c)

/-- **Sector blocks of the coupled mate.** The projection of the coupled mate
from source sector `s` to target sector `s'` is the sector mate of the block
`(s, s')` of the coupled crossing. -/
theorem sector_mate_block (s s' : CoupledSector) :
    sectorIn (C.DE₁.inc s) (C.DF₁.inc s) ≫ rouquierMate C.A₁ C.A₂ C.coupledCross ≫
        sectorOut (C.DE₂.proj s') (C.DF₂.proj s') =
      rouquierMate (C.adj₁ s) (C.adj₂ s') (C.crossEntry (s, s') (s, s')) := by
  rw [← Category.assoc, sectorIn_rouquierMate C.A₁ C.A₂ (C.adj₁ s) (C.DE₁.inc_mem s)
      (C.DF₁.inc_mem s) (inc_whiskerRight_coupledCounit C.DE₁ C.DF₁ C.adj₁ s),
    rouquierMate_sectorOut (C.adj₁ s) C.A₂ (C.adj₂ s') (C.DF₂.proj_mem s')
      (coupledUnit_whiskerLeft_proj C.DE₂ C.DF₂ C.adj₂ s')]
  congr 1
  rw [← (C.DE₁.comp C.DE₂).inc_mat_proj C.crossEntry (s, s'), coupledCross,
    SectorDecomp.comp_inc, SectorDecomp.comp_proj]
  dsimp only
  rw [← Category.assoc (C.O₁ s ◁ C.DE₂.inc s'), ← SectorDecomp.exch (C.DE₁.inc_mem s)]
  simp only [Category.assoc]

/-- The probe-to-reservoir projection of the coupled mate is the sector mate of
the rational block. -/
theorem probe_mate_reservoir :
    sectorIn (C.DE₁.inc CoupledSector.probe) (C.DF₁.inc CoupledSector.probe) ≫
        rouquierMate C.A₁ C.A₂ C.coupledCross ≫
          sectorOut (C.DE₂.proj CoupledSector.reservoir) (C.DF₂.proj CoupledSector.reservoir) =
      rouquierMate (C.adj₁ CoupledSector.probe) (C.adj₂ CoupledSector.reservoir)
        C.rationalPR :=
  C.sector_mate_block CoupledSector.probe CoupledSector.reservoir

end CoupledFactors

end OddMath.SKM
