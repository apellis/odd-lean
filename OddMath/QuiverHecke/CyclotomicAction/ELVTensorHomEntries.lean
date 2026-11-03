import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWords

/-! # Evaluation of surviving reservoir Hom entries

SwappedVacuumCoordinates §§2–6: a surviving layer entry postcomposes an
arbitrary supernatural map from its chosen source Hom object with the
literal whiskered reservoir generator. Evaluation at the regular probe
and the selected word chart commutes with this operation on every vector.
These are entry squares, before the completed swapped layer matrices.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorHomEntries
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P₀" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff N ΛR

private theorem entry_comp {x : X}
    {G Y Z : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    (f : G ⟶ Y) (g : Y ⟶ Z) (β : WeightBlocks D ΛR x)
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((f ≫ g).total P₀) β).total c z =
      ((g.total P₀) β).total c (((f.total P₀) β).total c z) := by
  rw [Superfunctor.comp_total]
  change (((f.total P₀) β ≫ (g.total P₀) β).total c) z = _
  rw [Superfunctor.comp_total, SVec.comp_apply]

/-- The surviving dot layer entry: the input is an arbitrary whole Hom
transformation, and the formula holds at every vector of its source.
No homogeneity or coordinate-comparison premise on the entry is imposed. -/
theorem dot_apply (ν : List I) (i : I)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])))
    (f : G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i))
    (β : WeightBlocks D ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])))
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom β).total c)
      ((((f ≫ (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i))).total P₀) β).total c z) =
    (PowerWordWeightDot.wordFamilyDot D Sc cutoff L ΛR ν i β).total c
      (((TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom β).total c
        (((f.total P₀) β).total c z)) := by
  rw [entry_comp]
  exact TensorVacuumWords.dot_apply D Sc m cutoff L ΛP ΛR ν i β c
    (((f.total P₀) β).total c z)

/-- The surviving crossing layer entry for every source Hom object and
every whole input transformation. The same chosen source and target pair
charts retain both colour cases and every coefficient vector. -/
theorem cross_apply (ν : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR xu)
    (f : G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫ (W).E j h₁ ≫ (W).E i h₂)
    (β : WeightBlocks D ΛR xu) (c : ContentCategory D Sc cutoff N β.1)
    (z : ((G.obj P₀) β).obj c) :
    (((TensorVacuumWords.pairChart D Sc m cutoff L ΛP ΛR ν j i h₃ h₄).hom β).total c)
      ((((f ≫ (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).cross i j h₁ h₂ h₃ h₄)).total P₀) β).total c z) =
    (PowerWordWeightCross.wordFamilyCross D Sc cutoff L ΛR ν i j (xu := xu) β).total c
      (((TensorVacuumWords.pairChart D Sc m cutoff L ΛP ΛR ν i j h₁ h₂).hom β).total c
        (((f.total P₀) β).total c z)) := by
  rw [entry_comp]
  exact TensorVacuumWords.cross_apply D Sc m cutoff L ΛP ΛR ν i j h₁ h₂ h₃ h₄ β c
    (((f.total P₀) β).total c z)

/-- Evaluation of the surviving entry in the unchanged target word chart.
It is defined on every whole Hom map; no injectivity is asserted. -/
def coordinates (ν τ : List I)
    (Y : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (PowerWordWeight.wordWeight D ΛR ν))
    (e : Y.obj P₀ ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR
      (PowerWordWeight.wordWeight D ΛR ν) τ)
    (f : TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ⟶ Y) :
    (PowerWordWeight.wordAt D Sc cutoff L τ (ν : Multiset I)).obj
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl) :=
  TensorVacuumWords.homEquiv D Sc m cutoff L ΛP ΛR ν τ (f.total P₀ ≫ e.hom)

/-- Coordinates of an actual Hom entry are evaluation of its total map at
the selected source cyclic vector. This formula covers arbitrary input
transformations, including inhomogeneous ones. -/
theorem coordinates_apply (ν τ : List I)
    (Y : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (PowerWordWeight.wordWeight D ΛR ν))
    (e : Y.obj P₀ ≅ PowerWordWeight.wordFamily D Sc cutoff L ΛR
      (PowerWordWeight.wordWeight D ΛR ν) τ)
    (f : TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ⟶ Y) :
    coordinates D Sc m cutoff L ΛP ΛR ν τ Y e f =
      ((f.total P₀ ≫ e.hom) (PowerWordWeight.wordBlock D ΛR ν)).total
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl)
        ((moduleIsoLinearEquiv
          (Pi.isoApp (TensorVacuumWords.valueIso D Sc m cutoff L ΛP ΛR ν)
            (PowerWordWeight.wordBlock D ΛR ν))
          (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset I) rfl)).symm
          (PowerWordHomCoordinates.unitVector D Sc cutoff L ΛR ν)) := by
  change PowerWordHomCoordinates.homEquiv D Sc cutoff L ΛR ν τ
    (((TensorVacuumWords.valueIso D Sc m cutoff L ΛP ΛR ν).inv ≫ (f.total P₀ ≫ e.hom)) ≫ 𝟙 _) = _
  rw [Category.comp_id, PowerWordHomCoordinates.homEquiv_apply]
  change (((TensorVacuumWords.valueIso D Sc m cutoff L ΛP ΛR ν).inv
      (PowerWordWeight.wordBlock D ΛR ν)) ≫
      (f.total P₀ ≫ e.hom) (PowerWordWeight.wordBlock D ΛR ν)).total _ _ = _
  rw [Superfunctor.comp_total, SVec.comp_apply]
  rfl

end OddMath.QuiverHecke.ELVOld.TensorHomEntries
