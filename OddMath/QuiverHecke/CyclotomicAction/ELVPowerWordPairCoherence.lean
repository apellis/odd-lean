import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightWhiskering

/-! # Recursive pair charts for the weight word family

SwappedVacuumCoordinates §§4–6: the supported crossing chart must agree
with the unchanged recursively selected whole single-append comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordPairCoherence
open CyclotomicAction CyclotomicCrossingTensor
universe u
private theorem chart_join {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {X₀ X₁ Y : C} {A Z W : B}
    (h₀ : A = F.obj X₀) (h₁ : X₀ = X₁) (h₂ : A = F.obj X₁) (h₃ : Z = F.obj Y)
    (e : X₁ ≅ Y) (f : F.obj Y ≅ W) :
    (eqToHom h₀ ≫ F.map (eqToHom h₁ ≫ e.hom) ≫ eqToHom h₃.symm) ≫
      (eqToHom h₃ ≫ f.hom) = eqToHom h₂ ≫ F.map e.hom ≫ f.hom := by
  cases h₁
  cases h₀
  cases h₃
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
  (hx : x₀ = PowerWordWeight.wordWeight D Λ ν)
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (hν : (ν : Multiset I) = (Subtype.val β))
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "M" => PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν
local notation "BJ" => blockSucc D Λ j h₁ β
local notation "BU" => blockSucc₂ D i j Λ h₁ h₂ β
local notation "K" => elvBlockInd D Sc cutoff N j Λ h₁ β
local notation "U" => elvBlockInd D Sc cutoff N i Λ h₂ BJ
local notation "HK" => elvBlockSucc_content_eq D j Λ h₁ β
local notation "HU" => elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β BU rfl
local notation "EK" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j (Subtype.val β) (Subtype.val BJ) hν HK
local notation "EU" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L (ν ++ [j]) i (Subtype.val BJ) (Subtype.val BU)
  (PowerWordContentCross.appendContentEq ν j (Subtype.val β) (Subtype.val BJ) hν HK) HU

/-- The recursively chosen whole pair chart agrees on its occupied component
with the existing rectangular chart and the recursively chosen content chart. -/
theorem recursive_pair_component :
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom BU =
      (PowerWordWeightCross.pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β BU rfl hν).hom := by
  have hxj : xj = PowerWordWeight.wordWeight D Λ (ν ++ [j]) :=
    h₁.symm.trans ((congrArg (fun x => x + D.α j) hx).trans
      (PowerWordWeight.wordWeight_append D Λ ν j))
  have hxu : xu = PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
    h₂.symm.trans ((congrArg (fun x => x + D.α i) hxj).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
  change (elvInductionComponent D Sc cutoff N i Λ h₂ BU).map
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν j x₀ xj hx hxj h₁).hom ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ (ν ++ [j]) i xj xu hxj hxu h₂).hom BU = _
  rw [elvInductionComponent_map_blockSucc D Sc cutoff N i Λ h₂ BJ,
    PowerWordWeightWhiskering.append_component D Sc cutoff L Λ ν j x₀ xj hx hxj h₁ β hν,
    PowerWordWeightWhiskering.append_component D Sc cutoff L Λ (ν ++ [j]) i xj xu hxj hxu h₂ BJ
      (PowerWordContentCross.appendContentEq ν j (Subtype.val β) (Subtype.val BJ) hν HK)]
  have hp := chart_join (U).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ BJ
      ((elvE D Sc cutoff N j Λ h₁).obj M))
    (elvInductionComponent_obj_blockSucc D Sc cutoff N j Λ h₁ β M)
    (Functor.congr_obj (elvEFunctor_comp₂_rectangular_eq D Sc cutoff N i j Λ h₁ h₂ β BU rfl) M)
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ BJ
      (PowerWordWeight.wordFamily D Sc cutoff L Λ xj (ν ++ [j]))) EK EU
  dsimp only [elvBlockInd, elvBlockAppend, PowerWordWeight.wordFamily, Superfunctor.map] at hp ⊢
  simpa only [PowerWordWeightCross.pairComponentIso, PowerWordContentCross.pairIsoTo,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom, eqToHom_app,
    Category.assoc] using hp

/-- The supported crossing chart has exactly the same whole hom as the
unchanged recursive single-append chart, including every zero component. -/
theorem recursive_pair_hom :
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom =
      (PowerWordWeightCross.pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom := by
  funext ε
  classical
  by_cases hε : BU = ε
  · subst ε
    rw [PowerWordWeightCross.pairFamilyIso_hom_of D Sc cutoff L Λ ν i j h₁ h₂ β hν BU rfl]
    exact recursive_pair_component D Sc cutoff L Λ ν i j hx h₁ h₂ β hν
  · exact (PowerWordWeightCross.pair_source_isZero D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε).eq_of_src _ _

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The given whole weight crossing in the unchanged recursively selected
word charts, for both colour cases and all exterior coefficient vectors. -/
theorem recursive_pair_cross :
    (elvActionCross D Sc cutoff N i j Λ h₁ h₂ h₃ h₄).app (D.parity i * D.parity j) M ≫
      (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν j i hx h₃ h₄).hom =
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L Λ ν i j (xu := xu) := by
  let β₀ : WeightBlocks D Λ x₀ := ⟨ν, hx.symm⟩
  rw [recursive_pair_hom D Sc cutoff L Λ ν j i hx h₃ h₄ β₀ rfl,
    recursive_pair_hom D Sc cutoff L Λ ν i j hx h₁ h₂ β₀ rfl]
  exact PowerWordWeightCross.weight_pair_cross D Sc cutoff L Λ ν i j h₁ h₂ β₀ rfl h₃ h₄
end OddMath.QuiverHecke.ELVOld.PowerWordPairCoherence
