import OddMath.QuiverHecke.CyclotomicAction.ELVWeightWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWindowInverseCoordinates

/-! # Finite unit inverse windows at absent predecessors

SwappedHomInversion §4 (7): absent lower induction kills principal closures,
but need not kill unit-window boundary coefficients. The chosen finite unit
inverse rows retain the weighted content inverse at every absent block.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
private theorem identity_obj {k : Type u} [CommRing k]
    (A : PiSCat.{u, u, u + 1} k) (V : A) :
    (𝟙 A : Superfunctor k A A).obj V = V := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

section Content
variable (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
variable (M : ContentModules D Sc cutoff N β)
local notation "P" => induced (contentInclusion D Sc cutoff N β) M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N β γ i hK M
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- Every finite row of a zero-principal content inverse is the chosen weighted row. -/
theorem contentAbsentUnitInverse_window
    (L : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M))
      (unitDotColumn K hDot M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i β))
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (j : ℕ) (hj : j < contentUnitCount D cutoff i β) :
    L.g' j = (Target).hom ≫ (weightedContentLocalInverseFrom D Sc cutoff N i P β hh).g' j ≫
      (Value).inv := by
  classical
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P β hh
  symm
  apply L.hom_ext
  · rw [Limits.zero_comp, L.fg j hj]
  · intro r hr
    have hs := contentUnitDotColumn_square D Sc cutoff N β i M r
    change unitDotColumn K hDot M r ≫ (Target).hom =
      (Value).hom ≫ (restriction Q).map
        (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P r) at hs
    calc
      unitDotColumn K hDot M r ≫ ((Target).hom ≫ B.g' j ≫ (Value).inv) =
          (Value).hom ≫ ((restriction Q).map
            (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P r) ≫ B.g' j) ≫
              (Value).inv := by rw [← Category.assoc, hs]; simp only [Category.assoc]
      _ = unitDotColumn K hDot M r ≫ L.g' j := by
        rw [B.gg r j hr hj, L.gg r j hr hj]
        split_ifs <;> simp
end Content

private theorem absentSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

/-- Stored successor contents retain the same absent finite unit row. -/
theorem contentAbsentUnitTargetInverse_window (β γ : Multiset I) (i : I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (L : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶
        (restriction (contentAppendTo D Sc cutoff N β [i] γ hγ)).obj
          (induced (contentAppendTo D Sc cutoff N β [i] γ hγ) M))
      (unitDotColumn (contentAppendTo D Sc cutoff N β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff N hγ hγ (absentSingletonDot_mem D Sc i)) M)
      (D.parity i) (fun n => n • D.parity i) (contentUnitCount D cutoff i β))
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (j : ℕ) (hj : j < contentUnitCount D cutoff i β) :
    L.g' j = (contentPrincipalTargetIso D Sc cutoff N β γ i hγ M).hom ≫
      (weightedContentLocalInverseFrom D Sc cutoff N i
        (induced (contentInclusion D Sc cutoff N β) M) β hh).g' j ≫
          (contentExtensionUnitIso D Sc cutoff N β M).inv := by
  subst γ
  exact contentAbsentUnitInverse_window D Sc cutoff N β i M L hh j hj

variable (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (δ : WeightBlocks D Λ x₁)
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ δ
local notation "ResU" => elvBlockRes D Sc cutoff N i Λ h₂ δ
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "UnitField" r => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷ elvF D Sc cutoff N i Λ h₂

/-- The prescribed absent-content inverse at the actual stored upper successor. -/
def elvContentAbsentUnitInverseAtWeight
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) :=
  Classical.choice (contentAbsentUnitTargetInverse_nonempty D Sc cutoff N δ.1 ε.1 i
    (elvBlockSucc_content_eq D i Λ h₂ δ)
    (fun hi => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hi)) (M δ))

/-- The following upper-loop chart retains all ordinary weight unit columns. -/
theorem elvWeightUnitPower_following_coordinates (r : ℕ) :
    (UnitField r).total M δ ≫ eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) =
      unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) r := by
  have ha : eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) =
      (ResU).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)) :=
    (eqToHom_map (ResU).toFunctor
      (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)).symm
  rw [ha]
  exact elvWeightUnit_gridColumn_comparison D Sc cutoff N i Λ h₂ δ M r

include hcutoff in
/-- Any finite weight unit inverse row has the prescribed absent content coordinate. -/
theorem elvAbsentUnitWindow_coordinates
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (L : SKM.SuperSumInvFrom (k := k) (φ) (fun r => UnitField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (-D.h i x₁).toNat)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (L.g' j).total M δ =
      eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) ≫
        (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M δ hδ).g' j := by
  let J := L.at M
  let B := elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M δ hδ
  let a := eqToIso (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M)
  change (L.g' j).total M δ = a.hom ≫ B.g' j
  have hcount := contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ
  have hj' : j < contentUnitCount D cutoff i δ.1 := by simpa only [hcount] using hj
  apply (cancel_epi a.inv).mp
  rw [← Category.assoc a.inv a.hom, a.inv_hom_id, Category.id_comp]
  apply B.hom_ext
  · rw [Limits.zero_comp, B.fg j hj']
  · intro r hr
    have hs := elvWeightUnitPower_following_coordinates D Sc cutoff N Λ i h₂ M δ r
    change (UnitField r).total M δ ≫ a.hom = _ at hs
    rw [← hs, Category.assoc, a.hom_inv_id_assoc, hs, B.gg r j hr hj']
    have hr' : r < (-D.h i x₁).toNat := by simpa only [hcount] using hr
    have he := (CategoryTheory.Pi.eval _ δ).congr_map (J.gg r j hr' hj)
    split_ifs at he ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvFrom.at_g'] using he
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvFrom.at_g'] using he

/-- The literal chosen absent unit row is retained; absence does not set it to zero. -/
theorem elvChosenAbsentUnitWindow_coordinates
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hh : D.h i x₁ ≤ 0)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh j =
      eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) ≫
        (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M δ hδ).g' j :=
  elvAbsentUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hδ
    (((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh) j hj

end OddMath.QuiverHecke.ELVOld
