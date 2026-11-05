import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToMateReindex
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToRowReindex

/-! # Prescribed local inverses at stored probe representatives

Brundan–Ellis (1.13)–(1.14): the selected mate and dotted rows at the
actual stored-target append functors have the transported original
finite inverses. No inverse premise or replacement of an inverse entry
is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
private theorem conjugate_of_square
    {C : Type*} [Category* C] {A A' B B' : C}
    (a : A ≅ A') (b : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f ≫ b.hom = g := by
  rw [h, ← Category.assoc, a.inv_hom_id, Category.id_comp]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "height" => -CyclotomicCrossingTensor.contentCrossingHeight
  D (probeCutoff D m) i ((i :: ν : List I) : Multiset I)
local notation "T" => probeReindexLoopFunctor D Sc m ν i h₁
local notation "L" => probeReindexLowerLoopSuperIso D Sc m ν i h₁
local notation "U" => probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂
local notation "Z" => probeReindexIdentityLoopIso D Sc m ν i h₁
local notation "C₀" => probeEvaluatedTarget D Sc m ν
local notation "C₁" => probeEvaluatedTarget D Sc m (i :: ν)
local notation "C₂" => probeEvaluatedTarget D Sc m (i :: i :: ν)
local notation "E₀" => probeEvaluatedE D Sc m ν i
local notation "F₀" => probeEvaluatedF D Sc m ν i
local notation "E₁" => probeEvaluatedE D Sc m (i :: ν) i
local notation "F₁" => probeEvaluatedF D Sc m (i :: ν) i
local notation "x₀" => probeEvaluatedInductionDot D Sc m ν i
local notation "x₁" => probeEvaluatedInductionDot D Sc m (i :: ν) i

private def originalCapRow (n : ℕ) :
    (⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν))) ⟶
      Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  BicategoryStruct.whiskerLeft (a := C₁) (b := C₀) (c := C₁) F₀
    (g := E₀) (h := E₀) (SKM.rouquierPower (a := C₀) (b := C₁) (E := E₀) x₀ n) ≫
      (probeEvaluatedRightAdjunction D Sc m ν i).counit

private def originalUnitColumn (n : ℕ) :
    Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)) ⟶
    (⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν))) :=
  (probeEvaluatedRightAdjunction D Sc m (i :: ν) i).unit ≫
    BicategoryStruct.whiskerRight (a := C₁) (b := C₂) (c := C₁)
      (f := E₁) (g := E₁) (SKM.rouquierPower (a := C₁) (b := C₂) (E := E₁) x₁ n) F₁

private theorem cap_standard (n : ℕ) :
    probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n = originalCapRow D Sc m ν i n :=
  probeAppendToCapRow_standard D Sc m ν i n
private theorem unit_standard (n : ℕ) :
    probeAppendToUnitColumn D Sc m (i :: ν) i (List.Perm.refl (i :: i :: ν)) n =
      originalUnitColumn D Sc m ν i n :=
  probeAppendToUnitColumn_standard D Sc m (i :: ν) i n

private theorem mate_coordinate :
    (L).inv ≫ (T).map (probeEvaluatedLocalMate D Sc m ν i) ≫ (U).hom =
      probeAppendToMate D Sc m ν i h₁ h₂ :=
  conjugate_of_square L U _ _ (probeAppendToMate_reindex D Sc m ν i h₁ h₂)

private theorem cap_coordinate (n : ℕ) :
    (L).inv ≫ (T).map (originalCapRow D Sc m ν i n) ≫ (Z).hom =
      probeAppendToCapRow D Sc m ν i h₁ n := by
  have h : (T).map (originalCapRow D Sc m ν i n) ≫ (Z).hom =
      (L).hom ≫ probeAppendToCapRow D Sc m ν i h₁ n := by
    change (T).map (originalCapRow D Sc m ν i n) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← cap_standard]
    exact probeAppendToCapRow_reindex D Sc m ν i h₁ n
  exact conjugate_of_square L Z _ _ h

private theorem unit_coordinate (n : ℕ) :
    (Z).inv ≫ (T).map (originalUnitColumn D Sc m ν i n) ≫ (U).hom =
      probeAppendToUnitColumn D Sc m ν₁ i h₂ n := by
  have h : (T).map (originalUnitColumn D Sc m ν i n) ≫ (U).hom =
      (Z).hom ≫ probeAppendToUnitColumn D Sc m ν₁ i h₂ n := by
    change (T).map (originalUnitColumn D Sc m ν i n) ≫ (U).hom = 𝟙 _ ≫ _
    rw [Category.id_comp, ← unit_standard]
    exact probeAppendToUnitColumn_reindex D Sc m ν i h₁ h₂ n
  exact conjugate_of_square Z U _ _ h

/-- The positive-height inverse uses every prescribed transported inverse entry. -/
def probeAppendToInvPos (hh : 0 ≤ height) :
    SKM.SuperSumInvTo (k := k) (probeAppendToMate D Sc m ν i h₁ h₂)
      (probeAppendToCapRow D Sc m ν i h₁) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (height).toNat :=
  (probeReindexInvPos D Sc m ν i h₁ h₂ hh).copyMaps
    (probeAppendToMate D Sc m ν i h₁ h₂) (probeAppendToCapRow D Sc m ν i h₁)
    (mate_coordinate D Sc m ν i h₁ h₂).symm
    (funext fun n => (cap_coordinate D Sc m ν i h₁ n).symm)

/-- The negative-height inverse uses every prescribed transported inverse entry. -/
def probeAppendToInvNeg (hh : height ≤ 0) :
    SKM.SuperSumInvFrom (k := k) (probeAppendToMate D Sc m ν i h₁ h₂)
      (probeAppendToUnitColumn D Sc m ν₁ i h₂) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-height).toNat :=
  (probeReindexInvNeg D Sc m ν i h₁ h₂ hh).copyMaps
    (probeAppendToMate D Sc m ν i h₁ h₂) (probeAppendToUnitColumn D Sc m ν₁ i h₂)
    (mate_coordinate D Sc m ν i h₁ h₂).symm
    (funext fun n => (unit_coordinate D Sc m ν i h₁ h₂ n).symm)

end OddMath.QuiverHecke
