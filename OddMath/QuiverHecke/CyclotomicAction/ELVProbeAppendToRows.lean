import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierPowers

/-! # Chosen dotted unit and counit rows at stored probe representatives

Brundan–Ellis (1.13)–(1.14): arbitrary ordered powers of the selected dot,
composed with the selected ordinary unit or counit, retain every OLD
homogeneous component on the full evaluated module categories.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
section Composition
variable {k C A : Type*} [CommRing k]
  [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A}
private theorem even_left_comp_app (η : F.toFunctor ⟶ G.toFunctor)
    (hη : ∀ N, η.app N ∈ parity (R := k) _ _ 0) (x : G ⟶ H) (q : ZMod 2) (N : C) :
    ((show F ⟶ G from SuperNatTrans.ofNatTrans η hη) ≫ x).app q N =
      η.app N ≫ x.app q N := by
  change η.app N ≫ x.app q N + 0 ≫ x.app (q + 1) N = _
  rw [Limits.zero_comp, add_zero]
private theorem even_right_comp_app (η : G.toFunctor ⟶ H.toFunctor)
    (hη : ∀ N, η.app N ∈ parity (R := k) _ _ 0) (x : F ⟶ G) (q : ZMod 2) (N : C) :
    (x ≫ (show G ⟶ H from SuperNatTrans.ofNatTrans η hη)).app q N =
      x.app q N ≫ η.app N := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change x.app 0 N ≫ η.app N + x.app 1 N ≫ 0 = _
    rw [Limits.comp_zero, add_zero]
  · change x.app 0 N ≫ 0 + x.app 1 N ≫ η.app N = _
    rw [Limits.comp_zero, zero_add]
end Composition

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {μ : List I} (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
local notation "hDot" => probeAppendToDot_supernatural D Sc m ν i μ h
local notation "C₀" => ProbeEvaluatedModules D Sc m ν
local notation "C₁" => ProbeEvaluatedModules D Sc m μ
local notation "O₀" => Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k)
local notation "O₁" => Superfunctor k (OldContentCategory D Sc (probeCutoff D m) μ) (SVec k)
local notation "R₀" => probeEvaluatedTarget D Sc m ν
local notation "R₁" => probeEvaluatedTarget D Sc m μ
local notation "e" => probeAppendToE D Sc m ν i μ h
local notation "f" => probeAppendToF D Sc m ν i μ h
local notation "A" => probeAppendToRightAdjunction D Sc m ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h
local notation "F" => probeEvaluatedRestrictTo D Sc m ν i μ h
private abbrev lower : Superfunctor k C₁ C₁ := ⟨F ⋙ E⟩
private abbrev upper : Superfunctor k C₀ C₀ := ⟨E ⋙ F⟩
private abbrev oldLower : Superfunctor k O₁ O₁ := ⟨restriction J ⋙ induction J⟩
private abbrev oldUpper : Superfunctor k O₀ O₀ := ⟨induction J ⋙ restriction J⟩

/-- The selected ordered dot/counit row, without a new choice of bending map. -/
def probeAppendToCapRow (n : ℕ) : lower D Sc m ν i h ⟶ Superfunctor.id k C₁ :=
  BicategoryStruct.whiskerLeft (a := R₁) (b := R₀) (c := R₁) f
    (g := e) (h := e) (probeAppendToDotPower D Sc m ν i h n) ≫ (A).counit

/-- The selected ordered unit/dot column, without a new choice of bending map. -/
def probeAppendToUnitColumn (n : ℕ) : Superfunctor.id k C₀ ⟶ upper D Sc m ν i h :=
  (A).unit ≫ BicategoryStruct.whiskerRight (a := R₀) (b := R₁) (c := R₀)
    («f» := e) (g := e) (probeAppendToDotPower D Sc m ν i h n) f

/-- The same ordered dot/counit row in the OLD module categories. -/
def oldAppendToCapRow (n : ℕ) : oldLower D Sc m ν i h ⟶ Superfunctor.id k O₁ :=
  restrictionModuleCell (k := k) J ◁ oldAppendToDotPower D Sc m ν i h n ≫
    (inductionModuleAdjunction (k := k) J).counit

/-- The same ordered unit/dot column in the OLD module categories. -/
def oldAppendToUnitColumn (n : ℕ) : Superfunctor.id k O₀ ⟶ oldUpper D Sc m ν i h :=
  (inductionModuleAdjunction (k := k) J).unit ≫ oldAppendToDotPower D Sc m ν i h n ▷
    restrictionModuleCell (k := k) J

/-- The selected OLD dotted counit is the given ordinary cap row. -/
theorem oldAppendToCapRow_eq (n : ℕ) :
    oldAppendToCapRow D Sc m ν i h n = gridCapRowTransformation J hDot n :=
  inductionModuleCapPower_eq J hDot n

/-- The selected OLD dotted unit is the given ordinary unit column. -/
theorem oldAppendToUnitColumn_eq (n : ℕ) :
    oldAppendToUnitColumn D Sc m ν i h n = gridUnitColumnTransformation J hDot n :=
  inductionModuleUnitPower_eq J hDot n

/-- Every component of every selected dotted counit is retained. -/
theorem probeAppendToCapRow_app (n : ℕ) (q : ZMod 2) (N : C₁) :
    ((probeAppendToCapRow D Sc m ν i h n).app q N).hom =
      (oldAppendToCapRow D Sc m ν i h n).app q N.obj := by
  unfold probeAppendToCapRow oldAppendToCapRow
  erw [even_right_comp_app («F» := lower D Sc m ν i h) (G := lower D Sc m ν i h)
      (H := Superfunctor.id k C₁) (probeAppendToAdjunction D Sc m ν i μ h).counit
      (probeAppendToAdjunction_counit_mem D Sc m ν i μ h),
    even_right_comp_app («F» := oldLower D Sc m ν i h) (G := oldLower D Sc m ν i h)
      (H := Superfunctor.id k O₁) (adjunction J).counit (adjunctionCounit_mem J)]
  change ((probeAppendToDotPower D Sc m ν i h n).app q ((F).obj N)).hom ≫
      (adjunction J).counit.app N.obj =
    (oldAppendToDotPower D Sc m ν i h n).app q ((restriction J).obj N.obj) ≫
      (adjunction J).counit.app N.obj
  rw [probeAppendToDotPower_app]
  rfl

/-- Every component of every selected dotted unit is retained. -/
theorem probeAppendToUnitColumn_app (n : ℕ) (q : ZMod 2) (N : C₀) :
    ((probeAppendToUnitColumn D Sc m ν i h n).app q N).hom =
      (oldAppendToUnitColumn D Sc m ν i h n).app q N.obj := by
  unfold probeAppendToUnitColumn oldAppendToUnitColumn
  erw [even_left_comp_app («F» := Superfunctor.id k C₀) (G := upper D Sc m ν i h)
      (H := upper D Sc m ν i h) (probeAppendToAdjunction D Sc m ν i μ h).unit
      (probeAppendToAdjunction_unit_mem D Sc m ν i μ h),
    even_left_comp_app («F» := Superfunctor.id k O₀) (G := oldUpper D Sc m ν i h)
      (H := oldUpper D Sc m ν i h) (adjunction J).unit (adjunctionUnit_mem J)]
  change (adjunction J).unit.app N.obj ≫
      (restriction J).map (((probeAppendToDotPower D Sc m ν i h n).app q N).hom) =
    (adjunction J).unit.app N.obj ≫
      (restriction J).map ((oldAppendToDotPower D Sc m ν i h n).app q N.obj)
  rw [probeAppendToDotPower_app]
end OddMath.QuiverHecke
