import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate.ProbeWeightMixedMate
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeAppendUpperLoop
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed.WeightTensorVacuum

/-!
# Probe reindex weight

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Probe weight unit columns in their stored successor coordinates

Brundan–Ellis (1.14): retain the selected upper unit and every ordered
power of the selected dot on every output block, including blocks with
no lower predecessor. These are the columns of the stored local inverse.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
private theorem rouquierPower_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {F : A ⟶ B} (d : F ⟶ F) (n : ℕ) (M : A.carrier) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem right_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    {F G : A ⟶ B} (z : F ⟶ G) (R : B ⟶ E) (M : A.carrier) :
    (z ▷ R).total M = R.map (z.total M) := by
  change R.toFunctor.map (z.app 0 M) + R.toFunctor.map (z.app 1 M) =
    R.toFunctor.map (z.app 0 M + z.app 1 M)
  exact (CategoryTheory.Functor.map_add R.toFunctor).symm

private theorem product_end_power
    {ι : Type*} {V : ι → Type*} [∀ a, Category (V a)]
    {M : ∀ a, V a} (d : End M) (n : ℕ) (a : ι) :
    (d ^ n) a = (show End (M a) from d a) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', End.mul_def, Pi.comp_apply, ih]

private theorem unit_conjugate_power
    {A B : Type*} [Category A] [Preadditive A] [Category B]
    (R : A ⥤ B) {P : B} {W V : A} (h : W = V)
    (η : P ⟶ R.obj V) (d : End V) (n : ℕ) :
    ((η ≫ R.map (eqToHom h.symm)) ≫
        R.map ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n)) ≫
      R.map (eqToHom h) = η ≫ R.map (d ^ n) := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]

private theorem unit_power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {E : A ⟶ B} {F : B ⟶ A} (a : SKM.SuperAdjunction (k := k) E F)
    (d : End E) (n : ℕ) (M : A.carrier) :
    (a.unit ≫ SKM.rouquierPower d n ▷ F).total M =
      a.unit.app 0 M ≫ F.map ((show End (E.obj M) from d.total M) ^ n) := by
  rw [Superfunctor.comp_total, right_whisker_total, rouquierPower_total,
    HomogeneousSuperfunctorIso.total_eq_app a.unit a.unit_mem]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x)
local notation "ε" => blockSucc D Λ i h δ
local notation "Res" => probeOldBlockRes D Sc m i Λ h δ
local notation "A" => probeOldActionAdjunction D Sc m i Λ h
local notation "d" => probeOldActionDot D Sc m i Λ h
local notation "F" => probeOldF D Sc m i Λ h
local notation "perm" => probeOldBlockTarget_perm D i Λ h δ (blockSucc D Λ i h δ) rfl

/-- The selected ordered dot powers retain their literal component powers. -/
theorem probeOldWeightDotPower_total_component
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) (ζ : WeightBlocks D Λ y) :
    (SKM.rouquierPower d n).total M ζ =
      (show End ((probeOldInductionComponent D Sc m i Λ h ζ).obj M) from
        probeOldWeightDotComponent D Sc m i Λ h (D.parity i) M ζ) ^ n := by
  have hP := rouquierPower_total d n M
  have hD := HomogeneousSuperfunctorIso.total_eq_app d (probeOldActionDot_mem D Sc m i Λ h) M
  have he := congrFun hP ζ
  rw [product_end_power, hD] at he
  exact he

private theorem unit_dotPower_comparison
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) :
    ((probeOldWeightUnitApp D Sc m i Λ h δ M ≫
        (Res).map ((show End ((probeOldInductionComponent D Sc m i Λ h ε).obj M) from
          probeOldWeightDotComponent D Sc m i Λ h (D.parity i) M ε) ^ n)) ≫
      (Res).map (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M))) =
    (probeOldBlockAdj D Sc m i Λ h δ).unit.app (M δ) ≫
      (Res).map ((show End ((probeOldBlockInd D Sc m i Λ h δ).obj (M δ)) from
        (probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  rw [probeOldWeightDotComponent_blockSucc]
  exact unit_conjugate_power (Res).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M)
    ((probeOldBlockAdj D Sc m i Λ h δ).unit.app (M δ))
    ((probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) (M δ)) n

private theorem storedUnitColumn_total (N : ProbeCanonicalModules D Sc m δ.1) (n : ℕ) :
    (probeAppendToUnitColumn D Sc m δ.1.toList i perm n).total N =
      (probeOldBlockAdj D Sc m i Λ h δ).unit.app N ≫
        (Res).map ((show End ((probeOldBlockInd D Sc m i Λ h δ).obj N) from
          (probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) N) ^ n) := by
  have ht := unit_power_total
    (probeAppendToRightAdjunction D Sc m δ.1.toList i ε.1.toList perm)
    (probeAppendToInductionDot D Sc m δ.1.toList i ε.1.toList perm) n N
  have hd := HomogeneousSuperfunctorIso.total_eq_app
    (probeOldBlockDot D Sc m i Λ h δ) (probeOldBlockDot_mem D Sc m i Λ h δ) N
  dsimp only [probeAppendToUnitColumn, probeAppendToDotPower] at ht ⊢
  rw [hd] at ht
  exact ht

/-- Every chosen global unit/power column retains its entire stored-target column. -/
theorem probeOldWeightUnitPower_total_comparison
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) :
    ((A).unit ≫ SKM.rouquierPower d n ▷ F).total M δ ≫
      (Res).map (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M)) =
    (probeAppendToUnitColumn D Sc m δ.1.toList i perm n).total (M δ) := by
  have ht := unit_power_total A d n M
  have hu : (A).unit.app 0 M = (probeOldWeightUnit D Sc m i Λ h).app M := rfl
  rw [hu] at ht
  have ha := congrFun ht δ
  dsimp only [probeOldF, Superfunctor.map, productFunctor, Functor.pi'] at ha
  simp only [Pi.comp_apply] at ha
  rw [product_end_power] at ha
  have hd := HomogeneousSuperfunctorIso.total_eq_app d (probeOldActionDot_mem D Sc m i Λ h) M
  have hδ := congrFun hd ε
  rw [hδ] at ha
  have hc := congrArg (fun f => f ≫ (Res).map
    (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M))) ha
  exact hc.trans ((unit_dotPower_comparison D Sc m i Λ h δ M n).trans
    (storedUnitColumn_total D Sc m i Λ h δ (M δ) n).symm)

end OddMath.QuiverHecke
end

end

section

/-! # Missing-colour boundary rows for the stored upper append

Brundan–Ellis (1.13)–(1.14): the constructed evaluated missing-colour
coefficients follow the selected even upper-loop chart, whose prescribed
dotted-unit square is proved for every exponent. No matrix inverse or
chart-compatibility premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso probeAppendUpperLoopSuperIso
  probeEvaluatedMissingCoefficients
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)

/-- The specified stored-target upper adjunction has the constructed finite
boundary coefficients, including count zero and every indexed inverse row. -/
def probeMissingStoredCoefficients :
    SKM.RouquierBoundary.Coefficients (probeAppendToRightAdjunction D Sc m γ i μ h)
      (probeAppendToInductionDot D Sc m γ i μ h) (D.parity i)
      (contentUnitCount D (probeCutoff D m) i (γ : Multiset I)) :=
  SKM.RouquierBoundaryTransport.ofIso (B := PiSCat.{u,u,u+1} k)
    (a := probeEvaluatedTarget D Sc m γ)
    (b := probeEvaluatedTarget D Sc m (i :: γ))
    (b' := probeEvaluatedTarget D Sc m μ)
    (E := probeAppendToE D Sc m γ i (i :: γ) (List.Perm.refl _))
    (F := probeAppendToF D Sc m γ i (i :: γ) (List.Perm.refl _))
    (E' := probeAppendToE D Sc m γ i μ h) (F' := probeAppendToF D Sc m γ i μ h)
    (A := probeAppendToRightAdjunction D Sc m γ i (i :: γ) (List.Perm.refl _))
    (x := probeAppendToInductionDot D Sc m γ i (i :: γ) (List.Perm.refl _))
    (probeEvaluatedMissingCoefficients D Sc m γ i hi)
    (probeAppendToRightAdjunction D Sc m γ i μ h)
    (probeAppendToInductionDot D Sc m γ i μ h)
    (probeAppendUpperLoopSuperIso D Sc m γ i h)
    (probeAppendUpperLoopSuperIso_hom_mem D Sc m γ i h)
    (probeAppendToInductionDot_mem D Sc m γ i μ h)
    (probeAppendUpperLoop_cup D Sc m γ i h)

end OddMath.QuiverHecke
end

end

section

/-! # The missing-colour local record at a stored upper representative

Brundan–Ellis (1.13)–(1.14): the selected evaluated upper adjunction and
dot, with the constructed zero lower cell, have the prescribed local
inverse at every missing-colour content, including height zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)
local notation "Z" => probeEvaluatedZeroCell D Sc m γ
local notation "A₀" => probeEvaluatedZeroAdjunction D Sc m γ
local notation "E" => probeAppendToE D Sc m γ i μ h
local notation "A₁" => probeAppendToRightAdjunction D Sc m γ i μ h
local notation "dot" => probeAppendToInductionDot D Sc m γ i μ h
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)

/-- The selected missing-colour local data retain both zero-height inverse
orientations, with no positive-cutoff or local-inverse premise. -/
def probeMissingStoredLoc :
    SKM.SuperRouquierLoc A₀ A₁ (0 : End Z) dot (0 : End (Z ≫ E)) (D.parity i)
      (-contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I)) := by
  have L := SKM.RouquierZeroLocal.ofCoefficients A₀ A₁ dot (D.parity i) count
    (probeMissingStoredCoefficients D Sc m γ i h hi)
    (probeEvaluatedZeroCell_comp_id D Sc m γ (probeEvaluatedTarget D Sc m γ) Z)
    (probeEvaluatedZeroCell_comp_id D Sc m γ (probeEvaluatedTarget D Sc m μ) E)
  simpa only [contentUnitCount_cast D (probeCutoff D m) i (γ : Multiset I)
    (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hi)] using L

end OddMath.QuiverHecke
end

end

section

/-! # Local inverses at missing probe weight predecessors

Brundan–Ellis (1.13)–(1.14): the missing-colour stored local record supplies
both prescribed global inverse presentations. The lower mixed coordinate
is the constructed zero object; the upper unit columns retain their
selected successor chart. The cutoff matches the categorical weight.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "E₁" => probeOldE D Sc m i Λ h₁
local notation "F₁" => probeOldF D Sc m i Λ h₁
local notation "E₂" => probeOldE D Sc m i Λ h₂
local notation "F₂" => probeOldF D Sc m i Λ h₂
local notation "A₁" => probeOldActionAdjunction D Sc m i Λ h₁
local notation "A₂" => probeOldActionAdjunction D Sc m i Λ h₂
local notation "φ" => SKM.rouquierMate A₁ A₂
  (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
local notation "UnitField" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₁) n ≫ SKM.SuperAdjunction.counit (probeOldActionAdjunction D Sc m i Λ h₁)
variable (δ : WeightBlocks D Λ x₁)
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "γ" => Multiset.toList (Subtype.val δ)
local notation "μ" => Multiset.toList (Subtype.val ε)
local notation "perm" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "Z" => probeEvaluatedZeroCell D Sc m γ
local notation "B₀" => probeEvaluatedZeroAdjunction D Sc m γ
local notation "e" => probeAppendToE D Sc m γ i μ perm
local notation "f" => probeAppendToF D Sc m γ i μ perm
local notation "B₁" => probeAppendToRightAdjunction D Sc m γ i μ perm
local notation "ψ" => SKM.rouquierMate B₀ B₁ (0 : End (Z ≫ e))
local notation "C" => ProbeEvaluatedModules D Sc m γ

/-- The following induction always uses its specified successor block. -/
theorem probeOldWeightFollowing_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ = (e ≫ f).obj (M δ) := by
  change (probeOldBlockRes D Sc m i Λ h₂ δ).obj
    ((probeOldInductionComponent D Sc m i Λ h₂ ε).obj M) = _
  exact congrArg (fun N => (probeOldBlockRes D Sc m i Λ h₂ δ).obj N)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)

/-- The chosen upper-loop coordinate equality keeps its even map explicitly. -/
theorem probeOldWeightFollowing_eqToHom (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) =
      (probeOldBlockRes D Sc m i Λ h₂ δ).map
        (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)) :=
  (eqToHom_map (probeOldBlockRes D Sc m i Λ h₂ δ).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)).symm

/-- Every missing predecessor has the specified unit inverse, including height zero. -/
theorem probeOldWeightAbsentUnitInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (UnitField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  have hil : i ∉ γ := by simpa only [Multiset.mem_toList] using hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]
  have hh : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) ≤ 0 :=
    neg_nonpos.mpr (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hil)
  let J := ((probeMissingStoredLoc D Sc m γ i perm hil).invNeg hh).at (M δ)
  let a := eqToIso (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ ((F₁).obj M)
  have hZ : Limits.IsZero ((Z ≫ Z).obj (M δ)) := probeEvaluatedZeroModule_isZero D Sc m γ
  let b := hB.iso hZ
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)) hb (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have hg (n : ℕ) : c.hom ≫ (𝟭 C).map
      ((probeAppendToUnitColumn D Sc m γ i perm n).total (M δ)) ≫ a.inv = (UnitField n).total M δ := by
    have hs : (UnitField n).total M δ ≫ a.hom = c.hom ≫
        (probeAppendToUnitColumn D Sc m γ i perm n).total (M δ) := by
      simpa only [a, eqToIso.hom, hc, Category.id_comp,
        probeOldWeightFollowing_eqToHom] using
        probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  let H' := H.copyMaps ((φ).app (D.parity i) M δ) (fun n => (UnitField n).total M δ)
    hf.symm (funext fun n => (hg n).symm)
  exact ⟨by simpa only [hHeight] using H'⟩

/-- The same missing-colour record supplies the cap orientation at height zero. -/
theorem probeOldWeightAbsentCapInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hh : 0 ≤ D.h i x₁)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (CapField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  have hil : i ∉ γ := by simpa only [Multiset.mem_toList] using hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]
  have hpos : 0 ≤ -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) := by
    simpa only [hHeight] using hh
  let J := ((probeMissingStoredLoc D Sc m γ i perm hil).invPos hpos).at (M δ)
  let a := eqToIso (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ ((F₁).obj M)
  have hZ : Limits.IsZero ((Z ≫ Z).obj (M δ)) := probeEvaluatedZeroModule_isZero D Sc m γ
  let b := hB.iso hZ
  let c := Iso.refl (M δ)
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 C) b a c hb
    (eqToHom_mem_parity_zero (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)) (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have hg (n : ℕ) : b.hom ≫ (𝟭 C).map
      ((Z ◁ SKM.rouquierPower (0 : End Z) n ≫ (B₀).counit).total (M δ)) ≫ c.inv =
      (CapField n).total M δ := hB.eq_of_src _ _
  exact ⟨by simpa only [hHeight, hf, hg] using H⟩

end OddMath.QuiverHecke
end

end

section

/-! # Probe weight cap rows in their stored predecessor coordinates

Brundan–Ellis (1.13): preserve the chosen lower dot powers and counit
through the supported source equality at each stored successor block.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
private theorem rouquierPower_total_2
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {F : A ⟶ B} (d : F ⟶ F) (n : ℕ) (M : A.carrier) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem left_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) {G H : B ⟶ E} (z : G ⟶ H) (M : A.carrier) :
    (F ◁ z).total M = z.total (F.obj M) := rfl

private theorem cap_power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {E : A ⟶ B} {F : B ⟶ A} (a : SKM.SuperAdjunction (k := k) E F)
    (d : End E) (n : ℕ) (M : B.carrier) :
    (F ◁ SKM.rouquierPower d n ≫ a.counit).total M =
      ((show End (E.obj (F.obj M)) from d.total (F.obj M)) ^ n) ≫ a.counit.app 0 M := by
  rw [Superfunctor.comp_total, left_whisker_total, rouquierPower_total_2,
    HomogeneousSuperfunctorIso.total_eq_app a.counit a.counit_mem]

private theorem conjugate_power_counit
    {A : Type*} [Category A] [Preadditive A]
    {V W Z : A} (h : W = V) (d : End V) (ε : V ⟶ Z) (n : ℕ) :
    ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n) ≫
      (eqToHom h ≫ ε) = eqToHom h ≫ (d ^ n) ≫ ε := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (β : WeightBlocks D Λ x)
local notation "δ" => blockSucc D Λ i h β
local notation "Res" => probeOldBlockRes D Sc m i Λ h β
local notation "A" => probeOldActionAdjunction D Sc m i Λ h
local notation "d" => probeOldActionDot D Sc m i Λ h
local notation "F" => probeOldF D Sc m i Λ h
local notation "perm" => probeOldBlockTarget_perm D i Λ h β (blockSucc D Λ i h β) rfl

private theorem counit_dotPower_comparison
    (M : ProbeOldWeightProduct D Sc m Λ y) (n : ℕ) :
    ((show End ((probeOldInductionComponent D Sc m i Λ h δ).obj ((F).obj M)) from
      probeOldWeightDotComponent D Sc m i Λ h (D.parity i) ((F).obj M) δ) ^ n) ≫
      (probeOldWeightCounit D Sc m i Λ h).app M δ =
    eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫
      ((show End ((probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj (M δ))) from
        (probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (probeOldBlockAdj D Sc m i Λ h β).counit.app (M δ) := by
  dsimp only [probeOldWeightCounit]
  rw [probeOldWeightDotComponent_blockSucc, probeOldWeightCounitComponent_blockSucc]
  exact conjugate_power_counit
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M))
    ((probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj (M δ)))
    ((probeOldBlockAdj D Sc m i Λ h β).counit.app (M δ)) n

private theorem storedCapRow_total (N : ProbeCanonicalModules D Sc m δ.1) (n : ℕ) :
    (probeAppendToCapRow D Sc m β.1.toList i perm n).total N =
      ((show End ((probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj N)) from
        (probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj N)) ^ n) ≫
        (probeOldBlockAdj D Sc m i Λ h β).counit.app N := by
  have ht := cap_power_total
    (probeAppendToRightAdjunction D Sc m β.1.toList i δ.1.toList perm)
    (probeAppendToInductionDot D Sc m β.1.toList i δ.1.toList perm) n N
  have hd := HomogeneousSuperfunctorIso.total_eq_app
    (probeOldBlockDot D Sc m i Λ h β) (probeOldBlockDot_mem D Sc m i Λ h β) ((Res).obj N)
  dsimp only [probeAppendToCapRow, probeAppendToDotPower] at ht ⊢
  rw [hd] at ht
  exact ht

/-- Every supported chosen global power/cap row retains the whole stored row. -/
theorem probeOldWeightCapPower_total_comparison
    (M : ProbeOldWeightProduct D Sc m Λ y) (n : ℕ) :
    ((F ◁ SKM.rouquierPower d n) ≫ (A).counit).total M δ =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫
        (probeAppendToCapRow D Sc m β.1.toList i perm n).total (M δ) := by
  have ht := Superfunctor.comp_total (F ◁ SKM.rouquierPower d n) (A).counit M
  rw [left_whisker_total] at ht
  have hc : (A).counit.total M = (probeOldWeightCounit D Sc m i Λ h).app M := by
    change (probeOldWeightCounit D Sc m i Λ h).app M + 0 = _
    exact add_zero _
  rw [hc] at ht
  have ha := congrFun ht δ
  simp only [Pi.comp_apply] at ha
  rw [probeOldWeightDotPower_total_component] at ha
  have hr := congrArg (fun f :
      (probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj (M δ)) ⟶ M δ =>
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫ f)
    (storedCapRow_total D Sc m i Λ h β (M δ) n).symm
  exact ha.trans ((counit_dotPower_comparison D Sc m i Λ h β M n).trans hr)

end OddMath.QuiverHecke
end

end
