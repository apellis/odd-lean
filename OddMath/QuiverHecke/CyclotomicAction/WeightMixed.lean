import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import OddMath.QuiverHecke.CyclotomicAction.WeightPair
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.SKM.RouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend
import OddMath.SKM.RouquierData
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerAnnihilation

/-!
# Weight mixed

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Tensor vacuum on the original weight products

SwappedVacuumCoordinates §2: the empty formal probe block defines a Hom
input between the full original-weight products. Evaluation at its regular
probe recovers the selected regular-power empty-word family by an even
module isomorphism on every reservoir block and every vector. Contents
with the same original weight are retained, rather than identified.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

private def forgetEmptyFunctor (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k) := by
  subst ν
  exact ObjectProperty.ι _

/-- The selected empty-word forgetting map, exposed for the native vacuum cap chart. -/
abbrev emptyContentForget (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k) :=
  forgetEmptyFunctor D Sc m ν h

private instance (ν : List I) (h : ν = []) :
    (forgetEmptyFunctor D Sc m ν h).Additive := by
  subst ν
  exact ⟨by intros; rfl⟩

private instance (ν : List I) (h : ν = []) :
    (forgetEmptyFunctor D Sc m ν h).Linear k := by
  subst ν
  exact ⟨fun _ _ => rfl⟩

private instance (ν : List I) (h : ν = []) :
    IsSuperfunctor k (forgetEmptyFunctor D Sc m ν h) := by
  subst ν
  exact ⟨fun hf => hf⟩

private def regularEmpty (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν := by
  subst ν
  exact ⟨probeOldVacuumRegular D Sc m, probeOldVacuumRegular_evaluates D Sc m⟩

private theorem forget_regular (ν : List I) (h : ν = []) :
    (forgetEmptyFunctor D Sc m ν h).obj (regularEmpty D Sc m ν h) =
      probeOldVacuumRegular D Sc m := by
  subst ν
  rfl

/-- The empty formal content at the lowest original probe weight. -/
def emptyBlock (Λ : X) : WeightBlocks D Λ (-Λ) := ⟨0, blockWeight_zero D Λ⟩

/-- Evaluate only at formal content zero, retaining the other source blocks. -/
def emptyProbe (Λ : X) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ (-Λ))
      (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)) :=
  (probeOldBlockEval D Sc m Λ (emptyBlock D Λ)).comp
    ⟨forgetEmptyFunctor D Sc m (0 : Multiset I).toList Multiset.toList_zero⟩

private def regularAt (β : Multiset I) (h : β = 0) : ProbeCanonicalModules D Sc m β := by
  subst β
  exact regularEmpty D Sc m _ Multiset.toList_zero

/-- The evaluated regular probe at formal content zero, with zero modules
at every other content, including collisions in the original weight group. -/
def regularProbe (Λ : X) : ProbeOldWeightProduct D Sc m Λ (-Λ) :=
  fun β => if h : β.1 = 0 then regularAt D Sc m β.1 h
    else probeOldZeroModule D Sc m β.1

theorem emptyProbe_regular (Λ : X) :
    (emptyProbe D Sc m Λ).obj (regularProbe D Sc m Λ) = probeOldVacuumRegular D Sc m := by
  change (forgetEmptyFunctor D Sc m _ Multiset.toList_zero).obj
    (if h : (0 : Multiset I) = 0 then regularAt D Sc m 0 h
      else probeOldZeroModule D Sc m 0) = _
  rw [dite_eq_left rfl]
  exact forget_regular D Sc m _ Multiset.toList_zero

private theorem probeScalar_mem :
    SVec.ofHom (probeVacuumScalarEquiv D Sc m).symm.toLinearMap ∈
      parity (R := k) ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m))
        SVec.unit 0 := by
  intro q
  apply LinearMap.ext
  intro v
  change (probeVacuumScalarEquiv D Sc m).symm
      (((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)).proj q v) =
    (SVec.unit (k := k)).proj (q + 0) ((probeVacuumScalarEquiv D Sc m).symm v)
  rw [SVec.proj_apply_of_mem_part _ (p := q) (probeVacuum_even D Sc m v)]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp only [ite_true, add_zero]
    exact (SVec.unit_proj_zero_apply _).symm
  · simp only [one_ne_zero, ite_false, map_zero, add_zero]
    exact (SVec.unit_proj_one_apply _).symm

variable (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (W : ELVWeightProduct D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0))

/-- Tensor with the reservoir family after empty formal probe evaluation. -/
def blockFunctor (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    Superfunctor k (ProbeOldWeightProduct D Sc m ΛP (-ΛP))
      (ContentModules D Sc cutoff bound β.1) :=
  (emptyProbe D Sc m ΛP).comp
    (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m))

def functor : ProbeOldWeightProduct D Sc m ΛP (-ΛP) ⥤
    ELVWeightProduct D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  Functor.pi' fun β => (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor

instance : (functor D Sc m cutoff bound ΛP ΛR W).Additive where
  map_add := funext fun β => (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor.map_add

instance : (functor D Sc m cutoff bound ΛP ΛR W).Linear k where
  map_smul f r := funext fun β =>
    (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor.map_smul r f

instance : IsSuperfunctor k (functor D Sc m cutoff bound ΛP ΛR W) where
  map_mem hf β := IsSuperfunctor.map_mem
    (F := (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor) hf

/-- A swapped Hom input between the two full original-weight products. -/
def hom : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
    elvWeightSpace D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  ⟨functor D Sc m cutoff bound ΛP ΛR W⟩

/-- The prescribed regular-probe evaluation before applying the scalar chart. -/
theorem regularBlock_eq (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    ((hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP)) β =
      VacuumTensor.object (W β)
        ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)) :=
  congrArg (fun M => (VacuumTensor.superfunctor (W β)
    (probeOldVacuumObject D Sc m)).obj M) (emptyProbe_regular D Sc m ΛP)

private def blockIso (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    ((hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP)) β ≅ W β :=
  eqToIso (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β) ≪≫
    VacuumTensor.scalarTensorIso (W β) _ (probeVacuumScalarEquiv D Sc m).symm
      (probeScalar_mem D Sc m)

/-- The tensor-vacuum Hom input evaluated at its specified regular probe
recovers the entire reservoir family, with no assumed comparison. -/
def regularIso :
    (hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP) ≅ W :=
  Pi.isoMk (blockIso D Sc m cutoff bound ΛP ΛR W)

theorem regularIso_hom_mem :
    (regularIso D Sc m cutoff bound ΛP ΛR W).hom ∈ parity (R := k) _ _ 0 := by
  intro β
  exact comp_mem (eqToHom_mem_parity_zero (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β))
    (VacuumTensor.scalarTensorIso_hom_mem _ _ _ _)

/-- The regular tensor vector carrying an arbitrary reservoir coefficient. -/
def tensorVector (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff bound β.1) (v : (W β).obj c) :
    (((hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP)) β).obj c :=
  (eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm).total c
    (v ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1)

theorem regularIso_hom_tensorVector
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff bound β.1) (v : (W β).obj c) :
    ((regularIso D Sc m cutoff bound ΛP ΛR W).hom β).total c
      (tensorVector D Sc m cutoff bound ΛP ΛR W β c v) = v := by
  let f := (VacuumTensor.scalarTensorIso (W β) _
    (probeVacuumScalarEquiv D Sc m).symm (probeScalar_mem D Sc m)).hom
  have h : eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm ≫
      (regularIso D Sc m cutoff bound ΛP ΛR W).hom β = f := by
    change eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm ≫
      (eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β) ≫ f) = f
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have ht := congrArg (fun g => g.total c) h
  rw [Superfunctor.comp_total] at ht
  change ((eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm).total c ≫
    ((regularIso D Sc m cutoff bound ΛP ΛR W).hom β).total c)
      (v ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1) = v
  rw [ht]
  exact (VacuumTensor.scalarTensorIso_hom_tmul (W β) _
    (probeVacuumScalarEquiv D Sc m).symm (probeScalar_mem D Sc m) c v
      (probeVacuumScalarEquiv D Sc m 1)).trans (by
        rw [LinearEquiv.symm_apply_apply, one_smul])

variable (L : I × ℕ → ℕ)

/-- The selected regular-power tensor-vacuum Hom input at sector `(0,0)`. -/
def selectedHom : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
    elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
      (ReservoirWord.weight D ΛR 0) :=
  hom D Sc m cutoff _ ΛP ΛR (ReservoirWordValue.initialValue D ΛR Sc cutoff L)

/-- Its reservoir value at the actual regular probe is the already selected
regular-power empty-word family on every original-weight block. -/
def selectedIso :
    (selectedHom D Sc m cutoff ΛP ΛR L).obj (regularProbe D Sc m ΛP) ≅
      ReservoirWordValue.initialValue D ΛR Sc cutoff L :=
  regularIso D Sc m cutoff _ ΛP ΛR _

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end

section

/-! # Weight cup and cap in rectangular mixed-mate coordinates

The remaining transport for Brundan–Ellis (1.12) compares the selected
weight adjunction maps through the supported content coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem unit_transport
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {P Q : Superfunctor k C (SVec k)} {W : Superfunctor k B (SVec k)}
    (hPQ : P = Q) (hWP : W = BalancedInduction.induced J P)
    (hWQ : W = BalancedInduction.induced J Q) :
    ((BalancedInduction.adjunctionUnit J).app P ≫
      (BalancedInduction.restriction J).map (eqToHom hWP.symm)) ≫
        (BalancedInduction.restriction J).map (eqToHom hWQ) =
      eqToHom hPQ ≫ (BalancedInduction.adjunctionUnit J).app Q := by
  subst Q
  subst W
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem map_counit_transport
    {A E : Type*} [Category* A] [Category* E] (L : A ⥤ E)
    {Y Z T : A} {P Q : E} (hYZ : Y = Z) (hP : P = L.obj Y)
    (hQ : Q = L.obj T) (hPZ : P = L.obj Z) (f : Z ⟶ T) :
    (eqToHom hP ≫ L.map (eqToHom hYZ ≫ f) ≫ eqToHom hQ.symm) ≫ eqToHom hQ =
      eqToHom hPZ ≫ L.map f := by
  subst Z
  subst P
  subst Q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The map of induction retains an arbitrary prescribed successor block. -/
theorem elvInductionComponent_map_of (i : I) (Λ : X) {x y : X}
    (h : x + D.α i = y) (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y)
    (hβ : blockSucc D Λ i h β = δ)
    {M N : ELVWeightProduct D Sc cutoff bound Λ x} (f : M ⟶ N) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).map f =
      eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h β δ hβ M) ≫
        (BalancedInduction.induction
          (contentAppendTo D Sc cutoff bound β.1 [i] δ.1
            ((elvBlockSucc_content_eq D i Λ h β).trans (congrArg Subtype.val hβ)))).map (f β) ≫
          eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h β δ hβ N).symm := by
  subst δ
  exact elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ h β f

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)
local notation "Fj" => elvF D Sc cutoff bound j Λ h₁
local notation "Ei" => elvE D Sc cutoff bound i Λ h₃
local notation "sourcePairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) rfl

/-- The selected upper weight cup commutes with the supported source and pair coordinates. -/
theorem elvWeightMixedUnit_comparison (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightUnitApp D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M))) ≫
      (BalancedInduction.restriction U).map
        (eqToHom (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)) =
      eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M) ≫
        (BalancedInduction.adjunctionUnit U).app
          (BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj))) := by
  have h := unit_transport U
    (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M)
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)
  simp only [PiSCat.comp_obj] at h ⊢
  dsimp only [elvWeightUnitApp, elvBlockAdj, BalancedInduction.adjunction, elvBlockEval, Pi.eval,
    Functor.comp_obj, Functor.id_obj, Superfunctor.obj, Superfunctor.comp, elvBlockRes] at h ⊢
  exact h

local notation "hUpper" => elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β))) hUpper
local notation "targetPairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) hComm

/-- The selected lower weight cap commutes with the supported pair and target coordinates. -/
theorem elvWeightMixedCounit_comparison (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).map
      ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M) ≫
      eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M) =
    eqToHom (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq) ≫
      (BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app (M δj)) := by
  have hm := elvInductionComponent_map_of D Sc cutoff bound i Λ h₂ δj ε hComm
    ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M)
  dsimp only [elvWeightCounit] at hm
  rw [elvWeightCounitComponent_blockSucc] at hm
  have ht := congrArg
    (fun f => f ≫ eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)) hm
  have h := map_counit_transport (BalancedInduction.induction L)
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₁ β ((Fj).obj M))
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm
      ((elvE D Sc cutoff bound j Λ h₁).obj ((Fj).obj M)))
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq)
    ((BalancedInduction.adjunctionCounit J).app (M δj))
  dsimp only [elvBlockEval, Pi.eval, Functor.comp_obj, Functor.id_obj, Superfunctor.obj,
    Superfunctor.comp, elvBlockRes, elvBlockAdj, BalancedInduction.adjunction, elvWeightCounit] at h ht ⊢
  exact ht.trans h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Assembly of the distinct weight mixed mate

For Brundan–Ellis (1.12), the selected supported cup, crossing and cap
are pasted through their literal content coordinates. Absent sectors
use the proved vanishing of both existing mixed-functor coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem mate_transport
    {A B : Type*} [Category* A] [Category* B] (R : A ⥤ B)
    {P Q : B} {S T V S' T' V' : A}
    (hP : P = Q) (hS : S = S') (hT : T = T') (hV : V = V')
    (η : P ⟶ R.obj S) (χ : S ⟶ T) (ε : T ⟶ V)
    (η' : Q ⟶ R.obj S') (χ' : S' ⟶ T') (ε' : T' ⟶ V')
    (hu : η ≫ R.map (eqToHom hS) = eqToHom hP ≫ η')
    (hx : χ = (eqToHom hS ≫ χ') ≫ eqToHom hT.symm)
    (hc : ε ≫ eqToHom hV = eqToHom hT ≫ ε') :
    ((η ≫ R.map χ) ≫ R.map ε) ≫ R.map (eqToHom hV) =
      eqToHom hP ≫ ((η' ≫ R.map χ') ≫ R.map ε') := by
  subst Q
  subst S'
  subst T'
  subst V'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu hx hc ⊢
  rw [hu, hx, hc]

private theorem rectangularMate_expansion
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k)) :
    BalancedInduction.orderedRectangularMateComponent J K L U hα N =
      ((BalancedInduction.adjunctionUnit U).app
          (BalancedInduction.induced K ((BalancedInduction.restriction J).obj N)) ≫
        (BalancedInduction.restriction U).map (BalancedInduction.rectangularCrossComponent J K L U hα
          ((BalancedInduction.restriction J).obj N))) ≫
        (BalancedInduction.restriction U).map
          ((BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app N)) := by
  exact (Category.assoc _ _ _).symm

private theorem isIso_of_homogeneous_components
    {k C B : Type*} [CommRing k] [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) F G p) (hi : ∀ M, IsIso (f.app p M)) : IsIso f := by
  let e : ∀ M, F.obj M ≅ G.obj M := fun M => by
    let : IsIso (f.app p M) := hi M
    exact asIso (f.app p M)
  have he (M) : (e M).hom = f.total M :=
    (HomogeneousSuperfunctorIso.total_eq_app f hf M).symm
  rw [← HomogeneousSuperfunctorIso.ofHom_hom f hf e he]
  infer_instance

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Fj" => elvF D Sc cutoff bound j Λ h₁
local notation "Ei" => elvE D Sc cutoff bound i Λ h₃
local notation "Cross" => elvActionCross D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂

/-- The selected weight mate component retains the ordinary selected cup and cap. -/
theorem elvWeightMixedMate_app_block (p : ZMod 2)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) (δ : WeightBlocks D Λ xi) :
    (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app p M δ =
      (elvWeightUnitApp D Sc cutoff bound j Λ h₄ δ ((Ei).obj ((Fj).obj M)) ≫
        (elvBlockRes D Sc cutoff bound j Λ h₄ δ).map
          ((Cross).app p ((Fj).obj M) (blockSucc D Λ j h₄ δ))) ≫
        (elvBlockRes D Sc cutoff bound j Λ h₄ δ).map
          ((elvInductionComponent D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₄ δ)).map
            ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M)) := by
  have h := congrFun (elvWeightMixedMate_app D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ p M) δ
  dsimp only [elvActionUnit, elvActionCounit, SuperNatTrans.ofNatTrans, elvWeightUnit,
    elvF, elvE, elvEFunctor, productFunctor, Superfunctor.map, Superfunctor.obj] at h ⊢
  simp only [Pi.comp_apply] at h
  dsimp only [Functor.pi'] at h
  exact h.trans (Category.assoc _ _ _).symm

variable (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)
local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)))
  (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
local notation "hα" => contentDistinctTargetsCross_supernatural D Sc cutoff bound (Subtype.val β) i j
  (Subtype.val (blockSucc D Λ j h₁ β)) (Subtype.val (blockSucc D Λ i h₃ β))
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)))
  (elvBlockSucc_content_eq D j Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₃ β)
  (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
  (elvBlockSucc_content_eq D j Λ h₄ (blockSucc D Λ i h₃ β))
local notation "sourcePairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) rfl
local notation "targetPairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) hComm

/-- The whole prescribed weight mate agrees with the positive content mate on every supported block. -/
theorem elvWeightMixedMate_comparison (hij : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M δi ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M) ≫
      BalancedInduction.orderedRectangularMateComponent J K L U hα (M δj) := by
  have hx := elvWeightCrossVia_rectangular D Sc cutoff bound j i Λ h₃ h₄ β ε rfl
    h₁ h₂ hij.symm ((Fj).obj M)
  rw [mul_comm (D.parity j) (D.parity i)] at hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app] at hx
  have hw := elvWeightCross_supported D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂
    (D.parity i * D.parity j) ((Fj).obj M) β ε rfl
  have hCross := hw.trans hx
  have hu := elvWeightMixedUnit_comparison D Sc cutoff bound i j Λ h₁ h₃ h₄ β M
  have hc := elvWeightMixedCounit_comparison D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M
  have hp := mate_transport (BalancedInduction.restriction U)
    (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq)
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)
    (elvWeightUnitApp D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    ((Cross).app (D.parity i * D.parity j) ((Fj).obj M) ε)
    ((elvInductionComponent D Sc cutoff bound i Λ h₂ ε).map
      ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M))
    ((BalancedInduction.adjunctionUnit U).app
      (BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj))))
    (BalancedInduction.rectangularCrossComponent J K L U hα ((BalancedInduction.restriction J).obj (M δj)))
    ((BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app (M δj)))
    hu hCross hc
  rw [eqToHom_map, ← rectangularMate_expansion] at hp
  have ha := congrArg
    (fun f => f ≫ eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M))
    (elvWeightMixedMate_app_block D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M δi)
  exact ha.trans hp

/-- The given weight mate is invertible at every supported output block. -/
theorem elvWeightMixedMate_supported_isIso (hij : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    IsIso ((elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M δi) := by
  let : IsIso (BalancedInduction.orderedRectangularMateComponent J K L U hα (M δj)) :=
    contentDistinctTargetsMate_isIso D Sc cutoff bound β.1 i j δj.1 δi.1 ε.1
      (elvBlockSucc_content_eq D j Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₃ β)
      (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
      (elvBlockSucc_content_eq D j Λ h₄ δi) hij (M δj)
  let : IsIso ((elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M δi ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M)) := by
    rw [elvWeightMixedMate_comparison D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β hij M]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M))

/-- Every output coordinate of the prescribed weight mate is invertible. -/
theorem elvWeightMixedMate_coordinate_isIso (hij : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) (δ : WeightBlocks D Λ xi) :
    IsIso ((elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M δ) := by
  by_cases hδ : ∃ β, blockSucc D Λ i h₃ β = δ
  · obtain ⟨β, rfl⟩ := hδ
    exact elvWeightMixedMate_supported_isIso D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β hij M
  · exact elvWeightMixedMate_absent_isIso D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij δ hδ
      (D.parity i * D.parity j) M

/-- The whole product-module component retains the inverse of its prescribed forward map. -/
theorem elvWeightMixedMate_component_isIso (hij : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    IsIso ((elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) M) :=
  (isIso_pi_iff _).mpr (elvWeightMixedMate_coordinate_isIso D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M)

/-- Brundan–Ellis (1.12): the selected distinct weight cup-crossing-cap is an isomorphism. -/
theorem elvWeightMixedMate_isIso (hij : i ≠ j) :
    IsIso (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) :=
  isIso_of_homogeneous_components _ (elvWeightMixedMate_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄)
    (elvWeightMixedMate_component_isIso D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The sideways crossing on ELV weight spaces

Brundan–Ellis (1.11)–(1.12): the presentation's ordered cup–crossing–cap
is the already constructed rectangular mate, with the same crossing and
both prescribed adjunctions. Its inverse therefore requires no new premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k] {A B C D : PiSCat.{u,u,u + 1} k}
  {E₁ : A ⟶ B} {F₁ : B ⟶ A} {E₂ : C ⟶ D} {F₂ : D ⟶ C}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (g : A ⟶ C) (h : B ⟶ D) (t : g ≫ E₂ ⟶ E₁ ≫ h)

/-- The presentation mate keeps all four weight corners independent. -/
theorem crossMate_piscat_app (p : ZMod 2) (Z : B.carrier) :
    (crossMate A₁ A₂ t).app p Z =
      A₂.unit.app 0 (g.obj (F₁.obj Z)) ≫
        F₂.map (t.app p (F₁.obj Z)) ≫ F₂.map (h.map (A₁.counit.app 0 Z)) := by
  have hu := Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0)
  have hc := Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [crossMate, PiSCat.whiskerLeft_def, PiSCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

/-- The two mate conventions agree for the prescribed even bending maps. -/
theorem crossMate_piscat_eq_rectangular :
    crossMate A₁ A₂ t = rectangularMate A₁ A₂ g h t := by
  apply Superfunctor.hom_ext
  intro p Z
  exact (crossMate_piscat_app A₁ A₂ g h t p Z).trans
    (rectangularMate_piscat_app A₁ A₂ g h t
      (Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0))
      (Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)) p Z).symm
end OddMath.SKM

namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d : X}
  (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
  (h₃ : a + D.α i = c) (h₄ : c + D.α j = d)

/-- The chosen sideways crossing is the constructed rectangular weight mate. -/
theorem elvActionCrossMate_eq :
    SKM.crossMate (elvActionAdjunction D Sc cutoff bound i Λ h₃)
      (elvActionAdjunction D Sc cutoff bound i Λ h₂)
      (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) =
      elvWeightMixedMate D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ :=
  SKM.crossMate_piscat_eq_rectangular _ _ _ _ _

/-- The exact distinct-colour inversion field of the presentation. -/
theorem elvActionCrossMate_isIso (hij : i ≠ j) :
    IsIso (SKM.crossMate (elvActionAdjunction D Sc cutoff bound i Λ h₃)
      (elvActionAdjunction D Sc cutoff bound i Λ h₂)
      (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄)) := by
  rw [elvActionCrossMate_eq]
  exact elvWeightMixedMate_isIso D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂ hij.symm
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Matrix counts on an entire original-weight fibre

DeformedActionAssembly §§1, 6 fixes a highest cutoff weight Λ with
cutoff(i)=h_i(Λ). Its induction categories have weight sum(α)-Λ.
Thus the content-matrix height is the negative categorical weight height,
and the finite counts agree on every content in an original-weight fibre.
No injectivity of the root or coroot maps is assumed.
-/

noncomputable section
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X : Type u} [AddCommGroup X]
  (D : SKM.Datum I X) (cutoff : I → ℕ)

/-- The matrix height is constant on each original-weight fibre, even
before the cutoff has been identified with the highest-weight pairings. -/
theorem contentCrossingHeight_weightBlock (i : I) (Λ x : X)
    (β : WeightBlocks D Λ x) :
    contentCrossingHeight D cutoff i β.1 =
      (cutoff i : ℤ) - D.h i Λ - D.h i x := by
  have hb := congrArg (D.cd.coroot i) β.2
  change (D.cd.coroot i) ((β.1.map D.α).sum - Λ) = (D.cd.coroot i) x at hb
  simp only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def] at hb
  unfold contentCrossingHeight SKM.Datum.h
  omega

/-- The source-required cutoff compatibility identifies the two height
conventions; it is not asserted for arbitrary unrelated Λ and cutoff. -/
theorem contentCrossingHeight_eq_neg_weight (i : I) (Λ x : X)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (β : WeightBlocks D Λ x) :
    contentCrossingHeight D cutoff i β.1 = -D.h i x := by
  rw [contentCrossingHeight_weightBlock D cutoff i Λ x β, hcutoff, sub_self, zero_sub]

/-- The unit-window count is exactly the negative categorical height. -/
theorem contentUnitCount_weightBlock (i : I) (Λ x : X)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (β : WeightBlocks D Λ x) :
    contentUnitCount D cutoff i β.1 = (-D.h i x).toNat := by
  unfold contentUnitCount
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x hcutoff β]

/-- The cap-window count is exactly the positive categorical height. -/
theorem contentCapCount_weightBlock (i : I) (Λ x : X)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (β : WeightBlocks D Λ x) :
    contentCapCount D cutoff i β.1 = (D.h i x).toNat := by
  unfold contentCapCount
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x hcutoff β, neg_neg]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Augmented inverse assembly over a weight fibre

BE (1.13)–(1.14): assemble pointwise augmented inverses in arbitrary
products of supercategories. The finite inverse window is common to all
components; the standing cutoff/highest-weight count identity supplies
that window on an original-weight fibre. No finite set of blocks or
injective root map is required.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.SKM
universe u v w t
variable {k : Type w} [CommRing k] {ι : Type t} {C : ι → Type u}
  [∀ a, Category.{v} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]
  {A B Z : ∀ a, C a} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

private theorem product_sum_apply {X Y : ∀ a, C a}
    (s : Finset ℕ) (h : ℕ → (X ⟶ Y)) (a : ι) :
    (∑ m ∈ s, h m) a = ∑ m ∈ s, h m a := by
  exact (CategoryTheory.Pi.eval C a).map_sum h s

/-- The given component column inverses assemble on the entire product,
without a finiteness condition on its index type. -/
def SuperSumInvFrom.pi
    {f : ∀ a, B a ⟶ A a} {g : ℕ → ∀ a, Z a ⟶ A a}
    (J : ∀ a, SuperSumInvFrom (k := k) (f a) (fun m => g m a) p q n) :
    SuperSumInvFrom (k := k) (show B ⟶ A from f) (fun m => (show Z ⟶ A from g m)) p q n where
  f' a := (J a).f'
  g' m a := (J a).g' m
  f_mem a := (J a).f_mem
  g_mem m a := (J a).g_mem m
  f'_mem a := (J a).f'_mem
  g'_mem m a := (J a).g'_mem m
  total := by
    funext a
    simpa only [Categorification.TwoRep.pi_add_apply, product_sum_apply, CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply] using (J a).total
  ff := funext fun a => (J a).ff
  fg m hm := funext fun a => (J a).fg m hm
  gf m hm := funext fun a => (J a).gf m hm
  gg m l hm hl := by
    by_cases hml : m = l
    · rw [ite_eq_left hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply, ite_eq_left hml] using (J a).gg m l hm hl
    · rw [ite_eq_right hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, Categorification.TwoRep.pi_zero_apply, ite_eq_right hml] using (J a).gg m l hm hl

/-- The given component row inverses assemble on an arbitrary product. -/
def SuperSumInvTo.pi
    {f : ∀ a, A a ⟶ B a} {g : ℕ → ∀ a, A a ⟶ Z a}
    (J : ∀ a, SuperSumInvTo (k := k) (f a) (fun m => g m a) p q n) :
    SuperSumInvTo (k := k) (show A ⟶ B from f) (fun m => (show A ⟶ Z from g m)) p q n where
  f' a := (J a).f'
  g' m a := (J a).g' m
  f_mem a := (J a).f_mem
  g_mem m a := (J a).g_mem m
  f'_mem a := (J a).f'_mem
  g'_mem m a := (J a).g'_mem m
  total := by
    funext a
    simpa only [Categorification.TwoRep.pi_add_apply, product_sum_apply, CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply] using (J a).total
  ff := funext fun a => (J a).ff
  fg m hm := funext fun a => (J a).fg m hm
  gf m hm := funext fun a => (J a).gf m hm
  gg m l hm hl := by
    by_cases hml : m = l
    · rw [ite_eq_left hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply, ite_eq_left hml] using (J a).gg m l hm hl
    · rw [ite_eq_right hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, Categorification.TwoRep.pi_zero_apply, ite_eq_right hml] using (J a).gg m l hm hl

end OddMath.SKM
end

end

section

/-! # The selected rank-one weight mate and its component formula

The principal field of Brundan–Ellis (1.13)–(1.14) is the local
Rouquier mate of the existing signed equal-colour crossing. It is the
same rectangular cup-crossing-cap used in the content matrix transport.
Its parity is p_i, and its lower and upper adjunctions remain those of
the prescribed adjacent weight steps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "A₁" => elvActionAdjunction D Sc cutoff bound i Λ h₁
local notation "A₂" => elvActionAdjunction D Sc cutoff bound i Λ h₂
local notation "Cross" => elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂

/-- The local-inversion principal entry is exactly the given rectangular weight mate. -/
theorem elvWeightRouquierMate_eq :
    SKM.rouquierMate A₁ A₂ Cross =
      elvWeightMixedMate D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ :=
  SKM.rouquierMate_piscat_eq_rectangular A₁ A₂ Cross

/-- The principal entry has the required rank-one matrix parity. -/
theorem elvWeightRouquierMate_mem :
    SKM.rouquierMate A₁ A₂ Cross ∈ parity (R := k) _ _ (D.parity i) := by
  rw [elvWeightRouquierMate_eq]
  simpa only [SKM.zmod2_mul_self] using
    elvWeightMixedMate_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Normalized weight mate in content coordinates

Brundan–Ellis (1.12)–(1.14): the selected cup-crossing-cap retains the
negative equal-colour crossing and positive distinct-colour crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem mate_transport_2
    {A B : Type*} [Category* A] [Category* B] (R : A ⥤ B)
    {P Q : B} {S T V S' T' V' : A}
    (hP : P = Q) (hS : S = S') (hT : T = T') (hV : V = V')
    (η : P ⟶ R.obj S) (χ : S ⟶ T) (ε : T ⟶ V)
    (η' : Q ⟶ R.obj S') (χ' : S' ⟶ T') (ε' : T' ⟶ V')
    (hu : η ≫ R.map (eqToHom hS) = eqToHom hP ≫ η')
    (hx : χ = (eqToHom hS ≫ χ') ≫ eqToHom hT.symm)
    (hc : ε ≫ eqToHom hV = eqToHom hT ≫ ε') :
    ((η ≫ R.map χ) ≫ R.map ε) ≫ R.map (eqToHom hV) =
      eqToHom hP ≫ ((η' ≫ R.map χ') ≫ R.map ε') := by
  subst Q
  subst S'
  subst T'
  subst V'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu hx hc ⊢
  rw [hu, hx, hc]

private theorem rectangularMate_expansion_2
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k)) :
    BalancedInduction.orderedRectangularMateComponent J K L U hα N =
      ((BalancedInduction.adjunctionUnit U).app
          (BalancedInduction.induced K ((BalancedInduction.restriction J).obj N)) ≫
        (BalancedInduction.restriction U).map (BalancedInduction.rectangularCrossComponent J K L U hα
          ((BalancedInduction.restriction J).obj N))) ≫
        (BalancedInduction.restriction U).map
          ((BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app N)) := by
  exact (Category.assoc _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Fj" => elvF D Sc cutoff bound j Λ h₁
local notation "Ei" => elvE D Sc cutoff bound i Λ h₃
local notation "Cross" => elvActionCross D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂

variable (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)
local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)))
  (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
local notation "hα" => normalizedContentTargetsCross_supernatural D Sc cutoff bound (Subtype.val β) i j
  (Subtype.val (blockSucc D Λ j h₁ β)) (Subtype.val (blockSucc D Λ i h₃ β))
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)))
  (elvBlockSucc_content_eq D j Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₃ β)
  (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
  (elvBlockSucc_content_eq D j Λ h₄ (blockSucc D Λ i h₃ β))
local notation "sourcePairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) rfl
local notation "targetPairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) hComm

/-- The whole prescribed weight mate agrees with the normalized content mate on every supported block. -/
theorem elvWeightNormalizedMate_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M δi ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M) ≫
      BalancedInduction.orderedRectangularMateComponent J K L U hα (M δj) := by
  have hx := elvWeightCrossVia_normalized_rectangular D Sc cutoff bound j i Λ h₃ h₄ β ε rfl
    h₁ h₂ ((Fj).obj M)
  rw [mul_comm (D.parity j) (D.parity i)] at hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app] at hx
  have hw := elvWeightCross_supported D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂
    (D.parity i * D.parity j) ((Fj).obj M) β ε rfl
  have hCross := hw.trans hx
  have hu := elvWeightMixedUnit_comparison D Sc cutoff bound i j Λ h₁ h₃ h₄ β M
  have hc := elvWeightMixedCounit_comparison D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M
  have hp := mate_transport_2 (BalancedInduction.restriction U)
    (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq)
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)
    (elvWeightUnitApp D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    ((Cross).app (D.parity i * D.parity j) ((Fj).obj M) ε)
    ((elvInductionComponent D Sc cutoff bound i Λ h₂ ε).map
      ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M))
    ((BalancedInduction.adjunctionUnit U).app
      (BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj))))
    (BalancedInduction.rectangularCrossComponent J K L U hα ((BalancedInduction.restriction J).obj (M δj)))
    ((BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app (M δj)))
    hu hCross hc
  rw [eqToHom_map, ← rectangularMate_expansion_2] at hp
  have ha := congrArg
    (fun f => f ≫ eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M))
    (elvWeightMixedMate_app_block D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M δi)
  exact ha.trans hp

section RankOne
variable (a : I) {y₀ y₁ y₂ : X}
  (ha : y₀ + D.α a = y₁) (hb : y₁ + D.α a = y₂)
  (b : WeightBlocks D Λ y₀)
local notation "d" => blockSucc D Λ a ha b
local notation "e" => blockSucc D Λ a hb (blockSucc D Λ a ha b)
local notation "Lower" => elvBlockAppend D Sc cutoff bound a Λ ha b
local notation "Upper" => elvBlockAppend D Sc cutoff bound a Λ hb (blockSucc D Λ a ha b)
local notation "hχ" => normalizedContentTargetsCross_supernatural D Sc cutoff bound
  (Subtype.val b) a a (Subtype.val (blockSucc D Λ a ha b))
  (Subtype.val (blockSucc D Λ a ha b))
  (Subtype.val (blockSucc D Λ a hb (blockSucc D Λ a ha b)))
  (elvBlockSucc_content_eq D a Λ ha b) (elvBlockSucc_content_eq D a Λ ha b)
  (elvBlockSucc_content_eq D a Λ hb (blockSucc D Λ a ha b))
  (elvBlockSucc_content_eq D a Λ hb (blockSucc D Λ a ha b))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff bound a Λ ha)
  (elvActionAdjunction D Sc cutoff bound a Λ hb)
  (elvActionCross D Sc cutoff bound a a Λ ha hb ha hb)

/-- The prescribed rank-one principal field retains the negative rectangular
crossing through its selected source and target content coordinates. -/
theorem elvWeightRouquierMate_comparison
    (N : ELVWeightProduct D Sc cutoff bound Λ y₁) :
    (φ).app (D.parity a) N d ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound a a Λ ha hb ha hb b N) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound a a Λ ha ha b N) ≫
      BalancedInduction.orderedRectangularMateComponent Lower Lower Upper Upper hχ (N d) := by
  rw [elvWeightRouquierMate_eq]
  have h := elvWeightNormalizedMate_comparison D Sc cutoff bound a a Λ ha hb ha hb b N
  have hp := congrArg
    (fun p => (elvWeightMixedMate D Sc cutoff bound a a Λ ha hb ha hb).app p N d)
    (SKM.zmod2_mul_self (D.parity a))
  exact (congrArg (fun f => f ≫ eqToHom
    (elvWeightMixedTarget_obj D Sc cutoff bound a a Λ ha hb ha hb b N)) hp.symm).trans h
end RankOne

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The selected weight Rouquier principal field in grid coordinates

BE (1.13)–(1.14): the negative normalized equal-colour crossing gives
precisely the ordinary grid mate used by the prescribed finite matrices.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hGrid" => contentTargetsGridCross_supernatural D Sc cutoff bound
  (Subtype.val β) (Subtype.val (blockSucc D Λ i h₁ β))
  (Subtype.val (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) i
  (elvBlockSucc_content_eq D i Λ h₁ β)
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ i h₁ β))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff bound i Λ h₁)
  (elvActionAdjunction D Sc cutoff bound i Λ h₂)
  (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂)

/-- The prescribed rank-one principal field is the given grid matrix mate
in the selected content source and target coordinates. -/
theorem elvWeightRouquierGridMate_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x₁) :
    (φ).app (D.parity i) M δ ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β M) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i i Λ h₁ h₁ β M) ≫
      BalancedInduction.orderedGridMateComponent J K hGrid (M δ) := by
  have h := elvWeightRouquierMate_comparison D Sc cutoff bound Λ i h₁ h₂ β M
  have hg := normalizedContentTargetsMate_eq_grid D Sc cutoff bound β.1 δ.1 ε.1 i
    (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
  exact h.trans (congrArg (fun f =>
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i i Λ h₁ h₁ β M) ≫ f) hg)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Selected weight unit columns in successor coordinates

The unit columns of BE (1.14) are compared at every output block,
including blocks without a predecessor of their own. Their following
induction always has the selected successor and retains every dot power.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h δ
local notation "Res" => elvBlockRes D Sc cutoff bound i Λ h δ
local notation "ε" => blockSucc D Λ i h δ

/-- The selected Rouquier dot powers retain the literal ordinary powers
of the selected dot component in each weight block. -/
theorem elvWeightDotPower_total_component
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ)
    (ζ : WeightBlocks D Λ y) :
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n).total M ζ =
      (show End ((elvInductionComponent D Sc cutoff bound i Λ h ζ).obj M) from
        elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M ζ) ^ n := by
  have hP := rouquierPower_total (elvActionDot D Sc cutoff bound i Λ h) n M
  have hD := HomogeneousSuperfunctorIso.total_eq_app
    (elvActionDot D Sc cutoff bound i Λ h) (elvActionDot_mem D Sc cutoff bound i Λ h) M
  have h := congrFun hP ζ
  rw [product_end_power, hD] at h
  exact h

/-- Every selected unit and dot power has its literal successor-content column,
including output blocks with no lower predecessor. -/
theorem elvWeightUnit_dotPower_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ) :
    ((elvWeightUnitApp D Sc cutoff bound i Λ h δ M) ≫
        (Res).map ((show End ((elvInductionComponent D Sc cutoff bound i Λ h ε).obj M) from
          elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M ε) ^ n)) ≫
      (Res).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M)) =
    (BalancedInduction.adjunctionUnit J).app (M δ) ≫
      (Res).map ((show End (BalancedInduction.induced J (M δ)) from
        (elvBlockDot D Sc cutoff bound i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  rw [elvWeightDotComponent_blockSucc]
  exact unit_conjugate_power (Res).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M)
    ((BalancedInduction.adjunctionUnit J).app (M δ))
    ((elvBlockDot D Sc cutoff bound i Λ h δ).app (D.parity i) (M δ)) n

/-- The specified weight unit/Rouquier-power field has exactly the
ordinary content unit/dot column after its selected successor chart. -/
theorem elvWeightUnitPower_total_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ) :
    ((elvActionUnit D Sc cutoff bound i Λ h ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ▷
          elvF D Sc cutoff bound i Λ h).total M δ) ≫
      (Res).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M)) =
    (BalancedInduction.adjunctionUnit J).app (M δ) ≫
      (Res).map ((show End (BalancedInduction.induced J (M δ)) from
        (elvBlockDot D Sc cutoff bound i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  have hw := right_whisker_total
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n)
    (elvF D Sc cutoff bound i Λ h) M
  have hc := Superfunctor.comp_total (elvActionUnit D Sc cutoff bound i Λ h)
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ▷
      elvF D Sc cutoff bound i Λ h) M
  rw [hw] at hc
  have hu : (elvActionUnit D Sc cutoff bound i Λ h).total M =
      (elvWeightUnit D Sc cutoff bound i Λ h).app M := by
    simp only [elvActionUnit, SuperNatTrans.ofNatTrans, SuperNatTrans.total,
      ite_true, one_ne_zero, ite_false, add_zero]
  rw [hu] at hc
  have ha := congrFun hc δ
  dsimp only [elvF, Superfunctor.map, productFunctor, Functor.pi'] at ha
  simp only [Pi.comp_apply] at ha
  have hp := elvWeightDotPower_total_component D Sc cutoff bound i Λ h M n ε
  rw [hp] at ha
  exact (congrArg (fun f => f ≫ (Res).map
    (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M))) ha).trans
      (elvWeightUnit_dotPower_comparison D Sc cutoff bound i Λ h δ M n)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Selected weight cap rows in predecessor coordinates

BE (1.13): the prescribed lower Rouquier dot powers followed by the
selected counit are ordinary content cap rows in the selected supported
source coordinate. Every power and the full input module are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem left_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) {G H : B ⟶ E} (z : G ⟶ H) (M : A.carrier) :
    (F ◁ z).total M = z.total (F.obj M) := rfl

private theorem conjugate_power_counit
    {A : Type*} [Category A] [Preadditive A]
    {V W Z : A} (h : W = V) (d : End V) (ε : V ⟶ Z) (n : ℕ) :
    ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n) ≫
      (eqToHom h ≫ ε) = eqToHom h ≫ (d ^ n) ≫ ε := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (β : WeightBlocks D Λ x)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h β
local notation "Res" => elvBlockRes D Sc cutoff bound i Λ h β
local notation "δ" => blockSucc D Λ i h β
local notation "F" => elvF D Sc cutoff bound i Λ h

/-- Every selected ordinary dot power/cap row retains its supported content source. -/
theorem elvWeightCounit_dotPower_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (n : ℕ) :
    ((show End ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj ((F).obj M)) from
      elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) ((F).obj M) δ) ^ n) ≫
      (elvWeightCounit D Sc cutoff bound i Λ h).app M δ =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β ((F).obj M)) ≫
      ((show End (BalancedInduction.induced J ((Res).obj (M δ))) from
        (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (BalancedInduction.adjunctionCounit J).app (M δ) := by
  dsimp only [elvWeightCounit]
  rw [elvWeightDotComponent_blockSucc, elvWeightCounitComponent_blockSucc]
  exact conjugate_power_counit
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β ((F).obj M))
    ((elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) ((Res).obj (M δ)))
    ((BalancedInduction.adjunctionCounit J).app (M δ)) n

/-- The specified lower Rouquier-power/cap field has the literal content cap row. -/
theorem elvWeightCapPower_total_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (n : ℕ) :
    ((F ◁ SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ≫
        elvActionCounit D Sc cutoff bound i Λ h).total M δ) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β ((F).obj M)) ≫
      ((show End (BalancedInduction.induced J ((Res).obj (M δ))) from
        (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (BalancedInduction.adjunctionCounit J).app (M δ) := by
  have hw := left_whisker_total F
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n) M
  have hc := Superfunctor.comp_total
    (F ◁ SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n)
    (elvActionCounit D Sc cutoff bound i Λ h) M
  rw [hw] at hc
  have hu : (elvActionCounit D Sc cutoff bound i Λ h).total M =
      (elvWeightCounit D Sc cutoff bound i Λ h).app M := by
    simp only [elvActionCounit, SuperNatTrans.ofNatTrans, SuperNatTrans.total,
      ite_true, one_ne_zero, ite_false, add_zero]
  rw [hu] at hc
  have ha := congrFun hc δ
  simp only [Pi.comp_apply] at ha
  rw [elvWeightDotPower_total_component] at ha
  exact ha.trans (elvWeightCounit_dotPower_comparison D Sc cutoff bound i Λ h β M n)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The selected weight power fields are the finite matrix columns and rows

BE (1.13)–(1.14): retain the literal ordinary unitDotColumn and capDotRow
module maps after applying the selected successor-content coordinate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I)

/-- The common-target selected dot is exactly the given module dot endomorphism. -/
theorem elvContentDotTo_component (β γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff bound β) :
    (elvContentDotTo D Sc cutoff bound i β γ hγ).app (D.parity i) M =
      BalancedInduction.dotEnd (contentAppendTo D Sc cutoff bound β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M := by
  exact inductionTransform_app_self _ _ _ M

variable (Λ : X) {x y : X} (h : x + D.α i = y) (β : WeightBlocks D Λ x)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h β
local notation "Res" => elvBlockRes D Sc cutoff bound i Λ h β
local notation "δ" => blockSucc D Λ i h β
/-- The given affine dot between the literal selected successor contents. -/
theorem elvBlockGridDot_supernatural : IsSupernatural k (D.parity i)
    (contentAppendToComponent D Sc cutoff bound
      (elvBlockSucc_content_eq D i Λ h β) (elvBlockSucc_content_eq D i Λ h β)
      (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc cutoff bound
    (elvBlockSucc_content_eq D i Λ h β) (elvBlockSucc_content_eq D i Λ h β) (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)
local notation "hDot" => elvBlockGridDot_supernatural D Sc cutoff bound i Λ h β

/-- Every selected weight unit/Rouquier-power field is the literal given finite unit column. -/
theorem elvWeightUnit_gridColumn_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ) :
    ((elvActionUnit D Sc cutoff bound i Λ h ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ▷
          elvF D Sc cutoff bound i Λ h).total M β) ≫
      (Res).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M)) =
    BalancedInduction.unitDotColumn J hDot (M β) n := by
  have hU := elvWeightUnitPower_total_comparison D Sc cutoff bound i Λ h β M n
  have hD := elvContentDotTo_component D Sc cutoff bound i β.1 δ.1
    (elvBlockSucc_content_eq D i Λ h β) (M β)
  have hC := congrArg (fun d : End (BalancedInduction.induced J (M β)) =>
    (BalancedInduction.adjunctionUnit J).app (M β) ≫ (Res).map (d ^ n)) hD
  exact hU.trans hC

/-- Every supported selected weight Rouquier-power/cap field is the literal given finite cap row. -/
theorem elvWeightCap_gridRow_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (n : ℕ) :
    ((elvF D Sc cutoff bound i Λ h ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ≫
        elvActionCounit D Sc cutoff bound i Λ h).total M δ) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
      ((elvF D Sc cutoff bound i Λ h).obj M)) ≫
      BalancedInduction.capDotRow J hDot (M δ) n := by
  have hC := elvWeightCapPower_total_comparison D Sc cutoff bound i Λ h β M n
  have hD := elvContentDotTo_component D Sc cutoff bound i β.1 δ.1
    (elvBlockSucc_content_eq D i Λ h β) ((Res).obj (M δ))
  have hR := congrArg (fun d : End (BalancedInduction.induced J ((Res).obj (M δ))) =>
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
      ((elvF D Sc cutoff bound i Λ h).obj M)) ≫
        (d ^ n) ≫ (BalancedInduction.adjunctionCounit J).app (M δ)) hD
  exact hC.trans hR

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Common coordinates for prescribed local weight matrix fields

BE (1.13)–(1.14): the unit columns and cap rows use exactly the same
source and target equations as the prescribed Rouquier principal mate.
These whole module-map identities supply the selected chart transport
for the supported weight local inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff N Λ x₁)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "ResU" => elvBlockRes D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hSource" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hTarget" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The selected principal-target equation is the upper induction equation under restriction. -/
theorem elvWeightLocalTarget_hom :
    eqToHom hTarget = (ResU).map (eqToHom
      (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)) := by
  exact (eqToHom_map (ResU).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)).symm

/-- The literal unit columns use the very same target chart as the principal mate. -/
theorem elvWeightUnitPower_localCoordinates (n : ℕ) :
    ((elvActionUnit D Sc cutoff N i Λ h₂ ≫
      SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
        elvF D Sc cutoff N i Λ h₂).total M δ) ≫ eqToHom hTarget =
      unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n := by
  have h := congrArg (fun f =>
    ((elvActionUnit D Sc cutoff N i Λ h₂ ≫
      SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
        elvF D Sc cutoff N i Λ h₂).total M δ) ≫ f)
    (elvWeightLocalTarget_hom D Sc cutoff N i Λ h₁ h₂ β M)
  exact h.trans (elvWeightUnit_gridColumn_comparison D Sc cutoff N i Λ h₂ δ M n)

/-- The literal cap rows use the very same source chart as the principal mate. -/
theorem elvWeightCapPower_localCoordinates (n : ℕ) :
    ((elvF D Sc cutoff N i Λ h₁ ◁
      SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
        elvActionCounit D Sc cutoff N i Λ h₁).total M δ) =
      eqToHom hSource ≫ capDotRow J
        (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n :=
  elvWeightCap_gridRow_comparison D Sc cutoff N i Λ h₁ β M n

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The regular empty probe generates the empty block

InverseColumnMoments, open item 1 (faithfulness of the regular-probe
evaluation). Every object of the old empty-content category is the empty
object, and every endomorphism of it is a coefficient. Scalar-evaluated
modules therefore see each endomorphism as one common scalar. Hence every
homogeneous vector of the empty block of a probe weight product is the image of
the prescribed empty idempotent under a morphism out of the regular probe, of
the same parity. This is the generating hypothesis of
`VacuumTensor.hom_ext_of_generating` for `emptyProbe` at `regularProbe`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

local notation "cut" => probeCutoff D m
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m)
  (probeScalarValues_vanish D m)
local notation "vac" => probeOldVacuumObject D Sc m
local notation "Reg" => probeOldVacuumRegular D Sc m

omit [Fintype I] in
/-- The old empty-content category has the empty object only. -/
theorem emptyObject_eq (v : OldContentCategory D Sc (probeCutoff D m) []) : v = vac := by
  obtain ⟨⟨w⟩, hw⟩ := v
  obtain rfl : w = [] := hw.eq_nil
  rfl

omit [Fintype I] in
/-- Every endomorphism of the empty object is the old coefficient of its
affine empty-word coordinate. -/
theorem vacuumEnd_eq (f : vac ⟶ vac) :
    f = probeOldCoefficient D m Sc [] vac (emptyCoefficientDecoder D Sc cut f) :=
  (emptyCoefficientEncoder_decoder D Sc cut f).symm

omit [Fintype I] in
/-- A scalar-evaluated module sees each empty endomorphism as one scalar,
determined by the endomorphism alone. -/
theorem vacuum_map_eq (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc [] N) (f : vac ⟶ vac) :
    N.map f = ev (emptyCoefficientDecoder D Sc cut f) • 𝟙 (N.obj vac) := by
  have h := hN vac (emptyCoefficientDecoder D Sc cut f)
  rwa [← vacuumEnd_eq] at h

/-- An odd endomorphism of the regular empty probe vanishes: the probe is purely even. -/
theorem regular_odd_eq_zero {g : (Reg).obj vac ⟶ (Reg).obj vac} (hg : g ∈ parity (R := k) _ _ 1) :
    g = 0 := by
  apply SVec.hom_ext
  intro x
  have h := LinearMap.congr_fun (hg 0) x
  change g (((Reg).obj vac).proj 0 x) = ((Reg).obj vac).proj (0 + 1) (g x) at h
  rw [SVec.proj_apply_of_mem_part _ (probeVacuum_even D Sc m x),
    SVec.proj_apply_of_mem_part _ (probeVacuum_even D Sc m (g x))] at h
  simpa using h

section Hom
variable (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k))

/-- The scalar coordinate of the regular probe, followed by `n`. -/
def vacuumLinear (n : N.obj vac) : (Reg).obj vac ⟶ N.obj vac :=
  SVec.ofHom (LinearMap.smulRight (probeVacuumScalarEquiv D Sc m).symm.toLinearMap n)

theorem vacuumLinear_apply (n : N.obj vac) (x : (Reg).obj vac) :
    vacuumLinear D Sc m N n x = (probeVacuumScalarEquiv D Sc m).symm x • n := rfl

theorem vacuumLinear_mem (q : ZMod 2) (n : N.obj vac) (hn : n ∈ (N.obj vac).part q) :
    vacuumLinear D Sc m N n ∈ parity (R := k) ((Reg).obj vac) (N.obj vac) q := by
  apply SVec.mem_parityHom_of_apply_mem
  intro r x hx
  rw [vacuumLinear_apply]
  rcases parity_eq_zero_or_one r with rfl | rfl
  · rw [zero_add]
    exact Submodule.smul_mem _ _ hn
  · have h0 := SVec.proj_apply_of_mem_part ((Reg).obj vac) (p := 0) hx
    rw [SVec.proj_apply_of_mem_part _ (probeVacuum_even D Sc m x)] at h0
    simp only [ite_true, zero_ne_one, ite_false] at h0
    rw [h0, map_zero, zero_smul]
    exact Submodule.zero_mem _

/-- Scalars of empty endomorphisms commute with `vacuumLinear`. -/
theorem vacuumLinear_natural (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N) (f : vac ⟶ vac) :
    vacuumLinear D Sc m N n ≫ N.map f = (Reg).map f ≫ vacuumLinear D Sc m N n := by
  rw [vacuum_map_eq D Sc m N hN, vacuum_map_eq D Sc m Reg (probeOldVacuumRegular_evaluates D Sc m),
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- The components of the morphism out of the regular probe. -/
def vacuumApp (q : ZMod 2) (n : N.obj vac) (p : ZMod 2) (Y : OldContentCategory D Sc (probeCutoff D m) []) :
    (Reg).obj Y ⟶ N.obj Y :=
  if p = q then
    eqToHom (congrArg (Reg).obj (emptyObject_eq D Sc m Y)) ≫ vacuumLinear D Sc m N n ≫
      eqToHom (congrArg N.obj (emptyObject_eq D Sc m Y).symm)
  else 0

theorem vacuumApp_vac (q : ZMod 2) (n : N.obj vac) (p : ZMod 2) :
    vacuumApp D Sc m N q n p vac = if p = q then vacuumLinear D Sc m N n else 0 := by
  simp only [vacuumApp, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The morphism out of the regular empty probe carrying the prescribed
empty idempotent to `n`. -/
def vacuumHom (q : ZMod 2) (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N) (hn : n ∈ (N.obj vac).part q) :
    Reg ⟶ N where
  app := vacuumApp D Sc m N q n
  app_mem p Y := by
    obtain rfl := emptyObject_eq D Sc m Y
    rw [vacuumApp_vac]
    split_ifs with h
    · subst h
      exact vacuumLinear_mem D Sc m N p n hn
    · exact Submodule.zero_mem _
  naturality p Y Z q' f hf := by
    obtain rfl := emptyObject_eq D Sc m Y
    obtain rfl := emptyObject_eq D Sc m Z
    change (Reg).map f ≫ vacuumApp D Sc m N q n p vac =
      koszulSign p q' • (vacuumApp D Sc m N q n p vac ≫ N.map f)
    rw [vacuumApp_vac]
    split_ifs with h
    · rw [vacuumLinear_natural D Sc m N n hN f]
      rcases parity_eq_zero_or_one q' with rfl | rfl
      · rw [koszulSign_zero_right, one_smul]
      · rw [regular_odd_eq_zero D Sc m ((Reg).map_mem hf), Limits.zero_comp, smul_zero]
    · rw [Limits.comp_zero, Limits.zero_comp, smul_zero]

theorem vacuumHom_mem (q : ZMod 2) (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N)
    (hn : n ∈ (N.obj vac).part q) :
    vacuumHom D Sc m N q n hN hn ∈ parity (R := k) Reg N q := by
  apply Superfunctor.mem_parityHom.mpr
  change vacuumApp D Sc m N q n (q + 1) = 0
  funext Y
  obtain rfl := emptyObject_eq D Sc m Y
  have hne : q + 1 ≠ q := by
    intro h
    have : (1 : ZMod 2) = 0 := by simpa using congrArg (· - q) h
    exact one_ne_zero this
  rw [vacuumApp_vac]
  simp only [hne, ↓reduceIte]
  rfl

theorem vacuumHom_vector (q : ZMod 2) (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N)
    (hn : n ∈ (N.obj vac).part q) :
    (vacuumHom D Sc m N q n hN hn).app q vac (probeOldVacuumVector D Sc m) = n := by
  change vacuumApp D Sc m N q n q vac (probeOldVacuumVector D Sc m) = n
  rw [vacuumApp_vac, ite_eq_left_iff.mpr (fun h => (h rfl).elim), vacuumLinear_apply, ← probeVacuumScalarEquiv_one,
    LinearEquiv.symm_apply_apply, one_smul]

end Hom

omit [Fintype I] in
/-- The empty forgetful functor preserves scalar evaluation. -/
theorem emptyContentForget_evaluates (ν : List I) (h : ν = [])
    (M : ProbeEvaluatedModules D Sc m ν) :
    ProbeEvaluatesCoefficients D m Sc [] ((emptyContentForget D Sc m ν h).obj M) := by
  subst h
  exact M.property

omit [Fintype I] in
/-- The empty forgetful functor is full, with parity. -/
theorem emptyContentForget_preimage (ν : List I) (h : ν = [])
    {M M' : ProbeEvaluatedModules D Sc m ν} {q : ZMod 2}
    (τ : (emptyContentForget D Sc m ν h).obj M ⟶ (emptyContentForget D Sc m ν h).obj M')
    (hτ : τ ∈ parity (R := k) _ _ q) :
    ∃ g : M ⟶ M', g ∈ parity (R := k) M M' q ∧ (emptyContentForget D Sc m ν h).map g = τ := by
  subst h
  exact ⟨⟨τ⟩, hτ, rfl⟩

omit [Fintype I] in
private theorem eqToHom_comp_app {F G H : Superfunctor k (OldContentCategory D Sc
    (probeCutoff D m) []) (SVec k)} (e : F = G) (e' : G = F) (τ : G ⟶ H) (q : ZMod 2) (Y)
    (y : G.obj Y) : ((eqToHom e ≫ τ).app q Y) ((eqToHom e' : G ⟶ F).app 0 Y y) = τ.app q Y y := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Superfunctor.id_app_zero]
  rfl

/-- The prescribed empty idempotent, as a vector of the empty block of the regular probe. -/
def regularVector (Λ : X) : ((emptyProbe D Sc m Λ).obj (regularProbe D Sc m Λ)).obj vac :=
  (eqToHom (emptyProbe_regular D Sc m Λ).symm).app 0 vac (probeOldVacuumVector D Sc m)

/-- Every homogeneous vector of the empty block is the image of the regular
vector under a morphism out of the regular probe of the same parity. -/
theorem regularProbe_generating (Λ : X) (Y : ProbeOldWeightProduct D Sc m Λ (-Λ))
    (q : ZMod 2) (n : ((emptyProbe D Sc m Λ).obj Y).obj vac)
    (hn : n ∈ (((emptyProbe D Sc m Λ).obj Y).obj vac).part q) :
    ∃ f : regularProbe D Sc m Λ ⟶ Y, f ∈ parity (R := k) _ _ q ∧
      ((emptyProbe D Sc m Λ).map f).app q vac (regularVector D Sc m Λ) = n := by
  have hN := emptyContentForget_evaluates D Sc m _ Multiset.toList_zero (Y (emptyBlock D Λ))
  let τ := vacuumHom D Sc m _ q n hN hn
  have hτ' : eqToHom (emptyProbe_regular D Sc m Λ) ≫ τ ∈ parity (R := k) _ _ q := by
    simpa only [zero_add] using
      comp_mem (eqToHom_mem_parity_zero (emptyProbe_regular D Sc m Λ))
        (vacuumHom_mem D Sc m _ q n hN hn)
  obtain ⟨g, hg, hgm⟩ := emptyContentForget_preimage D Sc m _ Multiset.toList_zero
    (M := regularProbe D Sc m Λ (emptyBlock D Λ)) (M' := Y (emptyBlock D Λ)) _ hτ'
  let f : regularProbe D Sc m Λ ⟶ Y := fun β =>
    if h : β = emptyBlock D Λ then (by subst h; exact g) else 0
  have hf : f (emptyBlock D Λ) = g := by
    simp only [f, ↓reduceDIte]
  refine ⟨f, ?_, ?_⟩
  · intro β
    by_cases h : β = emptyBlock D Λ
    · subst h
      rw [hf]
      exact hg
    · simp only [f, h, ↓reduceDIte]
      exact Submodule.zero_mem _
  · change ((emptyContentForget D Sc m _ Multiset.toList_zero).map
      (f (emptyBlock D Λ))).app q vac (regularVector D Sc m Λ) = n
    rw [hf, hgm, regularVector]
    exact (eqToHom_comp_app D Sc m _ _ τ q vac _).trans (vacuumHom_vector D Sc m _ q n hN hn)

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
