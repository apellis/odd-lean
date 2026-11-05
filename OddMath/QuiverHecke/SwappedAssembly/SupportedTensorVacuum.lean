import OddMath.QuiverHecke.SwappedAssembly.SupportedGeneratorEntries
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorReservoirWords

/-! # The selected tensor vacuum in the supported path action

SwappedVacuumCoordinates §§2–3: the initial supported object is the
specified whole-weight tensor Hom. The included supported path value is
identified with its prescribed reservoir-word postcomposition, using the
computed factor comparison and the existing even reservoir-word chart.
No presentation or central-inverse hypothesis is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorVacuumHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
local notation "Sc'" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L

private def atProbeWeight {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Sc' m ΛP x ⟶ elvWeightSpace D Sc' cutoff N ΛR z) :
    probeOldWeightSpace D Sc' m ΛP y ⟶ elvWeightSpace D Sc' cutoff N ΛR z := h ▸ F

private theorem atProbeWeight_comp {x y z z' : X} (h : x = y)
    (F : probeOldWeightSpace D Sc' m ΛP x ⟶ elvWeightSpace D Sc' cutoff N ΛR z)
    (K : elvWeightSpace D Sc' cutoff N ΛR z ⟶ elvWeightSpace D Sc' cutoff N ΛR z') :
    atProbeWeight D Sc m cutoff L ΛP ΛR h F ≫ K =
      atProbeWeight D Sc m cutoff L ΛP ΛR h (F ≫ K) := by subst y; rfl

private theorem atProbeWeight_supported {x y z : X} (h : x = y)
    (β : WeightBlocks D ΛP x) (γ : WeightBlocks D ΛR z)
    (F : probeOldWeightSpace D Sc' m ΛP x ⟶ elvWeightSpace D Sc' cutoff N ΛR z)
    (hF : ContentHomSupport.Supported D Sc' m cutoff N β γ F) :
    ContentHomSupport.Supported D Sc' m cutoff N
      (⟨β.1, β.2.trans h⟩ : WeightBlocks D ΛP y) γ
      (atProbeWeight D Sc m cutoff L ΛP ΛR h F) := by subst y; exact hF

omit [Fintype I] in
/-- The formal zero-content probe weight has its prescribed vacuum value. -/
theorem probeWeight_vacuum : probeWeight D ΛP (0,0) = -ΛP := by simp [probeWeight]

/-- Only the proved input-weight presentation changes in this tensor Hom. -/
def tensorHomAt {z : X}
    (F : probeOldWeightSpace D Sc' m ΛP (-ΛP) ⟶ elvWeightSpace D Sc' cutoff N ΛR z) :
    probeOldWeightSpace D Sc' m ΛP (probeWeight D ΛP (0,0)) ⟶
      elvWeightSpace D Sc' cutoff N ΛR z :=
  atProbeWeight D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm F

/-- The literal chosen tensor Hom, regarded as an object of the formal vacuum sector. -/
def tensorVacuum : H D Sc' m cutoff N ΛP ΛR (0,0) := by
  refine ⟨tensorHomAt D Sc m cutoff L ΛP ΛR
    (WeightTensorVacuum.selectedHom D Sc' m cutoff ΛP ΛR L), ?_⟩
  have hβ : (⟨(WeightTensorVacuum.emptyBlock D ΛP).1,
      (WeightTensorVacuum.emptyBlock D ΛP).2.trans (probeWeight_vacuum D ΛP).symm⟩ :
        WeightBlocks D ΛP (probeWeight D ΛP (0,0))) = probeBlock D ΛP (0,0) := by
    apply Subtype.ext
    simp [WeightTensorVacuum.emptyBlock, probeBlock]
  have hγ : ContentHomSupport.reservoirVacuumBlock D ΛR = reservoirBlock D ΛR (0,0) := by
    apply Subtype.ext
    simp [reservoirBlock, ContentHomSupport.reservoirVacuumBlock]
  have hs := atProbeWeight_supported D Sc m cutoff L ΛP ΛR
    (probeWeight_vacuum D ΛP).symm (WeightTensorVacuum.emptyBlock D ΛP)
    (ContentHomSupport.reservoirVacuumBlock D ΛR) _
    (ContentHomSupport.selectedVacuum_supported D Sc' m cutoff ΛP ΛR L)
  rw [hβ, hγ] at hs
  exact hs

/-- Full inclusion retains the literal tensor Hom with only its input-weight transport. -/
theorem tensorVacuum_obj :
    (tensorVacuum D Sc m cutoff L ΛP ΛR).obj = tensorHomAt D Sc m cutoff L ΛP ΛR
      (WeightTensorVacuum.selectedHom D Sc' m cutoff ΛP ΛR L) := rfl

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

/-- The included path value at the chosen supported vacuum is the selected
tensor Hom postcomposed by its actual reservoir word. -/
def tensorVacuumPathIso {l : List (Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ((pathFunctor D Sc' m cutoff N ΛP ΛR p).obj
      (tensorVacuum D Sc m cutoff L ΛP ΛR)).obj ≅
        tensorHomAt D Sc m cutoff L ΛP ΛR
          (TensorReservoirWords.pathHom D Sc' m cutoff L ΛP ΛR p hl) := by
  refine eqToIso (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
    (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≪≫ ?_
  refine (((P).reservoirWordFunctorIso p hl).app
    (tensorVacuum D Sc m cutoff L ΛP ΛR).obj) ≪≫ ?_
  exact eqToIso (atProbeWeight_comp D Sc m cutoff L ΛP ΛR
    (probeWeight_vacuum D ΛP).symm _ _)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
