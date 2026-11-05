import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuum
import OddMath.QuiverHecke.SwappedAssembly.SupportedMatrixModules
import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomZero
import OddMath.QuiverHecke.Label

/-! # Sector families of the selected tensor-vacuum source row

SwappedVacuumCoordinates §§1–3: the chosen target family is the literal
supported tensor vacuum at formal content zero and zero at every other
formal sector. For each fixed source word, its source family retains the
actual supported reservoir-path value at that word's formal content and
zero elsewhere. Original-weight collisions do not identify formal sectors,
and different source words of the same content keep their specified word
functors. These are families of whole functors, before regular-input
observation or any quotient-coordinate choice.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorFamiliesHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)

private def exactZero (t : Sector I) :
    ContentHomSupport.Hom D Sc m cutoff bound (probeBlock D ΛP t) (reservoirBlock D ΛR t) :=
  ⟨elvZeroFunctor D Sc cutoff bound (reservoirBlock D ΛR t).1⟩

/-- The actual exact-content zero functor, in the whole original-weight supported Hom. -/
def supportedZero (t : Sector I) : H D Sc m cutoff bound ΛP ΛR t :=
  ⟨ContentHomSupport.realization D Sc m cutoff bound (probeBlock D ΛP t) (reservoirBlock D ΛR t)
      (exactZero D Sc m cutoff bound ΛP ΛR t),
    ContentHomSupport.realization_supported D Sc m cutoff bound (probeBlock D ΛP t)
      (reservoirBlock D ΛR t) _⟩

/-- Zero padding vanishes as a whole functor, including every colliding weight block. -/
theorem supportedZero_obj_isZero (t : Sector I) :
    Limits.IsZero (supportedZero D Sc m cutoff bound ΛP ΛR t).obj := by
  have hz (M : probeOldWeightSpace D Sc m ΛP (probeWeight D ΛP t))
      (δ : WeightBlocks D ΛR (reservoirWeight D ΛR t)) :
      Limits.IsZero (((supportedZero D Sc m cutoff bound ΛP ΛR t).obj.obj M) δ) := by
    classical
    by_cases hδ : δ = reservoirBlock D ΛR t
    · subst δ
      change Limits.IsZero (((ContentHomSupport.realization D Sc m cutoff bound
        (probeBlock D ΛP t) (reservoirBlock D ΛR t)
          (exactZero D Sc m cutoff bound ΛP ΛR t)).obj M) (reservoirBlock D ΛR t))
      rw [ContentHomSupport.obj_selected]
      exact elvZeroModule_isZero D Sc cutoff bound (reservoirBlock D ΛR t).1
    · exact ContentHomSupport.obj_off_isZero D Sc m cutoff bound
        (probeBlock D ΛP t) (reservoirBlock D ΛR t)
          (exactZero D Sc m cutoff bound ΛP ΛR t) M δ hδ
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext_parity
  · intro M
    funext δ
    exact (hz M δ).eq_of_src _ _
  · intro M
    funext δ
    exact (hz M δ).eq_of_src _ _

/-- The supported zero remains a zero object under the literal full inclusion. -/
theorem supportedZero_isZero (t : Sector I) :
    Limits.IsZero (supportedZero D Sc m cutoff bound ΛP ΛR t) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply (inclusion D Sc m cutoff bound ΛP ΛR t).map_injective
  exact (Limits.IsZero.iff_id_eq_zero _).mp
    (supportedZero_obj_isZero D Sc m cutoff bound ΛP ΛR t)

variable [Fintype I] (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Sc'" => parameterTwist D Sc
local notation "μ" => ΛP - ΛR

/-- The target family of the chosen vacuum row, padded at actual formal sectors. -/
def tensorTargetFamily (t : Sector I) : H D Sc' m cutoff N ΛP ΛR t := by
  classical
  exact if h : t = (0,0) then by subst t; exact tensorVacuum D Sc m cutoff L ΛP ΛR
    else supportedZero D Sc' m cutoff N ΛP ΛR t

@[simp] theorem tensorTargetFamily_zero :
    tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0) = tensorVacuum D Sc m cutoff L ΛP ΛR := by
  simp [tensorTargetFamily]

/-- Off-vacuum padding is governed by formal content, independently of root-weight collisions. -/
theorem tensorTargetFamily_isZero (t : Sector I) (ht : t ≠ (0,0)) :
    Limits.IsZero (tensorTargetFamily D Sc m cutoff ΛP ΛR L t) := by
  rw [tensorTargetFamily, dite_eq_right ht]
  exact supportedZero_isZero D Sc' m cutoff N ΛP ΛR t

/-- The original labelled upward source word, at the literal vacuum external weight. -/
def tensorSourceLabels (s : List I) : List (Col I X) := wd D μ (upWord s)

omit [Fintype I] in
theorem tensorSourceLabels_up (s : List I) :
    ∀ a ∈ tensorSourceLabels D ΛP ΛR s, a.l.1 = true := by
  induction s with
  | nil => simp [tensorSourceLabels,upWord]
  | cons i s ih =>
    change ∀ a ∈ (⟨up i,SKM.wt D (ΛP - ΛR) (upWord s)⟩ ::
      wd D (ΛP - ΛR) (upWord s)), a.l.1 = true
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rfl
    · exact ih a ha

/-- Formal source content before applying the root-lattice map. -/
def tensorSourceContent (s : List I) : I →₀ ℕ :=
  SPath.wordContent (tensorSourceLabels D ΛP ΛR s) + 0

/-- The specified all-reservoir source path, without choosing a representative of its content. -/
def tensorSourcePath (s : List I) :
    SPath (tensorSourceLabels D ΛP ΛR s) (0,tensorSourceContent D ΛP ΛR s) (0,0) :=
  SPath.reservoirPath _ (tensorSourceLabels_up D ΛP ΛR s) 0

/-- The whole supported source-word functor on the specified tensor vacuum. -/
def tensorSourceObject (s : List I) : H D Sc' m cutoff N ΛP ΛR (0,tensorSourceContent D ΛP ΛR s) :=
  (pathFunctor D Sc' m cutoff N ΛP ΛR (tensorSourcePath D ΛP ΛR s)).obj
    (tensorVacuum D Sc m cutoff L ΛP ΛR)

/-- The fixed-source row retains its literal word functor, even when other words have the same content. -/
def tensorSourceFamily (s : List I) (t : Sector I) : H D Sc' m cutoff N ΛP ΛR t := by
  classical
  exact if h : t = (0,tensorSourceContent D ΛP ΛR s) then by
    subst t
    exact tensorSourceObject D Sc m cutoff ΛP ΛR L s
  else supportedZero D Sc' m cutoff N ΛP ΛR t

@[simp] theorem tensorSourceFamily_source (s : List I) :
    tensorSourceFamily D Sc m cutoff ΛP ΛR L s (0,tensorSourceContent D ΛP ΛR s) =
      tensorSourceObject D Sc m cutoff ΛP ΛR L s := by
  simp [tensorSourceFamily]

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

/-- The specified vacuum corner has exactly the original external weight ΛP − ΛR. -/
theorem tensorVacuumWeight : (P).wt (0,0) = ΛP - ΛR := by
  simp [ProbeReservoir.wt,ProbeReservoir.muP,ProbeReservoir.muM,elvProbeReservoir,sub_eq_add_neg]

/-- The real supported matrix module for a fixed source word and arbitrary target word. -/
abbrev tensorWordMatrixModule (s t : List I) :=
  matrixModule D Sc m cutoff N ΛP ΛR
    (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)
    (SKM.ob D μ (upWord t))

omit [Fintype I] in
/-- The word matrix's chosen terminal sector has its original external weight. -/
theorem tensorWordVacuumEndpoint (s : List I) :
    (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) =
      (SKM.ob D (ΛP - ΛR) (upWord s)).endR := by
  rw [SKM.ob_endR]
  simp [sub_eq_add_neg]

/-- The cyclic matrix vector is the identity of the specified actual source-word functor. -/
def tensorMatrixVacuum (s : List I) : tensorWordMatrixModule D Sc m cutoff ΛP ΛR L s s := by
  classical
  intro sl sr p
  by_cases hsl : sl = (0,tensorSourceContent D ΛP ΛR s)
  · subst sl
    by_cases hsr : sr.1 = (0,0)
    · rcases sr with ⟨sr,hweight⟩
      dsimp only at hsr
      subst sr
      have hp : p = tensorSourcePath D ΛP ΛR s :=
        (SPath.subsingleton_of_upward_probe_zero (tensorSourceLabels_up D ΛP ΛR s) rfl).elim _ _
      subst p
      rw [tensorSourceFamily_source,tensorTargetFamily_zero]
      exact 𝟙 _
    · exact 0
  · exact 0

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
