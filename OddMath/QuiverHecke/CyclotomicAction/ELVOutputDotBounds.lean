import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDotBounds
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBendEvaluation
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ProductCoefficients

/-! # Dot bounds before input evaluation

`SwappedHomInversion.md` §3 (3)–(6): the fixed-content source bound
annihilates the dot uniformly in the input module. Parity shifts,
precomposition and reservoir restriction preserve the same exponent.
No exponent uniform over a weight fibre is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction SwappedAssembly
universe u
local instance outputBoundHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

section Shift
variable (Λ x : X) (A : PiSCat.{u,u,u+1} k)
local notation "Wgt" => elvWeightSpace D Sc cutoff bound Λ x

/-- A parity shift preserves a specified exponent at the same output. -/
theorem homParityShift_component_pow_zero (p : ZMod 2) (F : A ⟶ Wgt)
    (f : End F) (M : A) (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : End.of (f.total M δ) ^ n = 0) :
    End.of (((SKM.homParityShift (k := k) (C := A ⟶ Wgt) p).map f).total M δ) ^ n = 0 := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · let Q : ((A ⟶ Wgt) ⥤ (A ⟶ Wgt)) → Prop :=
      fun G => End.of ((G.map f).total M δ) ^ n = 0
    exact (congrArg Q (SKM.homParityShift_zero (k := k) (C := A ⟶ Wgt))).mpr hf
  · rw [SKM.homParityShift_one]
    let _ := elvWeightPi D Sc cutoff bound Λ x
    change End.of
      (((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 0 M)) δ +
       ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 1 M)) δ) ^ n = 0
    rw [productPi_map_end_component, productPi_map_end_component]
    let ψ := productPiEndEvaluation (k := k)
      (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) (F.obj M) δ
    have h : ψ (End.of (f.total M δ)) ^ n = 0 := by
      rw [← map_pow, hf, map_zero]
    change ψ (End.of (f.app 0 M δ) + End.of (f.app 1 M δ)) ^ n = 0 at h
    exact (ψ.map_add (End.of (f.app 0 M δ)) (End.of (f.app 1 M δ))) ▸ h

/-- Probe precomposition preserves the exponent and changes only its input. -/
theorem shiftedPrecomposition_component_pow_zero
    (A' : PiSCat.{u,u,u+1} k) (K : A' ⟶ A) (p : ZMod 2)
    (F : A ⟶ Wgt) (f : End F) (M : A') (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : End.of (f.total (K.obj M) δ) ^ n = 0) :
    End.of (((SKM.homPre (k := k) K ⋙ SKM.homParityShift (k := k) p).map f).total M δ) ^ n = 0 := by
  exact homParityShift_component_pow_zero D Sc cutoff bound Λ x A' p
    ((SKM.homPre (k := k) K).obj F) ((SKM.homPre (k := k) K).map f) M δ n hf

/-- A bound uniform in the input annihilates the whole projected map. -/
theorem outputEnd_pow_zero (F : A ⟶ Wgt) (f : End F)
    (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : ∀ M : A, End.of (f.total M δ) ^ n = 0) :
    ((RegularReservoir.evalHomFunctor (k := k)
      (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) A δ).mapEnd F f) ^ n = 0 := by
  apply supernatural_hom_ext_total (k := k) (C := A)
    (B := ContentModules D Sc cutoff bound δ.1)
  intro M
  let L := RegularReservoir.evalHomFunctor (k := k)
    (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) A δ
  change (supernaturalEndEvaluation (k := k) (L.obj F) M) ((L.mapEnd F f) ^ n) =
    (supernaturalEndEvaluation (k := k) (L.obj F) M) 0
  rw [map_pow, map_zero]
  exact hf M
end Shift

section Restriction
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y) (A : PiSCat.{u,u,u+1} k)
  (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ y) (f : End F)

/-- Restriction reads the successor block and preserves its fixed exponent. -/
theorem shiftedPostRestriction_component_pow_zero (p : ZMod 2)
    (M : A) (δ : WeightBlocks D Λ x) (n : ℕ)
    (hf : End.of (f.total M (blockSucc D Λ i h δ)) ^ n = 0) :
    End.of (((SKM.homParityShift (k := k) p ⋙ SKM.homPost (k := k)
      (elvF D Sc cutoff bound i Λ h)).map f).total M δ) ^ n = 0 := by
  let g := (SKM.homParityShift (k := k) p).map f
  let R := (elvBlockRes D Sc cutoff bound i Λ h δ).toFunctor
  let V := ((SKM.homParityShift (k := k) p).obj F).obj M (blockSucc D Λ i h δ)
  have hg := homParityShift_component_pow_zero D Sc cutoff bound Λ y A p F f M
    (blockSucc D Λ i h δ) n hf
  have hmap : (R.mapEnd V) (End.of (g.total M (blockSucc D Λ i h δ))) ^ n = 0 := by
    rw [← map_pow, hg, Functor.mapEnd_apply, R.map_zero]
  change End.of (((SKM.homPost (k := k) (elvF D Sc cutoff bound i Λ h)).map g).total M δ) ^ n = 0
  rw [homPost_elvF_total]
  exact hmap
end Restriction

section PostDot
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A : PiSCat.{u,u,u+1} k} (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)

/-- The actual postdot has one exponent for every input at a fixed output. -/
theorem elvPostEndEvaluation_dot_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (δ : WeightBlocks D Λ y) :
    ∃ n : ℕ, 0 < n ∧ ∀ M : A,
      elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ
        (elvPostDot D Sc cutoff bound i Λ h F) ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := elvWeightDotComponent_pow_zero D Sc cutoff bound i Λ h hdot δ
  refine ⟨n, hn, fun M => ?_⟩
  rw [elvPostEndEvaluation_of_mem D Sc cutoff bound i Λ h F M δ _
    (elvPostDot_mem D Sc cutoff bound i Λ h F)]
  exact hp (F.obj M)

/-- The same module-uniform exponent survives the chosen content shift. -/
theorem elvShiftedPostEndEvaluation_dot_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (κ : ZMod 2)
    (δ : WeightBlocks D Λ y) :
    ∃ n : ℕ, 0 < n ∧ ∀ M : A,
      elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F κ M δ
        (elvShiftedPostDot D Sc cutoff bound i Λ h F κ) ^ n = 0 := by
  obtain ⟨n, hn, hp⟩ := elvPostEndEvaluation_dot_pow_zero D Sc cutoff bound i Λ h F hdot δ
  refine ⟨n, hn, fun M => ?_⟩
  exact homParityShift_component_pow_zero D Sc cutoff bound Λ y A κ
    (elvPostInduction D Sc cutoff bound i Λ h F) (elvPostDot D Sc cutoff bound i Λ h F) M δ n (hp M)
end PostDot
end OddMath.QuiverHecke.ELVOld
