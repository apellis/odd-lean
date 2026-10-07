import OddMath.Frontier.EQFunctorRingTensor

/-!
# `OPol_m ⊗ OPol_n ≅ OPol_{m+n}` as dg rings

The odd polynomial dg rings satisfy `OPol_m ⊗ OPol_n ≅ OPol_{m+n}`, `f ⊗ g ↦ f(x) g(y)` (first `m`
variables `x`, last `n` variables `y`), for dg-lean's graded tensor product of dg rings (Koszul sign
rule): `EQFunctor.opolTensorDG m n`, bijective (`opolTensorDG_bijective`). This is the inclusion
`ι_{m,n} : ONH_m ⊗ ONH_n → ONH_{m+n}` of Ellis–Qi, arXiv:1504.01712v2, §3.6, restricted to polynomials;
for `m + n ≤ 1` it is all of `ι_{m,n}` (`ONH_0 = OPol_0`, `ONH_1 = OPol_1`).
-/

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY)
open DG
open scoped TensorProduct

noncomputable section

local instance (priority := high) opolTensorNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))
local instance (priority := high) opolTensorNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {a b : ℕ}

theorem opolToX_apply (f : OPol a) :
    opolToX a b f = OPol.equiv (a+b) (inclX a b ((OPol.equiv a).symm f)) := rfl

theorem opolToY_apply (g : OPol b) :
    opolToY a b g = OPol.equiv (a+b) (inclY a b ((OPol.equiv b).symm g)) := rfl

theorem opolToX_mem_grading {k : ℤ} {f : OPol a} (hf : f ∈ DG.grading (M := OPol a) k) :
    opolToX a b f ∈ DG.grading (M := OPol (a+b)) k :=
  OPol.equiv_mem_grading_iff.mpr (inclX_mem_grading (OPol.equiv_mem_grading_iff.mp hf))

theorem opolToY_mem_grading {k : ℤ} {g : OPol b} (hg : g ∈ DG.grading (M := OPol b) k) :
    opolToY a b g ∈ DG.grading (M := OPol (a+b)) k :=
  OPol.equiv_mem_grading_iff.mpr (inclY_mem_grading (OPol.equiv_mem_grading_iff.mp hg))

theorem opolToX_mul_opolToY {i j : ℤ} (f : DGAlgebra.gradingSubmodule ℤ (OPol a) i)
    (g : DGAlgebra.gradingSubmodule ℤ (OPol b) j) :
    (opolToX a b).toIntAlgHom (f : OPol a) * (opolToY a b).toIntAlgHom (g : OPol b) =
      (-1 : ℤˣ) ^ (j * i) •
        ((opolToY a b).toIntAlgHom (g : OPol b) * (opolToX a b).toIntAlgHom (f : OPol a)) := by
  have hf : ((OPol.equiv a).symm (f : OPol a) : SkewPolynomial a) ∈ grading a i :=
    OPol.equiv_mem_grading_iff.mp f.2
  have hg : ((OPol.equiv b).symm (g : OPol b) : SkewPolynomial b) ∈ grading b j :=
    OPol.equiv_mem_grading_iff.mp g.2
  change opolToX a b f * opolToY a b g = koszulSign (j * i) • (opolToY a b g * opolToX a b f)
  rw [opolToX_apply, opolToY_apply, ← map_mul, ← map_mul, inclY_mul_inclX_of_mem hf hg, map_zsmul,
    Units.smul_def, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

variable (a b) in
/-- `OPol_a ⊗ OPol_b → OPol_{a+b}`, `f ⊗ g ↦ f(x) g(y)`. -/
def opolTensorAlgHom :
    (DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)) →ₐ[ℤ]
      OPol (a+b) :=
  GradedTensorProduct.lift _ _ (opolToX a b).toIntAlgHom (opolToY a b).toIntAlgHom
    fun _ _ f g => opolToX_mul_opolToY f g

theorem opolTensorAlgHom_tmul (f : OPol a) (g : OPol b) :
    opolTensorAlgHom a b (f ᵍ⊗ₜ[ℤ] g) = opolToX a b f * opolToY a b g :=
  GradedTensorProduct.lift_tmul _ _ _ _ _ f g

theorem opolTensorAlgHom_mem_grading {n : ℤ}
    {x : DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)}
    (hx : x ∈ DG.grading n) : opolTensorAlgHom a b x ∈ DG.grading (M := OPol (a+b)) n := by
  refine GradedTensorProduct.grading_induction _ _ hx
    (motive := fun x => opolTensorAlgHom a b x ∈ DG.grading (M := OPol (a+b)) n)
    (by rw [map_zero]; exact zero_mem _) ?_ ?_
  · rintro i j f g rfl
    rw [opolTensorAlgHom_tmul]
    exact DG.mul_mem_grading (opolToX_mem_grading f.2) (opolToY_mem_grading g.2)
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

theorem opolToX_d (f : OPol a) : opolToX a b (DG.d f) = DG.d (opolToX a b f) := by
  rw [opolToX_apply, opolToX_apply, OPol.d_equiv, OPol.symm_d, EQZab.d_inclX]

theorem opolToY_d (g : OPol b) : opolToY a b (DG.d g) = DG.d (opolToY a b g) := by
  rw [opolToY_apply, opolToY_apply, OPol.d_equiv, OPol.symm_d, EQZab.d_inclY]

theorem opolTensorAlgHom_d
    (x : DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)) :
    opolTensorAlgHom a b (DG.d x) = DG.d (opolTensorAlgHom a b x) := by
  induction x using GradedTensorProduct.induction_on_tmul with
  | zero => rw [d_zero, map_zero, d_zero]
  | @tmul i j f hf g hg =>
    rw [GradedTensorProduct.d_tmul hf, map_add, Units.smul_def, map_zsmul, opolTensorAlgHom_tmul,
      opolTensorAlgHom_tmul, opolToX_d, opolToY_d, opolTensorAlgHom_tmul,
      DG.d_mul (opolToX_mem_grading hf), Units.smul_def]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

variable (a b) in
/-- **`ι : OPol_a ⊗ OPol_b → OPol_{a+b}`** as a morphism of dg rings. -/
def opolTensorDG :
    (DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)) →ᵈᵍ+*
      OPol (a+b) where
  __ := (opolTensorAlgHom a b).toRingHom
  map_mem' hx := opolTensorAlgHom_mem_grading hx
  map_d' x := opolTensorAlgHom_d x

theorem opolTensorDG_apply
    (x : DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)) :
    opolTensorDG a b x = opolTensorAlgHom a b x := rfl

theorem opolTensorDG_injective : Function.Injective (opolTensorDG a b) := by
  intro x y h
  have key : ∀ z, opolTensorDG a b z =
      opolMul a b ((GradedTensorProduct.of ℤ (DGAlgebra.gradingSubmodule ℤ (OPol a))
        (DGAlgebra.gradingSubmodule ℤ (OPol b))).symm z) := by
    intro z
    induction z using GradedTensorProduct.induction_on_tmul with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul _ _ =>
      rw [opolTensorDG_apply, opolTensorAlgHom_tmul]
      rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  rw [key, key] at h
  exact (GradedTensorProduct.of ℤ _ _).symm.injective (opolMul_injective h)

theorem opolTensorDG_surjective : Function.Surjective (opolTensorDG a b) := by
  intro F
  obtain ⟨G, rfl⟩ := (OPol.equiv (a+b)).surjective F
  induction G using induction_generator with
  | hgen j =>
    rw [EQZab.generator_eq_append]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine ⟨OPol.equiv a (generator i) ᵍ⊗ₜ[ℤ] (1 : OPol b), ?_⟩
      rw [Fin.append_left, opolTensorDG_apply, opolTensorAlgHom_tmul, map_one, mul_one, opolToX_apply,
        RingEquiv.symm_apply_apply]
    · refine ⟨(1 : OPol a) ᵍ⊗ₜ[ℤ] OPol.equiv b (generator i), ?_⟩
      rw [Fin.append_right, opolTensorDG_apply, opolTensorAlgHom_tmul, map_one, one_mul, opolToY_apply,
        RingEquiv.symm_apply_apply]
  | h0 => exact ⟨0, by rw [map_zero, map_zero]⟩
  | h1 => exact ⟨1, by rw [map_one, map_one]⟩
  | hadd f g hf hg =>
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    exact ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
  | hneg f hf =>
    obtain ⟨x, hx⟩ := hf
    exact ⟨-x, by rw [map_neg, hx, map_neg]⟩
  | hmul f g hf hg =>
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    exact ⟨x * y, by rw [map_mul, hx, hy, map_mul]⟩

theorem opolTensorDG_bijective : Function.Bijective (opolTensorDG a b) :=
  ⟨opolTensorDG_injective, opolTensorDG_surjective⟩

variable (a b) in
/-- **`OPol_a ⊗ OPol_b ≅ OPol_{a+b}`** as dg rings. -/
def opolTensorEquiv :
    (DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)) ≃ᵈᵍₐ[ℤ]
      OPol (a+b) :=
  DGAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (opolTensorDG a b).toRingHom
      opolTensorDG_bijective) fun m => by
        rw [eq_intCast (algebraMap ℤ (DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ]
          DGAlgebra.gradingSubmodule ℤ (OPol b))), eq_intCast (algebraMap ℤ (OPol (a+b))),
          map_intCast])
    (fun hx => (opolTensorDG a b).map_mem hx) (fun x => (opolTensorDG a b).map_d x)

theorem opolTensorEquiv_apply
    (x : DGAlgebra.gradingSubmodule ℤ (OPol a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol b)) :
    opolTensorEquiv a b x = opolTensorDG a b x := rfl

end

end OddMath.Frontier.EQFunctor
