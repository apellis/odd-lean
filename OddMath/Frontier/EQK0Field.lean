import OddMath.Frontier.EQK0Gaussian
import OddMath.Frontier.EQFunctorRing
import OddMath.Frontier.EQOnhDGAcyclic

/-!
# The Grothendieck groups of Ellis–Qi §3.6 and §4.4 over a field

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
(printed numbering): §2.2.4 (`K₀` of half-graded complexes is `ℤ[√−1]`), the proof of Theorem 3.18
(`K₀(D(ONH_n)) = 0` for `n ≥ 2`, `K₀(D(ONH_n)) ≅ ℤ[√−1]` for `n ≤ 1`), Lemma 4.16 and the first line
of the proof of Theorem 4.17 (`K₀(D(OΛ_a)) ≅ ℤ[√−1]`).

The dg rings of the library are over `ℤ` and graded by half the Ellis–Qi `q`-degree; the
`ℤ × ℤ/2`-graded (half-graded) dg ring of Ellis–Qi is the diagonal half-graded dg ring
`DG.HalfGradedDGRing.ofDGRing` (degree `k` placed in bidegree `(2k, k mod 2)`), and `K₀` is the compact
super Grothendieck group `DG.HalfGradedDGRing.SuperK0c` (classes up to isomorphisms of either parity,
the convention of Ellis–Qi §2.2.4), a `ℤ[√−1]`-module with `√−1` acting by the internal shift `⟨1⟩`.
Ellis–Qi fix a field `K` in §4.4; here the dg rings are base changed to `K` (`DG.ExtendScalars K`).

* `isConnectedInt_opol`, `isConnectedInt_dgSubring`: `OPol_n` and its dg subrings (`OΛ_n = osymDG n`,
  `OΛ_{a,b} = EQFunctor.osymABDG a b`) are connected over `ℤ`.
* `superK0OsymEquiv K a : K₀(D(OΛ_a)) ≃ₗ[ℤ[√−1]] ℤ[√−1]`, `[OΛ_a] ↦ 1` (`superK0OsymEquiv_self`);
  `superK0OsymABEquiv K a b` for `OΛ_{a,b}`; `superK0OPolEquiv K n` for `OPol_n` (so for `ONH_0 = K`,
  `ONH_1 = K[x]`).
* `lemma_4_16 K a b : K₀(D(OΛ_a)) ⊗_{ℤ[√−1]} K₀(D(OΛ_b)) ≃ₗ[ℤ[√−1]] K₀(D(OΛ_{a,b}))`, sending
  `[OΛ_a] ⊗ [OΛ_b]` to `[OΛ_{a,b}]` (`lemma_4_16_tmul_self`): Lemma 4.16, both sides being free of
  rank one on these classes.
* `superK0c_onh_subsingleton K n`: `K₀(D(ONH_{n+2})) = 0` over `K` (over `ℤ`:
  `EQDiagonal.superK0c_eq_zero`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe w'

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing
open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.EQSkewDifferential (OPol osymDG grading totalDeg)

/-! ### Connectedness over `ℤ` -/

section Connected

variable {n : ℕ}

theorem totalDeg_nonneg (e : Fin n → ℕ) : 0 ≤ totalDeg e :=
  Finset.sum_nonneg fun i _ => Int.natCast_nonneg (e i)

theorem eq_zero_of_totalDeg_eq_zero {e : Fin n → ℕ} (he : totalDeg e = 0) : e = 0 := by
  funext i
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Int.natCast_nonneg (e j))).mp he i
    (Finset.mem_univ i)
  exact_mod_cast h

theorem opol_intCast_coe (m : ℤ) :
    ((OPol.equiv n).symm (m : OPol n) : SkewPolynomial n) = Finsupp.single 0 m := by
  change m • Finsupp.single (0 : Fin n → ℕ) (1 : ℤ) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem opol_eq_zero_of_mem_grading_neg {k : ℤ} (hk : k < 0) {f : OPol n}
    (hf : f ∈ DG.grading (M := OPol n) k) : f = 0 := by
  have hf' : ((OPol.equiv n).symm f : SkewPolynomial n) ∈ grading n k := OPol.mem_grading_iff.mp hf
  have : ((OPol.equiv n).symm f : SkewPolynomial n) = 0 := by
    refine Finsupp.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem fun e he => ?_)
    have := hf' e he
    have := totalDeg_nonneg e
    omega
  exact (OPol.equiv n).symm.injective (this.trans (map_zero _).symm)

theorem opol_exists_intCast_of_mem_grading_zero {f : OPol n} (hf : f ∈ DG.grading (M := OPol n) 0) :
    ∃ m : ℤ, (m : OPol n) = f := by
  have hf' : ((OPol.equiv n).symm f : SkewPolynomial n) ∈ grading n 0 := OPol.mem_grading_iff.mp hf
  refine ⟨((OPol.equiv n).symm f : SkewPolynomial n) 0, ?_⟩
  apply (OPol.equiv n).symm.injective
  refine (opol_intCast_coe _).trans (Finsupp.ext fun e => ?_)
  by_cases he : e = 0
  · subst he; rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_apply, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm he))]
    by_contra h
    exact he (eq_zero_of_totalDeg_eq_zero (hf' e (Finsupp.mem_support_iff.mpr (Ne.symm h)))) |>.elim

theorem opol_intCast_injective {m : ℤ} (h : (m : OPol n) = 0) : m = 0 := by
  have := congrArg (fun F : OPol n => ((OPol.equiv n).symm F : SkewPolynomial n) 0) h
  rw [opol_intCast_coe, Finsupp.single_eq_same] at this
  exact this

/-- `OPol_n` is connected over `ℤ`. -/
theorem isConnectedInt_opol (n : ℕ) : IsConnectedInt (OPol n) where
  grading_neg _ hk := eq_bot_iff.mpr fun _ hf =>
    (AddSubgroup.mem_bot).mpr (opol_eq_zero_of_mem_grading_neg hk hf)
  grading_zero _ hf := opol_exists_intCast_of_mem_grading_zero hf
  intCast_injective _ h := opol_intCast_injective h

/-- Every dg subring of `OPol_n` is connected over `ℤ`; in particular `OΛ_n` and `OΛ_{a,b}`. -/
theorem isConnectedInt_dgSubring (S : DGSubring (OPol n)) : IsConnectedInt S where
  grading_neg _ hk := eq_bot_iff.mpr fun _ hf => (AddSubgroup.mem_bot).mpr
    (Subtype.ext (opol_eq_zero_of_mem_grading_neg hk ((DGSubring.mem_grading_iff _).mp hf)))
  grading_zero _ hf := by
    obtain ⟨m, hm⟩ := opol_exists_intCast_of_mem_grading_zero ((DGSubring.mem_grading_iff _).mp hf)
    exact ⟨m, Subtype.ext (by rw [SubringClass.coe_intCast S m, hm])⟩
  intCast_injective m h := opol_intCast_injective (by
    rw [← SubringClass.coe_intCast S m, h, ZeroMemClass.coe_zero])

end Connected

/-! ### `K₀ ≅ ℤ[√−1]` -/

section Field

variable (K : Type) [Field K]

section Osym

variable (a : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG a))]
  [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymDG a))).Regraded)]

/-- **`K₀(D(OΛ_a)) ≅ ℤ[√−1]`** over a field `K`, as `ℤ[√−1]`-modules (Ellis–Qi, proof of
Theorem 4.17). -/
def superK0OsymEquiv :
    SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (osymDG a))) ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfConnected K (isConnectedInt_dgSubring (osymDG a))

/-- The class of the regular module `OΛ_a` is `1`. -/
theorem superK0OsymEquiv_self :
    superK0OsymEquiv K a (superK0cMk.{w', 0} _ (Diagonal.mapCompactK0.{w', 0, 0}
      (ExtendScalars K (osymDG a)) (DGRing.K0.self (ExtendScalars K (osymDG a))))) = 1 :=
  superK0GaussianOfConnected_self K _

end Osym

section OsymAB

variable (a b : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (EQFunctor.osymABDG a b))]
  [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (EQFunctor.osymABDG a b))).Regraded)]

/-- `K₀(D(OΛ_{a,b})) ≅ ℤ[√−1]` over a field `K`. -/
def superK0OsymABEquiv :
    SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (EQFunctor.osymABDG a b))) ≃ₗ[GaussianInt]
      GaussianInt :=
  superK0GaussianOfConnected K (isConnectedInt_dgSubring (EQFunctor.osymABDG a b))

theorem superK0OsymABEquiv_self :
    superK0OsymABEquiv K a b (superK0cMk.{w', 0} _ (Diagonal.mapCompactK0.{w', 0, 0}
      (ExtendScalars K (EQFunctor.osymABDG a b))
        (DGRing.K0.self (ExtendScalars K (EQFunctor.osymABDG a b))))) = 1 :=
  superK0GaussianOfConnected_self K _

end OsymAB

section Kunneth

variable (a b : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG a))]
  [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymDG a))).Regraded)]
  [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG b))]
  [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymDG b))).Regraded)]
  [HasDerivedCategory.{0, 0} (ExtendScalars K (EQFunctor.osymABDG a b))]
  [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (EQFunctor.osymABDG a b))).Regraded)]

/-- **Lemma 4.16** (Ellis–Qi): `K₀(D(OΛ_a)) ⊗_{ℤ[√−1]} K₀(D(OΛ_b)) ≅ K₀(D(OΛ_{a,b}))` as free
`ℤ[√−1]`-modules (of rank one), with `[OΛ_a] ⊗ [OΛ_b] ↦ [OΛ_{a,b}]`. -/
def lemma_4_16 :
    SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (osymDG a))) ⊗[GaussianInt]
        SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (osymDG b))) ≃ₗ[GaussianInt]
      SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (EQFunctor.osymABDG a b))) :=
  tensorEquivOfGaussian (superK0OsymEquiv K a) (superK0OsymEquiv K b) (superK0OsymABEquiv K a b)

theorem lemma_4_16_tmul_self :
    lemma_4_16 K a b
        (superK0cMk.{w', 0} _ (Diagonal.mapCompactK0.{w', 0, 0} (ExtendScalars K (osymDG a))
            (DGRing.K0.self (ExtendScalars K (osymDG a)))) ⊗ₜ[GaussianInt]
          superK0cMk.{w', 0} _ (Diagonal.mapCompactK0.{w', 0, 0} (ExtendScalars K (osymDG b))
            (DGRing.K0.self (ExtendScalars K (osymDG b))))) =
      superK0cMk.{w', 0} _ (Diagonal.mapCompactK0.{w', 0, 0}
        (ExtendScalars K (EQFunctor.osymABDG a b))
          (DGRing.K0.self (ExtendScalars K (EQFunctor.osymABDG a b)))) :=
  tensorEquivOfGaussian_tmul _ _ _ (superK0OsymEquiv_self K a) (superK0OsymEquiv_self K b)
    (superK0OsymABEquiv_self K a b)

end Kunneth

section OPol

variable (n : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (OPol n))]
  [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (OPol n))).Regraded)]

/-- `K₀(D(OPol_n)) ≅ ℤ[√−1]` over a field `K`; for `n ≤ 1`, `ONH_n = OPol_n` (Ellis–Qi, proof of
Theorem 3.18). -/
def superK0OPolEquiv :
    SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (OPol n))) ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfConnected K (isConnectedInt_opol n)

theorem superK0OPolEquiv_self :
    superK0OPolEquiv K n (superK0cMk.{w', 0} _ (Diagonal.mapCompactK0.{w', 0, 0}
      (ExtendScalars K (OPol n)) (DGRing.K0.self (ExtendScalars K (OPol n))))) = 1 :=
  superK0GaussianOfConnected_self K _

end OPol

section ONH

open OddMath.Frontier.EQOnhDG

variable (n : ℕ)

local notation "𝒦" => DGAlgebra.gradingSubmodule ℤ (DegreeZeroRing K)
local notation "𝒪" => DGAlgebra.gradingSubmodule ℤ (ONH n)

/-- `1 ⊗ ∂₁ ∈ K ⊗ ONH_{n+2}` has degree `-1` and differential `1`. -/
theorem d_one_tmul_del :
    DG.d ((1 : DegreeZeroRing K) ᵍ⊗ₜ[ℤ] ONH.del (n := n) 0 : ExtendScalars K (ONH n)) = 1 := by
  rw [GradedTensorProduct.d_tmul (DG.one_mem_grading (A := DegreeZeroRing K)), DG.d_one,
    GradedTensorProduct.zero_tmul, zero_add, koszulSign_zero, one_smul, ONH.d_del]
  rfl

theorem one_tmul_del_mem :
    ((1 : DegreeZeroRing K) ᵍ⊗ₜ[ℤ] ONH.del (n := n) 0 : ExtendScalars K (ONH n)) ∈
      DG.grading (M := ExtendScalars K (ONH n)) (-1) := by
  have := GradedTensorProduct.tmul_mem_grading (R := ℤ)
    (DG.one_mem_grading (A := DegreeZeroRing K)) (ONH.del_mem_grading (n := n) 0)
  rwa [zero_add] at this

variable [HasDerivedCategory.{0, 0} (ExtendScalars K (ONH n))]

/-- Every object of `D(K ⊗ ONH_{n+2})` is zero. -/
theorem isZero_derivedCategory_extendScalars (X : DG.DerivedCategory.{0, 0} (ExtendScalars K (ONH n))) :
    IsZero X := by
  have hQ : ∀ M : DG.DGModuleCat.{0} (ExtendScalars K (ONH n)), IsZero (DG.DerivedCategory.Q.obj M) :=
    fun M => (DG.DerivedCategory.isZero_Q_obj_iff M).mpr
      (isAcyclic_of_d_eq_one (one_tmul_del_mem K n) (d_one_tmul_del K n) M)
  have := Localization.essSurj (DG.DerivedCategory.Q (A := ExtendScalars K (ONH n)))
    (DG.DGModuleCat.quasiIso (ExtendScalars K (ONH n)))
  exact (hQ _).of_iso (DG.DerivedCategory.Q.objObjPreimageIso X).symm

instance baseK0_onh_subsingleton : Subsingleton (Diagonal.BaseK0.{0, 0} (ExtendScalars K (ONH n))) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ x : Diagonal.BaseK0.{0, 0} (ExtendScalars K (ONH n)), x = 0 := by
    intro x
    induction x using K0.induction_on with
    | zero => rfl
    | mk X =>
      exact K0.mk_eq_zero_of_isZero ((IsZero.iff_id_eq_zero X).mpr (by
        ext
        exact (isZero_derivedCategory_extendScalars K n X.obj).eq_of_src _ _))
    | neg x hx => simp only [hx, neg_zero]
    | add x y hx hy => simp only [hx, hy, add_zero]
  rw [h x, h y]

variable [CatModule.HasDerivedCategory.{w', 0}
    (WeightCategory (ofDGRing (ExtendScalars K (ONH n))).Regraded)]

/-- **`K₀(D(ONH_{n+2})) = 0`** over a field `K` (Ellis–Qi, proof of Theorem 3.18, via
Proposition 3.16 (2)). -/
theorem superK0c_onh_subsingleton :
    Subsingleton (SuperK0c.{w', 0} (ofDGRing (ExtendScalars K (ONH n)))) :=
  superK0c_subsingleton_of_base.{w', 0, 0} (ExtendScalars K (ONH n))

end ONH

end Field

end OddMath.Frontier.EQK0
