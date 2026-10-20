/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.Ordinary
import OddMath.CoveringQuantum.UDot.FormUniqueness
import OddMath.CoveringQuantum.UDot.TriangularTensor
import OddMath.CoveringQuantum.UDot.Nondegeneracy
import LieLean.Algebra.QuantumGroup.Modified.BaseChange
import LieLean.Algebra.QuantumGroup.Modified.FormPlus
import LieLean.Algebra.QuantumGroup.Modified.TriangularBasis
import LieLean.Algebra.QuantumGroup.TriangularDecomposition
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.ModifiedCanonicalForm
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# At `π = 1` the modified covering algebra is Lusztig's `U̇`

This file proves the nondegeneracy assertion of Brundan–Ellis, arXiv:1701.04133v2 ([BE2]),
Theorem 10.1, for root data of the form `C.rootDatumOf R`, from Lusztig's form on `U̇`. At
`π = 1` the `ρ`-adjoint form on the modified covering algebra is the pullback of Lusztig's form on
`U̇` ([Lus] 26.1.2), so its nondegeneracy follows from that of Lusztig's form ([Lus] 26.3.1,
LieLean's `QuantumGroup.Modified.eq_zero_of_forall_form_eq_zero` over `ℚ(v)`).

Let `k` be a field, `q ∈ kˣ` with `v = q⁻¹` not a root of unity, `C` a super Cartan datum and
`R` a LieLean root datum (coweight lattice `Y`) for the Cartan datum `C.lusztigDatum`. The
odd-lean root datum `C.rootDatumOf R` has weight lattice `X = Hom(Y, ℤ)`, `αⱼ = R.root j` and
`⟨hᵢ, λ⟩ = λ(R.coroot i)`. We construct a multiplicative linear map
`toLusztig : modified (C.rootDatumOf R) q 1 → U̇` to Lusztig's modified quantum group at `v`,
with `1_λ ↦ 1_λ`, `eᵢ1_λ ↦ Eᵢ1_λ`, `fᵢ1_λ ↦ Fᵢ1_λ`, by checking the defining relations in
the unitization of `U̇` (`lusztigHom`). It is bijective: surjectivity because the image is
stable under the left action of `U`; injectivity because, on each right column `U̇ 1_μ`, it
composes with Lusztig's map `Φ_μ : U̇ → U⁻ ⊗ U⁺` ([Lus] 23.2.1) to the tensor square of the
embeddings of the Serre half algebra into `U^∓` (whose kernels are the Serre ideal, by
LieLean's `plusHom_eq_zero_iff`, `minusHom_eq_zero_iff`).

Over `L = \overline{ℚ(q)}` the parameters `q` and `t q` (`t² = -1`) have inverses that are not
roots of unity; in fact they are transcendental over `ℚ`, so LieLean's base change
`QuantumGroup.Modified.form_nondegenerate_of_transcendental` (along `ℚ(v) → L`, `v ↦ q'⁻¹`)
transfers [Lus] 26.3.1 to Lusztig's form at both parameters. Lusztig's theorem needs dominant
weights that are arbitrarily large on all simple coroots; these exist when `Y` is free of finite
rank and the simple coroots are linearly independent
(`exists_dominant_ge_of_linearIndependent_coroot`). Then
`UDot.positiveModifiedForm_leftRadical_trivial_algebraicClosure` and
`UDot.sesquilinearForm_leftRadical_trivial` give the nondegeneracy assertion of [BE2]
Theorem 10.1. The root datum is presented as `C.rootDatumOf R`
(`X = Hom(Y, ℤ)`). The bar-consistency hypothesis `hD`, used by the twistor
reduction, is the additional nondegeneracy assumption (10.2) in [BE2].

## Main definitions

* `SuperCartanDatum.rootDatumOf`: the odd-lean root datum of a LieLean root datum.
* `UDot.lusztigHom`: `U̇_{q,1}` (unital envelope) to the unitization of Lusztig's `U̇` at `q⁻¹`.
* `UDot.toLusztig`: the induced linear map on the modified algebra.

## Main results

* `UDot.toLusztig_mul`, `UDot.toLusztig_injective`, `UDot.toLusztig_surjective`.
* `UDot.form_toLusztig_rho`: the pulled back form is left `ρ`-adjoint.
* `UDot.form_toLusztig_positiveWord`: its values on positive words.
* `exists_dominant_ge_of_linearIndependent_coroot`: dominant weights large on all simple coroots.
* `UDot.positiveFormNondegenerate_of_lusztig`: `UDot.PositiveFormNondegenerate` at `π = 1`,
  from the nondegeneracy of Lusztig's form on `U̇` at a general parameter (hypothesis `hLus`).
* `UDot.positiveFormNondegenerate_of_ratFunc`: the same for any `q'` with `q'⁻¹` transcendental
  over `ℚ`, from the nondegeneracy of Lusztig's form over `ℚ(v)` (hypothesis `hQ`).
* `UDot.positiveModifiedForm_nondegenerate`, `UDot.sesquilinearForm_nondegenerate`: [BE2]
  Theorem 10.1 (nondegeneracy) for root data `C.rootDatumOf R`.
-/

noncomputable section

open LieLean
open LieLean.QuantumGroup (qSerre qSerre_inv map_qSerre qBinomial qSerreDiv_eq)

namespace OddMath.CoveringQuantum

namespace SuperCartanDatum

variable {I Y : Type*} [AddCommGroup Y] (C : SuperCartanDatum I) (R : C.lusztigDatum.RootDatum Y)

/-- The odd-lean root datum of a LieLean root datum for `C.lusztigDatum`: weights
`X = Hom(Y, ℤ)`, simple roots `αⱼ = R.root j`, and `⟨hᵢ, λ⟩ = λ(R.coroot i)`. -/
abbrev rootDatumOf : RootDatum I (Y →+ ℤ) where
  toSuperCartanDatum := C
  cd :=
    { root := R.root
      coroot := fun i ↦
        { toFun := fun μ ↦ μ (R.coroot i)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ by simp }
      coroot_root_self := fun i ↦ by
        change R.root i (R.coroot i) = 2
        rw [R.root_coroot, LusztigCartanDatum.cartanMatrix_self] }
  coroot_root i j := by
    change R.root j (R.coroot i) = C.a i j
    rw [R.root_coroot, lusztigDatum_cartanMatrix]

@[simp] theorem rootDatumOf_α (j : I) : (C.rootDatumOf R).α j = R.root j := rfl

@[simp] theorem rootDatumOf_d (i : I) : (C.rootDatumOf R).d i = C.d i := rfl

@[simp] theorem rootDatumOf_h (i : I) (μ : Y →+ ℤ) : (C.rootDatumOf R).h i μ = μ (R.coroot i) :=
  rfl

end SuperCartanDatum

/-! ### Dominant weights that are large on the simple coroots -/

section DominantWeights

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I}

/-- If the coweight lattice `Y` is free of finite rank and the simple coroots are linearly
independent, then for every `N` there is a dominant weight `Λ ∈ Hom(Y, ℤ)` with
`⟨hᵢ, Λ⟩ ≥ N` for all `i`. Proof: the coroots stay linearly independent in `Y ⊗ ℚ`, so some
`ℚ`-linear functional takes the value `1` on each of them; clearing denominators on a `ℤ`-basis of
`Y` gives an integral functional `f` with `f(hᵢ) = d > 0`, and `Λ = N f` works. -/
theorem exists_dominant_ge_of_linearIndependent_coroot [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (R : D.RootDatum Y) (hc : LinearIndependent ℤ R.coroot) (N : ℕ) :
    ∃ Λ : QuantumGroup.GrandLoop.Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i) := by
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let φ : Y →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Y → ℚ) :=
    LinearMap.pi fun j ↦ (Int.castAddHom ℚ).toIntLinearMap ∘ₗ b.coord j
  have hφ : Function.Injective φ := by
    intro y y' h
    apply b.repr.injective
    ext j
    simpa [φ] using congrFun h j
  have hφb : ∀ j, φ (b j) = Pi.single j 1 := by
    intro j
    funext j'
    by_cases h : j' = j
    · subst h
      simp [φ]
    · simp [φ, h]
  have hvQ : LinearIndependent ℚ (φ ∘ R.coroot) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 (hc.map' φ (LinearMap.ker_eq_bot.2 hφ))
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℚ (fun _ : I ↦ (1 : ℚ))) ∘ₗ hvQ.repr)
  have hgv : ∀ i, g (φ (R.coroot i)) = 1 := by
    intro i
    have h := LinearMap.congr_fun hg ⟨φ (R.coroot i), Submodule.subset_span ⟨i, rfl⟩⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, LinearMap.comp_apply, hvQ.repr_eq_single i _ rfl, Finsupp.linearCombination_single,
      smul_eq_mul, mul_one]
  -- a common denominator of the values of `g` on the coordinate vectors
  let e : Module.Free.ChooseBasisIndex ℤ Y → ℚ := fun j ↦ g (Pi.single j 1)
  let d : ℕ := ∏ j, (e j).den
  have hd : 0 < d := Finset.prod_pos fun j _ ↦ (e j).den_pos
  have hm : ∀ j, ∃ m : ℤ, (m : ℚ) = d * e j := by
    intro j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j ↦ (e j).den) (Finset.mem_univ j)
    refine ⟨c * (e j).num, ?_⟩
    change (((c : ℤ) * (e j).num : ℤ) : ℚ) = ((∏ j, (e j).den : ℕ) : ℚ) * e j
    rw [hc]
    push_cast
    rw [mul_comm ((e j).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose m hm using hm
  let f : Y →ₗ[ℤ] ℤ := b.constr ℤ m
  have hf : ∀ y, (f y : ℚ) = d * g (φ y) := by
    have h : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ f = (d : ℚ) • ((g.restrictScalars ℤ) ∘ₗ φ) :=
      b.ext fun j ↦ by simp [f, hφb, hm, e]
    exact fun y ↦ LinearMap.congr_fun h y
  have hfc : ∀ i, f (R.coroot i) = d := by
    intro i
    have h := hf (R.coroot i)
    rw [hgv, mul_one] at h
    exact_mod_cast h
  refine ⟨⟨N • f.toAddMonoidHom, fun i ↦ ?_⟩, fun i ↦ ?_⟩
  · simp only [AddMonoidHom.nsmul_apply, LinearMap.toAddMonoidHom_coe, hfc, nsmul_eq_mul]
    positivity
  · simp only [AddMonoidHom.nsmul_apply, LinearMap.toAddMonoidHom_coe, hfc, nsmul_eq_mul]
    exact_mod_cast Nat.le_mul_of_pos_right N hd

end DominantWeights

namespace UDot

/-! ### Lusztig's `U̇`: the elements `u 1_λ` -/

section LusztigSide

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {Dl : LusztigCartanDatum I}
  (R : Dl.RootDatum Y) {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- `u ↦ u 1_λ`, the left action of `U` on `1_λ ∈ U̇`. -/
def leftActOne (μ : Y →+ ℤ) : QuantumGroup R v →ₗ[k] QuantumGroup.Modified R v :=
  (QuantumGroup.Modified.leftAct R v hv).flip (QuantumGroup.Modified.one μ)

variable {R}

theorem leftActOne_apply (μ : Y →+ ℤ) (u : QuantumGroup R v) :
    leftActOne R hv μ u = QuantumGroup.Modified.leftAct R v hv u (QuantumGroup.Modified.one μ) :=
  rfl

theorem leftActOne_one (μ : Y →+ ℤ) :
    leftActOne R hv μ 1 = QuantumGroup.Modified.one μ :=
  QuantumGroup.Modified.leftAct_one hv _

theorem leftActOne_eq_elt {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ QuantumGroup.adWeightSpace R v χ) (μ : Y →+ ℤ) :
    leftActOne R hv μ u = QuantumGroup.Modified.elt (μ + χ) μ u (by simpa using hu) :=
  QuantumGroup.Modified.leftAct_one_eq_elt hv _

omit [NeZero v] in
theorem F_mem_adWeightSpace (i : I) :
    QuantumGroup.F R v i ∈ QuantumGroup.adWeightSpace R v (-R.root i) :=
  fun μ ↦ by simpa using QuantumGroup.K_mul_F R v μ i

theorem pow_mem_adWeightSpace {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ QuantumGroup.adWeightSpace R v χ) (n : ℕ) :
    u ^ n ∈ QuantumGroup.adWeightSpace R v (n • χ) := by
  induction n with
  | zero => simpa using QuantumGroup.one_mem_adWeightSpace
  | succ n ih =>
    rw [pow_succ', succ_nsmul']
    exact QuantumGroup.mul_mem_adWeightSpace hu ih

/-- `plusHom_monomial_mem_adWeightSpace`, stated for the monomials of `'f`. -/
theorem plusHom_preMonomial_mem (w : List I) :
    QuantumGroup.plusHom R v (PreF.monomial k w) ∈
      QuantumGroup.adWeightSpace R v (QuantumGroup.wordChar R w) :=
  QuantumGroup.plusHom_monomial_mem_adWeightSpace w

/-- `minusHom_monomial_mem_adWeightSpace`, stated for the monomials of `'f`. -/
theorem minusHom_preMonomial_mem (w : List I) :
    QuantumGroup.minusHom R v (PreF.monomial k w) ∈
      QuantumGroup.adWeightSpace R v (-QuantumGroup.wordChar R w) :=
  QuantumGroup.minusHom_monomial_mem_adWeightSpace w

open scoped Classical in
/-- `u 1_μ · u' 1_ν = δ_{μ, ν + χ'} u u' 1_ν` for `u'` of weight `χ'`. -/
theorem leftActOne_mul_leftActOne {χ χ' : Y →+ ℤ} {u u' : QuantumGroup R v}
    (hu : u ∈ QuantumGroup.adWeightSpace R v χ) (hu' : u' ∈ QuantumGroup.adWeightSpace R v χ')
    (μ ν : Y →+ ℤ) :
    leftActOne R hv μ u * leftActOne R hv ν u' =
      if μ = ν + χ' then leftActOne R hv ν (u * u') else 0 := by
  rw [leftActOne_eq_elt hv hu, leftActOne_eq_elt hv hu']
  split_ifs with h
  · subst h
    rw [QuantumGroup.Modified.elt_mul_elt,
      leftActOne_eq_elt hv (QuantumGroup.mul_mem_adWeightSpace hu hu')]
    exact QuantumGroup.Modified.elt_index (by abel) rfl rfl _ _
  · exact QuantumGroup.Modified.elt_mul_elt_of_ne h _ _

open scoped Classical in
theorem one_mul_elt_eq_ite (ν : Y →+ ℤ) {l₁ l₂ : Y →+ ℤ} {t : QuantumGroup R v}
    (ht : t ∈ QuantumGroup.adWeightSpace R v (l₁ - l₂)) :
    QuantumGroup.Modified.one ν * QuantumGroup.Modified.elt l₁ l₂ t ht =
      if ν = l₁ then QuantumGroup.Modified.elt l₁ l₂ t ht else 0 := by
  split_ifs with h
  · subst h
    exact QuantumGroup.Modified.one_mul_elt _ _ _
  · exact QuantumGroup.Modified.elt_mul_elt_of_ne h _ _

/-- `u 1_μ · w = u · (1_μ w)` for homogeneous `u`. -/
theorem leftActOne_mul {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ QuantumGroup.adWeightSpace R v χ) (μ : Y →+ ℤ) (w : QuantumGroup.Modified R v) :
    leftActOne R hv μ u * w =
      QuantumGroup.Modified.leftAct R v hv u (QuantumGroup.Modified.one μ * w) := by
  induction w using QuantumGroup.Modified.induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [mul_add, mul_add, map_add, hx, hy]
  | helt l₁ l₂ t ht =>
    rw [one_mul_elt_eq_ite, leftActOne_eq_elt hv hu]
    split_ifs with h
    · subst h
      rw [QuantumGroup.Modified.elt_mul_elt, QuantumGroup.Modified.leftAct_elt hv hu]
    · rw [QuantumGroup.Modified.elt_mul_elt_of_ne h, map_zero]

theorem leftAct_K_elt (x : Y) {l₁ l₂ : Y →+ ℤ} {t : QuantumGroup R v}
    (ht : t ∈ QuantumGroup.adWeightSpace R v (l₁ - l₂)) :
    QuantumGroup.Modified.leftAct R v hv (QuantumGroup.K R v x)
        (QuantumGroup.Modified.elt l₁ l₂ t ht) =
      v ^ l₁ x • QuantumGroup.Modified.elt l₁ l₂ t ht := by
  have h2 : QuantumGroup.K R v x * t ∈ QuantumGroup.adWeightSpace R v (l₁ - l₂) := by
    simpa using QuantumGroup.mul_mem_adWeightSpace (QuantumGroup.K_mem_adWeightSpace x) ht
  rw [QuantumGroup.Modified.leftAct_elt hv (QuantumGroup.K_mem_adWeightSpace x),
    QuantumGroup.Modified.elt_index (add_zero l₁) rfl rfl _ h2,
    QuantumGroup.Modified.elt_K_mul l₁ l₂ x ht h2]

theorem leftActOne_K (μ : Y →+ ℤ) (x : Y) :
    leftActOne R hv μ (QuantumGroup.K R v x) = v ^ μ x • QuantumGroup.Modified.one μ := by
  rw [leftActOne_apply, QuantumGroup.Modified.one, leftAct_K_elt]

/-- `(1_ν x, y) = (x, 1_ν y)` for Lusztig's form. -/
theorem form_one_mul (ν : Y →+ ℤ) (x y : QuantumGroup.Modified R v) :
    QuantumGroup.Modified.form R v hv (QuantumGroup.Modified.one ν * x) y =
      QuantumGroup.Modified.form R v hv x (QuantumGroup.Modified.one ν * y) := by
  induction x using QuantumGroup.Modified.induction_on with
  | h0 => simp
  | hadd x x' hx hx' => rw [mul_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      hx, hx']
  | helt l₁ l₂ s hs =>
  induction y using QuantumGroup.Modified.induction_on with
  | h0 => simp
  | hadd y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy']
  | helt m₁ m₂ t ht =>
    rw [one_mul_elt_eq_ite, one_mul_elt_eq_ite]
    split_ifs with h1 h2 h2
    · rfl
    · rw [map_zero, QuantumGroup.Modified.form_elt_elt_of_ne hv]
      intro h
      exact h2 (h1.trans (Prod.mk.inj h).1)
    · rw [map_zero, LinearMap.zero_apply, QuantumGroup.Modified.form_elt_elt_of_ne hv]
      intro h
      exact h1 (h2.trans (Prod.mk.inj h).1.symm)
    · simp

/-- `1_ν ρ(Eᵢ) w = vᵢ v^{⟨K̃ᵢ, ν⟩} Fᵢ 1_{ν+αᵢ} w`. -/
theorem one_mul_leftAct_rho_E (i : I) (ν : Y →+ ℤ) (w : QuantumGroup.Modified R v) :
    QuantumGroup.Modified.one ν *
        QuantumGroup.Modified.leftAct R v hv (QuantumGroup.rho R v (QuantumGroup.E R v i)) w =
      (v ^ Dl.d i * v ^ ν (QuantumGroup.ktilde R i)) •
        QuantumGroup.Modified.leftAct R v hv (QuantumGroup.F R v i)
          (QuantumGroup.Modified.one (ν + R.root i) * w) := by
  induction w using QuantumGroup.Modified.induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, mul_add, hx, hy, mul_add, map_add, smul_add]
  | helt m₁ m₂ t ht =>
    rw [QuantumGroup.rho_E, QuantumGroup.rhoE, map_smul, LinearMap.smul_apply,
      QuantumGroup.Modified.leftAct_mul,
      QuantumGroup.Modified.leftAct_elt hv (F_mem_adWeightSpace i),
      leftAct_K_elt, mul_smul_comm, mul_smul_comm, one_mul_elt_eq_ite, one_mul_elt_eq_ite]
    by_cases h : ν = m₁ + -R.root i
    · rw [ite_eq_left h, ite_eq_left (by rw [h]; abel), QuantumGroup.Modified.leftAct_elt hv
        (F_mem_adWeightSpace i), smul_smul, h]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (by rw [← h']; abel)), smul_zero, map_zero,
        smul_zero, smul_zero]

/-- `1_ν ρ(Fᵢ) w = vᵢ v^{-⟨K̃ᵢ, ν⟩} Eᵢ 1_{ν-αᵢ} w`. -/
theorem one_mul_leftAct_rho_F (i : I) (ν : Y →+ ℤ) (w : QuantumGroup.Modified R v) :
    QuantumGroup.Modified.one ν *
        QuantumGroup.Modified.leftAct R v hv (QuantumGroup.rho R v (QuantumGroup.F R v i)) w =
      (v ^ Dl.d i * v ^ ν (-QuantumGroup.ktilde R i)) •
        QuantumGroup.Modified.leftAct R v hv (QuantumGroup.E R v i)
          (QuantumGroup.Modified.one (ν - R.root i) * w) := by
  induction w using QuantumGroup.Modified.induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, mul_add, hx, hy, mul_add, map_add, smul_add]
  | helt m₁ m₂ t ht =>
    rw [QuantumGroup.rho_F, QuantumGroup.rhoF, map_smul, LinearMap.smul_apply,
      QuantumGroup.Modified.leftAct_mul,
      QuantumGroup.Modified.leftAct_elt hv (QuantumGroup.E_mem_adWeightSpace i),
      leftAct_K_elt, mul_smul_comm, mul_smul_comm, one_mul_elt_eq_ite, one_mul_elt_eq_ite]
    by_cases h : ν = m₁ + R.root i
    · rw [ite_eq_left h, ite_eq_left (by rw [h]; abel), QuantumGroup.Modified.leftAct_elt hv
        (QuantumGroup.E_mem_adWeightSpace i), smul_smul, h]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (by rw [← h']; abel)), smul_zero, map_zero,
        smul_zero, smul_zero]

end LusztigSide

/-! ### The comparison map -/

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] [DecidableEq (Y →+ ℤ)]
  {C : SuperCartanDatum I} (R : C.lusztigDatum.RootDatum Y) (q : kˣ)

/-- `q⁻¹ ≠ 0`. -/
instance neZero_inv_units : NeZero ((q : k)⁻¹) := ⟨inv_ne_zero q.ne_zero⟩

variable (hv : ∀ n : ℕ, 0 < n → ((q : k)⁻¹) ^ n ≠ 1)

/-- The generators of `U̇_{q,1}` in the unitization of Lusztig's `U̇` at `q⁻¹`. -/
def lusztigGen : Gen I (Y →+ ℤ) → Unitization k (QuantumGroup.Modified R (q : k)⁻¹)
  | .one μ => (QuantumGroup.Modified.one μ : QuantumGroup.Modified R (q : k)⁻¹)
  | .e i μ => (leftActOne R hv μ (QuantumGroup.E R _ i) : QuantumGroup.Modified R (q : k)⁻¹)
  | .f i μ => (leftActOne R hv μ (QuantumGroup.F R _ i) : QuantumGroup.Modified R (q : k)⁻¹)

/-- The generators on the free algebra. -/
def lusztigFree : Free k I (Y →+ ℤ) →ₐ[k] Unitization k (QuantumGroup.Modified R (q : k)⁻¹) :=
  FreeAlgebra.lift k (lusztigGen R q hv)

omit [DecidableEq (Y →+ ℤ)] in
theorem lusztigFree_one (μ : Y →+ ℤ) :
    lusztigFree R q hv (Free.one k μ) = Unitization.inr (QuantumGroup.Modified.one μ) := by
  simp [lusztigFree, Free.one, lusztigGen]

omit [DecidableEq (Y →+ ℤ)] in
theorem lusztigFree_E (i : I) (μ : Y →+ ℤ) :
    lusztigFree R q hv (Free.E k i μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.E R _ i)) := by
  simp [lusztigFree, Free.E, lusztigGen]

omit [DecidableEq (Y →+ ℤ)] in
theorem lusztigFree_F (i : I) (μ : Y →+ ℤ) :
    lusztigFree R q hv (Free.F k i μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.F R _ i)) := by
  simp [lusztigFree, Free.F, lusztigGen]

omit [DecidableEq (Y →+ ℤ)] in
theorem lusztigFree_one' (μ : Y →+ ℤ) :
    lusztigFree R q hv (Free.one k μ) = Unitization.inr (leftActOne R hv μ 1) := by
  rw [lusztigFree_one, leftActOne_one]

omit [DecidableEq (Y →+ ℤ)] in
theorem lusztigFree_epow (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    lusztigFree R q hv (epow (C.rootDatumOf R) i n μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.E R _ i ^ n)) := by
  induction n with
  | zero => rw [epow, lusztigFree_one', pow_zero]
  | succ n ih =>
    rw [epow, map_mul, lusztigFree_E, ih, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (QuantumGroup.E_mem_adWeightSpace i)
        (pow_mem_adWeightSpace (QuantumGroup.E_mem_adWeightSpace i) n), ite_eq_left rfl, pow_succ']

omit [DecidableEq (Y →+ ℤ)] in
theorem lusztigFree_fpow (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    lusztigFree R q hv (fpow (C.rootDatumOf R) i n μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.F R _ i ^ n)) := by
  induction n with
  | zero => rw [fpow, lusztigFree_one', pow_zero]
  | succ n ih =>
    rw [fpow, map_mul, lusztigFree_F, ih, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (F_mem_adWeightSpace i)
        (pow_mem_adWeightSpace (F_mem_adWeightSpace i) n),
      ite_eq_left (show μ - n • R.root i = μ + n • -R.root i by rw [smul_neg, ← sub_eq_add_neg]),
      pow_succ']

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
variable (C) in
theorem serreCoeff_one (i j : I) (r : ℕ) :
    C.serreCoeff q 1 i j r = (-1) ^ r * qBinomial ((q : k) ^ C.d i) (C.serreDeg i j) r := by
  simp only [SuperCartanDatum.serreCoeff, SuperCartanDatum.pii, one_pow, mul_one,
    qpBinom_one, SuperCartanDatum.qi, Units.val_pow_eq_pow_val]

omit [DecidableEq (Y →+ ℤ)] in
/-- The quantum Serre relation for the `Eᵢ` in the form of the covering algebra at `π = 1`. -/
theorem qSerre_E {i j : I} (h : i ≠ j) :
    qSerre ((q : k) ^ C.d i) (C.serreDeg i j) (QuantumGroup.E R (q : k)⁻¹ i)
      (QuantumGroup.E R (q : k)⁻¹ j) = 0 := by
  have := QuantumGroup.serre_E R ((q : k)⁻¹) h
  rw [SuperCartanDatum.lusztigDatum_d, SuperCartanDatum.lusztigDatum_cartanMatrix, inv_pow,
    qSerre_inv] at this
  exact this

omit [DecidableEq (Y →+ ℤ)] in
/-- The quantum Serre relation for the `Fᵢ` in the form of the covering algebra at `π = 1`. -/
theorem qSerre_F {i j : I} (h : i ≠ j) :
    qSerre ((q : k) ^ C.d i) (C.serreDeg i j) (QuantumGroup.F R (q : k)⁻¹ i)
      (QuantumGroup.F R (q : k)⁻¹ j) = 0 := by
  have := QuantumGroup.serre_F R ((q : k)⁻¹) h
  rw [SuperCartanDatum.lusztigDatum_d, SuperCartanDatum.lusztigDatum_cartanMatrix, inv_pow,
    qSerre_inv] at this
  exact this

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
/-- `(Q - Q⁻¹) [n]_{Q,1} = Q^n - Q^{-n}`. -/
theorem sub_mul_qpInt_one (Q : kˣ) (n : ℤ) :
    ((Q : k) - (Q : k)⁻¹) * qpInt Q 1 n = (Q : k) ^ n - (Q : k) ^ (-n) := by
  have hQ : ((Q⁻¹ : kˣ) : k) = (Q : k)⁻¹ := Units.val_inv_eq_inv_val Q
  have key := fun m : ℕ ↦ qpNat_mul_sub (q := Q) (π := (1 : k)) m
  simp only [one_mul, one_pow, hQ] at key
  rcases n with m | m
  · change ((Q : k) - (Q : k)⁻¹) * qpNat Q 1 m = (Q : k) ^ (m : ℤ) - (Q : k) ^ (-(m : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact key m
  · change ((Q : k) - (Q : k)⁻¹) * (-((1 : k) ^ (m + 1) * qpNat Q 1 (m + 1))) =
      (Q : k) ^ (Int.negSucc m) - (Q : k) ^ (-(Int.negSucc m))
    rw [one_pow, one_mul, mul_neg, key (m + 1), zpow_neg, zpow_negSucc, inv_inv, inv_pow]
    ring

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
/-- `[n]_{qᵢ,1}` is Lusztig's balanced quantum integer at `vᵢ = q⁻ᵈ`. -/
theorem qpInt_one_eq (d : ℕ) (hd : ((q : k)⁻¹) ^ (2 * d) ≠ 1) (n : ℤ) :
    qpInt (q ^ d) 1 n =
      (((q : k)⁻¹) ^ d - (((q : k)⁻¹) ^ d)⁻¹)⁻¹ *
        (((q : k)⁻¹) ^ (d * n) - ((q : k)⁻¹) ^ (-(d * n))) := by
  set Q : kˣ := q ^ d
  have hQ : ((Q : kˣ) : k) = (q : k) ^ d := Units.val_pow_eq_pow_val q d
  have hne : (Q : k) - (Q : k)⁻¹ ≠ 0 := by
    intro h0
    apply hd
    have hQ0 : (Q : k) ≠ 0 := Q.ne_zero
    have : (Q : k) ^ 2 = 1 := by
      field_simp at h0
      linear_combination h0
    rw [pow_mul', inv_pow, ← hQ, inv_pow, this, inv_one]
  have h1 := sub_mul_qpInt_one Q n
  have e1 : ((q : k)⁻¹) ^ d = (Q : k)⁻¹ := by rw [hQ, inv_pow]
  have e2 : ((q : k)⁻¹) ^ ((d : ℤ) * n) = (Q : k) ^ (-n) := by
    rw [hQ, zpow_mul, zpow_natCast, inv_pow, inv_zpow']
  have e3 : ((q : k)⁻¹) ^ (-((d : ℤ) * n)) = (Q : k) ^ n := by
    rw [zpow_neg, e2, zpow_neg, inv_inv]
  have hne' : (Q : k)⁻¹ - Q ≠ 0 := fun h ↦ hne (by linear_combination -h)
  rw [e1, e2, e3, inv_inv, eq_inv_mul_iff_mul_eq₀ hne']
  linear_combination -h1

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
theorem inr_finset_sum {A ι : Type*} [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] (s : Finset ι) (f : ι → A) :
    ((∑ i ∈ s, f i : A) : Unitization k A) = ∑ i ∈ s, (f i : Unitization k A) :=
  map_sum (Unitization.inrNonUnitalAlgHom k A) f s

theorem lusztigFree_rel {x y : Free k I (Y →+ ℤ)} (h : Rel (C.rootDatumOf R) q 1 x y) :
    lusztigFree R q hv x = lusztigFree R q hv y := by
  cases h with
  | one_one μ ν =>
    rw [map_mul, lusztigFree_one, lusztigFree_one, ← Unitization.inr_mul]
    split_ifs with h
    · subst h
      rw [QuantumGroup.Modified.one_mul_one_self, lusztigFree_one]
    · rw [QuantumGroup.Modified.one_mul_one_of_ne h, map_zero, Unitization.inr_zero]
  | one_E i μ =>
    rw [map_mul, lusztigFree_one', lusztigFree_E, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv QuantumGroup.one_mem_adWeightSpace
        (QuantumGroup.E_mem_adWeightSpace i), ite_eq_left rfl, one_mul]
  | E_one i μ =>
    rw [map_mul, lusztigFree_one', lusztigFree_E, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (QuantumGroup.E_mem_adWeightSpace i)
        QuantumGroup.one_mem_adWeightSpace, ite_eq_left (add_zero μ).symm, mul_one]
  | one_F i μ =>
    rw [map_mul, lusztigFree_one', lusztigFree_F, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv QuantumGroup.one_mem_adWeightSpace (F_mem_adWeightSpace i),
      ite_eq_left (sub_eq_add_neg _ _), one_mul]
  | F_one i μ =>
    rw [map_mul, lusztigFree_one', lusztigFree_F, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (F_mem_adWeightSpace i) QuantumGroup.one_mem_adWeightSpace,
      ite_eq_left (add_zero μ).symm, mul_one]
  | comm i j μ =>
    rw [map_sub, map_mul, map_smul, map_mul, lusztigFree_E, lusztigFree_F, lusztigFree_E,
      lusztigFree_F, one_pow, one_smul, ← Unitization.inr_mul, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (QuantumGroup.E_mem_adWeightSpace i) (F_mem_adWeightSpace j),
      leftActOne_mul_leftActOne hv (F_mem_adWeightSpace j) (QuantumGroup.E_mem_adWeightSpace i),
      ite_eq_left (sub_eq_add_neg _ _), ite_eq_left rfl, ← Unitization.inr_sub, ← map_sub,
      QuantumGroup.E_mul_F_sub]
    split_ifs with hij
    · subst hij
      rw [map_smul (leftActOne R hv μ), map_sub, leftActOne_K, leftActOne_K, ← sub_smul,
        smul_smul, map_smul (lusztigFree R q hv), lusztigFree_one, ← Unitization.inr_smul]
      congr 2
      have hd : ((q : k)⁻¹) ^ (2 * C.d i) ≠ 1 :=
        hv _ (Nat.mul_pos (by norm_num) (C.d_pos i))
      have hμ : μ (QuantumGroup.ktilde R i) = (C.d i : ℤ) * μ (R.coroot i) := by
        simp [QuantumGroup.ktilde, SuperCartanDatum.lusztigDatum_d]
      simp only [SuperCartanDatum.pii, one_pow, SuperCartanDatum.qi]
      rw [map_neg, hμ, SuperCartanDatum.lusztigDatum_d]
      exact (qpInt_one_eq q (C.d i) hd _).symm
    · simp
  | serreE i j μ h =>
    rw [map_zero]
    simp only [serreE, map_sum, map_smul, map_mul, lusztigFree_epow, lusztigFree_E]
    have hterm : ∀ r ∈ Finset.range ((C.rootDatumOf R).serreDeg i j + 1),
        (C.rootDatumOf R).serreCoeff q 1 i j r •
          ((leftActOne R hv (μ + r • (C.rootDatumOf R).α i + (C.rootDatumOf R).α j)
              (QuantumGroup.E R _ i ^ ((C.rootDatumOf R).serreDeg i j - r)) :
              Unitization k (QuantumGroup.Modified R (q : k)⁻¹)) *
            Unitization.inr
              (leftActOne R hv (μ + r • (C.rootDatumOf R).α i) (QuantumGroup.E R _ j)) *
            Unitization.inr (leftActOne R hv μ (QuantumGroup.E R _ i ^ r))) =
        Unitization.inr ((leftActOne R hv μ
          (((-1) ^ r * qBinomial ((q : k) ^ C.d i) (C.serreDeg i j) r) •
          (QuantumGroup.E R _ i ^ (C.serreDeg i j - r) * QuantumGroup.E R _ j *
            QuantumGroup.E R _ i ^ r)) :
          QuantumGroup.Modified R (q : k)⁻¹)) := by
      intro r _
      have hEr := pow_mem_adWeightSpace (QuantumGroup.E_mem_adWeightSpace (R := R)
        (v := (q : k)⁻¹) i) r
      have hc : (C.rootDatumOf R).serreCoeff q 1 i j r =
          (-1) ^ r * qBinomial ((q : k) ^ C.d i) (C.serreDeg i j) r := serreCoeff_one C q i j r
      rw [← Unitization.inr_mul, ← Unitization.inr_mul,
        leftActOne_mul_leftActOne hv
          (pow_mem_adWeightSpace (QuantumGroup.E_mem_adWeightSpace i) _)
          (QuantumGroup.E_mem_adWeightSpace j), ite_eq_left rfl,
        leftActOne_mul_leftActOne hv (QuantumGroup.mul_mem_adWeightSpace
          (pow_mem_adWeightSpace (QuantumGroup.E_mem_adWeightSpace i) _)
          (QuantumGroup.E_mem_adWeightSpace j)) hEr, ite_eq_left rfl,
        ← Unitization.inr_smul, ← map_smul, hc]
    refine (Finset.sum_congr rfl hterm).trans ?_
    rw [← inr_finset_sum, ← map_sum]
    change Unitization.inr (leftActOne R hv μ (qSerre ((q : k) ^ C.d i) (C.serreDeg i j)
      (QuantumGroup.E R _ i) (QuantumGroup.E R _ j))) = 0
    rw [qSerre_E R q h, map_zero, Unitization.inr_zero]
  | serreF i j μ h =>
    rw [map_zero]
    simp only [serreF, map_sum, map_smul, map_mul, lusztigFree_fpow, lusztigFree_F]
    have hterm : ∀ r ∈ Finset.range ((C.rootDatumOf R).serreDeg i j + 1),
        (C.rootDatumOf R).serreCoeff q 1 i j r •
          ((leftActOne R hv (μ - r • (C.rootDatumOf R).α i - (C.rootDatumOf R).α j)
              (QuantumGroup.F R _ i ^ ((C.rootDatumOf R).serreDeg i j - r)) :
              Unitization k (QuantumGroup.Modified R (q : k)⁻¹)) *
            Unitization.inr
              (leftActOne R hv (μ - r • (C.rootDatumOf R).α i) (QuantumGroup.F R _ j)) *
            Unitization.inr (leftActOne R hv μ (QuantumGroup.F R _ i ^ r))) =
        Unitization.inr ((leftActOne R hv μ
          (((-1) ^ r * qBinomial ((q : k) ^ C.d i) (C.serreDeg i j) r) •
          (QuantumGroup.F R _ i ^ (C.serreDeg i j - r) * QuantumGroup.F R _ j *
            QuantumGroup.F R _ i ^ r)) :
          QuantumGroup.Modified R (q : k)⁻¹)) := by
      intro r _
      have hFr := pow_mem_adWeightSpace (F_mem_adWeightSpace (R := R)
        (v := (q : k)⁻¹) i) r
      have hc : (C.rootDatumOf R).serreCoeff q 1 i j r =
          (-1) ^ r * qBinomial ((q : k) ^ C.d i) (C.serreDeg i j) r := serreCoeff_one C q i j r
      rw [← Unitization.inr_mul, ← Unitization.inr_mul,
        leftActOne_mul_leftActOne hv
          (pow_mem_adWeightSpace (F_mem_adWeightSpace i) _) (F_mem_adWeightSpace j),
        ite_eq_left (sub_eq_add_neg _ _),
        leftActOne_mul_leftActOne hv (QuantumGroup.mul_mem_adWeightSpace
          (pow_mem_adWeightSpace (F_mem_adWeightSpace i) _) (F_mem_adWeightSpace j)) hFr,
        ite_eq_left (show μ - r • R.root i = μ + r • -R.root i by rw [smul_neg, sub_eq_add_neg]),
        ← Unitization.inr_smul, ← map_smul, hc]
    refine (Finset.sum_congr rfl hterm).trans ?_
    rw [← inr_finset_sum, ← map_sum]
    change Unitization.inr (leftActOne R hv μ (qSerre ((q : k) ^ C.d i) (C.serreDeg i j)
      (QuantumGroup.F R _ i) (QuantumGroup.F R _ j))) = 0
    rw [qSerre_F R q h, map_zero, Unitization.inr_zero]

/-- `U̇_{q,1}` (unital envelope) to the unitization of Lusztig's `U̇` at `q⁻¹`:
`1_λ ↦ 1_λ`, `eᵢ1_λ ↦ Eᵢ1_λ`, `fᵢ1_λ ↦ Fᵢ1_λ`. -/
def lusztigHom :
    CoveringUDot k (C.rootDatumOf R) q 1 →ₐ[k] Unitization k (QuantumGroup.Modified R (q : k)⁻¹) :=
  RingQuot.liftAlgHom k ⟨lusztigFree R q hv, fun _ _ h ↦ lusztigFree_rel R q hv h⟩

theorem lusztigHom_mk (x : Free k I (Y →+ ℤ)) :
    lusztigHom R q hv (mk (C.rootDatumOf R) q 1 x) = lusztigFree R q hv x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

theorem lusztigHom_one (μ : Y →+ ℤ) :
    lusztigHom R q hv (one (C.rootDatumOf R) q 1 μ) =
      Unitization.inr (QuantumGroup.Modified.one μ) := by
  rw [one, lusztigHom_mk, lusztigFree_one]

theorem lusztigHom_E (i : I) (μ : Y →+ ℤ) :
    lusztigHom R q hv (E (C.rootDatumOf R) q 1 i μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.E R _ i)) := by
  rw [E, lusztigHom_mk, lusztigFree_E]

theorem lusztigHom_F (i : I) (μ : Y →+ ℤ) :
    lusztigHom R q hv (F (C.rootDatumOf R) q 1 i μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.F R _ i)) := by
  rw [F, lusztigHom_mk, lusztigFree_F]

theorem fst_lusztigHom {x : CoveringUDot k (C.rootDatumOf R) q 1}
    (hx : x ∈ modified (C.rootDatumOf R) q 1) : (lusztigHom R q hv x).fst = 0 := by
  refine Submodule.iSup_induction (fun b : (Y →+ ℤ) × (Y →+ ℤ) ↦ block _ q 1 b.1 b.2)
    (motive := fun x ↦ (lusztigHom R q hv x).fst = 0) hx ?_ (by simp) ?_
  · intro b x hx
    rw [← hx.1, map_mul, Unitization.fst_mul, lusztigHom_one, Unitization.fst_inr, zero_mul]
  · intro x y hx hy
    rw [map_add, Unitization.fst_add, hx, hy, add_zero]

/-- The comparison map on the modified algebra, `U̇_{q,1} → U̇` (Lusztig, at `q⁻¹`). -/
def toLusztig :
    modified (C.rootDatumOf R) q 1 →ₗ[k] QuantumGroup.Modified R (q : k)⁻¹ where
  toFun x := (lusztigHom R q hv x).snd
  map_add' x y := by simp
  map_smul' c x := by simp

theorem lusztigHom_coe (x : modified (C.rootDatumOf R) q 1) :
    lusztigHom R q hv x = Unitization.inr (toLusztig R q hv x) :=
  Unitization.ext (fst_lusztigHom R q hv x.property) rfl

theorem toLusztig_mul (x y : modified (C.rootDatumOf R) q 1) :
    toLusztig R q hv (x * y) = toLusztig R q hv x * toLusztig R q hv y := by
  apply Unitization.inr_injective (R := k)
  rw [← lusztigHom_coe, Unitization.inr_mul, ← lusztigHom_coe, ← lusztigHom_coe,
    NonUnitalSubalgebra.coe_mul, map_mul]

theorem toLusztig_apply_of_lusztigHom {x : modified (C.rootDatumOf R) q 1}
    {w : QuantumGroup.Modified R (q : k)⁻¹} (h : lusztigHom R q hv x = Unitization.inr (w)) :
    toLusztig R q hv x = w := by
  apply Unitization.inr_injective (R := k)
  rw [← lusztigHom_coe, h]

theorem toLusztig_one (μ : Y →+ ℤ) :
    toLusztig R q hv ⟨one _ q 1 μ, one_mem_modified _ q 1 μ⟩ = QuantumGroup.Modified.one μ :=
  toLusztig_apply_of_lusztigHom R q hv (lusztigHom_one R q hv μ)

theorem toLusztig_E (i : I) (μ : Y →+ ℤ) :
    toLusztig R q hv ⟨E _ q 1 i μ, E_mem_modified _ q 1 i μ⟩ =
      leftActOne R hv μ (QuantumGroup.E R _ i) :=
  toLusztig_apply_of_lusztigHom R q hv (lusztigHom_E R q hv i μ)

theorem toLusztig_F (i : I) (μ : Y →+ ℤ) :
    toLusztig R q hv ⟨F _ q 1 i μ, F_mem_modified _ q 1 i μ⟩ =
      leftActOne R hv μ (QuantumGroup.F R _ i) :=
  toLusztig_apply_of_lusztigHom R q hv (lusztigHom_F R q hv i μ)

/-! ### Half words -/

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
theorem halfWeight_true (w : List I) :
    halfWeight (C.rootDatumOf R) true (PreF.wordWeight w) = QuantumGroup.wordChar R w := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [PreF.wordWeight_cons, halfWeight_add, halfWeight_single, ih, QuantumGroup.wordChar_cons]
    rfl

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
theorem halfWeight_false (w : List I) :
    halfWeight (C.rootDatumOf R) false (PreF.wordWeight w) = -QuantumGroup.wordChar R w := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [PreF.wordWeight_cons, halfWeight_add, halfWeight_single, ih, QuantumGroup.wordChar_cons,
      neg_add]
    rfl

theorem lusztigHom_halfWord_true (w : List I) (μ : Y →+ ℤ) :
    lusztigHom R q hv (halfWord (C.rootDatumOf R) q 1 true w μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.plusHom R _ (PreF.monomial k w))) := by
  induction w with
  | nil =>
    rw [halfWord, lusztigHom_one, PreF.monomial_nil, map_one, leftActOne_one]
  | cons i w ih =>
    rw [halfWord, map_mul, ih]
    change lusztigHom R q hv (E _ q 1 i _) * _ = _
    rw [lusztigHom_E, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (QuantumGroup.E_mem_adWeightSpace i)
        (plusHom_preMonomial_mem w),
      ite_eq_left (show μ + halfWeight (C.rootDatumOf R) true (PreF.wordWeight w) =
        μ + QuantumGroup.wordChar R w by rw [halfWeight_true]),
      PreF.monomial_cons, map_mul (QuantumGroup.plusHom R _),
      show PreF.θ k i = LusztigF.θ k i from rfl, QuantumGroup.plusHom_θ]

theorem lusztigHom_halfWord_false (w : List I) (μ : Y →+ ℤ) :
    lusztigHom R q hv (halfWord (C.rootDatumOf R) q 1 false w μ) =
      Unitization.inr (leftActOne R hv μ (QuantumGroup.minusHom R _ (PreF.monomial k w))) := by
  induction w with
  | nil =>
    rw [halfWord, lusztigHom_one, PreF.monomial_nil, map_one, leftActOne_one]
  | cons i w ih =>
    rw [halfWord, map_mul, ih]
    change lusztigHom R q hv (F _ q 1 i _) * _ = _
    rw [lusztigHom_F, ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (F_mem_adWeightSpace i)
        (minusHom_preMonomial_mem w),
      ite_eq_left (show μ + halfWeight (C.rootDatumOf R) false (PreF.wordWeight w) =
        μ + -QuantumGroup.wordChar R w by rw [halfWeight_false]),
      PreF.monomial_cons, map_mul (QuantumGroup.minusHom R _),
      show PreF.θ k i = LusztigF.θ k i from rfl, QuantumGroup.minusHom_θ]

/-! ### The pulled back form: `ρ`-adjointness and positive values -/

/-- Adjointness of the pulled back form, on the unital envelope. -/
theorem form_lusztigHom_rho (u : CoveringUDot k (C.rootDatumOf R) q 1)
    (a b : QuantumGroup.Modified R (q : k)⁻¹) :
    QuantumGroup.Modified.form R _ hv (lusztigHom R q hv u * Unitization.inr (a)).snd b =
      QuantumGroup.Modified.form R _ hv a
        (lusztigHom R q hv (rho (C.rootDatumOf R) q 1 (one_pow 2) u).unop *
          Unitization.inr b).snd := by
  obtain ⟨z, rfl⟩ := mk_surjective (C.rootDatumOf R) q 1 u
  induction z using FreeAlgebra.induction generalizing a b with
  | grade0 c =>
    simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      Unitization.algebraMap_eq_inl, Unitization.inl_mul_inr, Unitization.snd_inr, map_smul,
      LinearMap.smul_apply]
  | grade1 g =>
    cases g with
    | one μ =>
      change QuantumGroup.Modified.form R _ hv
          (lusztigHom R q hv (one _ q 1 μ) * Unitization.inr (a)).snd b =
        QuantumGroup.Modified.form R _ hv a
          (lusztigHom R q hv (rho _ q 1 (one_pow 2) (one _ q 1 μ)).unop * Unitization.inr (b)).snd
      rw [rho_one, lusztigHom_one, ← Unitization.inr_mul, Unitization.snd_inr,
        ← Unitization.inr_mul, Unitization.snd_inr, form_one_mul]
    | e i μ =>
      change QuantumGroup.Modified.form R _ hv
          (lusztigHom R q hv (E _ q 1 i μ) * Unitization.inr (a)).snd b =
        QuantumGroup.Modified.form R _ hv a
          (lusztigHom R q hv (rho _ q 1 (one_pow 2) (E _ q 1 i μ)).unop * Unitization.inr (b)).snd
      rw [rho_E, map_smul, lusztigHom_F, lusztigHom_E, ← Unitization.inr_mul, Unitization.snd_inr,
        ← Unitization.inr_smul, ← Unitization.inr_mul, Unitization.snd_inr,
        leftActOne_mul hv (QuantumGroup.E_mem_adWeightSpace i),
        QuantumGroup.Modified.form_leftAct_left, form_one_mul, one_mul_leftAct_rho_E,
        smul_mul_assoc, leftActOne_mul hv (F_mem_adWeightSpace i)]
      congr 2
      rw [qp, Units.val_zpow_eq_zpow_val, SuperCartanDatum.rootDatumOf_d,
        SuperCartanDatum.rootDatumOf_h, SuperCartanDatum.lusztigDatum_d]
      have hμ : μ (QuantumGroup.ktilde R i) = (C.d i : ℤ) * μ (R.coroot i) := by
        simp [QuantumGroup.ktilde, SuperCartanDatum.lusztigDatum_d]
      rw [hμ, ← zpow_natCast, ← zpow_add₀ (inv_ne_zero q.ne_zero), inv_zpow']
      congr 1
      ring
    | f i μ =>
      change QuantumGroup.Modified.form R _ hv
          (lusztigHom R q hv (F _ q 1 i μ) * Unitization.inr (a)).snd b =
        QuantumGroup.Modified.form R _ hv a
          (lusztigHom R q hv (rho _ q 1 (one_pow 2) (F _ q 1 i μ)).unop * Unitization.inr (b)).snd
      rw [rho_F, map_smul, lusztigHom_E, lusztigHom_F, ← Unitization.inr_mul, Unitization.snd_inr,
        ← Unitization.inr_smul, ← Unitization.inr_mul, Unitization.snd_inr,
        leftActOne_mul hv (F_mem_adWeightSpace i),
        QuantumGroup.Modified.form_leftAct_left, form_one_mul, one_mul_leftAct_rho_F,
        smul_mul_assoc, leftActOne_mul hv (QuantumGroup.E_mem_adWeightSpace i)]
      congr 2
      rw [qp, Units.val_zpow_eq_zpow_val, SuperCartanDatum.rootDatumOf_d,
        SuperCartanDatum.rootDatumOf_h, SuperCartanDatum.lusztigDatum_d]
      have hμ : μ (-QuantumGroup.ktilde R i) = -((C.d i : ℤ) * μ (R.coroot i)) := by
        simp [QuantumGroup.ktilde, SuperCartanDatum.lusztigDatum_d]
      rw [hμ, ← zpow_natCast, ← zpow_add₀ (inv_ne_zero q.ne_zero), inv_zpow']
      congr 1
      ring
  | add x y hx hy =>
    rw [map_add, map_add, add_mul, Unitization.snd_add, map_add, LinearMap.add_apply, hx, hy,
      map_add, MulOpposite.unop_add, map_add, add_mul, Unitization.snd_add, map_add]
  | mul x y hx hy =>
    have hinr : ∀ (z : Unitization k (QuantumGroup.Modified R (q : k)⁻¹))
        (c : QuantumGroup.Modified R (q : k)⁻¹),
        z * Unitization.inr c = Unitization.inr ((z * Unitization.inr c).snd) :=
      fun z c ↦ Unitization.ext (by simp) rfl
    rw [map_mul, map_mul, mul_assoc, hinr (lusztigHom R q hv (mk _ q 1 y)), hx, hy, rho_mul,
      map_mul, mul_assoc, ← hinr]

/-- The pulled back form is left `ρ`-adjoint. -/
theorem form_toLusztig_rho (u x y : modified (C.rootDatumOf R) q 1) :
    QuantumGroup.Modified.form R _ hv (toLusztig R q hv (u * x)) (toLusztig R q hv y) =
      QuantumGroup.Modified.form R _ hv (toLusztig R q hv x)
        (toLusztig R q hv (rhoModified _ q 1 (one_pow 2) u * y)) := by
  have h1 : toLusztig R q hv (u * x) =
      (lusztigHom R q hv u * Unitization.inr (toLusztig R q hv x)).snd := by
    rw [← lusztigHom_coe, ← map_mul]
    rfl
  have h2 : toLusztig R q hv (rhoModified _ q 1 (one_pow 2) u * y) =
      (lusztigHom R q hv (rho _ q 1 (one_pow 2) u).unop *
        Unitization.inr (toLusztig R q hv y)).snd := by
    rw [← lusztigHom_coe, ← map_mul]
    rfl
  rw [h1, h2, form_lusztigHom_rho]

theorem toLusztig_positiveWord (a : List I) (μ : Y →+ ℤ) :
    toLusztig R q hv (positiveWord _ q 1 a μ) =
      leftActOne R hv μ (QuantumGroup.plusHom R _ (PreF.monomial k a)) :=
  toLusztig_apply_of_lusztigHom R q hv (lusztigHom_halfWord_true R q hv a μ)

/-- The values of the pulled back form on positive words ([Lus] 26.1.5 and `form_one`). -/
theorem form_toLusztig_positiveWord (a b : List I) (μ ν : Y →+ ℤ) :
    QuantumGroup.Modified.form R _ hv (toLusztig R q hv (positiveWord _ q 1 a μ))
        (toLusztig R q hv (positiveWord _ q 1 b ν)) =
      if μ = ν then (C.rootDatumOf R).form q 1 (PreF.monomial k a) (PreF.monomial k b)
      else 0 := by
  rw [toLusztig_positiveWord, toLusztig_positiveWord]
  split_ifs with h
  · subst h
    rw [leftActOne_apply, leftActOne_apply, QuantumGroup.Modified.form_plusHom_leftAct_one,
      ← C.form_one q]
  · rw [leftActOne_eq_elt hv (plusHom_preMonomial_mem a),
      leftActOne_eq_elt hv (plusHom_preMonomial_mem b),
      QuantumGroup.Modified.form_elt_elt_of_ne hv]
    intro h'
    exact h (Prod.mk.inj h').2

/-! ### Surjectivity -/

theorem leftAct_mem_range_of_gen {χ : Y →+ ℤ} {u : QuantumGroup R (q : k)⁻¹}
    (hu : u ∈ QuantumGroup.adWeightSpace R _ χ)
    (hgen : ∀ μ, leftActOne R hv μ u ∈ LinearMap.range (toLusztig R q hv))
    (x : modified (C.rootDatumOf R) q 1) :
    QuantumGroup.Modified.leftAct R _ hv u (toLusztig R q hv x) ∈
      LinearMap.range (toLusztig R q hv) := by
  obtain ⟨s, hs, -⟩ := exists_localUnit _ q 1 x.property
  have hx : x = ∑ μ ∈ s, (⟨one _ q 1 μ, one_mem_modified _ q 1 μ⟩ :
      modified (C.rootDatumOf R) q 1) * x := by
    apply Subtype.ext
    rw [← Finset.sum_mul]
    simpa using hs.symm
  rw [hx, map_sum, map_sum]
  refine Submodule.sum_mem _ fun μ _ ↦ ?_
  rw [toLusztig_mul, toLusztig_one, ← leftActOne_mul hv hu]
  obtain ⟨g, hg⟩ := hgen μ
  rw [← hg, ← toLusztig_mul]
  exact LinearMap.mem_range_self _ _

theorem leftAct_mem_range (u : QuantumGroup R (q : k)⁻¹) :
    ∀ w ∈ LinearMap.range (toLusztig R q hv),
      QuantumGroup.Modified.leftAct R _ hv u w ∈ LinearMap.range (toLusztig R q hv) := by
  induction u using QuantumGroup.induction_on with
  | algebraMap c =>
    intro w hw
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.smul_apply,
      QuantumGroup.Modified.leftAct_one]
    exact Submodule.smul_mem _ c hw
  | E i =>
    rintro _ ⟨x, rfl⟩
    exact leftAct_mem_range_of_gen R q hv (QuantumGroup.E_mem_adWeightSpace i)
      (fun μ ↦ ⟨_, toLusztig_E R q hv i μ⟩) x
  | F i =>
    rintro _ ⟨x, rfl⟩
    exact leftAct_mem_range_of_gen R q hv (F_mem_adWeightSpace i)
      (fun μ ↦ ⟨_, toLusztig_F R q hv i μ⟩) x
  | K y =>
    rintro _ ⟨x, rfl⟩
    refine leftAct_mem_range_of_gen R q hv (QuantumGroup.K_mem_adWeightSpace y)
      (fun μ ↦ ?_) x
    rw [leftActOne_K, ← toLusztig_one R q hv μ]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  | add x y hx hy =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hx w hw) (hy w hw)
  | mul x y hx hy =>
    intro w hw
    rw [QuantumGroup.Modified.leftAct_mul]
    exact hx _ (hy w hw)

theorem toLusztig_surjective : Function.Surjective (toLusztig R q hv) := by
  intro w
  change w ∈ LinearMap.range (toLusztig R q hv)
  induction w using QuantumGroup.Modified.induction_on with
  | h0 => exact zero_mem _
  | hadd x y hx hy => exact add_mem hx hy
  | helt l₁ l₂ u hu =>
    rw [← QuantumGroup.Modified.leftAct_one_eq_elt hv hu]
    exact leftAct_mem_range R q hv u _ ⟨_, toLusztig_one R q hv l₂⟩

/-! ### Injectivity -/

omit [DecidableEq (Y →+ ℤ)] in
variable (C) in
omit [DecidableEq I] in
include hv in
/-- The Lusztig Serre ideal lies in the covering Serre ideal at `π = 1`, for `q⁻¹` not a root
of unity. -/
theorem lusztigSerreIdeal_le :
    LusztigF.serreIdeal C.lusztigDatum ((q : k)⁻¹) ≤ C.serreIdeal q 1 := by
  apply TwoSidedIdeal.span_le.mpr
  rintro x ⟨i, j, hij, rfl⟩
  have hf := LusztigF.qFactorial_ne_zero_of_not_root (D := C.lusztigDatum)
    (inv_ne_zero q.ne_zero) hv i (C.serreDeg i j)
  apply (C.mem_serreIdeal q 1 _).mpr
  rw [LusztigF.serreElement, SuperCartanDatum.lusztigDatum_cartanMatrix,
    ← SuperCartanDatum.serreDeg, qSerreDiv_eq hf]
  rw [SuperCartanDatum.lusztigDatum_d, inv_pow, qSerre_inv, ← C.serreElt_one q, map_smul,
    C.toSerreF_serreElt q 1 hij, smul_zero]

omit [DecidableEq I] [DecidableEq (Y →+ ℤ)] in
theorem lift_mem_adjoin {A : Type*} [Ring A] [Algebra k A] (f : I → A) (x : PreF k I) :
    FreeAlgebra.lift k f x ∈ Algebra.adjoin k (Set.range f) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
  | grade1 i => rw [FreeAlgebra.lift_ι_apply]; exact Algebra.subset_adjoin ⟨i, rfl⟩
  | mul a b ha hb => rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb

/-- `f → U⁺`, `θᵢ ↦ Eᵢ`, from the covering Serre presentation at `π = 1`. -/
def serrePlus : C.serreF q 1 →ₐ[k] QuantumGroup R (q : k)⁻¹ :=
  RingQuot.liftAlgHom k ⟨QuantumGroup.plusHom R _, fun _ _ h ↦ by
    cases h with
    | serre i j h =>
      rw [map_zero, SuperCartanDatum.serreElt_one, map_qSerre, QuantumGroup.plusHom_θ,
        QuantumGroup.plusHom_θ, qSerre_E R q h]⟩

/-- `f → U⁻`, `θᵢ ↦ Fᵢ`, from the covering Serre presentation at `π = 1`. -/
def serreMinus : C.serreF q 1 →ₐ[k] QuantumGroup R (q : k)⁻¹ :=
  RingQuot.liftAlgHom k ⟨QuantumGroup.minusHom R _, fun _ _ h ↦ by
    cases h with
    | serre i j h =>
      rw [map_zero, SuperCartanDatum.serreElt_one, map_qSerre, QuantumGroup.minusHom_θ,
        QuantumGroup.minusHom_θ, qSerre_F R q h]⟩

omit [DecidableEq (Y →+ ℤ)] in
theorem serrePlus_toSerreF (x : PreF k I) :
    serrePlus R q (C.toSerreF q 1 x) = QuantumGroup.plusHom R _ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

omit [DecidableEq (Y →+ ℤ)] in
theorem serreMinus_toSerreF (x : PreF k I) :
    serreMinus R q (C.toSerreF q 1 x) = QuantumGroup.minusHom R _ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

omit [DecidableEq (Y →+ ℤ)] in
include hv in
theorem serrePlus_injective : Function.Injective (serrePlus R q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective q 1 x
  rw [serrePlus_toSerreF, QuantumGroup.plusHom_eq_zero_iff R _ hv] at hx
  exact (C.mem_serreIdeal q 1 x).mp (lusztigSerreIdeal_le C q hv hx)

omit [DecidableEq (Y →+ ℤ)] in
include hv in
theorem serreMinus_injective : Function.Injective (serreMinus R q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := C.toSerreF_surjective q 1 x
  rw [serreMinus_toSerreF, QuantumGroup.minusHom_eq_zero_iff R _ hv] at hx
  exact (C.mem_serreIdeal q 1 x).mp (lusztigSerreIdeal_le C q hv hx)

/-- `f → U⁺` with codomain `U⁺`. -/
def serrePlusLin :
    C.serreF q 1 →ₗ[k] Algebra.adjoin k (Set.range (QuantumGroup.E R (q : k)⁻¹)) where
  toFun x := ⟨serrePlus R q x, by
    obtain ⟨x, rfl⟩ := C.toSerreF_surjective q 1 x
    rw [serrePlus_toSerreF]
    exact lift_mem_adjoin _ x⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)

/-- `f → U⁻` with codomain `U⁻`. -/
def serreMinusLin :
    C.serreF q 1 →ₗ[k] Algebra.adjoin k (Set.range (QuantumGroup.F R (q : k)⁻¹)) where
  toFun x := ⟨serreMinus R q x, by
    obtain ⟨x, rfl⟩ := C.toSerreF_surjective q 1 x
    rw [serreMinus_toSerreF]
    exact lift_mem_adjoin _ x⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)

/-- On the right column `U̇ 1_μ`, Lusztig's `Φ_μ` composed with `toLusztig` is the tensor
square of the embeddings `f → U^∓`. -/
theorem phi_toLusztig_triangularModified (μ : Y →+ ℤ) :
    QuantumGroup.Modified.Phi R hv μ ∘ₗ toLusztig R q hv ∘ₗ
        triangularModified (C.rootDatumOf R) q 1 μ =
      TensorProduct.map (serreMinusLin R q) (serrePlusLin R q) := by
  have hsurj : Function.Surjective (TensorProduct.map (C.toSerreF q 1).toLinearMap
      (C.toSerreF q 1).toLinearMap) :=
    TensorProduct.map_surjective (C.toSerreF_surjective q 1) (C.toSerreF_surjective q 1)
  refine (LinearMap.cancel_right hsurj).mp ?_
  refine ((FreeAlgebra.wordBasis k I).tensorProduct (FreeAlgebra.wordBasis k I)).ext fun ab ↦ ?_
  obtain ⟨a, b⟩ := ab
  simp only [Module.Basis.tensorProduct_apply, LusztigF.wordBasis_eq_monomial,
    LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  have hn : (triangularModified (C.rootDatumOf R) q 1 μ
      (C.toSerreF q 1 (LusztigF.monomial k a) ⊗ₜ[k] C.toSerreF q 1 (LusztigF.monomial k b)) :
        CoveringUDot k (C.rootDatumOf R) q 1) = normalWord _ q 1 a b μ :=
    triangularTensor_monomial _ q 1 μ a b
  have hl : toLusztig R q hv (triangularModified (C.rootDatumOf R) q 1 μ
      (C.toSerreF q 1 (LusztigF.monomial k a) ⊗ₜ[k] C.toSerreF q 1 (LusztigF.monomial k b))) =
        leftActOne R hv μ (QuantumGroup.minusHom R _ (PreF.monomial k a) *
          QuantumGroup.plusHom R _ (PreF.monomial k b)) := by
    apply toLusztig_apply_of_lusztigHom
    rw [hn, normalWord, map_mul, lusztigHom_halfWord_false, lusztigHom_halfWord_true,
      ← Unitization.inr_mul,
      leftActOne_mul_leftActOne hv (minusHom_preMonomial_mem a)
        (plusHom_preMonomial_mem b),
      ite_eq_left (show μ + halfWeight (C.rootDatumOf R) true (PreF.wordWeight b) =
        μ + QuantumGroup.wordChar R b by rw [halfWeight_true])]
  rw [hl, leftActOne_eq_elt hv (QuantumGroup.mul_mem_adWeightSpace
      (minusHom_preMonomial_mem a)
      (plusHom_preMonomial_mem b)),
    QuantumGroup.Modified.Phi_elt, ite_eq_left rfl]
  have hy : (serreMinusLin R q (C.toSerreF q 1 (LusztigF.monomial k a)) :
      QuantumGroup R (q : k)⁻¹) = QuantumGroup.minusHom R _ (PreF.monomial k a) :=
    serreMinus_toSerreF R q _
  have hx : (serrePlusLin R q (C.toSerreF q 1 (LusztigF.monomial k b)) :
      QuantumGroup R (q : k)⁻¹) = QuantumGroup.plusHom R _ (PreF.monomial k b) :=
    serrePlus_toSerreF R q _
  rw [← hy, ← hx]
  exact QuantumGroup.PhiU_mul_plus hv μ _ _

theorem toLusztig_injective : Function.Injective (toLusztig R q hv) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap : Function.Injective (TensorProduct.map (serreMinusLin R q) (serrePlusLin R q)) :=
    TensorProduct.map_injective_of_flat_flat _ _
      (fun a b h ↦ serreMinus_injective R q hv (congrArg Subtype.val h))
      (fun a b h ↦ serrePlus_injective R q hv (congrArg Subtype.val h))
  have hcol : ∀ μ, (x : CoveringUDot k (C.rootDatumOf R) q 1) * one _ q 1 μ = 0 := by
    intro μ
    have hmem : (x : CoveringUDot k (C.rootDatumOf R) q 1) * one _ q 1 μ ∈
        LinearMap.range (triangularTensor (C.rootDatumOf R) q 1 μ) := by
      rw [range_triangularTensor]
      change _ * _ * _ = _
      rw [mul_assoc, one_mul_one_self]
    obtain ⟨t, ht⟩ := hmem
    have hxt : triangularModified (C.rootDatumOf R) q 1 μ t =
        x * ⟨one _ q 1 μ, one_mem_modified _ q 1 μ⟩ := Subtype.ext ht
    have h0 : TensorProduct.map (serreMinusLin R q) (serrePlusLin R q) t = 0 := by
      rw [← phi_toLusztig_triangularModified R q hv μ, LinearMap.comp_apply,
        LinearMap.comp_apply, hxt, toLusztig_mul, hx, zero_mul, map_zero]
    rw [← ht, (injective_iff_map_eq_zero _).mp hmap t h0, map_zero]
  obtain ⟨s, -, hs⟩ := exists_localUnit _ q 1 x.property
  apply Subtype.ext
  change (x : CoveringUDot k (C.rootDatumOf R) q 1) = 0
  rw [← hs, Finset.mul_sum, Finset.sum_eq_zero fun μ _ ↦ hcol μ]

/-! ### The `π = 1` nondegeneracy input from Lusztig's form -/

/-- **The `π = 1` nondegeneracy input from [Lus] 26.3.1.** If Lusztig's form on `U̇` at
`v = q⁻¹` has trivial left radical (the hypothesis `hLus`, [Lus] 26.3.1), then every left
`ρ`-adjoint bilinear form on the modified covering algebra `U̇_{q,1}` of `C.rootDatumOf R` with
the standard values `(E_a 1_μ, E_b 1_ν) = δ_{μν} (θ_a, θ_b)` on positive words has trivial left
radical. -/
theorem positiveFormNondegenerate_of_lusztig
    (hLus : ∀ x : QuantumGroup.Modified R (q : k)⁻¹,
      (∀ y, QuantumGroup.Modified.form R _ hv x y = 0) → x = 0) :
    PositiveFormNondegenerate (C.rootDatumOf R) k q 1 (one_pow 2) := by
  intro B hB hval x hx
  set B' : LinearMap.BilinForm k (modified (C.rootDatumOf R) q 1) :=
    (QuantumGroup.Modified.form R _ hv).compl₁₂ (toLusztig R q hv) (toLusztig R q hv)
  have hB' (x y) : B' x y =
      QuantumGroup.Modified.form R _ hv (toLusztig R q hv x) (toLusztig R q hv y) := rfl
  have heq : B = B' := forms_eq_of_positiveWord (C.rootDatumOf R) q 1 (one_pow 2) B B' hB
    (fun u x y ↦ by rw [hB', hB', form_toLusztig_rho])
    (fun a b μ ν ↦ by rw [hval, hB', form_toLusztig_positiveWord])
  apply toLusztig_injective R q hv
  rw [map_zero]
  apply hLus
  intro w
  obtain ⟨y, rfl⟩ := toLusztig_surjective R q hv w
  rw [← hB', ← heq, hx]

/-! ### The nondegeneracy theorem over `ℚ(q)[π]/(π² - 1)` -/

section Generic

attribute [local instance] QuantumGroup.neZero_ratFunc_X

/-- **The `π = 1` nondegeneracy input from [Lus] 26.3.1 over `ℚ(v)`.** If Lusztig's form on `U̇`
over `ℚ(v)` at `v = X` has trivial left radical (the hypothesis `hQ`, [Lus] 26.3.1), then for any
field `L` of characteristic zero and `q' ∈ Lˣ` with `q'⁻¹` transcendental over `ℚ`, every left
`ρ`-adjoint form on `U̇_{q',1}` with the standard values on positive words has trivial left radical.
The transfer from `ℚ(v)` to `L` is LieLean's
`QuantumGroup.Modified.form_nondegenerate_of_transcendental` (base change along `v ↦ q'⁻¹`). -/
theorem positiveFormNondegenerate_of_ratFunc
    (hQ : ∀ x : QuantumGroup.Modified R (RatFunc.X : RatFunc ℚ),
      (∀ y, QuantumGroup.Modified.form R _ QuantumGroup.ratFunc_X_not_root x y = 0) → x = 0)
    {L : Type*} [Field L] [CharZero L] (q' : Lˣ) (hw : Transcendental ℚ ((q' : L)⁻¹)) :
    PositiveFormNondegenerate (C.rootDatumOf R) L q' 1 (one_pow 2) :=
  positiveFormNondegenerate_of_lusztig R q'
    (fun _ hn ↦ LusztigF.pow_ne_one_of_transcendental hw hn)
    (QuantumGroup.Modified.form_nondegenerate_of_transcendental hQ hw)

variable [Finite I] (hD : (C.rootDatumOf R).toSuperCartanDatum.BarConsistent)

include hD in
/-- **Nondegeneracy of the `ρ`-adjoint form on `U̇`.** This is the nondegeneracy assertion of
[BE2] Theorem 10.1 (Brundan–Ellis, arXiv:1701.04133v2) for `GenericTensor.positiveModifiedForm`
on the modified covering algebra of `C.rootDatumOf R` over `ℚ(q)[π]/(π² - 1)`: its left radical is
trivial. The setting is that of [BE2] §1: finite `I`, the coweight lattice `Y` free of finite rank,
simple roots `hα` and simple coroots `hcoroot` linearly independent. The root datum is presented
as `C.rootDatumOf R` (weights `X = Hom(Y, ℤ)`). The hypothesis `hD` is the bar-consistency
assumption (10.2) of [BE2], used here by the twistor reduction. The `π = 1`
input is Lusztig's [Lus] 26.3.1 over `ℚ(v)`, LieLean's `Modified.eq_zero_of_forall_form_eq_zero`,
whose dominance hypothesis is `exists_dominant_ge_of_linearIndependent_coroot`; inside the proof it
is transferred to `L = \overline{ℚ(q)}` at `v = q⁻¹` and `v = (t q)⁻¹` (`t² = -1`), both
transcendental over `ℚ`. -/
theorem positiveModifiedForm_nondegenerate [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (hα : LinearIndependent ℤ (C.rootDatumOf R).α) (hcoroot : LinearIndependent ℤ R.coroot) :
    ∀ x, (∀ y, GenericTensor.positiveModifiedForm (C.rootDatumOf R) x y = 0) → x = 0 := by
  have hQ := QuantumGroup.Modified.eq_zero_of_forall_form_eq_zero (R := R) hα
    (exists_dominant_ge_of_linearIndependent_coroot R hcoroot)
  refine positiveModifiedForm_leftRadical_trivial_algebraicClosure (C.rootDatumOf R) hD hα
    (positiveFormNondegenerate_of_ratFunc R hQ _ QuantumGroup.transcendental_inv_X)
    fun t ht ↦ positiveFormNondegenerate_of_ratFunc R hQ _
      (QuantumGroup.transcendental_inv_mul_X (t := t) ?_)
  rw [← Units.val_pow_eq_pow_val, ht, Units.val_neg, Units.val_one]

include hD in
/-- **Nondegeneracy of the sesquilinear form on `U̇`.** The nondegeneracy assertion of [BE2]
Theorem 10.1 (Brundan–Ellis, arXiv:1701.04133v2) for `GenericTensor.sesquilinearForm`, under the
hypotheses of `positiveModifiedForm_nondegenerate`, including the bar-consistency assumption
(10.2) of [BE2] and the root datum presentation `C.rootDatumOf R`. -/
theorem sesquilinearForm_nondegenerate [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (hα : LinearIndependent ℤ (C.rootDatumOf R).α) (hcoroot : LinearIndependent ℤ R.coroot) :
    ∀ x, (∀ y, GenericTensor.sesquilinearForm (C.rootDatumOf R) x y = 0) → x = 0 := by
  have hQ := QuantumGroup.Modified.eq_zero_of_forall_form_eq_zero (R := R) hα
    (exists_dominant_ge_of_linearIndependent_coroot R hcoroot)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (-1 : AlgebraicClosure (RatFunc ℚ))
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have ht : Units.mk0 z hz0 ^ 2 = -1 := Units.ext (by simp [sq, ← hz])
  exact sesquilinearForm_leftRadical_trivial (C.rootDatumOf R) hD hα _ ht
    (positiveFormNondegenerate_of_ratFunc R hQ _ QuantumGroup.transcendental_inv_X)
    (positiveFormNondegenerate_of_ratFunc R hQ _
      (QuantumGroup.transcendental_inv_mul_X (t := z) (by rw [sq, ← hz])))

end Generic

end UDot

end OddMath.CoveringQuantum
