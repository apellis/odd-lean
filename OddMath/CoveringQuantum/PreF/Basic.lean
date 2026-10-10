/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The free algebra `'f` with a bicharacter twist: grading, twists and skew derivations

Clark–Hill–Wang, *Quantum supergroups I*, arXiv:1301.1665v2 ([CHW1]), §1.4, define `'f` as the
free associative superalgebra with `1` over `ℚ(q)^π` on generators `θᵢ` (`i ∈ I`), graded by
`ℕ[I]`, with `𝐟 ⊗ 𝐟` carrying the twisted multiplication
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = q^{|x₂|·|x₁'|} π^{p(x₂)p(x₁')} x₁x₁' ⊗ x₂x₂'`.
Brundan–Ellis, arXiv:1701.04133v2 ([BE2]), §10, use the same construction with `q` replaced by
`q⁻¹`: `(x ⊗ y)(x' ⊗ y') = π^{|y||x'|} q^{-(β,α')} xx' ⊗ yy'`.

Both twists have the form `χ(|x₂|, |x₁'|)` for a *symmetric bicharacter* `χ` of `ℕ[I]`,
determined by its values `χ(i, j)` on generators. This file and its companions
(`OddMath.CoveringQuantum.PreF.Comul`, `OddMath.CoveringQuantum.PreF.Form`) develop `'f`, the
twisted coproduct `r` and the bilinear form for an arbitrary symmetric `χ : I → I → k` over a
commutative ring `k`; the covering quantum group is the case
`χ(i, j) = q^{-i·j} π^{|i||j|}` (`OddMath.CoveringQuantum.HalfAlgebra`). The super signs enter only
through `χ`: the generator `π` is a formal parameter, not a Koszul sign. The development follows
the template of lie-lean's `LusztigF` (the purely even case `χ(i, j) = v^{i·j}` over a field).

For `i ∈ I` we define
* the twist `σᵢ`, the algebra endomorphism `θⱼ ↦ χ(i, j) θⱼ`, so that `σᵢ(x) = χ(i, |x|) x` for
  homogeneous `x`;
* skew derivations `rᵢ`, `ᵢr` with `rᵢ(θⱼ) = ᵢr(θⱼ) = δᵢⱼ` and
  `rᵢ(xy) = x rᵢ(y) + rᵢ(x) σᵢ(y)`, `ᵢr(xy) = ᵢr(x) y + σᵢ(x) ᵢr(y)` ([CHW1] §1.5, (1.8)),
  constructed as off-diagonal entries of algebra maps to `2 × 2` upper triangular matrices.

## Main definitions

* `Bichar k I`: a symmetric function `χ : I → I → k`; `Bichar.wt`: its extension to `ℕ[I]`.
* `PreF k I`: the free algebra `'f`; `PreF.θ k i`; `PreF.counit`.
* `PreF.monomial`, `PreF.wordWeight`, `PreF.weightSpace ν` (= `'f_ν`).
* `PreF.twist χ i` (`σᵢ`), `PreF.rDeriv χ i` (`rᵢ`), `PreF.lDeriv χ i` (`ᵢr`).

## Main results

* `PreF.induction_left`, `PreF.induction_right`.
* `PreF.mul_mem_weightSpace`, `PreF.iSup_weightSpace`, `PreF.iSupIndep_weightSpace`.
* `PreF.twist_of_mem`: `σᵢ(x) = χ(i, ν) x` on `'f_ν`.
* `PreF.rDeriv_mul`, `PreF.lDeriv_mul`, `PreF.rDeriv_θ`, `PreF.lDeriv_θ`.
-/

noncomputable section

open Finset

namespace OddMath.CoveringQuantum

/-- A symmetric function `χ : I → I → k`, the values on generators of a symmetric bicharacter of
`ℕ[I]` (`Bichar.wt`). -/
structure Bichar (k I : Type*) [CommRing k] where
  /-- The values `χ(i, j)`. -/
  toFun : I → I → k
  symm : ∀ i j, toFun i j = toFun j i

namespace Bichar

variable {k I : Type*} [CommRing k]

instance : CoeFun (Bichar k I) (fun _ ↦ I → I → k) := ⟨Bichar.toFun⟩

variable (χ : Bichar k I)

theorem comm (i j : I) : χ i j = χ j i := χ.symm i j

/-- The bicharacter `χ(ν, μ) = ∏ᵢⱼ χ(i, j)^{νᵢ μⱼ}` of `ℕ[I]`. -/
def wt (ν μ : I →₀ ℕ) : k := ν.prod fun i m ↦ μ.prod fun j n ↦ χ i j ^ (m * n)

theorem wt_zero_left (μ : I →₀ ℕ) : χ.wt 0 μ = 1 := by simp [wt]

theorem wt_zero_right (ν : I →₀ ℕ) : χ.wt ν 0 = 1 := by simp [wt]

theorem wt_add_right (ν μ μ' : I →₀ ℕ) : χ.wt ν (μ + μ') = χ.wt ν μ * χ.wt ν μ' := by
  simp only [wt]
  rw [← Finsupp.prod_mul]
  refine Finsupp.prod_congr fun i _ ↦ ?_
  exact Finsupp.prod_add_index' (by simp) (fun j a b ↦ by rw [mul_add, pow_add])

theorem wt_add_left (ν ν' μ : I →₀ ℕ) : χ.wt (ν + ν') μ = χ.wt ν μ * χ.wt ν' μ := by
  simp only [wt]
  refine Finsupp.prod_add_index' (by simp) (fun i a b ↦ ?_)
  rw [← Finsupp.prod_mul]
  refine Finsupp.prod_congr fun j _ ↦ ?_
  rw [add_mul, pow_add]

@[simp] theorem wt_single_single (i j : I) :
    χ.wt (Finsupp.single i 1) (Finsupp.single j 1) = χ i j := by
  simp [wt, Finsupp.prod_single_index]

theorem wt_comm (ν μ : I →₀ ℕ) : χ.wt ν μ = χ.wt μ ν := by
  simp only [wt]
  rw [Finsupp.prod_comm]
  refine Finsupp.prod_congr fun j _ ↦ Finsupp.prod_congr fun i _ ↦ ?_
  rw [χ.comm, mul_comm]

end Bichar

variable {k I : Type*} [CommRing k]

/-- The free algebra `'f` ([CHW1] §1.4; [BE2] §10): the free associative `k`-algebra with `1` on
generators `θᵢ`, `i ∈ I`. -/
abbrev PreF (k I : Type*) [CommRing k] := FreeAlgebra k I

namespace PreF

variable (k) in
/-- The generator `θᵢ` of `'f`. -/
abbrev θ (i : I) : PreF k I := FreeAlgebra.ι k i

/-- The augmentation `'f → k` (the constant term). -/
abbrev counit : PreF k I →ₐ[k] k := FreeAlgebra.algebraMapInv

@[simp] lemma counit_θ (i : I) : counit (θ k i) = 0 := by
  simp [counit, FreeAlgebra.algebraMapInv]

@[simp] lemma counit_algebraMap (c : k) : counit (algebraMap k (PreF k I) c) = c :=
  FreeAlgebra.algebraMap_leftInverse c

/-! ### Induction principles -/

/-- Induction on `'f` by left multiplication with generators. -/
theorem induction_left {P : PreF k I → Prop} (algebraMap : ∀ c, P (algebraMap k _ c))
    (smul : ∀ (c : k) x, P x → P (c • x)) (add : ∀ x y, P x → P y → P (x + y))
    (θ_mul : ∀ i x, P x → P (θ k i * x)) (x : PreF k I) : P x := by
  have key : ∀ a : PreF k I, ∀ y, P y → P (a * y) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c => intro y hy; rw [← Algebra.smul_def]; exact smul c y hy
    | grade1 i => exact θ_mul i
    | mul a b ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb _ hy)
    | add a b ha hb => intro y hy; rw [add_mul]; exact add _ _ (ha _ hy) (hb _ hy)
  simpa using key x 1 (by simpa using algebraMap 1)

/-- Induction on `'f` by right multiplication with generators. -/
theorem induction_right {P : PreF k I → Prop} (algebraMap : ∀ c, P (algebraMap k _ c))
    (smul : ∀ (c : k) x, P x → P (c • x)) (add : ∀ x y, P x → P y → P (x + y))
    (mul_θ : ∀ x i, P x → P (x * θ k i)) (x : PreF k I) : P x := by
  have key : ∀ a : PreF k I, ∀ y, P y → P (y * a) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c => intro y hy; rw [← Algebra.commutes, ← Algebra.smul_def]; exact smul c y hy
    | grade1 i => exact fun y hy ↦ mul_θ y i hy
    | mul a b ha hb => intro y hy; rw [← mul_assoc]; exact hb _ (ha _ hy)
    | add a b ha hb => intro y hy; rw [mul_add]; exact add _ _ (ha _ hy) (hb _ hy)
  simpa using key x 1 (by simpa using algebraMap 1)

/-! ### Monomials and the grading -/

variable (k) in
/-- The monomial `θ_{i₁} ⋯ θ_{iₙ}` of a word `[i₁, …, iₙ]`. -/
def monomial (w : List I) : PreF k I := (w.map (θ k)).prod

/-- The weight `i₁ + ⋯ + iₙ ∈ ℕ[I]` of a word `[i₁, …, iₙ]`. -/
def wordWeight (w : List I) : I →₀ ℕ := (w.map fun i ↦ Finsupp.single i 1).sum

@[simp] lemma monomial_nil : monomial k ([] : List I) = 1 := rfl

@[simp] lemma monomial_cons (i : I) (w : List I) :
    monomial k (i :: w) = θ k i * monomial k w := by simp [monomial]

lemma monomial_append (w w' : List I) :
    monomial k (w ++ w') = monomial k w * monomial k w' := by simp [monomial]

@[simp] lemma wordWeight_nil : wordWeight ([] : List I) = 0 := rfl

@[simp] lemma wordWeight_cons (i : I) (w : List I) :
    wordWeight (i :: w) = Finsupp.single i 1 + wordWeight w := by simp [wordWeight]

lemma wordWeight_append (w w' : List I) :
    wordWeight (w ++ w') = wordWeight w + wordWeight w' := by simp [wordWeight]

lemma wordWeight_apply (w : List I) (i : I) [DecidableEq I] :
    wordWeight w i = w.count i := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, Finsupp.add_apply, ih, List.count_cons, Finsupp.single_apply,
      beq_iff_eq]
    split_ifs <;> omega

variable (k) in
/-- The weight space `'f_ν`, spanned by the monomials of weight `ν`. -/
def weightSpace (ν : I →₀ ℕ) : Submodule k (PreF k I) :=
  Submodule.span k (monomial k '' {w | wordWeight w = ν})

lemma monomial_mem_weightSpace (w : List I) : monomial k w ∈ weightSpace k (wordWeight w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

lemma one_mem_weightSpace : (1 : PreF k I) ∈ weightSpace k 0 :=
  monomial_mem_weightSpace (k := k) ([] : List I)

lemma algebraMap_mem_weightSpace (c : k) : algebraMap k (PreF k I) c ∈ weightSpace k 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ one_mem_weightSpace

lemma θ_mem_weightSpace (i : I) : θ k i ∈ weightSpace k (Finsupp.single i 1) := by
  simpa [monomial] using monomial_mem_weightSpace (k := k) [i]

lemma mul_mem_weightSpace {ν μ : I →₀ ℕ} {x y : PreF k I} (hx : x ∈ weightSpace k ν)
    (hy : y ∈ weightSpace k μ) : x * y ∈ weightSpace k (ν + μ) := by
  have : weightSpace k ν * weightSpace k μ ≤ weightSpace k (ν + μ) := by
    rw [weightSpace, weightSpace, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, _, ⟨w', hw', rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw hw'
    dsimp only
    rw [← monomial_append, ← hw, ← hw', ← wordWeight_append]
    exact monomial_mem_weightSpace _
  exact this (Submodule.mul_mem_mul hx hy)

lemma span_monomial : Submodule.span k (Set.range (monomial k (I := I))) = ⊤ := by
  suffices h : ∀ x, x ∈ Submodule.span k (Set.range (monomial k (I := I))) from
    eq_top_iff.2 fun x _ ↦ h x
  intro x
  induction x using induction_left with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | smul c x hx => exact Submodule.smul_mem _ _ hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | θ_mul i x hx =>
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact Submodule.subset_span ⟨i :: w, monomial_cons i w⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

theorem iSup_weightSpace : ⨆ ν, weightSpace k (I := I) ν = ⊤ := by
  rw [eq_top_iff, ← span_monomial, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace w)

variable (k I) in
/-- The algebra homomorphism `'f → 'f[ℕ[I]]`, `θᵢ ↦ θᵢ e^{i}`, which encodes the grading. -/
def gradingHom : PreF k I →ₐ[k] AddMonoidAlgebra (PreF k I) (I →₀ ℕ) :=
  FreeAlgebra.lift k fun i ↦ AddMonoidAlgebra.single (Finsupp.single i 1) (θ k i)

lemma gradingHom_monomial (w : List I) :
    gradingHom k I (monomial k w) = AddMonoidAlgebra.single (wordWeight w) (monomial k w) := by
  induction w with
  | nil => simp [AddMonoidAlgebra.one_def]
  | cons i w ih =>
    rw [monomial_cons, map_mul, ih]
    simp [gradingHom, AddMonoidAlgebra.single_mul_single]

lemma gradingHom_of_mem {ν : I →₀ ℕ} {x : PreF k I} (hx : x ∈ weightSpace k ν) :
    gradingHom k I x = AddMonoidAlgebra.single ν x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [gradingHom_monomial, hw]
  | zero => simp [AddMonoidAlgebra.single_zero]
  | add y z _ _ hy hz => rw [map_add, hy, hz, AddMonoidAlgebra.single_add]
  | smul c y _ hy =>
    rw [map_smul, hy, AddMonoidAlgebra.smul_single]

theorem iSupIndep_weightSpace : iSupIndep (weightSpace k (I := I)) := by
  classical
  intro ν
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : (gradingHom k I x).coeff ν = x := by
    rw [gradingHom_of_mem hx]; simp [AddMonoidAlgebra.coeff_single]
  have h2 : ∀ y ∈ ⨆ μ, ⨆ (_ : μ ≠ ν), weightSpace k μ, (gradingHom k I y).coeff ν = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem μ y hy =>
      induction hy using Submodule.iSup_induction' with
      | mem hμ y hy =>
        rw [gradingHom_of_mem hy]
        simp [AddMonoidAlgebra.coeff_single, hμ]
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
  rw [← h1, h2 x hx']

/-! ### Twists and skew derivations -/

/-- The diagonal endomorphism `θⱼ ↦ cⱼ θⱼ` of `'f`. -/
def diagTwist (c : I → k) : PreF k I →ₐ[k] PreF k I :=
  FreeAlgebra.lift k fun j ↦ c j • θ k j

@[simp] lemma diagTwist_θ (c : I → k) (j : I) : diagTwist c (θ k j) = c j • θ k j := by
  simp [diagTwist]

lemma diagTwist_diagTwist (c c' : I → k) (x : PreF k I) :
    diagTwist c (diagTwist c' x) = diagTwist (c * c') x := by
  have : (diagTwist c).comp (diagTwist c') = diagTwist (k := k) (c * c') := by
    ext l
    simp [smul_smul, mul_comm]
  exact congr($this x)

lemma diagTwist_comm (c c' : I → k) (x : PreF k I) :
    diagTwist c (diagTwist c' x) = diagTwist c' (diagTwist c x) := by
  rw [diagTwist_diagTwist, diagTwist_diagTwist, mul_comm]

@[simp] lemma counit_diagTwist (c : I → k) (x : PreF k I) :
    counit (diagTwist c x) = counit x := by
  have : counit.comp (diagTwist (k := k) (I := I) c) = counit := by ext l; simp
  exact congr($this x)

variable (χ : Bichar k I)

/-- The twist `σᵢ : 'f → 'f`, `θⱼ ↦ χ(i, j) θⱼ`; on `'f_ν` it is multiplication by `χ(i, ν)`. -/
def twist (i : I) : PreF k I →ₐ[k] PreF k I := diagTwist fun j ↦ χ i j

@[simp] lemma twist_θ (i j : I) : twist χ i (θ k j) = χ i j • θ k j := by
  simp [twist]

lemma twist_comm (i j : I) (x : PreF k I) :
    twist χ i (twist χ j x) = twist χ j (twist χ i x) := diagTwist_comm _ _ x

@[simp] lemma counit_twist (i : I) (x : PreF k I) : counit (twist χ i x) = counit x :=
  counit_diagTwist _ x

variable {χ} in
/-- On `'f_ν` the twist `σᵢ` is multiplication by `χ(i, ν)`. -/
theorem twist_of_mem (i : I) {ν : I →₀ ℕ} {x : PreF k I} (hx : x ∈ weightSpace k ν) :
    twist χ i x = χ.wt (Finsupp.single i 1) ν • x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w with
    | nil => simp [Bichar.wt_zero_right]
    | cons l w ih =>
      rw [monomial_cons, map_mul, ih, twist_θ, smul_mul_smul_comm, wordWeight_cons,
        χ.wt_add_right, χ.wt_single_single]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul c y _ hy => rw [map_smul, hy, smul_comm]

lemma twist_mem_weightSpace (i : I) {ν : I →₀ ℕ} {x : PreF k I}
    (hx : x ∈ weightSpace k ν) : twist χ i x ∈ weightSpace k ν := by
  rw [twist_of_mem i hx]; exact Submodule.smul_mem _ _ hx

variable [DecidableEq I]

/-- The algebra homomorphism `x ↦ [[x, rᵢ(x)], [0, σᵢ(x)]]`. -/
def rMat (i : I) : PreF k I →ₐ[k] Matrix (Fin 2) (Fin 2) (PreF k I) :=
  FreeAlgebra.lift k fun j ↦ !![θ k j, if i = j then 1 else 0; 0, χ i j • θ k j]

/-- The algebra homomorphism `x ↦ [[σᵢ(x), ᵢr(x)], [0, x]]`. -/
def lMat (i : I) : PreF k I →ₐ[k] Matrix (Fin 2) (Fin 2) (PreF k I) :=
  FreeAlgebra.lift k fun j ↦ !![χ i j • θ k j, if i = j then 1 else 0; 0, θ k j]

/-- The linear map extracting the `(0, 1)` entry of a `2 × 2` matrix. -/
def entry01 : Matrix (Fin 2) (Fin 2) (PreF k I) →ₗ[k] PreF k I where
  toFun M := M 0 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The skew derivation `rᵢ : 'f → 'f` ([CHW1] §1.5): `rᵢ(θⱼ) = δᵢⱼ` and
`rᵢ(xy) = x rᵢ(y) + rᵢ(x) σᵢ(y)` (`rDeriv_mul`). -/
def rDeriv (i : I) : PreF k I →ₗ[k] PreF k I :=
  entry01 ∘ₗ (rMat χ i).toLinearMap

/-- The skew derivation `ᵢr : 'f → 'f` ([CHW1] §1.5): `ᵢr(θⱼ) = δᵢⱼ` and
`ᵢr(xy) = ᵢr(x) y + σᵢ(x) ᵢr(y)` (`lDeriv_mul`). -/
def lDeriv (i : I) : PreF k I →ₗ[k] PreF k I :=
  entry01 ∘ₗ (lMat χ i).toLinearMap

lemma rMat_entries (i : I) (x : PreF k I) :
    rMat χ i x 0 0 = x ∧ rMat χ i x 1 0 = 0 ∧ rMat χ i x 1 1 = twist χ i x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [rMat]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2]
    simp
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

lemma lMat_entries (i : I) (x : PreF k I) :
    lMat χ i x 0 0 = twist χ i x ∧ lMat χ i x 1 0 = 0 ∧ lMat χ i x 1 1 = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Matrix.algebraMap_matrix_apply]
  | grade1 j => simp [lMat]
  | mul a b ha hb =>
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1,
      hb.2.2]
    simp
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

lemma rDeriv_apply (i : I) (x : PreF k I) : rDeriv χ i x = rMat χ i x 0 1 := rfl

lemma lDeriv_apply (i : I) (x : PreF k I) : lDeriv χ i x = lMat χ i x 0 1 := rfl

/-- `rᵢ(xy) = x rᵢ(y) + rᵢ(x) σᵢ(y)`. -/
theorem rDeriv_mul (i : I) (x y : PreF k I) :
    rDeriv χ i (x * y) = x * rDeriv χ i y + rDeriv χ i x * twist χ i y := by
  simp only [rDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (rMat_entries χ i x).1,
    (rMat_entries χ i y).2.2]

/-- `ᵢr(xy) = ᵢr(x) y + σᵢ(x) ᵢr(y)`. -/
theorem lDeriv_mul (i : I) (x y : PreF k I) :
    lDeriv χ i (x * y) = lDeriv χ i x * y + twist χ i x * lDeriv χ i y := by
  simp only [lDeriv_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two, (lMat_entries χ i x).1,
    (lMat_entries χ i y).2.2]
  rw [add_comm]

@[simp] lemma rDeriv_θ (i j : I) : rDeriv χ i (θ k j) = if i = j then 1 else 0 := by
  simp [rDeriv_apply, rMat]

@[simp] lemma lDeriv_θ (i j : I) : lDeriv χ i (θ k j) = if i = j then 1 else 0 := by
  simp [lDeriv_apply, lMat]

@[simp] lemma rDeriv_algebraMap (i : I) (c : k) : rDeriv χ i (algebraMap k _ c) = 0 := by
  simp [rDeriv_apply, Matrix.algebraMap_matrix_apply]

@[simp] lemma lDeriv_algebraMap (i : I) (c : k) : lDeriv χ i (algebraMap k _ c) = 0 := by
  simp [lDeriv_apply, Matrix.algebraMap_matrix_apply]

@[simp] lemma rDeriv_one (i : I) : rDeriv χ i 1 = 0 := by
  simpa using rDeriv_algebraMap χ i (1 : k)

@[simp] lemma lDeriv_one (i : I) : lDeriv χ i 1 = 0 := by
  simpa using lDeriv_algebraMap χ i (1 : k)

lemma rDeriv_θ_mul (i j : I) (x : PreF k I) :
    rDeriv χ i (θ k j * x) = θ k j * rDeriv χ i x + if i = j then twist χ i x else 0 := by
  rw [rDeriv_mul, rDeriv_θ]; split_ifs <;> simp

lemma rDeriv_mul_θ (i j : I) (x : PreF k I) :
    rDeriv χ i (x * θ k j) = (if i = j then x else 0) + χ i j • (rDeriv χ i x * θ k j) := by
  rw [rDeriv_mul, rDeriv_θ, twist_θ, mul_smul_comm]; split_ifs <;> simp

lemma lDeriv_θ_mul (i j : I) (x : PreF k I) :
    lDeriv χ i (θ k j * x) = (if i = j then x else 0) + χ i j • (θ k j * lDeriv χ i x) := by
  rw [lDeriv_mul, lDeriv_θ, twist_θ, smul_mul_assoc]; split_ifs <;> simp

/-- `rᵢ ∘ φ = cᵢ φ ∘ rᵢ` for the diagonal twist `φ : θⱼ ↦ cⱼ θⱼ`. -/
lemma rDeriv_diagTwist (c : I → k) (i : I) (x : PreF k I) :
    rDeriv χ i (diagTwist c x) = c i • diagTwist c (rDeriv χ i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 a => simp
  | grade1 l =>
    simp only [diagTwist_θ, map_smul, rDeriv_θ]
    split_ifs with h <;> simp [h]
  | mul a b ha hb =>
    rw [map_mul, rDeriv_mul, rDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist,
      diagTwist_comm c]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

/-- `ᵢr ∘ φ = cᵢ φ ∘ ᵢr` for the diagonal twist `φ : θⱼ ↦ cⱼ θⱼ`. -/
lemma lDeriv_diagTwist (c : I → k) (i : I) (x : PreF k I) :
    lDeriv χ i (diagTwist c x) = c i • diagTwist c (lDeriv χ i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 a => simp
  | grade1 l =>
    simp only [diagTwist_θ, map_smul, lDeriv_θ]
    split_ifs with h <;> simp [h]
  | mul a b ha hb =>
    rw [map_mul, lDeriv_mul, lDeriv_mul, ha, hb, map_add, map_mul, map_mul, twist,
      diagTwist_comm c]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add]
  | add a b ha hb => simp [ha, hb]

/-- `rᵢ ∘ σⱼ = χ(i, j) σⱼ ∘ rᵢ`. -/
lemma rDeriv_twist (i j : I) (x : PreF k I) :
    rDeriv χ i (twist χ j x) = χ i j • twist χ j (rDeriv χ i x) := by
  rw [twist, rDeriv_diagTwist, χ.comm]

/-- `ᵢr ∘ σⱼ = χ(i, j) σⱼ ∘ ᵢr`. -/
lemma lDeriv_twist (i j : I) (x : PreF k I) :
    lDeriv χ i (twist χ j x) = χ i j • twist χ j (lDeriv χ i x) := by
  rw [twist, lDeriv_diagTwist, χ.comm]

lemma counit_rDeriv_θ_mul (i j : I) (x : PreF k I) :
    counit (rDeriv χ i (θ k j * x)) = if i = j then counit x else 0 := by
  rw [rDeriv_θ_mul]; split_ifs <;> simp

end PreF

end OddMath.CoveringQuantum
