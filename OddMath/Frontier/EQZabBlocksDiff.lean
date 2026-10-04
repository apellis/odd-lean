import OddMath.Frontier.EQZabBlocks
import OddMath.Frontier.EQFixZabCells

/-!
# Ellis–Qi, Proposition 4.13 (2) for any number of blocks: the basis spans a `d`-stable lattice

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, the definition of the dg bimodule `Z_{a_1,…,a_r}` and Proposition 4.13 (2).

The source gives `Z_a` the differential determined by
`d 1_z = Σ_{i ≥ 2} {a_1 + ⋯ + a_{i−1}} ẽ_1(X_i) 1_z`. In the model of `EQZabBlocks` (compositions
last block first) this is `dB a = τ ∘ d_α ∘ τ` (`dB`), with `d_α` the local differential of
Ellis–Qi (3.3) for `α = (a_1 + ⋯ + a_{i−1}) mod 2` on the `i`-th block (`alpha`) and `τ` the
blockwise twist `θ_{a_1} ⊗ ⋯ ⊗ θ_{a_r}` (`tauB`), as for the differential
`EQZab.dT = τ ∘ d_Z ∘ τ` of Definition 4.6 for two blocks. `dB_one_cons`: `dB (k :: a) 1 = dB a 1 (x) + {m} ẽ_1(y)`, the
printed formula for `d 1_z`.

**Proposition 4.13 (2)** (`prop_4_13_two`): the `ℤ`-span of the basis
`s̃_{λ_1}(X_1) ⋯ s̃_{λ_r}(X_r)` of Proposition 4.13 (1) (`SpanT`) is `d`-stable. The proof applies
Lemma 4.7 / Corollary 4.8 (`EQZab.cor_4_8_stable`) to each block, through the Leibniz rule across
the last block (`dAlpha_cons`).
-/

namespace OddMath.Frontier.EQBlocks

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (theta elementary osym parityInv ringHom_ext dAlpha sAlpha
  dAlpha_apply)
open OddMath.Frontier.EQZab (inclX inclY)
open OddMath.Frontier.EQBorel (sp_mul_assoc sp_zero_mul sp_mul_zero skew_induction)
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqBlocksDNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqBlocksDNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {m k : ℕ}

/-! ## Supercommutation of a first-block variable with the second block -/

theorem inclX_generator_mul_inclY (i : Fin m) (Q : SkewPolynomial k) :
    inclX m k (generator i) * inclY m k Q = inclY m k (parityInv k Q) * inclX m k (generator i) := by
  induction Q using skew_induction with
  | hgen j =>
    rw [EQZab.inclY_generator, EQSkewDifferential.parityInv_generator, map_neg,
      EQZab.inclX_generator, EQZab.inclY_generator, neg_mul]
    have hne : Fin.castAdd k i ≠ Fin.natAdd m j := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    exact eq_neg_of_add_eq_zero_left (OddMath.PbwL1.rel_sum _ _ hne)
  | hint z => simp only [map_intCast]; exact (Int.cast_comm _ _).symm
  | hadd f g hf hg => rw [map_add, map_add, map_add, mul_add, add_mul, hf, hg]
  | hmul f g hf hg =>
    rw [map_mul, map_mul, map_mul, ← sp_mul_assoc, hf, sp_mul_assoc, hg, ← sp_mul_assoc]

theorem inclX_sAlpha_mul_inclY (α : Fin m → ℤ) (Q : SkewPolynomial k) :
    inclX m k (sAlpha α) * inclY m k Q = inclY m k (parityInv k Q) * inclX m k (sAlpha α) := by
  simp only [sAlpha, map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, inclX_generator_mul_inclY]

/-! ## The differential -/

/-- `α`: on the block `i`, the parity of `a_1 + ⋯ + a_{i−1}`. -/
def alpha : (a : List ℕ) → Fin (blocksN a) → ℤ
  | [] => fun _ => 0
  | _ :: a => Fin.append (alpha a) (fun _ => EQZab.par (blocksN a))

/-- `alpha (k :: a)` with its type written as `Fin (blocksN a + k) → ℤ`. -/
abbrev alphaC (a : List ℕ) (k : ℕ) : Fin (blocksN a + k) → ℤ :=
  Fin.append (alpha a) (fun _ => EQZab.par (blocksN a))

/-- The blockwise twist coefficients. -/
def tc : (a : List ℕ) → Fin (blocksN a) → ℤ
  | [] => fun _ => 1
  | _ :: a => Fin.append (tc a) (fun j => (-1 : ℤ) ^ j.val)

/-- The blockwise twist `τ = θ_{a_1} ⊗ ⋯ ⊗ θ_{a_r}`. -/
def tauB (a : List ℕ) : SkewPolynomial (blocksN a) →+* SkewPolynomial (blocksN a) :=
  EQZab.diagHom _ (tc a)

/-- `tauB (k :: a)` with its type written over `blocksN a + k`. -/
abbrev tauC (a : List ℕ) (k : ℕ) : SkewPolynomial (blocksN a + k) →+* SkewPolynomial (blocksN a + k) :=
  EQZab.diagHom _ (Fin.append (tc a) (fun j => (-1 : ℤ) ^ j.val))

/-- **The differential of `Z_a`**: `dB a = τ ∘ d_α ∘ τ`. -/
def dB (a : List ℕ) : SkewPolynomial (blocksN a) →+ SkewPolynomial (blocksN a) :=
  (tauB a).toAddMonoidHom.comp ((dAlpha (alpha a)).comp (tauB a).toAddMonoidHom)

theorem tauC_inclX (a : List ℕ) (k : ℕ) (P : SkewPolynomial (blocksN a)) :
    tauC a k (inclX (blocksN a) k P) = inclX (blocksN a) k (tauB a P) := by
  have h : (tauC a k).comp (inclX (blocksN a) k) = (inclX (blocksN a) k).comp (tauB a) :=
    ringHom_ext fun j => by simp [tauB, Fin.append_left]
  exact RingHom.congr_fun h P

theorem tauC_inclY (a : List ℕ) (k : ℕ) (Q : SkewPolynomial k) :
    tauC a k (inclY (blocksN a) k Q) = inclY (blocksN a) k (theta k Q) := by
  have h : (tauC a k).comp (inclY (blocksN a) k) = (inclY (blocksN a) k).comp (theta k) :=
    ringHom_ext fun j => by simp [Fin.append_right]
  exact RingHom.congr_fun h Q

theorem sAlpha_alphaC (a : List ℕ) (k : ℕ) :
    sAlpha (alphaC a k) = inclX (blocksN a) k (sAlpha (alpha a)) +
      EQZab.par (blocksN a) • inclY (blocksN a) k (elementary k 1) := by
  rw [sAlpha, sAlpha, Fin.sum_univ_add, map_sum, elementary, EQZab.strictSum_one, map_sum,
    Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [Fin.append_left]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [Fin.append_right]

/-- The Leibniz rule across the last block. -/
theorem dAlpha_cons (a : List ℕ) (k : ℕ) (P : SkewPolynomial (blocksN a)) (Q : SkewPolynomial k) :
    dAlpha (alphaC a k) (inclX (blocksN a) k P * inclY (blocksN a) k Q) =
      inclX (blocksN a) k (dAlpha (alpha a) P) * inclY (blocksN a) k Q +
        parityInv (blocksN a + k) (inclX (blocksN a) k P) *
          EQZab.dZ (blocksN a) k (inclY (blocksN a) k Q) := by
  rw [dAlpha_apply, dAlpha_apply, EQZab.dZ_apply, sAlpha_alphaC, EQSkewDifferential.d_mul,
    map_mul, map_add, map_mul, EQZab.d_inclX, EQZab.parityInv_inclX, EQZab.parityInv_inclY]
  rw [mul_add, mul_add, add_mul]
  have e1 : inclX (blocksN a) k (parityInv _ P) * inclY (blocksN a) k (parityInv k Q) *
      inclX (blocksN a) k (sAlpha (alpha a)) = inclX (blocksN a) k (parityInv _ P) *
        inclX (blocksN a) k (sAlpha (alpha a)) * inclY (blocksN a) k Q := by
    rw [sp_mul_assoc, ← inclX_sAlpha_mul_inclY, ← sp_mul_assoc]
  have e2 : inclX (blocksN a) k (parityInv _ P) * inclY (blocksN a) k (parityInv k Q) *
      (EQZab.par (blocksN a) • inclY (blocksN a) k (elementary k 1)) =
      inclX (blocksN a) k (parityInv _ P) * (inclY (blocksN a) k (parityInv k Q) *
        (EQZab.par (blocksN a) • inclY (blocksN a) k (elementary k 1))) := sp_mul_assoc _ _ _
  rw [e1, e2]
  abel

theorem dB_one_cons (a : List ℕ) (k : ℕ) :
    (dB (k :: a) 1 : SkewPolynomial (blocksN a + k)) = inclX (blocksN a) k (dB a 1) +
      EQZab.par (blocksN a) • inclY (blocksN a) k (theta k (elementary k 1)) := by
  show tauC a k (dAlpha (alphaC a k) (tauC a k 1)) = _
  rw [map_one, dAlpha_apply, EQSkewDifferential.d_one, map_one, one_mul, zero_add,
    sAlpha_alphaC, map_add, map_zsmul, tauC_inclX, tauC_inclY]
  congr 2
  show _ = tauB a (dAlpha (alpha a) (tauB a 1))
  rw [map_one, dAlpha_apply, EQSkewDifferential.d_one, map_one, one_mul, zero_add]

/-! ## The untwisted basis -/

/-- The untwisted products `s_{λ_1}(X_1) ⋯ s_{λ_r}(X_r)`. -/
def BasU : (a : List ℕ) → Idx a → SkewPolynomial (blocksN a)
  | [] => fun _ => 1
  | k :: a => fun i =>
      inclX (blocksN a) k (BasU a i.1) * inclY (blocksN a) k (EQSchur.untwisted k i.2.1)

/-- The `ℤ`-span of the untwisted basis. -/
def SpanU (a : List ℕ) : Submodule ℤ (SkewPolynomial (blocksN a)) :=
  Submodule.span ℤ (Set.range (BasU a))

/-- The `ℤ`-span of the basis of Proposition 4.13 (1). -/
def SpanT (a : List ℕ) : Submodule ℤ (SkewPolynomial (blocksN a)) :=
  Submodule.span ℤ (Set.range (Bas a))

theorem tauB_BasU : ∀ (a : List ℕ) (i : Idx a), tauB a (BasU a i) = Bas a i
  | [], _ => map_one _
  | k :: a, i => by
    show tauC a k (inclX (blocksN a) k (BasU a i.1) *
      inclY (blocksN a) k (EQSchur.untwisted k i.2.1)) = _
    rw [map_mul, tauC_inclX, tauC_inclY, tauB_BasU a i.1, ← EQSchur.twisted_eq_theta_untwisted]
    rfl

theorem tauB_Bas : ∀ (a : List ℕ) (i : Idx a), tauB a (Bas a i) = BasU a i
  | [], _ => map_one _
  | k :: a, i => by
    show tauC a k (inclX (blocksN a) k (Bas a i.1) *
      inclY (blocksN a) k (EQSchur.twisted k i.2.1)) = _
    rw [map_mul, tauC_inclX, tauC_inclY, tauB_Bas a i.1, EQSchur.twisted_eq_theta_untwisted,
      EQSchur.theta_theta]
    rfl

theorem mem_box_iff {μ : Fin k → ℕ} : μ ∈ BoxPartitionCount.box k m ↔ Antitone μ ∧ ∀ j, μ j ≤ m := by
  simp [BoxPartitionCount.box, Fintype.mem_piFinset, and_comm]

theorem mulY_mem {a : List ℕ} {P : SkewPolynomial (blocksN a)} (hP : P ∈ SpanU a)
    (μ : ↥(BoxPartitionCount.box k (blocksN a))) :
    inclX (blocksN a) k P * inclY (blocksN a) k (EQSchur.untwisted k μ.1) ∈ SpanU (k :: a) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, rfl⟩ := hx
    exact Submodule.subset_span ⟨(β, μ), rfl⟩
  | zero => rw [map_zero, sp_zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem mulSchur_mem {a : List ℕ} {P : SkewPolynomial (blocksN a)} (hP : P ∈ SpanU a)
    {F : SkewPolynomial (blocksN a + k)} (hF : F ∈ EQZab.schurSpan (blocksN a) k) :
    inclX (blocksN a) k P * F ∈ SpanU (k :: a) := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, rfl⟩ := hx
    exact mulY_mem hP ⟨ν.1, mem_box_iff.mpr ν.2⟩
  | zero => rw [sp_mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem parityInv_mem_SpanU : ∀ (a : List ℕ) {P : SkewPolynomial (blocksN a)}, P ∈ SpanU a →
    parityInv _ P ∈ SpanU a := by
  intro a P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    cases a with
    | nil =>
      show parityInv _ 1 ∈ _
      rw [map_one]; exact Submodule.subset_span ⟨(), rfl⟩
    | cons k a =>
      show parityInv (blocksN a + k) (inclX (blocksN a) k (BasU a i.1) *
        inclY (blocksN a) k (EQSchur.untwisted k i.2.1)) ∈ SpanU (k :: a)
      rw [map_mul, EQZab.parityInv_inclX, EQZab.parityInv_inclY,
        EQSkewDifferential.parityInv_of_mem (EQFix.untwisted_mem_grading k i.2.1), map_zsmul,
        mul_smul_comm]
      refine Submodule.smul_mem _ _ (mulY_mem ?_ i.2)
      exact parityInv_mem_SpanU a (Submodule.subset_span ⟨i.1, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx

/-- `d_α` preserves the span of the untwisted basis. -/
theorem dAlpha_BasU_mem : ∀ (a : List ℕ) (i : Idx a), dAlpha (alpha a) (BasU a i) ∈ SpanU a
  | [], i => by
    show dAlpha (alpha []) 1 ∈ _
    rw [dAlpha_apply, EQSkewDifferential.d_one, map_one, one_mul, zero_add]
    rw [show sAlpha (alpha []) = 0 from Finset.sum_empty]
    exact zero_mem _
  | k :: a, i => by
    show dAlpha (alphaC a k) (inclX (blocksN a) k (BasU a i.1) *
      inclY (blocksN a) k (EQSchur.untwisted k i.2.1)) ∈ SpanU (k :: a)
    rw [dAlpha_cons, EQZab.parityInv_inclX]
    refine add_mem ?_ ?_
    · refine mulY_mem ?_ i.2
      exact dAlpha_BasU_mem a i.1
    · refine mulSchur_mem (parityInv_mem_SpanU a (Submodule.subset_span ⟨i.1, rfl⟩))
        (EQZab.cor_4_8_stable (Submodule.subset_span ⟨⟨i.2.1, mem_box_iff.mp i.2.2⟩, rfl⟩))

/-- **Ellis–Qi, Proposition 4.13 (2)**: the `ℤ`-span of the basis
`s̃_{λ_1}(X_1) ⋯ s̃_{λ_r}(X_r)` of `Z_a` is stable under the differential `dB a`. -/
theorem prop_4_13_two (a : List ℕ) {G : SkewPolynomial (blocksN a)} (hG : G ∈ SpanT a) :
    dB a G ∈ SpanT a := by
  have hτ : ∀ {P}, P ∈ SpanU a → tauB a P ∈ SpanT a := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; rw [tauB_BasU]; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    show tauB a (dAlpha (alpha a) (tauB a (Bas a i))) ∈ SpanT a
    rw [tauB_Bas]
    exact hτ (dAlpha_BasU_mem a i)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx

end

end OddMath.Frontier.EQBlocks
