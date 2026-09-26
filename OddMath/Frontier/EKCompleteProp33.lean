import OddMath.Frontier.EKPrimitives

/-!
# [EK] Proposition 3.3 as one statement about all of `Λ`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §3.2, Proposition 3.3 (p. 25): the primitive
elements of `Λ` are spanned by `m_1` and the `m_{2k}`, `k ≥ 1`.

`EKPrimitives.proposition_3_3` treats one homogeneous degree at a time. Here the statement is
for an arbitrary, possibly inhomogeneous, `x ∈ Λ` (over `ℤ`, at `q = −1`):
`x` is primitive iff `x ∈ span_ℤ {m_(n) : n = 1 or n ≥ 2 even}` (`proposition_3_3_all`).

Route: `x` is primitive iff `(ab, x) = ε(a)(b, x) + (a, x)ε(b)` for all `a, b`
(adjointness and integral tensor separation). The pairing is degree-orthogonal, so this
derivation identity passes to every homogeneous component of `x`
(`decompose_primitive`); the degree-zero component vanishes; the per-degree statement then
applies. The paper works over a field of characteristic `0`; the integral statement is
stronger than its rational form on the lattice `Λ_ℤ`, and base change is not formalized.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKComplete
open EKRadicalQuotient EKCoideal EKIntegralBases EKPrimitives
open EKPartitionSpanning (hPartition)

/-- The primitive elements, as a submodule: the kernel of `x ↦ Δx − 1 ⊗ x − x ⊗ 1`. -/
def primitives : Submodule ℤ Q :=
  LinearMap.ker (quotientCoproduct -
    (TensorProduct.mk ℤ Q Q 1 + (TensorProduct.mk ℤ Q Q).flip 1))

theorem mem_primitives (x : Q) : x ∈ primitives ↔ IsPrimitive x := by
  simp [primitives, IsPrimitive, sub_eq_zero]

/-- The derivation defect `(a, b) ↦ (ab, x) − ε(a)(b, x) − (a, x)ε(b)`. -/
def primDefect (x : Q) : Q →ₗ[ℤ] Q →ₗ[ℤ] ℤ :=
  (LinearMap.mul ℤ Q).compr₂ (quotientPairing.flip x) -
    (LinearMap.mul ℤ ℤ).compl₁₂ quotientCounit.toLinearMap (quotientPairing.flip x) -
    (LinearMap.mul ℤ ℤ).compl₁₂ (quotientPairing.flip x) quotientCounit.toLinearMap

theorem primDefect_apply (x a b : Q) :
    primDefect x a b = quotientPairing (a * b) x - quotientCounit a * quotientPairing b x -
      quotientPairing a x * quotientCounit b := rfl

/-- Primitivity is the derivation identity against the pairing. -/
theorem isPrimitive_iff_defect (x : Q) : IsPrimitive x ↔ primDefect x = 0 := by
  constructor
  · intro hx
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    rw [primDefect_apply, prim_deriv hx]
    simp
  · intro h
    unfold IsPrimitive
    rw [← sub_eq_zero]
    apply tensor_separation
    intro a b
    have hab := LinearMap.congr_fun₂ h a b
    rw [primDefect_apply, LinearMap.zero_apply, LinearMap.zero_apply] at hab
    rw [map_sub, test_coproduct, map_add, tensorTest_tmul, tensorTest_tmul,
      quotientPairing_symm 1 a, quotientPairing_right_one, quotientPairing_symm 1 b,
      quotientPairing_right_one, quotientPairing_symm x a, quotientPairing_symm x b]
    linarith

/-- Pairing a homogeneous element against a homogeneous component. -/
theorem pair_decompose {e d : ℕ} {y : Q} (hy : y ∈ degreePiece e) (x : Q) :
    quotientPairing y (decompose x d) = if e = d then quotientPairing y x else 0 := by
  split_ifs with hed
  · subst hed
    conv_rhs => rw [← recompose_decompose x]
    rw [recompose_apply, Finsupp.sum, map_sum, Finset.sum_eq_single e]
    · intro b _ hb
      exact pairing_degree_orth (Ne.symm hb) hy (decompose_mem x b)
    · intro he
      rw [Finsupp.not_mem_support_iff.mp he, map_zero]
  · exact pairing_degree_orth hed hy (decompose_mem x d)

theorem defect_decompose {p r d : ℕ} {a b : Q} (ha : a ∈ degreePiece p)
    (hb : b ∈ degreePiece r) (x : Q) :
    primDefect (decompose x d) a b = if p + r = d then primDefect x a b else 0 := by
  have hab := degreePiece_mul ha hb
  have hεa : p ≠ 0 → quotientCounit a = 0 := fun hp => counit_degree_pos (Nat.pos_of_ne_zero hp) ha
  have hεb : r ≠ 0 → quotientCounit b = 0 := fun hr => counit_degree_pos (Nat.pos_of_ne_zero hr) hb
  rw [primDefect_apply, primDefect_apply, pair_decompose hab, pair_decompose hb,
    pair_decompose ha]
  by_cases hp : p = 0 <;> by_cases hr : r = 0
  · subst hp hr; split_ifs <;> omega
  · subst hp; rw [hεb hr]; split_ifs <;> omega
  · subst hr; rw [hεa hp]; split_ifs <;> omega
  · rw [hεa hp, hεb hr]; split_ifs <;> omega

/-- Every homogeneous component of a primitive element is primitive. -/
theorem decompose_primitive {x : Q} (hx : IsPrimitive x) (d : ℕ) :
    IsPrimitive (decompose x d) := by
  rw [isPrimitive_iff_defect] at hx ⊢
  refine hBasis.ext fun μ => hBasis.ext fun ν => ?_
  rw [hBasis_apply, hBasis_apply, defect_decompose (hPartition_mem μ) (hPartition_mem ν), hx]
  simp

theorem rowLens_eq_nil {μ : YoungDiagram} (h : μ.card = 0) : μ.rowLens = [] := by
  cases hl : μ.rowLens with
  | nil => rfl
  | cons a t =>
    have ha := μ.pos_of_mem_rowLens a (by simp [hl])
    have hs := rowLens_sum μ
    rw [hl, h, List.sum_cons] at hs
    omega

/-- A primitive element has no degree-zero component. -/
theorem decompose_zero_of_primitive {x : Q} (hx : IsPrimitive x) : decompose x 0 = 0 := by
  have h1 : quotientPairing 1 x = 0 := by
    have := prim_deriv hx 1 1
    have hε : quotientCounit (1 : Q) = 1 := map_one _
    rw [mul_one, hε] at this
    linarith
  apply quotientPairing_nondegenerate_left
  intro y
  rw [quotientPairing_symm]
  have hlin : quotientPairing.flip (decompose x 0) = 0 := by
    refine hBasis.ext fun μ => ?_
    rw [hBasis_apply, LinearMap.flip_apply, pair_decompose (hPartition_mem μ)]
    split_ifs with hμ
    · rw [EKPartitionSpanning.hPartition, rowLens_eq_nil hμ]
      simpa using h1
    · rfl
  exact LinearMap.congr_fun hlin y

/-- The generators of Proposition 3.3: `m_1` and `m_{2k}`, `k ≥ 1`. -/
def primGen : Set Q := {y | ∃ n : ℕ, 0 < n ∧ (n = 1 ∨ Even n) ∧ y = (mRow n : Q)}

/-- **EK Proposition 3.3, all of `Λ` at once** (integral form): an arbitrary `x ∈ Λ` is
primitive iff it lies in the `ℤ`-span of `m_1, m_2, m_4, m_6, …`. -/
theorem proposition_3_3_all (x : Q) :
    IsPrimitive x ↔ x ∈ Submodule.span ℤ primGen := by
  constructor
  · intro hx
    rw [← recompose_decompose x, recompose_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hd := decompose_primitive hx d
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [decompose_zero_of_primitive hx]; exact Submodule.zero_mem _
    by_cases hn : d = 1 ∨ Even d
    · have hm := (primitive_iff_span d hpos hn ⟨_, decompose_mem x d⟩).mp hd
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      have hc' := congrArg Subtype.val hc
      simp only [Submodule.coe_smul] at hc'
      rw [← hc']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hpos, hn, rfl⟩)
    · have hodd : Odd d := Nat.not_even_iff_odd.mp (fun he => hn (Or.inr he))
      have h3 : 3 ≤ d := by
        obtain ⟨k, rfl⟩ := hodd
        rcases k with _ | k
        · exact absurd (Or.inl rfl) hn
        · omega
      have hz := (primitive_iff_zero d hodd h3 ⟨_, decompose_mem x d⟩).mp hd
      have hz' : decompose x d = 0 := congrArg Subtype.val hz
      rw [hz']
      exact Submodule.zero_mem _
  · intro hx
    rw [← mem_primitives]
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨n, hpos, hn, rfl⟩
    exact (mem_primitives _).mpr (mRow_primitive n hn hpos)

/-- Proposition 3.3 as an equality of submodules of `Λ`. -/
theorem primitives_eq_span : primitives = Submodule.span ℤ primGen :=
  Submodule.ext fun x => (mem_primitives x).trans (proposition_3_3_all x)

end OddMath.Frontier.EKComplete
