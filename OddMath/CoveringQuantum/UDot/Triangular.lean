import OddMath.CoveringQuantum.UDot.HalfWeights

/-!
# Triangular spanning for the modified covering quantum group

The defining commutator in [BE2] (9.2) puts negative generators before positive
ones. We prove the spanning part of triangular decomposition directly in the
presented modified algebra. This is not an injectivity or basis theorem.
Compare the reordering argument in [CHW1] Proposition 2.3.2.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

variable {k I X : Type*} [CommRing k] [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- Products of negative and positive words, allowing independent right weights. -/
def triangularSpan : Submodule k (CoveringUDot k D q π) :=
  Submodule.span k {z | ∃ (a b : List I) (ν μ : X),
    z = halfWord D q π false a ν * halfWord D q π true b μ}

theorem halfWords_mem_triangularSpan (a b : List I) (ν μ : X) :
    halfWord D q π false a ν * halfWord D q π true b μ ∈ triangularSpan D q π :=
  Submodule.subset_span ⟨a, b, ν, μ, rfl⟩

theorem halfGen_mul_halfWord (positive : Bool) (i : I) (η : X) (w : List I) (μ : X) :
    halfGen D q π positive i η * halfWord D q π positive w μ =
      if η = μ + halfWeight D positive (PreF.wordWeight w) then
        halfWord D q π positive (i :: w) μ else 0 := by
  split_ifs with h
  · rw [h]; rfl
  · exact mul_eq_zero_of_mem_block D q π (halfGen_mem_block D q π positive i η)
      (halfWord_mem_block D q π positive w μ) h

private theorem F_mul_triangularSpan (i : I) (η : X) {x : CoveringUDot k D q π}
    (hx : x ∈ triangularSpan D q π) : F D q π i η * x ∈ triangularSpan D q π := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, ν, μ, rfl⟩ := hx
    rw [← mul_assoc]
    change halfGen D q π false i η * halfWord D q π false a ν * _ ∈ _
    rw [halfGen_mul_halfWord]
    split_ifs
    · exact halfWords_mem_triangularSpan D q π _ b ν μ
    · simp
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih

private theorem one_mul_halfWords (η : X) (a b : List I) (ν μ : X) :
    one D q π η * (halfWord D q π false a ν * halfWord D q π true b μ) ∈
      triangularSpan D q π := by
  rw [← mul_assoc, one_mul_of_mem_block D q π (halfWord_mem_block D q π false a ν)]
  split_ifs
  · exact halfWords_mem_triangularSpan D q π a b ν μ
  · simp

private theorem E_mul_halfWords (i : I) (η : X) (a b : List I) (ν μ : X) :
    E D q π i η * (halfWord D q π false a ν * halfWord D q π true b μ) ∈
      triangularSpan D q π := by
  induction a generalizing η ν with
  | nil =>
    rw [halfWord, ← mul_assoc, E_mul_one]
    split_ifs with h
    · change halfGen D q π true i η * halfWord D q π true b μ ∈ _
      rw [halfGen_mul_halfWord]
      split_ifs
      · have hm := (halfWord_mem_block D q π true (i :: b) μ).1
        rw [← hm]
        exact halfWords_mem_triangularSpan D q π [] (i :: b) _ μ
      · exact Submodule.zero_mem _
    · simp
  | cons j a ih =>
    rw [halfWord]
    change E D q π i η *
      ((F D q π j (ν + halfWeight D false (PreF.wordWeight a)) *
        halfWord D q π false a ν) * halfWord D q π true b μ) ∈ _
    let ξ := ν + halfWeight D false (PreF.wordWeight a)
    by_cases h : η = ξ - D.α j
    · rw [h]
      rw [← mul_assoc, ← mul_assoc]
      rw [sub_eq_iff_eq_add.mp (comm_rel D q π i j ξ), add_mul, add_mul]
      apply Submodule.add_mem
      · split_ifs
        · rw [smul_mul_assoc, smul_mul_assoc, mul_assoc]
          exact Submodule.smul_mem _ _ (one_mul_halfWords D q π ξ a b ν μ)
        · simp
      · rw [smul_mul_assoc, smul_mul_assoc, mul_assoc, mul_assoc]
        exact Submodule.smul_mem _ _ (F_mul_triangularSpan D q π j _ (ih (ξ) ν))
    · have hz := mul_eq_zero_of_mem_block D q π
        (halfGen_mem_block D q π true i η)
        (halfGen_mem_block D q π false j ξ)
        (by simpa only [halfRoot, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] using h)
      change E D q π i η * F D q π j ξ = 0 at hz
      rw [← mul_assoc, ← mul_assoc, hz, zero_mul, zero_mul]
      exact Submodule.zero_mem _

private theorem gen_mul_triangularSpan (g : Gen I X) {x : CoveringUDot k D q π}
    (hx : x ∈ triangularSpan D q π) :
    mk D q π (FreeAlgebra.ι k g) * x ∈ triangularSpan D q π := by
  cases g with
  | f i η => exact F_mul_triangularSpan D q π i η hx
  | one η =>
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ν, μ, rfl⟩ := hx
      exact one_mul_halfWords D q π η a b ν μ
    | zero => simp
    | add x y hx hy ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih
  | e i η =>
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ν, μ, rfl⟩ := hx
      exact E_mul_halfWords D q π i η a b ν μ
    | zero => simp
    | add x y hx hy ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih

private theorem mul_one_mem_triangularSpan (x : CoveringUDot k D q π) (μ : X) :
    x * one D q π μ ∈ triangularSpan D q π := by
  obtain ⟨x, rfl⟩ := mk_surjective D q π x
  induction x using PreF.induction_left with
  | algebraMap c =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    apply Submodule.smul_mem
    rw [← one_mul_one_self D q π μ]
    exact halfWords_mem_triangularSpan D q π [] [] μ μ
  | smul c x hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  | add x y hx hy => rw [map_add, add_mul]; exact Submodule.add_mem _ hx hy
  | θ_mul g x hx =>
    rw [map_mul, mul_assoc]
    exact gen_mul_triangularSpan D q π g hx

/-- The modified algebra is spanned by negative words followed by positive words.
This establishes only the surjectivity part of triangular decomposition. -/
theorem triangularSpan_eq_modified : triangularSpan D q π = (modified D q π).toSubmodule := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨a, b, ν, μ, rfl⟩
    exact (modified D q π).mul_mem
      (block_le_modified D q π _ _ (halfWord_mem_block D q π false a ν))
      (block_le_modified D q π _ _ (halfWord_mem_block D q π true b μ))
  · change (⨆ b : X × X, block D q π b.1 b.2) ≤ triangularSpan D q π
    refine iSup_le fun b x hx ↦ ?_
    rw [← hx.2]
    exact mul_one_mem_triangularSpan D q π x b.2

/-- A matched negative-positive word with right weight `μ`. -/
def normalWord (a b : List I) (μ : X) : CoveringUDot k D q π :=
  halfWord D q π false a (μ + halfWeight D true (PreF.wordWeight b)) *
    halfWord D q π true b μ

/-- Matched negative-positive words span the actual modified algebra. No linear independence
is asserted. -/
theorem span_normalWords_eq_modified :
    Submodule.span k {z | ∃ (a b : List I) (μ : X), z = normalWord D q π a b μ} =
      (modified D q π).toSubmodule := by
  rw [← triangularSpan_eq_modified]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨a, b, μ, rfl⟩
    exact halfWords_mem_triangularSpan D q π a b _ μ
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨a, b, ν, μ, rfl⟩
    by_cases h : ν = μ + halfWeight D true (PreF.wordWeight b)
    · rw [h]
      exact Submodule.subset_span ⟨a, b, μ, rfl⟩
    · rw [mul_eq_zero_of_mem_block D q π (halfWord_mem_block D q π false a ν)
        (halfWord_mem_block D q π true b μ) h]
      exact Submodule.zero_mem _

/-- The triangular spanning theorem expressed using the actual Serre half maps. -/
theorem span_halfProducts_eq_modified :
    Submodule.span k {z | ∃ (x y : D.serreF q π) (ν μ : X),
      z = (negativeHalf D q π ν x : CoveringUDot k D q π) *
        (positiveHalf D q π μ y : CoveringUDot k D q π)} =
      (modified D q π).toSubmodule := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨x, y, ν, μ, rfl⟩
    exact (modified D q π).mul_mem (negativeHalf D q π ν x).property
      (positiveHalf D q π μ y).property
  · rw [← triangularSpan_eq_modified]
    refine Submodule.span_le.mpr ?_
    rintro z ⟨a, b, ν, μ, rfl⟩
    apply Submodule.subset_span
    refine ⟨D.toSerreF q π (PreF.monomial k a), D.toSerreF q π (PreF.monomial k b), ν, μ, ?_⟩
    change _ = halfMap D q π false ν _ * halfMap D q π true μ _
    rw [halfMap_monomial, halfMap_monomial]

end OddMath.CoveringQuantum.UDot
