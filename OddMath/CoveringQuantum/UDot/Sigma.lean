import OddMath.CoveringQuantum.UDot.HalfWeights

/-!
# The linear E/F-swapping antiautomorphism

The map `σ` used in the proof of [BE2, arXiv:1701.04133v2, Theorem 10.1]
is constructed by descent through the relations of §9. It fixes weight idempotents,
exchanges the two Chevalley families, and reverses products without changing scalars.
The construction works over a commutative ring with a unit `q` and `π² = 1`;
no finiteness or bar-consistency assumption is needed. `sigmaModifiedEquiv` acts
on the nonunital modified algebra, not just its unital envelope.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open Finset MulOpposite

variable {k I X : Type*} [CommRing k] [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- The generator assignment, including the changed right weight. -/
def sigmaGen : Gen I X → CoveringUDot k D q π
  | .one μ => one D q π μ
  | .e i μ => F D q π i (μ + D.α i)
  | .f i μ => E D q π i (μ - D.α i)

/-- The generator assignment extended to the free algebra with opposite codomain. -/
def sigmaFree : Free k I X →ₐ[k] (CoveringUDot k D q π)ᵐᵒᵖ :=
  FreeAlgebra.lift k fun g ↦ op (sigmaGen D q π g)

private def sigmaU (x : Free k I X) : CoveringUDot k D q π := (sigmaFree D q π x).unop

variable {D q π}

private theorem sigmaU_mul (x y : Free k I X) :
    sigmaU D q π (x * y) = sigmaU D q π y * sigmaU D q π x := by simp [sigmaU]

private theorem sigmaU_sub (x y : Free k I X) :
    sigmaU D q π (x - y) = sigmaU D q π x - sigmaU D q π y := by simp [sigmaU]

private theorem sigmaU_smul (c : k) (x : Free k I X) :
    sigmaU D q π (c • x) = c • sigmaU D q π x := by simp [sigmaU]

private theorem sigmaU_zero : sigmaU D q π (0 : Free k I X) = 0 := by simp [sigmaU]

private theorem sigmaU_sum {ι : Type*} (s : Finset ι) (f : ι → Free k I X) :
    sigmaU D q π (∑ x ∈ s, f x) = ∑ x ∈ s, sigmaU D q π (f x) := by
  simp only [sigmaU, map_sum]
  exact map_sum (opAddEquiv : CoveringUDot k D q π ≃+ _).symm _ _

private theorem sigmaU_one (μ : X) : sigmaU D q π (Free.one k μ) = one D q π μ := by
  simp [sigmaU, sigmaFree, Free.one, sigmaGen]

private theorem sigmaU_E (i : I) (μ : X) :
    sigmaU D q π (Free.E k i μ) = F D q π i (μ + D.α i) := by
  simp [sigmaU, sigmaFree, Free.E, sigmaGen]

private theorem sigmaU_F (i : I) (μ : X) :
    sigmaU D q π (Free.F k i μ) = E D q π i (μ - D.α i) := by
  simp [sigmaU, sigmaFree, Free.F, sigmaGen]

private theorem sigmaU_epow (i : I) (n : ℕ) (μ : X) :
    sigmaU D q π (epow D i n μ) = mk D q π (fpow D i n (μ + n • D.α i)) := by
  induction n with
  | zero => simpa only [epow, fpow, zero_smul, add_zero, one] using (sigmaU_one (D := D) (q := q) (π := π) μ)
  | succ n ih =>
    rw [epow, sigmaU_mul, ih, sigmaU_E, mk_fpow_succ', succ_nsmul,
      ← add_assoc, add_sub_cancel_right]

private theorem sigmaU_fpow (i : I) (n : ℕ) (μ : X) :
    sigmaU D q π (fpow D i n μ) = mk D q π (epow D i n (μ - n • D.α i)) := by
  induction n with
  | zero => simpa only [epow, fpow, zero_smul, sub_zero, one] using (sigmaU_one (D := D) (q := q) (π := π) μ)
  | succ n ih =>
    rw [fpow, sigmaU_mul, ih, sigmaU_F, mk_epow_succ', succ_nsmul,
      ← sub_sub, sub_add_cancel]

/-- Every defining relation is respected by the E/F swap into the opposite algebra. -/
theorem sigmaFree_rel {x y : Free k I X} (hπ : π ^ 2 = 1) (h : Rel D q π x y) :
    sigmaFree D q π x = sigmaFree D q π y := by
  apply unop_injective
  change sigmaU D q π x = sigmaU D q π y
  cases h with
  | one_one μ ν =>
    rw [sigmaU_mul, sigmaU_one, sigmaU_one, one_mul_one]
    split_ifs with h₁ h₂ h₂
    · rw [sigmaU_one, h₁]
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · rw [sigmaU_zero]
  | one_E i μ => rw [sigmaU_mul, sigmaU_E, sigmaU_one, F_mul_one_self]
  | E_one i μ =>
    rw [sigmaU_mul, sigmaU_E, sigmaU_one, one_mul_F, add_sub_cancel_right]
    simp only [ite_true, eq_self]
  | one_F i μ => rw [sigmaU_mul, sigmaU_F, sigmaU_one, E_mul_one_self]
  | F_one i μ =>
    rw [sigmaU_mul, sigmaU_F, sigmaU_one, one_mul_E, sub_add_cancel]
    simp only [ite_true, eq_self]
  | comm i j μ =>
    let ν := μ + D.α i - D.α j
    have w1 : μ - D.α j = ν - D.α i := by dsimp [ν]; abel
    have w2 : μ - D.α j + D.α i = ν := by dsimp [ν]; abel
    have w3 : μ + D.α i = ν + D.α j := by dsimp [ν]; abel
    rw [sigmaU_sub, sigmaU_mul, sigmaU_smul, sigmaU_mul, sigmaU_E, sigmaU_F,
      sigmaU_E, sigmaU_F, w2, w3, w1, add_sub_cancel_right, mul_comm (D.parity i), comm_rel]
    split_ifs with h₁ h₂ h₂
    · subst h₁
      simp only [ν, add_sub_cancel_right, sigmaU_smul, sigmaU_one]
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · rw [sigmaU_zero]
  | serreE i j μ h =>
    rw [sigmaU_zero, serreE, sigmaU_sum]
    set N := D.serreDeg i j
    set ν := μ + N • D.α i + D.α j
    set fw : ℕ → Free k I X := fun s ↦
      fpow D i (N - s) (ν - s • D.α i - D.α j) * Free.F k j (ν - s • D.α i) * fpow D i s ν
    have key : ∀ r ∈ range (N + 1), sigmaU D q π (D.serreCoeff q π i j r •
        (epow D i (N - r) (μ + r • D.α i + D.α j) * Free.E k j (μ + r • D.α i) * epow D i r μ)) =
        D.serreCoeff q π i j (N - (N - r)) • mk D q π (fw (N - r)) := by
      intro r hr
      obtain ⟨m, hm⟩ : ∃ m, N = r + m := ⟨N - r, by have := mem_range.1 hr; omega⟩
      have e1 : N - r = m := by omega
      have e2 : N - m = r := by omega
      obtain ⟨w1, w2, w3⟩ := weight_aux μ (D.α i) (D.α j) r m
      simp only [fw, e1, e2]
      dsimp only [ν]
      rw [hm, sigmaU_smul, sigmaU_mul, sigmaU_mul, sigmaU_epow, sigmaU_E,
        sigmaU_epow, w1, w2, w3, map_mul, map_mul, mul_assoc]
      rfl
    rw [sum_congr rfl key]
    have hreflect := sum_range_reflect (fun s ↦ D.serreCoeff q π i j (N - s) •
      mk D q π (fw s)) (N + 1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [hreflect]
    have key2 : ∀ s ∈ range (N + 1), D.serreCoeff q π i j (N - s) • mk D q π (fw s) =
        ((-1) ^ N * D.pii π i ^ (N * (D.parity j).val + N.choose 2)) •
          mk D q π (D.serreCoeff q π i j s • fw s) := by
      intro s hs
      rw [D.serreCoeff_reflect q π hπ h (Nat.lt_succ_iff.1 (mem_range.1 hs)), map_smul, smul_smul]
    rw [sum_congr rfl key2, ← smul_sum, ← map_sum]
    have : ∑ s ∈ range (N + 1), D.serreCoeff q π i j s • fw s = serreF D q π i j ν := rfl
    rw [this, serreF_rel D q π h, smul_zero]
  | serreF i j μ h =>
    rw [sigmaU_zero, serreF, sigmaU_sum]
    set N := D.serreDeg i j
    set ν := μ - N • D.α i - D.α j
    set ew : ℕ → Free k I X := fun s ↦
      epow D i (N - s) (ν + s • D.α i + D.α j) * Free.E k j (ν + s • D.α i) * epow D i s ν
    have key : ∀ r ∈ range (N + 1), sigmaU D q π (D.serreCoeff q π i j r •
        (fpow D i (N - r) (μ - r • D.α i - D.α j) * Free.F k j (μ - r • D.α i) * fpow D i r μ)) =
        D.serreCoeff q π i j (N - (N - r)) • mk D q π (ew (N - r)) := by
      intro r hr
      obtain ⟨m, hm⟩ : ∃ m, N = r + m := ⟨N - r, by have := mem_range.1 hr; omega⟩
      have e1 : N - r = m := by omega
      have e2 : N - m = r := by omega
      obtain ⟨w1, w2, w3⟩ := weight_aux' μ (D.α i) (D.α j) r m
      simp only [ew, e1, e2]
      dsimp only [ν]
      rw [hm, sigmaU_smul, sigmaU_mul, sigmaU_mul, sigmaU_fpow, sigmaU_F,
        sigmaU_fpow, w1, w2, w3, map_mul, map_mul, mul_assoc]
      rfl
    rw [sum_congr rfl key]
    have hreflect := sum_range_reflect (fun s ↦ D.serreCoeff q π i j (N - s) •
      mk D q π (ew s)) (N + 1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [hreflect]
    have key2 : ∀ s ∈ range (N + 1), D.serreCoeff q π i j (N - s) • mk D q π (ew s) =
        ((-1) ^ N * D.pii π i ^ (N * (D.parity j).val + N.choose 2)) •
          mk D q π (D.serreCoeff q π i j s • ew s) := by
      intro s hs
      rw [D.serreCoeff_reflect q π hπ h (Nat.lt_succ_iff.1 (mem_range.1 hs)), map_smul, smul_smul]
    rw [sum_congr rfl key2, ← smul_sum, ← map_sum]
    have : ∑ s ∈ range (N + 1), D.serreCoeff q π i j s • ew s = serreE D q π i j ν := rfl
    rw [this, serreE_rel D q π h, smul_zero]

variable (D q π)

/-- The linear E/F-swapping antiautomorphism on the presentation quotient. -/
def sigma (hπ : π ^ 2 = 1) : CoveringUDot k D q π →ₐ[k] (CoveringUDot k D q π)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨sigmaFree D q π, fun _ _ h ↦ sigmaFree_rel hπ h⟩

variable {D q π}

@[simp] theorem sigma_mk (hπ : π ^ 2 = 1) (x : Free k I X) :
    sigma D q π hπ (mk D q π x) = sigmaFree D q π x := by
  simp only [sigma, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem sigma_one (hπ : π ^ 2 = 1) (μ : X) :
    (sigma D q π hπ (one D q π μ)).unop = one D q π μ := by
  rw [one, sigma_mk]; exact sigmaU_one μ

@[simp] theorem sigma_E (hπ : π ^ 2 = 1) (i : I) (μ : X) :
    (sigma D q π hπ (E D q π i μ)).unop = F D q π i (μ + D.α i) := by
  rw [E, sigma_mk]; exact sigmaU_E i μ

@[simp] theorem sigma_F (hπ : π ^ 2 = 1) (i : I) (μ : X) :
    (sigma D q π hπ (F D q π i μ)).unop = E D q π i (μ - D.α i) := by
  rw [F, sigma_mk]; exact sigmaU_F i μ

theorem sigma_smul (hπ : π ^ 2 = 1) (c : k) (x : CoveringUDot k D q π) :
    (sigma D q π hπ (c • x)).unop = c • (sigma D q π hπ x).unop := by simp

theorem sigma_mul (hπ : π ^ 2 = 1) (x y : CoveringUDot k D q π) :
    (sigma D q π hπ (x * y)).unop = (sigma D q π hπ y).unop * (sigma D q π hπ x).unop := by simp

/-- Applying the swap twice is the identity on the quotient, including its adjoined scalars. -/
theorem sigma_sigma (hπ : π ^ 2 = 1) (x : CoveringUDot k D q π) :
    (sigma D q π hπ (sigma D q π hπ x).unop).unop = x := by
  obtain ⟨y, rfl⟩ := mk_surjective D q π x
  induction y using FreeAlgebra.induction with
  | grade0 c => simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, unop_op]
  | grade1 g =>
    cases g with
    | one μ => rw [← Free.one, ← one, sigma_one, sigma_one]
    | e i μ => rw [← Free.E, ← E, sigma_E, sigma_F, add_sub_cancel_right]
    | f i μ => rw [← Free.F, ← F, sigma_F, sigma_E, sub_add_cancel]
  | add a b ha hb => simpa only [map_add, unop_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb => rw [map_mul, sigma_mul, sigma_mul, ha, hb]

/-- The quotient map into the opposite algebra is bijective. -/
theorem sigma_bijective (hπ : π ^ 2 = 1) : Function.Bijective (sigma D q π hπ) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z ↦ (sigma D q π hπ z.unop).unop) h
    simpa only [sigma_sigma] using h'
  · intro y
    refine ⟨(sigma D q π hπ y.unop).unop, unop_injective ?_⟩
    exact sigma_sigma hπ y.unop

/-- `σ` interchanges the left and right weight indices. -/
theorem sigma_mem_block {μ η : X} {x : CoveringUDot k D q π} (hπ : π ^ 2 = 1)
    (hx : x ∈ block D q π μ η) : (sigma D q π hπ x).unop ∈ block D q π η μ := by
  constructor
  · have := congrArg (fun z ↦ (sigma D q π hπ z).unop) hx.2
    simpa only [sigma_mul, sigma_one] using this
  · have := congrArg (fun z ↦ (sigma D q π hπ z).unop) hx.1
    simpa only [sigma_mul, sigma_one] using this

/-- The finite block sum is preserved; the adjoined scalar unit is not used. -/
theorem sigma_mem_modified {x : CoveringUDot k D q π} (hπ : π ^ 2 = 1)
    (hx : x ∈ modified D q π) : (sigma D q π hπ x).unop ∈ modified D q π := by
  refine Submodule.iSup_induction (fun b : X × X ↦ block D q π b.1 b.2)
    (motive := fun x ↦ (sigma D q π hπ x).unop ∈ modified D q π) hx ?_ ?_ ?_
  · intro b x hx
    exact block_le_modified D q π b.2 b.1 (sigma_mem_block hπ hx)
  · simp only [map_zero, unop_zero]; exact zero_mem _
  · intro x y hx hy
    simpa only [map_add, unop_add] using add_mem hx hy

variable (D q π)

/-- The actual linear restriction to the nonunital modified algebra. -/
def sigmaModified (hπ : π ^ 2 = 1) : modified D q π →ₗ[k] modified D q π where
  toFun x := ⟨(sigma D q π hπ x).unop, sigma_mem_modified hπ x.property⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_sigmaModified (hπ : π ^ 2 = 1) (x : modified D q π) :
    (sigmaModified D q π hπ x : CoveringUDot k D q π) = (sigma D q π hπ x).unop := rfl

/-- The genuine nonunital restriction reverses multiplication. -/
theorem sigmaModified_mul (hπ : π ^ 2 = 1) (x y : modified D q π) :
    sigmaModified D q π hπ (x * y) = sigmaModified D q π hπ y * sigmaModified D q π hπ x :=
  Subtype.ext (sigma_mul (D := D) (q := q) hπ x.val y.val)

@[simp] theorem sigmaModified_sigmaModified (hπ : π ^ 2 = 1) (x : modified D q π) :
    sigmaModified D q π hπ (sigmaModified D q π hπ x) = x :=
  Subtype.ext (sigma_sigma (D := D) (q := q) hπ x.val)

/-- The involutive linear E/F swap on the modified covering algebra. -/
def sigmaModifiedEquiv (hπ : π ^ 2 = 1) : modified D q π ≃ₗ[k] modified D q π :=
  { sigmaModified D q π hπ with
    invFun := sigmaModified D q π hπ
    left_inv := sigmaModified_sigmaModified D q π hπ
    right_inv := sigmaModified_sigmaModified D q π hπ }

@[simp] theorem sigmaModifiedEquiv_apply (hπ : π ^ 2 = 1) (x : modified D q π) :
    sigmaModifiedEquiv D q π hπ x = sigmaModified D q π hπ x := rfl

/-- The linear equivalence is anti-multiplicative, not multiplicative. -/
theorem sigmaModifiedEquiv_mul (hπ : π ^ 2 = 1) (x y : modified D q π) :
    sigmaModifiedEquiv D q π hπ (x * y) =
      sigmaModifiedEquiv D q π hπ y * sigmaModifiedEquiv D q π hπ x :=
  sigmaModified_mul D q π hπ x y

/-- Concatenating half words uses the weight of the right-hand word. -/
theorem halfWord_append (positive : Bool) (v w : List I) (μ : X) :
    halfWord D q π positive (v ++ w) μ =
      halfWord D q π positive v (μ + halfWeight D positive (PreF.wordWeight w)) *
        halfWord D q π positive w μ := by
  induction v with
  | nil => exact (halfWord_mem_block D q π positive w μ).1.symm
  | cons i v ih =>
    simp only [List.cons_append, halfWord, PreF.wordWeight_append, halfWeight_add, ih,
      mul_assoc, add_assoc]
    rw [add_comm (halfWeight D positive (PreF.wordWeight v))]

private theorem halfWord_singleton (positive : Bool) (i : I) (μ : X) :
    halfWord D q π positive [i] μ = halfGen D q π positive i μ := by
  simp only [halfWord, PreF.wordWeight_nil, halfWeight_zero, add_zero]
  exact (halfGen_mem_block D q π positive i μ).2

omit [DecidableEq I] [DecidableEq X] in
private theorem halfRoot_not (positive : Bool) (i : I) :
    halfRoot D (!positive) i = -halfRoot D positive i := by
  cases positive <;> simp [halfRoot]

private theorem sigma_halfGen (hπ : π ^ 2 = 1) (positive : Bool) (i : I) (μ : X) :
    (sigma D q π hπ (halfGen D q π positive i μ)).unop =
      halfGen D q π (!positive) i (μ + halfRoot D positive i) := by
  cases positive <;> simp [halfGen, halfRoot, sub_eq_add_neg]

/-- `σ` reverses a half word, exchanges its sign, and moves the right weight to
its original left endpoint. There is no scalar factor. -/
theorem sigma_halfWord (hπ : π ^ 2 = 1) (positive : Bool) (w : List I) (μ : X) :
    (sigma D q π hπ (halfWord D q π positive w μ)).unop =
      halfWord D q π (!positive) w.reverse
        (μ + halfWeight D positive (PreF.wordWeight w)) := by
  induction w with
  | nil => simp [halfWord]
  | cons i w ih =>
    rw [halfWord, sigma_mul, ih, sigma_halfGen, List.reverse_cons, halfWord_append,
      halfWord_singleton]
    simp only [PreF.wordWeight_cons, PreF.wordWeight_nil, halfWeight_add, halfWeight_single,
      add_zero, halfRoot_not]
    congr 2 <;> abel

/-- On a genuine positive half-map value, `σ` gives the reversed negative half word. -/
theorem sigmaModified_positiveHalf_monomial (hπ : π ^ 2 = 1) (w : List I) (μ : X) :
    sigmaModified D q π hπ (positiveHalf D q π μ (D.toSerreF q π (PreF.monomial k w))) =
      negativeHalf D q π (μ + halfWeight D true (PreF.wordWeight w))
        (D.toSerreF q π (PreF.monomial k w.reverse)) := by
  apply Subtype.ext
  change (sigma D q π hπ (halfMap D q π true μ
    (D.toSerreF q π (PreF.monomial k w)))).unop = halfMap D q π false _ _
  simpa only [halfMap_monomial, Bool.not_true] using sigma_halfWord D q π hπ true w μ

/-- The analogous formula on the actual negative half map. -/
theorem sigmaModified_negativeHalf_monomial (hπ : π ^ 2 = 1) (w : List I) (μ : X) :
    sigmaModified D q π hπ (negativeHalf D q π μ (D.toSerreF q π (PreF.monomial k w))) =
      positiveHalf D q π (μ + halfWeight D false (PreF.wordWeight w))
        (D.toSerreF q π (PreF.monomial k w.reverse)) := by
  apply Subtype.ext
  change (sigma D q π hπ (halfMap D q π false μ
    (D.toSerreF q π (PreF.monomial k w)))).unop = halfMap D q π true _ _
  simpa only [halfMap_monomial, Bool.not_false] using sigma_halfWord D q π hπ false w μ

end OddMath.CoveringQuantum.UDot
