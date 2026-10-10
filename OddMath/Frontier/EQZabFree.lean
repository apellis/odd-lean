import OddMath.Frontier.EQZabFrobenius

/-!
# Ellis–Qi, Definition 4.9: `Z^∨_{a,b}` is free of rank one over `OΛ_a ⊗ OΛ_b` on `w₀ ∘ z^∨`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Definition 4.9 and (4.26) (printed numbering).

Rank `n + 2 = a + b`. In the literal model `Z_{a,b} = OΛ̃_a ⊠ OΛ̃_b · z` (`EQZab.tosymAB`), the
right action of `h ∈ OΛ_{a+b}` is right multiplication by `(θ ∘ w₀)(h)` and the left action of
`u ∈ OΛ_a ⊗ OΛ_b` is left multiplication by `τ(u) ∈ OΛ̃_a ⊠ OΛ̃_b`. The dual
`Z^∨_{a,b} = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})` (right-linear maps) is a right
`OΛ_a ⊗ OΛ_b`-module by `(φ · u)(x) = φ(u x)`. Ellis–Qi assert `Z^∨_{a,b} = z^∨ · (OΛ_a ⊗ OΛ_b)`, free
of rank one, for the trace `z^∨ = θ ∘ ∂_{a,b}` (`EQZab.trace`). By erratum [EQ] 19 the printed `z^∨` is
only `w₀`-semilinear; the corrected trace `w₀ ∘ z^∨` is right linear (`EQZab.trace_linear`).

* `def_4_9_mem` (the module `(w₀ ∘ z^∨) · (OΛ_a ⊗ OΛ_b)` lies in `Z^∨_{a,b}`): for every `g ∈ OΛ̃_a ⊠ OΛ̃_b`,
  `x ↦ w₀(z^∨(g x))` is additive, right `OΛ_{a+b}`-linear and `OΛ_{a+b}`-valued;
* **Definition 4.9, freeness** (`def_4_9_free`): every right-linear `OΛ_{a+b}`-valued additive
  `φ : Z_{a,b} → OΛ_{a+b}` is `x ↦ w₀(z^∨(g x))` for a unique `g ∈ OΛ̃_a ⊠ OΛ̃_b`; i.e. `Z^∨_{a,b}` is free
  of rank one over `OΛ_a ⊗ OΛ_b` on `w₀ ∘ z^∨` (the case `g = 1`).
* The differential (4.26) of the generator is Corollary 4.10 (`EQZab.cor_4_10`), which holds for
  `w₀ ∘ z^∨` as well since `d ∘ w₀ = w₀ ∘ d`.

The proof: `T = w₀ ∘ θ ∘ ∂_{a,b}` pairs the right basis `s̃_μ(y) z` of `Z_{a,b}` (Corollary 4.8) with the
left multipliers `rev(s_α)(x)` (EKL (4.35), `EQZab.pairing`), and `Γ(k)` slides through `∂_{a,b}` for
`k ∈ OΛ̃_{a+b}` (`EQFrob.pdAB_gamma_mul`), producing all of `OΛ_{a+b}` as coefficients; injectivity uses
the left spanning `OΛ̃_a ⊠ OΛ̃_b = Σ_μ Γ(OΛ̃_{a+b}) s̃_μ(y)` (`EQFrob.RT_left_span`).
-/

namespace OddMath.Frontier.EQFrob

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (parityInv longestPerm theta grading osym twistRev)
open BoxComplement BoxPartitionCount

noncomputable section

local instance (priority := high) freeNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) freeNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-- `rev` preserves the grading. -/
theorem rev_mem_grading {N : ℕ} {k : ℤ} {f : SkewPolynomial N} (hf : f ∈ grading N k) :
    EQZab.rev f ∈ grading N k := by
  classical
  have hf' : f = ∑ c ∈ f.support, f c • monomial c 1 := by
    conv_lhs => rw [← Finsupp.sum_single f]
    simp [Finsupp.sum, OddMath.SkewPolynomial.monomial]
  rw [hf', EQZab.rev_sum]
  refine AddSubgroup.sum_mem _ fun c hc => ?_
  obtain ⟨ε, -, hε⟩ := EQZab.rev_monomial c
  rw [EQZab.rev_zsmul, hε, smul_smul]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have h := EQSkewDifferential.single_mem_grading c 1
  rwa [hf c hc] at h

section Free

variable {a b : ℕ} (hab : a + b = n + 2)

/-- The corrected trace `w₀ ∘ θ ∘ ∂_{a,b}` in rank `n + 2`. -/
def T (n a b : ℕ) (X : SkewPolynomial (n+2)) : SkewPolynomial (n+2) :=
  longestPerm (n+2) (theta (n+2) (EQZab.pdAB n a b X))

theorem T_add (X Y : SkewPolynomial (n+2)) : T n a b (X + Y) = T n a b X + T n a b Y := by
  simp only [T, map_add]

theorem T_zsmul (c : ℤ) (X : SkewPolynomial (n+2)) : T n a b (c • X) = c • T n a b X := by
  simp only [T, map_zsmul]

theorem T_sum {ι : Type*} (s : Finset ι) (X : ι → SkewPolynomial (n+2)) :
    T n a b (∑ i ∈ s, X i) = ∑ i ∈ s, T n a b (X i) := by
  simp only [T, map_sum]

theorem T_sub (X Y : SkewPolynomial (n+2)) : T n a b (X - Y) = T n a b X - T n a b Y := by
  simp only [T, map_sub]

/-- The coefficient map `k ↦ w₀ θ (w₀^{EKL} k)` on `OΛ̃_{a+b}`. -/
def Lam (k : SkewPolynomial (n+2)) : SkewPolynomial (n+2) :=
  longestPerm (n+2) (theta (n+2) (SignedPermutation.skewAction (LongestElementary.longest (n+2)) k))

theorem Lam_kernel {k : SkewPolynomial (n+2)} (hk : k ∈ OddSymmetricKernel.kernelSubring n) :
    ∃ c ∈ osym (a+b), Lam k = EQZab.castHom hab c := by
  obtain ⟨d, hd, hdk⟩ := EQZab.kernel_eq_castHom hab (LongestElementary.action_mem_kernel n k hk)
  refine ⟨d, hd, ?_⟩
  rw [Lam, hdk, twistRev, RingHom.comp_apply, EQZab.castHom_theta, EQSchur.theta_theta,
    EQZab.castHom_longestPerm, EQSchur.longestPerm_longestPerm]

theorem Lam_surj {c : SkewPolynomial (a+b)} (hc : c ∈ osym (a+b)) :
    ∃ k ∈ OddSymmetricKernel.kernelSubring n, Lam k = EQZab.castHom hab c := by
  refine ⟨SignedPermutation.skewAction (LongestElementary.longest (n+2))
    (EQZab.castHom hab (twistRev (a+b) c)),
    LongestElementary.action_mem_kernel n _ (EQZab.castHom_twistRev_mem hab hc), ?_⟩
  rw [Lam, LongestElementary.action_involutive, twistRev, RingHom.comp_apply, EQZab.castHom_theta,
    EQSchur.theta_theta, EQZab.castHom_longestPerm, EQSchur.longestPerm_longestPerm]

theorem Lam_eq_zero {k : SkewPolynomial (n+2)} (h : Lam k = 0) : k = 0 := by
  have e := congrArg (fun z => SignedPermutation.skewAction (LongestElementary.longest (n+2))
    (theta (n+2) (longestPerm (n+2) z))) h
  simp only [Lam, EQSchur.longestPerm_longestPerm, EQSchur.theta_theta,
    LongestElementary.action_involutive, map_zero] at e
  exact e

/-- `Γ(k)` slides through `T`, producing the coefficient `Λ(k)`. -/
theorem T_gamma {k : SkewPolynomial (n+2)} (hk : k ∈ OddSymmetricKernel.kernelSubring n)
    {F : SkewPolynomial (n+2)} (hF : F ∈ RT hab) :
    T n a b (gammaN hab k * F) = Lam k * T n a b F := by
  rw [T, pdAB_gamma_mul hab hk (RT_blocksym hab hF), map_mul, map_mul, Lam, T]

/-- `T` is right linear over `OΛ_{a+b}` acting through `θ ∘ w₀`. -/
theorem T_mul_twistRev (F : SkewPolynomial (n+2)) {c : SkewPolynomial (a+b)} (hc : c ∈ osym (a+b)) :
    T n a b (F * EQZab.castHom hab (twistRev (a+b) c)) = T n a b F * EQZab.castHom hab c := by
  rw [T, EQZab.pdAB_mul_kernel _ _ _ (EQZab.castHom_twistRev_mem hab hc), map_mul, map_mul, T,
    twistRev, RingHom.comp_apply, EQZab.castHom_theta, EQSchur.theta_theta, EQZab.castHom_longestPerm,
    EQSchur.longestPerm_longestPerm]

/-- The right basis element `s̃_μ(y) z` in rank `n + 2`. -/
abbrev Yb (hab : a + b = n + 2) (μ : Fin b → ℕ) : SkewPolynomial (n+2) :=
  ProjectorRank.place a (EQThick.right_le hab) (EQSchur.twisted b μ)

/-- The left multiplier `rev(s_α)(x)`. -/
abbrev Sb (hab : a + b = n + 2) (α : Fin a → ℕ) : SkewPolynomial (n+2) :=
  EQZab.schurQ n a (EQThick.left_le hab) α

theorem Yb_eq (μ : Fin b → ℕ) : Yb hab μ = EQZab.castHom hab (EQZab.inclY a b (EQSchur.twisted b μ)) := by
  rw [EQZab.castHom_inclY]

theorem inclY_twisted_mem (μ : Fin b → ℕ) : EQZab.inclY a b (EQSchur.twisted b μ) ∈ EQZab.tosymAB a b :=
  ⟨EQZab.inclY a b (EQSchur.untwisted b μ), EQZab.sY_mem μ, EQZab.tauAB_inclY_untwisted μ⟩

theorem Yb_mem (μ : Fin b → ℕ) : Yb hab μ ∈ RT hab :=
  ⟨_, inclY_twisted_mem μ, (Yb_eq hab μ).symm⟩

theorem Sb_mem (α : Fin a → ℕ) : Sb hab α ∈ RT hab := by
  rcases a with _ | _ | m
  · show ProjectorRank.place 0 _ 1 ∈ RT hab
    rw [map_one]; exact one_mem _
  · show ProjectorRank.place 0 _ (generator 0 ^ α 0) ∈ RT hab
    rw [map_pow]
    refine pow_mem ?_ _
    have h := place_left_elem_mem hab 1
    rwa [SmallRank.elementaryPoly_one_one] at h
  · show ProjectorRank.place 0 _ (EQZab.rev (ThickDots.schur α)) ∈ RT hab
    have hk : EQZab.rev (ThickDots.schur α) ∈ OddSymmetricKernel.kernelSubring m :=
      EQZab.rev_mem_kernel (ThickDots.schur_mem_kernel α)
    rw [ElementaryGeneration.kernel_eq_elementaryClosure] at hk
    generalize EQZab.rev (ThickDots.schur α) = x at hk ⊢
    induction hk using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨k, -, -, rfl⟩ := hx
      exact place_left_elem_mem hab k
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact one_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem generator_pow_mem_grading {N : ℕ} (j : Fin N) (e : ℕ) :
    (generator j : SkewPolynomial N) ^ e ∈ grading N e := by
  induction e with
  | zero => rw [pow_zero]; exact EQSkewDifferential.one_mem_grading'
  | succ e ih =>
    rw [pow_succ]
    have h := EQSkewDifferential.mul_mem_grading' ih (EQSkewDifferential.generator_mem_grading j)
    rwa [show ((e : ℕ) : ℤ) + 1 = ((e + 1 : ℕ) : ℤ) by push_cast; ring] at h

theorem Sb_graded (α : Fin a → ℕ) :
    ∃ (f : SkewPolynomial a) (i : ℤ), f ∈ grading a i ∧
      Sb hab α = ProjectorRank.place 0 (EQThick.left_le hab) f := by
  rcases a with _ | _ | m
  · exact ⟨1, 0, EQSkewDifferential.one_mem_grading', rfl⟩
  · exact ⟨generator 0 ^ α 0, _, generator_pow_mem_grading 0 (α 0), rfl⟩
  · have hs : ThickDots.schur α ∈ grading (m+2) (EQSkewDifferential.totalDeg α) := by
      rw [← EQSchur.twisted_eq_ekl, EQSchur.twisted_eq_theta_untwisted]
      exact EQFix.theta_mem_grading (EQFix.untwisted_mem_grading _ α)
    exact ⟨EQZab.rev (ThickDots.schur α), _, rev_mem_grading hs, rfl⟩

/-- **The pairing** (EKL (4.35)): `T(s̃_μ(y) rev(s_α)(x)) = ± δ_{μ, α̂}`. -/
theorem T_Y_S {α : Fin a → ℕ} (hα : α ∈ box a b) :
    ∃ σ : ℤ, EQZab.IsSign σ ∧ ∀ μ ∈ box b a,
      T n a b (Yb hab μ * Sb hab α) = if μ = hat b α then σ • 1 else 0 := by
  have hαb := mem_box.1 hα
  refine ⟨(-1 : ℤ) ^ (b.choose 4 + (∑ j, hat b α j) * b.choose 2) *
      (-1 : ℤ) ^ ThickBubble.bubbleSign a b α, (EQZab.IsSign.pow _).mul (EQZab.IsSign.pow _),
      fun μ hμ => ?_⟩
  have hμb := mem_box.1 hμ
  have hq := EQZab.dualQ_twisted (n := n) (a := a) (b := b) (EQThick.right_le hab) μ
  have hp : Yb hab μ = (-1 : ℤ) ^ (b.choose 4 + (∑ j, μ j) * b.choose 2) •
      EQZab.dualQ n a b (EQThick.right_le hab) μ := by
    rw [hq, smul_smul, (EQZab.IsSign.pow _).mul_self, one_smul]
  rw [hp, smul_mul_assoc, T_zsmul, T, EQZab.pairing hab hαb.1 hαb.2 hμb.1 hμb.2]
  split_ifs with h
  · subst h
    rw [EQZab.theta_smul_one, map_zsmul, map_one, smul_smul]
  · rw [zero_smul, map_zero, map_zero, smul_zero]

/-- The pairing in the other order: `T(rev(s_α)(x) s̃_ν(y)) = ± δ_{ν, α̂}`. -/
theorem T_S_Y {α : Fin a → ℕ} (hα : α ∈ box a b) :
    ∃ σ : ℤ, EQZab.IsSign σ ∧ ∀ ν ∈ box b a,
      T n a b (Sb hab α * Yb hab ν) = if ν = hat b α then σ • 1 else 0 := by
  obtain ⟨σ, hσ, hT⟩ := T_Y_S hab hα
  obtain ⟨f, i, hf, hS⟩ := Sb_graded hab α
  refine ⟨(-1 : ℤ) ^ (i.natAbs * ∑ j, hat b α j) * σ, (EQZab.IsSign.pow _).mul hσ, fun ν hν => ?_⟩
  have hc := place_right_mul_place_left hab hf ((parityInv b)^[i.natAbs] (EQSchur.twisted b ν))
  rw [iterate_parityInv_iterate, iterate_parityInv_of_parity _ _ (EQSchur.parityInv_twisted ν),
    map_zsmul, smul_mul_assoc, ← hS] at hc
  rw [← hc, T_zsmul, hT ν hν]
  split_ifs with h
  · subst h; rw [smul_smul]
  · rw [smul_zero]

/-- **Existence**: prescribed `OΛ_{a+b}`-values on the basis `s̃_ν(y) z` are attained by some `g`. -/
theorem T_exists (v : (Fin b → ℕ) → SkewPolynomial (n+2))
    (hv : ∀ ν, ∃ c ∈ osym (a+b), v ν = EQZab.castHom hab c) :
    ∃ X ∈ RT hab, ∀ ν ∈ box b a, T n a b (X * Yb hab ν) = v ν := by
  classical
  have hS : ∀ α, ∃ σ : ℤ, EQZab.IsSign σ ∧ (α ∈ box a b → ∀ ν ∈ box b a,
      T n a b (Sb hab α * Yb hab ν) = if ν = hat b α then σ • 1 else 0) := fun α => by
    by_cases hα : α ∈ box a b
    · obtain ⟨σ, hσ, h⟩ := T_S_Y hab hα
      exact ⟨σ, hσ, fun _ => h⟩
    · exact ⟨1, EQZab.IsSign.one, fun h => absurd h hα⟩
  choose σ hσ hσT using hS
  have hk : ∀ α, ∃ k ∈ OddSymmetricKernel.kernelSubring n, Lam k = σ α • v (hat b α) := fun α => by
    obtain ⟨c, hc, hvc⟩ := hv (hat b α)
    obtain ⟨k, hk, hkc⟩ := Lam_surj hab (Subring.zsmul_mem _ hc (σ α))
    exact ⟨k, hk, by rw [hkc, map_zsmul, hvc]⟩
  choose k hkK hkL using hk
  refine ⟨∑ α ∈ box a b, gammaN hab (k α) * Sb hab α,
    Subring.sum_mem _ fun α _ => mul_mem (gammaN_mem_RT hab (kernel_le_RT hab (hkK α))) (Sb_mem hab α),
    fun ν hν => ?_⟩
  have hνb := mem_box.1 hν
  have hα₀ : hat a ν ∈ box a b := mem_box.2 ⟨hat_antitone, hat_le⟩
  have hhat : hat b (hat a ν) = ν := ThickBubble.hat_hat hνb.1 hνb.2
  rw [Finset.sum_mul, T_sum, Finset.sum_eq_single (hat a ν)]
  · rw [EQBorel.sp_mul_assoc, T_gamma hab (hkK _) (mul_mem (Sb_mem hab _) (Yb_mem hab ν)),
      hσT _ hα₀ ν hν]
    split_ifs with hc
    · rw [hkL, mul_smul_comm, mul_one, smul_smul, (hσ _).mul_self, one_smul, hhat]
    · exact absurd hhat.symm hc
  · intro α hα hne
    rw [EQBorel.sp_mul_assoc, T_gamma hab (hkK _) (mul_mem (Sb_mem hab _) (Yb_mem hab ν)),
      hσT _ hα ν hν]
    split_ifs with hc
    · subst hc
      exact absurd (ThickBubble.hat_hat (mem_box.1 hα).1 (mem_box.1 hα).2).symm hne
    · rw [EQThick.sp_mul_zero]
  · intro h; exact absurd hα₀ h

/-- `T(X · G) = 0` for all `G` in the right `OΛ_{a+b}`-span of the `s̃_ν(y) z` once it vanishes on them. -/
theorem T_vanish {X : SkewPolynomial (n+2)} (h0 : ∀ ν ∈ box b a, T n a b (X * Yb hab ν) = 0)
    {G : SkewPolynomial (a+b)} (hG : G ∈ EQZab.tosymAB a b) : T n a b (X * EQZab.castHom hab G) = 0 := by
  obtain ⟨c, hc, rfl⟩ := EQZab.zab_span_twisted hG
  rw [map_sum, Finset.mul_sum, T_sum]
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [map_mul, ← EQBorel.sp_mul_assoc, T_mul_twistRev hab _ (hc ν), ← Yb_eq, h0 ν hν, EQThick.sp_zero_mul]

/-- **Uniqueness**: `g` is determined by the values `T(g · s̃_ν(y) z)`. -/
theorem T_unique {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab)
    (h0 : ∀ ν ∈ box b a, T n a b (X * Yb hab ν) = 0) : X = 0 := by
  classical
  obtain ⟨K, hK, hXK⟩ := RT_left_span hab hX
  have hKz : ∀ μ ∈ box b a, K μ = 0 := by
    intro μ hμ
    have hμb := mem_box.1 hμ
    have hα : hat a μ ∈ box a b := mem_box.2 ⟨hat_antitone, hat_le⟩
    have hhat : hat b (hat a μ) = μ := ThickBubble.hat_hat hμb.1 hμb.2
    obtain ⟨σ, hσ, hT⟩ := T_Y_S hab hα
    obtain ⟨G, hG, hGS⟩ := Sb_mem hab (hat a μ)
    have hv := T_vanish hab h0 hG
    rw [hGS] at hv
    conv_lhs at hv => rw [hXK]
    rw [Finset.sum_mul, T_sum, Finset.sum_eq_single μ] at hv
    · rw [EQBorel.sp_mul_assoc, T_gamma hab (hK μ) (mul_mem (Yb_mem hab μ) (Sb_mem hab _)),
        hT μ hμ] at hv
      split_ifs at hv with hc
      swap; · exact absurd hhat.symm hc
      rw [mul_smul_comm, mul_one] at hv
      have hv' := congrArg (fun z => σ • z) hv
      simp only [smul_smul, hσ.mul_self, one_smul, smul_zero] at hv'
      exact Lam_eq_zero hv'
    · intro ν hν hne
      rw [EQBorel.sp_mul_assoc, T_gamma hab (hK ν) (mul_mem (Yb_mem hab ν) (Sb_mem hab _)),
        hT ν hν]
      split_ifs with hc
      · exact absurd (hc.trans hhat) hne
      · rw [EQThick.sp_mul_zero]
    · intro h; exact absurd hμ h
  rw [hXK]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  rw [hKz μ hμ, map_zero, EQThick.sp_zero_mul]

/-- `T` is `OΛ_{a+b}`-valued on `OΛ̃_a ⊠ OΛ̃_b`. -/
theorem T_mem {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab) :
    ∃ c ∈ osym (a+b), T n a b X = EQZab.castHom hab c := by
  classical
  obtain ⟨K, hK, hXK⟩ := RT_left_span hab hX
  have hY : ∀ μ ∈ box b a, ∃ z : ℤ, T n a b (Yb hab μ) = z • 1 := by
    intro μ hμ
    have h := EQZab.trace_sY hab hμ
    refine ⟨if μ = EQZab.boxP a b then (-1 : ℤ) ^ (b.choose 4 + (a * b) * b.choose 2) *
        (-1) ^ ThickBubble.bubbleSign a b 0 else 0, ?_⟩
    rw [EQZab.trace, EQZab.castHom_inclY] at h
    rw [T, h, map_zsmul, map_one]
  choose! z hz using hY
  have hterm : ∀ μ ∈ box b a, ∃ c ∈ osym (a+b),
      T n a b (gammaN hab (K μ) * Yb hab μ) = EQZab.castHom hab c := by
    intro μ hμ
    obtain ⟨c, hc, hcK⟩ := Lam_kernel hab (hK μ)
    refine ⟨z μ • c, Subring.zsmul_mem _ hc _, ?_⟩
    rw [T_gamma hab (hK μ) (Yb_mem hab μ), hz μ hμ, hcK, mul_smul_comm, mul_one, map_zsmul]
  choose! c hc hcT using hterm
  refine ⟨∑ μ ∈ box b a, c μ, Subring.sum_mem _ fun μ hμ => hc μ hμ, ?_⟩
  rw [hXK, T_sum, map_sum]
  exact Finset.sum_congr rfl fun μ hμ => hcT μ hμ

theorem phi_sum (φ : SkewPolynomial (a+b) → SkewPolynomial (n+2))
    (hφadd : ∀ F ∈ EQZab.tosymAB a b, ∀ G ∈ EQZab.tosymAB a b, φ (F + G) = φ F + φ G)
    {ι : Type*} (s : Finset ι) (f : ι → SkewPolynomial (a+b)) (hf : ∀ i ∈ s, f i ∈ EQZab.tosymAB a b) :
    φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  classical
  have h0 : φ 0 = 0 := by
    have := hφadd 0 (zero_mem _) 0 (zero_mem _)
    rw [add_zero] at this
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hφadd _ (hf i (Finset.mem_insert_self _ _)) _
        (Subring.sum_mem _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- **Ellis–Qi, Definition 4.9** (the module structure): for `g ∈ OΛ̃_a ⊠ OΛ̃_b` (`g = τ(u)`, the left
action of `u ∈ OΛ_a ⊗ OΛ_b` on `Z_{a,b}`), `(w₀ ∘ z^∨) · u : x ↦ w₀(z^∨(g x))` is an element of
`Z^∨_{a,b}`: additive, right `OΛ_{a+b}`-linear and `OΛ_{a+b}`-valued. -/
theorem def_4_9_mem {g : SkewPolynomial (a+b)} (hg : g ∈ EQZab.tosymAB a b) :
    (∀ F G : SkewPolynomial (a+b), longestPerm (n+2) (EQZab.trace hab (g * (F + G))) =
      longestPerm (n+2) (EQZab.trace hab (g * F)) + longestPerm (n+2) (EQZab.trace hab (g * G))) ∧
    (∀ G : SkewPolynomial (a+b), ∀ c ∈ osym (a+b),
      longestPerm (n+2) (EQZab.trace hab (g * (G * twistRev (a+b) c))) =
        longestPerm (n+2) (EQZab.trace hab (g * G)) * EQZab.castHom hab c) ∧
    (∀ G ∈ EQZab.tosymAB a b, ∃ c ∈ osym (a+b),
      longestPerm (n+2) (EQZab.trace hab (g * G)) = EQZab.castHom hab c) := by
  refine ⟨fun F G => ?_, fun G c hc => ?_, fun G hG => ?_⟩
  · rw [mul_add, EQZab.trace_add, map_add]
  · rw [← EQBorel.sp_mul_assoc, EQZab.trace_linear hab _ hc]
  · have h := T_mem hab (X := EQZab.castHom hab (g * G)) ⟨_, mul_mem hg hG, rfl⟩
    simpa only [T, EQZab.trace] using h

/-- **Ellis–Qi, Definition 4.9** (`Z^∨_{a,b}` is free of rank one over `OΛ_a ⊗ OΛ_b` on `w₀ ∘ z^∨`,
corrected by erratum [EQ] 19): every additive, right `OΛ_{a+b}`-linear, `OΛ_{a+b}`-valued map
`φ : Z_{a,b} → OΛ_{a+b}` is `x ↦ w₀(z^∨(g x))` for a unique `g ∈ OΛ̃_a ⊠ OΛ̃_b`. -/
theorem def_4_9_free (φ : SkewPolynomial (a+b) → SkewPolynomial (n+2))
    (hφadd : ∀ F ∈ EQZab.tosymAB a b, ∀ G ∈ EQZab.tosymAB a b, φ (F + G) = φ F + φ G)
    (hφlin : ∀ G ∈ EQZab.tosymAB a b, ∀ c ∈ osym (a+b),
      φ (G * twistRev (a+b) c) = φ G * EQZab.castHom hab c)
    (hφval : ∀ G ∈ EQZab.tosymAB a b, ∃ c ∈ osym (a+b), φ G = EQZab.castHom hab c) :
    ∃! g : EQZab.tosymAB a b, ∀ G ∈ EQZab.tosymAB a b,
      φ G = longestPerm (n+2) (EQZab.trace hab (g * G)) := by
  have key : ∀ g : SkewPolynomial (a+b), g ∈ EQZab.tosymAB a b →
      ((∀ G ∈ EQZab.tosymAB a b, φ G = longestPerm (n+2) (EQZab.trace hab (g * G))) ↔
        ∀ ν ∈ box b a, T n a b (EQZab.castHom hab g * Yb hab ν) =
          φ (EQZab.inclY a b (EQSchur.twisted b ν))) := by
    intro g hg
    constructor
    · intro h ν _
      rw [h _ (inclY_twisted_mem ν), EQZab.trace, Yb_eq, ← map_mul]; rfl
    · intro h G hG
      obtain ⟨c, hc, rfl⟩ := EQZab.zab_span_twisted hG
      rw [phi_sum φ hφadd _ _ fun ν _ => mul_mem (inclY_twisted_mem ν)
          ⟨EQZab.phiAB a b (c ν), EQZab.phiAB_mem (hc ν), EQZab.tauAB_phiAB _⟩]
      have hR : longestPerm (n+2) (EQZab.trace hab (g * ∑ ν ∈ box b a,
          EQZab.inclY a b (EQSchur.twisted b ν) * twistRev (a+b) (c ν))) =
          T n a b (EQZab.castHom hab g * ∑ ν ∈ box b a,
            Yb hab ν * EQZab.castHom hab (twistRev (a+b) (c ν))) := by
        rw [EQZab.trace, map_mul, map_sum]
        simp only [map_mul, Yb_eq]
        rfl
      rw [hR, Finset.mul_sum, T_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hφlin _ (inclY_twisted_mem ν) _ (hc ν), ← EQBorel.sp_mul_assoc, T_mul_twistRev hab _ (hc ν),
        h ν hν]
  obtain ⟨X, ⟨g, hg, rfl⟩, hXv⟩ := T_exists hab (fun ν => φ (EQZab.inclY a b (EQSchur.twisted b ν)))
    (fun ν => hφval _ (inclY_twisted_mem ν))
  refine ⟨⟨g, hg⟩, (key g hg).2 hXv, ?_⟩
  rintro ⟨g', hg'⟩ h'
  have h1 := (key g' hg').1 h'
  have hd : EQZab.castHom hab g' - EQZab.castHom hab g = 0 :=
    T_unique hab (sub_mem ⟨g', hg', rfl⟩ ⟨g, hg, rfl⟩) fun ν hν => by
      rw [sub_mul, T_sub, h1 ν hν, hXv ν hν, sub_self]
  exact Subtype.ext (EQZab.castHom_injective hab (sub_eq_zero.mp hd))

end Free

end

end OddMath.Frontier.EQFrob
