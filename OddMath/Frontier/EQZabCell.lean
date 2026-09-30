import OddMath.Frontier.EQZabBasis

/-!
# `Z_{a,b}` is a finite-cell right dg module over `OΛ_{a+b}` (Ellis–Qi, Corollary 4.8)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, (4.21) and Corollary 4.8 (printed numbering).

Model of `EQZabModule`: `Z_{a,b} = OΛ_a ⊠ OΛ_b` (untwisted), differential `dZ a b`, right action
`G · h = G φ(h)`, `φ = phiAB a b`. `Par(b,a)` is `BoxPartitionCount.box b a` (antitone
`μ : Fin b → ℕ` with `μ_j ≤ a`).

* `zab_span`, `zab_indep` (**(4.21)**, the basis used in Corollary 4.8): `{s̃_μ(y) z : μ ∈ Par(b,a)}`
  is a basis of `Z_{a,b}` as a right `OΛ_{a+b}`-module: every `F ∈ OΛ_a ⊠ OΛ_b` is
  `Σ_μ s_μ(y) φ(c_μ)` with `c_μ ∈ OΛ_{a+b}`, and the `c_μ` are unique. In Ellis–Qi's twisted
  notation this is `F z = Σ_μ s̃_μ(y) z · c_μ`; `zab_span_twisted`, `zab_indep_twisted` state it
  for `OΛ̃_a ⊠ OΛ̃_b` and the right action by `(θ ∘ w₀)(OΛ_{a+b}) = OΛ̃_{a+b}`.
  The proof transports `EQZabBasis.ps_span`/`ps_indep` (EKL Theorem 4.16 and (4.54) reflected by
  `ψ`) along `θ_a ⊗ θ_b` and `rev(ŝ_μ) = ± s̃_μ`.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open BoxComplement BoxPartitionCount
open scoped BigOperators

noncomputable section

local instance (priority := high) zabCellNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabCellNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## Changing the rank by an equality -/

/-- `OPol_m ≅ OPol_{m'}` for `m = m'`. -/
def castHom {m m' : ℕ} (h : m = m') : SkewPolynomial m →+* SkewPolynomial m' :=
  skewLift (fun j => generator (Fin.cast h j))
    (generator_anticomm_of_injective _ (Fin.cast_injective h))

@[simp] theorem castHom_generator {m m' : ℕ} (h : m = m') (j : Fin m) :
    castHom h (generator j) = generator (Fin.cast h j) := by
  simp [castHom]

theorem castHom_symm_castHom {m m' : ℕ} (h : m = m') (f : SkewPolynomial m) :
    castHom h.symm (castHom h f) = f := by
  have e : (castHom h.symm).comp (castHom h) = RingHom.id _ := ringHom_ext fun j => by simp
  exact RingHom.congr_fun e f

theorem castHom_injective {m m' : ℕ} (h : m = m') : Function.Injective (castHom h) :=
  Function.LeftInverse.injective (castHom_symm_castHom h)

theorem castHom_elementaryPoly {m m' : ℕ} (h : m = m') (k : ℕ) :
    castHom h (FiniteCompleteElementary.elementaryPoly m k) =
      FiniteCompleteElementary.elementaryPoly m' k := by
  subst h
  have e : castHom (rfl : m = m) = RingHom.id _ := ringHom_ext fun j => by simp
  rw [e, RingHom.id_apply]

/-! ## The block-symmetry of `OΛ̃_a ⊠ OΛ̃_b` -/

variable {n a b : ℕ}

theorem divided_ringHom_eq_zero {m : ℕ} (E : SkewPolynomial m →+* SkewPolynomial (n+2))
    (i : Fin (n+1)) (hE : ∀ j, AllRankDivided.divided i (E (generator j)) = 0)
    (f : SkewPolynomial m) : AllRankDivided.divided i (E f) = 0 := by
  induction f using induction_generator with
  | hgen j => exact hE j
  | h0 => simp
  | h1 => rw [map_one, AllRankDivided.divided_one]
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | hneg f hf => rw [map_neg, map_neg, hf, neg_zero]
  | hmul f g hf hg =>
    rw [map_mul, AllRankDivided.divided_mul, hf, hg, ThickDecomposition.skew_zero_mul,
      ThickDecomposition.skew_mul_zero, add_zero]

theorem castHom_inclX (hab : a + b = n+2) (f : SkewPolynomial a) :
    castHom hab (inclX a b f) = ProjectorRank.place 0 (by omega) f := by
  have e : (castHom hab).comp (inclX a b) = ProjectorRank.place 0 (by omega) :=
    ringHom_ext fun j => by
      simp only [RingHom.comp_apply, inclX_generator, castHom_generator,
        ProjectorRank.place_generator]
      rfl
  exact RingHom.congr_fun e f

theorem castHom_inclY (hab : a + b = n+2) (f : SkewPolynomial b) :
    castHom hab (inclY a b f) = ProjectorRank.place a (by omega) f := by
  have e : (castHom hab).comp (inclY a b) = ProjectorRank.place a (by omega) :=
    ringHom_ext fun j => by
      simp only [RingHom.comp_apply, inclY_generator, castHom_generator,
        ProjectorRank.place_generator]
      congr 1
      exact Fin.ext (by simp; omega)
  exact RingHom.congr_fun e f

/-- `∂_i` kills a placed odd symmetric polynomial on its own window. -/
theorem divided_place_kernel {m p : ℕ} (h : p + (m+2) ≤ n+2) {f : SkewPolynomial (m+2)}
    (hf : f ∈ OddSymmetricKernel.kernelSubring m) (i : Fin (n+1)) (hi1 : p ≤ i.val)
    (hi2 : i.val + 1 < p + (m+2)) :
    AllRankDivided.divided i (ProjectorRank.place p h f) = 0 := by
  have hi : i = OnhWindow.shiftIndex h ⟨i.val - p, by omega⟩ := Fin.ext (by simp; omega)
  rw [hi, (ProjectorRank.place_divided_and_s h _ _).1, hf _, map_zero]

/-- `∂_i` kills a placed polynomial when `x_i`, `x_{i+1}` lie outside the window. -/
theorem divided_place_spectator {k p : ℕ} (h : p + k ≤ n+2) (f : SkewPolynomial k)
    (i : Fin (n+1)) (hi : i.val + 1 < p ∨ p + k ≤ i.val) :
    AllRankDivided.divided i (ProjectorRank.place p h f) = 0 := by
  refine divided_ringHom_eq_zero _ i (fun j => ?_) f
  rw [ProjectorRank.place_generator, AllRankDivided.divided_generator, ite_eq_right_iff]
  intro hj
  exfalso
  rcases hj with hj | hj <;> have := congrArg Fin.val hj <;> simp at this <;> omega

theorem theta_elementary_mem_kernel (m k : ℕ) :
    theta (m+2) (elementary (m+2) k) ∈ OddSymmetricKernel.kernelSubring m := by
  rw [theta_elementary, ← StaircaseIndependence.E_eq_kernel]
  exact Subring.subset_closure (Set.mem_range_self k)

/-- `τ(OΛ_a ⊠ OΛ_b) = OΛ̃_a ⊠ OΛ̃_b` is killed by the `∂_i` inside the two blocks. -/
theorem blockSym_tau (hab : a + b = n+2) {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b) :
    BlockSym n a (castHom hab (tauAB a b F)) := by
  intro i hi
  refine osymAB_induction (P := fun F => AllRankDivided.divided i (castHom hab (tauAB a b F)) = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hF
  · intro k
    rw [tauAB_inclX, castHom_inclX]
    rcases hi with hi | hi
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
      exact divided_place_kernel _ (theta_elementary_mem_kernel m k) i (by omega) (by omega)
    · exact divided_place_spectator _ _ i (Or.inr (by omega))
  · intro k
    rw [tauAB_inclY, castHom_inclY]
    rcases hi with hi | hi
    · exact divided_place_spectator _ _ i (Or.inl hi)
    · obtain ⟨m, rfl⟩ : ∃ m, b = m + 2 := ⟨b - 2, by omega⟩
      exact divided_place_kernel _ (theta_elementary_mem_kernel m k) i hi (by omega)
  · simp
  · rw [map_one, map_one, AllRankDivided.divided_one]
  · intro f g hf hg; rw [map_add, map_add, map_add, hf, hg, add_zero]
  · intro f hf; rw [map_neg, map_neg, map_neg, hf, neg_zero]
  · intro f g hf hg
    rw [map_mul, map_mul, AllRankDivided.divided_mul, hf, hg, ThickDecomposition.skew_zero_mul,
      ThickDecomposition.skew_mul_zero, add_zero]


/-! ## `rev(ŝ_β)` is `± s̃_β` placed on the window of `y` -/

/-- Ellis–Qi's `s̃̂_β` is EKL's dual Schur polynomial `ŝ_β` (Definition 4.10). -/
theorem twistedHat_eq_dualSchur {m : ℕ} (β : Fin (m+2) → ℕ) :
    twistedHat (m+2) β = ThickDots.dualSchur β := by
  have hexp : (fun k : Fin (m+2) => k.val + β (Fin.rev k)) = hatExp β := by
    funext k; simp only [hatExp]; ring
  have hpar : parityInv (m+2) (monomial (hatExp β) 1) =
      (-1 : ℤ) ^ ((m+2).choose 2 + ∑ j, β j) • monomial (hatExp β) 1 := by
    rw [parityInv_monomial, sum_hatExp]
  have hD := parityInv_D_of β _ hpar
  rw [ThickDots.dualSchur, hexp, skewAction_longest _ _ hD, smul_smul, twistedHat, ThickDots.chi]
  congr 1
  rw [← pow_add]
  apply MonomialReversal.neg_one_pow_of_even_add
  refine ⟨(m+2).choose 3 + etaHat β + (∑ j, β j) * (m+2).choose 2, ?_⟩
  simp only [etaHat]
  ring

theorem twisted_zero_rank (β : Fin 0 → ℕ) : twisted 0 β = 1 := by
  rw [twisted_eq_schurAll, SmallRank.schurAll_small (by norm_num)]
  have : β = 0 := funext fun i => i.elim0
  subst this
  rfl

theorem twisted_one_rank (β : Fin 1 → ℕ) : twisted 1 β = generator 0 ^ β 0 := by
  rw [twisted_eq_schurAll, SmallRank.schurAll_small (by norm_num), MonomialReversal.monomial_eq_prod]
  simp

theorem dualQ_eq {a b : ℕ} (h : a + b ≤ n+2) (β : Fin b → ℕ) :
    ∃ ε, IsSign ε ∧ dualQ n a b h β = ε • ProjectorRank.place a h (twisted b β) := by
  match b, h, β with
  | 0, h, β => exact ⟨1, IsSign.one, by rw [dualQ, twisted_zero_rank, map_one, one_smul]⟩
  | 1, h, β =>
    refine ⟨1, IsSign.one, ?_⟩
    rw [dualQ, twisted_one_rank, map_pow, ProjectorRank.place_generator, one_smul]
    congr 2
    exact Fin.ext (by simp)
  | m+2, h, β =>
    obtain ⟨ε, hε, he⟩ := rev_twisted β
    refine ⟨ε, hε, ?_⟩
    have h2 : twistedHat (m+2) β = ε • rev (twisted (m+2) β) := by
      rw [he, smul_smul, hε.mul_self, one_smul]
    rw [dualQ, ← twistedHat_eq_dualSchur, h2, rev_zsmul, rev_rev, map_zsmul]

/-! ## `OΛ̃_{a+b}` in the two ambient ranks -/

theorem theta_mem_E {N : ℕ} {f : SkewPolynomial N} (hf : f ∈ osym N) :
    theta N f ∈ ElementaryBranching.E N := by
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [theta_elementary]
    exact Subring.subset_closure (Set.mem_range_self k)
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem twistRev_mem_E {N : ℕ} {f : SkewPolynomial N} (hf : f ∈ osym N) :
    twistRev N f ∈ ElementaryBranching.E N := by
  rw [twistRev, RingHom.comp_apply]
  exact theta_mem_E (longestPerm_mem_osym hf)

theorem E_le_map_twistRev (N : ℕ) : ElementaryBranching.E N ≤ (osym N).map (twistRev N) := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨longestPerm N (elementary N k), longestPerm_elementary_mem N k, ?_⟩
  change twistRev N (longestPerm N (elementary N k)) = _
  rw [twistRev, RingHom.comp_apply, longestPerm_longestPerm, theta_elementary]

theorem castHom_mem_E {m m' : ℕ} (h : m = m') {f : SkewPolynomial m}
    (hf : f ∈ ElementaryBranching.E m) : castHom h f ∈ ElementaryBranching.E m' := by
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [castHom_elementaryPoly]
    exact Subring.subset_closure (Set.mem_range_self k)
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem kernel_eq_castHom (hab : a + b = n+2) {c : SkewPolynomial (n+2)}
    (hc : c ∈ OddSymmetricKernel.kernelSubring n) :
    ∃ d ∈ osym (a+b), c = castHom hab (twistRev (a+b) d) := by
  rw [← StaircaseIndependence.E_eq_kernel] at hc
  have hc' : c ∈ (ElementaryBranching.E (a+b)).map (castHom hab) := by
    have e : ElementaryBranching.E (n+2) ≤ (ElementaryBranching.E (a+b)).map (castHom hab) := by
      refine Subring.closure_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨_, Subring.subset_closure (Set.mem_range_self k), castHom_elementaryPoly hab k⟩
    exact e hc
  obtain ⟨e, he, rfl⟩ := hc'
  obtain ⟨d, hd, rfl⟩ := E_le_map_twistRev (a+b) he
  exact ⟨d, hd, rfl⟩

theorem castHom_twistRev_mem (hab : a + b = n+2) {d : SkewPolynomial (a+b)} (hd : d ∈ osym (a+b)) :
    castHom hab (twistRev (a+b) d) ∈ OddSymmetricKernel.kernelSubring n := by
  rw [← StaircaseIndependence.E_eq_kernel]
  exact castHom_mem_E hab (twistRev_mem_E hd)

/-! ## Reindexing `P(a,b) ≅ P(b,a)` -/

theorem sum_box_hat {M : Type*} [AddCommMonoid M] (f : (Fin b → ℕ) → M) :
    ∑ α ∈ box a b, f (hat b α) = ∑ μ ∈ box b a, f μ := by
  refine Finset.sum_nbij' (hat b) (hat a) (fun α hα => ?_) (fun μ hμ => ?_) (fun α hα => ?_)
    (fun μ hμ => ?_) (fun α _ => rfl)
  · exact mem_box.2 ⟨hat_antitone, hat_le⟩
  · exact mem_box.2 ⟨hat_antitone, hat_le⟩
  · exact ThickBubble.hat_hat (mem_box.1 hα).1 (mem_box.1 hα).2
  · exact ThickBubble.hat_hat (mem_box.1 hμ).1 (mem_box.1 hμ).2


/-! ## Degenerate ranks `a + b ≤ 1` -/

theorem osym_small {N : ℕ} (hN : N ≤ 1) (f : SkewPolynomial N) : f ∈ osym N := by
  induction f using induction_generator with
  | hgen j =>
    rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
    · exact j.elim0
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have : elementary 1 1 = generator 0 := by
        rw [elementary, strictSum_one, Fin.sum_univ_one]
      rw [← this]
      exact elementary_mem 1 1
  | h0 => exact zero_mem _
  | h1 => exact one_mem _
  | hadd f g hf hg => exact add_mem hf hg
  | hneg f hf => exact neg_mem hf
  | hmul f g hf hg => exact mul_mem hf hg

theorem untwisted_zero_small {N : ℕ} (hN : N ≤ 1) : untwisted N 0 = 1 := by
  rw [untwisted_eq_theta_twisted, twisted_eq_schurAll, SmallRank.schurAll_small hN]
  exact map_one (theta N)

theorem phiAB_small (hs : a + b ≤ 1) (f : SkewPolynomial (a+b)) : phiAB a b f = f := by
  have e : phiAB a b = RingHom.id _ := ringHom_ext fun j => by
    have hj : j.rev = j := by
      rcases (by omega : a + b = 0 ∨ a + b = 1) with h | h
      · exact absurd j.isLt (by omega)
      · exact Fin.ext (by have := j.isLt; simp [Fin.val_rev]; omega)
    simp only [phiAB, epsAB, RingHom.comp_apply, longestPerm_generator, hj, diagHom_generator,
      RingHom.id_apply, epsCoeff]
    split_ifs with h
    · rw [show ((-1 : ℤ) ^ a) = 1 by rw [show a = 0 by have := j.isLt; omega, pow_zero],
        one_smul]
    · rw [one_smul]
  rw [e, RingHom.id_apply]

theorem box_small (h : a = 0 ∨ b = 0) : box b a = {0} := by
  ext μ
  rw [mem_box, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hμ⟩
    funext j
    rcases h with h | h
    · have := hμ j; simp only [Pi.zero_apply]; omega
    · exact (h ▸ j).elim0
  · rintro rfl
    exact ⟨fun _ _ _ => le_rfl, fun _ => Nat.zero_le _⟩

/-! ## The basis theorem -/

theorem castHom_tau_injective (hab : a + b = n+2) :
    Function.Injective (fun F : SkewPolynomial (a+b) => castHom hab (tauAB a b F)) :=
  fun x y hxy => by
    have := congrArg (tauAB a b) (castHom_injective hab hxy)
    simpa only [tauAB_tauAB] using this

/-- **Ellis–Qi (4.21) / Corollary 4.8, spanning**: every element of `Z_{a,b}` is
`Σ_{μ ∈ Par(b,a)} s̃_μ(y) z · c_μ` with `c_μ ∈ OΛ_{a+b}`; in the untwisted model,
`F = Σ_μ s_μ(y) φ(c_μ)`. -/
theorem zab_span {F : SkewPolynomial (a+b)} (hF : F ∈ osymAB a b) :
    ∃ c : (Fin b → ℕ) → SkewPolynomial (a+b), (∀ μ, c μ ∈ osym (a+b)) ∧
      F = ∑ μ ∈ box b a, inclY a b (untwisted b μ) * phiAB a b (c μ) := by
  by_cases hs : a + b ≤ 1
  · refine ⟨fun _ => F, fun _ => osym_small hs F, ?_⟩
    rw [box_small (by omega), Finset.sum_singleton, untwisted_zero_small (by omega), map_one,
      one_mul, phiAB_small hs]
  · obtain ⟨n, hab⟩ : ∃ n, a + b = n + 2 := ⟨a + b - 2, by omega⟩
    obtain ⟨c', hc', hG⟩ := ps_span hab (castHom hab (tauAB a b F)) (blockSym_tau hab hF)
    choose ε hε hQ using fun α : Fin a → ℕ =>
      dualQ_eq (n := n) (a := a) (b := b) (by omega) (hat b α)
    choose d hd hcd using fun α => kernel_eq_castHom hab (hc' α)
    refine ⟨fun μ => ε (hat a μ) • d (hat a μ), fun μ => Subring.zsmul_mem _ (hd _) _, ?_⟩
    apply castHom_tau_injective hab
    show castHom hab (tauAB a b F) = castHom hab (tauAB a b _)
    rw [hG, map_sum, map_sum, ← sum_box_hat (a := a) (b := b)]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [map_mul, map_mul, hQ, tauAB_inclY_untwisted, castHom_inclY, tauAB_phiAB, hcd α]
    simp only
    rw [ThickBubble.hat_hat (mem_box.1 hα).1 (mem_box.1 hα).2, map_zsmul, map_zsmul,
      smul_mul_assoc, mul_smul_comm]

/-- **Ellis–Qi (4.21) / Corollary 4.8, independence**: the coefficients `c_μ ∈ OΛ_{a+b}` are
unique. -/
theorem zab_indep (c : (Fin b → ℕ) → SkewPolynomial (a+b)) (hc : ∀ μ, c μ ∈ osym (a+b))
    (h0 : ∑ μ ∈ box b a, inclY a b (untwisted b μ) * phiAB a b (c μ) = 0) :
    ∀ μ ∈ box b a, c μ = 0 := by
  by_cases hs : a + b ≤ 1
  · intro μ hμ
    rw [box_small (by omega)] at hμ h0
    rw [Finset.mem_singleton] at hμ
    subst hμ
    rwa [Finset.sum_singleton, untwisted_zero_small (by omega), map_one, one_mul,
      phiAB_small hs] at h0
  · obtain ⟨n, hab⟩ : ∃ n, a + b = n + 2 := ⟨a + b - 2, by omega⟩
    choose ε hε hQ using fun α : Fin a → ℕ =>
      dualQ_eq (n := n) (a := a) (b := b) (by omega) (hat b α)
    have h1 := congrArg (fun F => castHom hab (tauAB a b F)) h0
    simp only [map_sum, map_mul, map_zero] at h1
    rw [← sum_box_hat (a := a) (b := b)] at h1
    have h2 := ps_indep hab (fun α => ε α • castHom hab (twistRev (a+b) (c (hat b α))))
      (fun α => Subring.zsmul_mem _ (castHom_twistRev_mem hab (hc _)) _) (by
        rw [← h1]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hQ, tauAB_inclY_untwisted, castHom_inclY, tauAB_phiAB, smul_mul_assoc, mul_smul_comm,
          smul_smul, (hε α).mul_self, one_smul])
    intro μ hμ
    have hα : hat a μ ∈ box a b := mem_box.2 ⟨hat_antitone, hat_le⟩
    have h3 := h2 _ hα
    rw [ThickBubble.hat_hat (mem_box.1 hμ).1 (mem_box.1 hμ).2] at h3
    have h4 : castHom hab (twistRev (a+b) (c μ)) = 0 := by
      have := congrArg (fun x => ε (hat a μ) • x) h3
      simpa only [smul_smul, (hε _).mul_self, one_smul, smul_zero] using this
    have h5 : twistRev (a+b) (c μ) = 0 := castHom_injective hab (by rw [h4, map_zero])
    exact twistRev_injective (by rw [h5, map_zero])

/-- **Ellis–Qi (4.21)**, literally: every `G ∈ OΛ̃_a ⊠ OΛ̃_b` is
`Σ_{μ ∈ Par(b,a)} s̃_μ(y) (θ ∘ w₀)(c_μ)` with `c_μ ∈ OΛ_{a+b}`, i.e.
`G z = Σ_μ s̃_μ(y) z · c_μ`. -/
theorem zab_span_twisted {G : SkewPolynomial (a+b)} (hG : G ∈ tosymAB a b) :
    ∃ c : (Fin b → ℕ) → SkewPolynomial (a+b), (∀ μ, c μ ∈ osym (a+b)) ∧
      G = ∑ μ ∈ box b a, inclY a b (twisted b μ) * twistRev (a+b) (c μ) := by
  obtain ⟨F, hF, rfl⟩ := hG
  obtain ⟨c, hc, hFc⟩ := zab_span hF
  refine ⟨c, hc, ?_⟩
  rw [hFc, map_sum]
  simp only [map_mul, tauAB_inclY_untwisted, tauAB_phiAB]

theorem zab_indep_twisted (c : (Fin b → ℕ) → SkewPolynomial (a+b)) (hc : ∀ μ, c μ ∈ osym (a+b))
    (h0 : ∑ μ ∈ box b a, inclY a b (twisted b μ) * twistRev (a+b) (c μ) = 0) :
    ∀ μ ∈ box b a, c μ = 0 := by
  refine zab_indep c hc ?_
  have h1 := congrArg (tauAB a b) h0
  simp only [map_sum, map_mul, map_zero, tauAB_inclY_twisted, ← tauAB_phiAB, tauAB_tauAB] at h1
  exact h1

end

end OddMath.Frontier.EQZab
