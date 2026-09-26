import OddMath.Frontier.CyclotomicGraded
import OddMath.Frontier.SmallRank2Cyclotomic
import OddMath.Frontier.EKLSectionTwoE
import Mathlib.RingTheory.TensorProduct.Basic

/-! # EKL §5–§6: "graded local" and (5.8)

EKL = Ellis–Khovanov–Lauda, *The odd nilHecke algebra and its diagrammatics*,
arXiv:1111.1320v1.

* §6, p. 47: "the odd Grassmannian ring `OH_{a,N}` is graded local" is false over `ℤ`. For a
  connected graded ring `R` over `ℤ` (`R_d = 0` for `d < 0`, `R_0 = ℤ`, `R = ⊕ R_d`) with
  augmentation `ε : R → ℤ`, the maximal homogeneous left ideals are exactly the `ε⁻¹(pℤ)`, `p`
  prime (`Augmented.isMax_iff`), so `R` is not graded local (`Augmented.not_gradedLocal`).
  This applies to `OH_{a,N}` for every `a ≤ N` (`oh_not_gradedLocal`, `ohZero_not_gradedLocal`,
  `ohOne_not_gradedLocal`; `OH_{a,a} ≅ ℤ`), and `OH_{a,N} = 0` for `a > N`. What the argument of
  p. 47 uses is connectedness (`Cyclotomic.ohConnected`), which gives `K₀(OH_{a,N}) ≅ ℤ[q,q⁻¹]`.
* Positive form: for every field `k`, `k ⊗_ℤ OH_{a,N}` is graded local, with unique maximal
  homogeneous left ideal the kernel of the augmentation (`oh_baseChange_gradedLocal`,
  `oh_baseChange_isMax_iff`, `ohZero_baseChange_gradedLocal`, `ohOne_baseChange_gradedLocal`;
  general statement `FieldAugmented.isMax_iff`, `Augmented.baseChange`).
* Proof of Proposition 5.2, pp. 45–46: (5.8) with the exponent `C(N-a+2,2)` (`eq_5_8`,
  `eq_5_8_step`); the printed `C(N-a,2)` is refuted by `Cyclotomic.eq_5_8_false`. The inductive
  claim `(M^{N-a+1}v)_j = (-1)^{C(N-a+j+1,2)} f_{j,N-a}` with the printed matrix (5.4) already
  fails at `N = a = 2` (`prop_5_2_claim_base_false`).
-/

namespace OddMath.Frontier.EKLGaps
open GradedK0 TensorProduct
noncomputable section

section General
variable {R : Type*} [Ring R] (A : ℤ → AddSubgroup R)

/-- A left ideal `I` is homogeneous if every element of `I` is a finite sum of homogeneous
elements of `I`. -/
def IsGradedIdeal (I : Ideal R) : Prop :=
  ∀ x ∈ I, ∃ f : ℤ →₀ R, (∀ d, f d ∈ A d ∧ f d ∈ I) ∧ f.sum (fun _ y => y) = x

/-- `I` is a maximal homogeneous left ideal. -/
def IsMaxGradedIdeal (I : Ideal R) : Prop :=
  IsGradedIdeal A I ∧ I ≠ ⊤ ∧ ∀ J : Ideal R, IsGradedIdeal A J → I ≤ J → J = I ∨ J = ⊤

/-- `R` is graded local: it has exactly one maximal homogeneous left ideal. -/
def IsGradedLocal : Prop := ∃! I : Ideal R, IsMaxGradedIdeal A I

variable {A}

/-- The ideal `ε⁻¹(pℤ)`. -/
def augIdeal (ε : R →+* ℤ) (p : ℤ) : Ideal R := Ideal.comap ε (Ideal.span {p})

theorem mem_augIdeal {ε : R →+* ℤ} {p : ℤ} {x : R} : x ∈ augIdeal ε p ↔ p ∣ ε x := by
  rw [augIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]

/-- The hypotheses: `A` is connected, `ε : R → ℤ` kills every nonzero degree, and every element
is a finite sum of homogeneous elements. -/
structure Augmented (A : ℤ → AddSubgroup R) (ε : R →+* ℤ) : Prop where
  conn : Connected A
  vanish : ∀ d ≠ 0, ∀ x ∈ A d, ε x = 0
  span : ∀ x : R, ∃ f : ℤ →₀ R, (∀ d, f d ∈ A d) ∧ f.sum (fun _ y => y) = x

variable {ε : R →+* ℤ} (h : Augmented A ε)
include h

theorem Augmented.eps_sum (f : ℤ →₀ R) (hf : ∀ d, f d ∈ A d) :
    ε (f.sum (fun _ y => y)) = ε (f 0) := by
  rw [Finsupp.sum, map_sum]
  by_cases h0 : (0 : ℤ) ∈ f.support
  · rw [Finset.sum_eq_single_of_mem 0 h0]
    intro d _ hd
    exact h.vanish d hd _ (hf d)
  · rw [Finsupp.not_mem_support_iff.mp h0, map_zero]
    exact Finset.sum_eq_zero fun d hd => h.vanish d (fun e => h0 (e ▸ hd)) _ (hf d)

theorem Augmented.eps_of_mem_zero {x : R} (hx : x ∈ A 0) : ((ε x : ℤ) : R) = x := by
  obtain ⟨z, rfl⟩ := h.conn.zero x hx
  rw [map_intCast, Int.cast_id]

theorem Augmented.augIdeal_graded (p : ℤ) : IsGradedIdeal A (augIdeal ε p) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := h.span x
  refine ⟨f, fun d => ⟨hf d, ?_⟩, rfl⟩
  rw [mem_augIdeal]
  by_cases hd : d = 0
  · subst hd
    rw [mem_augIdeal, h.eps_sum f hf] at hx
    exact hx
  · rw [h.vanish d hd _ (hf d)]
    exact dvd_zero p

omit h in
theorem augIdeal_ne_top {p : ℤ} (hp : ¬ IsUnit p) : augIdeal ε p ≠ ⊤ := by
  intro h
  have h1 : (1 : R) ∈ augIdeal ε p := h ▸ Submodule.mem_top
  rw [mem_augIdeal, map_one] at h1
  exact hp (isUnit_of_dvd_one h1)

omit h in
/-- For `p` prime, `ε⁻¹(pℤ)` is a maximal left ideal. -/
theorem augIdeal_maximal {p : ℤ} (hp : Prime p) (J : Ideal R) (hJ : augIdeal ε p ≤ J)
    (hne : J ≠ augIdeal ε p) : J = ⊤ := by
  obtain ⟨x, hxJ, hxI⟩ : ∃ x ∈ J, x ∉ augIdeal ε p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm h hJ)
  rw [mem_augIdeal] at hxI
  obtain ⟨u, v, huv⟩ := (hp.irreducible.coprime_iff_not_dvd).mpr hxI
  have hpJ : ((p : ℤ) : R) ∈ J := hJ (by rw [mem_augIdeal, map_intCast, Int.cast_id])
  have hdiff : x - ((ε x : ℤ) : R) ∈ J := hJ (by
    rw [mem_augIdeal, map_sub, map_intCast, Int.cast_id, sub_self]; exact dvd_zero p)
  have hεJ : ((ε x : ℤ) : R) ∈ J := by
    have := J.sub_mem hxJ hdiff
    rwa [sub_sub_cancel] at this
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : R) = (u : R) * (p : R) + (v : R) * ((ε x : ℤ) : R) := by
    rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, huv, Int.cast_one]
  rw [h1]
  exact J.add_mem (J.mul_mem_left _ hpJ) (J.mul_mem_left _ hεJ)

theorem Augmented.augIdeal_isMax {p : ℤ} (hp : Prime p) : IsMaxGradedIdeal A (augIdeal ε p) :=
  ⟨h.augIdeal_graded p, augIdeal_ne_top hp.not_unit, fun J _ hJ => by
    by_cases hne : J = augIdeal ε p
    · exact Or.inl hne
    · exact Or.inr (augIdeal_maximal hp J hJ hne)⟩

/-- **Classification of the maximal homogeneous left ideals**: they are exactly the ideals
`ε⁻¹(pℤ)`, `p` prime. -/
theorem Augmented.isMax_iff (I : Ideal R) :
    IsMaxGradedIdeal A I ↔ ∃ p : ℤ, Prime p ∧ I = augIdeal ε p := by
  constructor
  · rintro ⟨hI, htop, hmax⟩
    let D : Ideal ℤ := Ideal.comap (Int.castRingHom R) I
    have hD : ∀ z : ℤ, z ∈ D ↔ (z : R) ∈ I := fun z => Iff.rfl
    have hDtop : ¬ IsUnit (Submodule.IsPrincipal.generator D) := by
      intro hu
      apply htop
      have h1 : (1 : ℤ) ∈ D := by
        rw [Submodule.IsPrincipal.mem_iff_generator_dvd]
        exact hu.dvd
      rw [hD, Int.cast_one] at h1
      exact (Ideal.eq_top_iff_one I).mpr h1
    obtain ⟨p, hp, hpg⟩ : ∃ p : ℤ, Prime p ∧ p ∣ Submodule.IsPrincipal.generator D := by
      by_cases h0 : Submodule.IsPrincipal.generator D = 0
      · exact ⟨2, Int.prime_two, h0 ▸ dvd_zero 2⟩
      · obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hDtop h0
        exact ⟨q, hq.prime, hqd⟩
    have hle : I ≤ augIdeal ε p := by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := hI x hx
      rw [mem_augIdeal, h.eps_sum f fun d => (hf d).1]
      have h0 : ((ε (f 0) : ℤ) : R) ∈ I := by
        rw [h.eps_of_mem_zero (hf 0).1]; exact (hf 0).2
      rw [← hD, Submodule.IsPrincipal.mem_iff_generator_dvd] at h0
      exact hpg.trans h0
    rcases hmax _ (h.augIdeal_graded p) hle with e | e
    · exact ⟨p, hp, e.symm⟩
    · exact absurd e (augIdeal_ne_top hp.not_unit)
  · rintro ⟨p, hp, rfl⟩
    exact h.augIdeal_isMax hp

omit h in
theorem augIdeal_two_ne_three : augIdeal ε 2 ≠ augIdeal ε 3 := by
  intro e
  have h2 : ((2 : ℤ) : R) ∈ augIdeal ε 2 := by rw [mem_augIdeal, map_intCast, Int.cast_id]
  rw [e, mem_augIdeal, map_intCast, Int.cast_id] at h2
  norm_num at h2

/-- A connected graded ring over `ℤ` with such an augmentation is never graded local:
`ε⁻¹(2ℤ)` and `ε⁻¹(3ℤ)` are distinct maximal homogeneous left ideals. -/
theorem Augmented.not_gradedLocal : ¬ IsGradedLocal A := by
  rintro ⟨I, -, huniq⟩
  have h2 := huniq _ (h.augIdeal_isMax Int.prime_two)
  have h3 := huniq _ (h.augIdeal_isMax Int.prime_three)
  exact augIdeal_two_ne_three (h2.trans h3.symm)

omit h in
/-- The zero ring is not graded local: it has no proper ideal. -/
theorem not_gradedLocal_of_subsingleton [Subsingleton R] : ¬ IsGradedLocal A := by
  rintro ⟨I, ⟨-, htop, -⟩, -⟩
  exact htop (Ideal.eq_top_iff_one I |>.mpr (Subsingleton.elim (0 : R) 1 ▸ I.zero_mem))

end General

/-! ### `OH_{a,N}` -/

open Cyclotomic

theorem constTerm_eq_zero {N : ℕ} {d : ℤ} (hd : d ≠ 0) {f : OddMath.SkewPolynomial.SkewPolynomial N}
    (hf : f ∈ NilHeckeGradedEnd.polynomialPiece N d) : f 0 = 0 :=
  hf 0 (by simpa [NilHeckeGradedEnd.pdegree] using hd.symm)

/-- `OH_{a,N}` (`2 ≤ a ≤ N`) with its constant term. -/
theorem ohAugmented (n N : ℕ) (h : n+2 ≤ N) : Augmented (ohGrading n N) (constOHN n N h) where
  conn := ohConnected n N h
  vanish d hd x := by
    rintro ⟨k, hk, rfl⟩
    exact constTerm_eq_zero hd hk
  span x := by
    obtain ⟨f, hf, -⟩ := ohDecomposition n N x
    exact ⟨f, hf.1, hf.2⟩

/-- `OH_{0,N} ≅ ℤ`, concentrated in degree `0`. -/
theorem ohZeroAugmented (N : ℕ) :
    Augmented (SmallRank.ohZeroGrading N) (SmallRank.OH_zero_equiv N).toRingHom where
  conn := SmallRank.ohZeroConnected N
  vanish d hd x hx := by
    rw [SmallRank.mem_ohZeroGrading_iff] at hx
    rcases hx with hx | hx
    · exact hx
    · exact absurd hx hd
  span x := ⟨Finsupp.single 0 x, fun d => by
    by_cases hd : d = 0
    · subst hd
      rw [Finsupp.single_eq_same, SmallRank.mem_ohZeroGrading_iff]
      exact Or.inr rfl
    · rw [Finsupp.single_eq_of_ne (Ne.symm hd)]; exact zero_mem _,
    Finsupp.sum_single_index rfl⟩

/-- `OH_{1,N} ≅ ℤ[x]/(x^N)`, `N ≥ 1`, with its constant term. -/
theorem ohOneAugmented {N : ℕ} (hN : 1 ≤ N) :
    Augmented (SmallRank.ohOneGrading N) ((constONH1 hN).comp (SmallRank.OH_one_equiv N).toRingHom) where
  conn := SmallRank.ohOneConnected hN
  vanish d hd x hx := by
    rw [SmallRank.mem_ohOneGrading_iff] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    change constONH1 hN (SmallRank.OH_one_equiv N x) = 0
    rw [← hyx]
    exact constTerm_eq_zero hd hy
  span x := by
    obtain ⟨f, hf, -⟩ := SmallRank.ohOneDecomposition N x
    exact ⟨f, hf.1, hf.2⟩

/-- **"`OH_{a,N}` is graded local" (EKL §6, p. 47) is false over `ℤ`**, for every `2 ≤ a ≤ N`:
the maximal homogeneous left ideals of `OH_{a,N}` are exactly the `ε⁻¹(pℤ)`, `p` prime, where
`ε` is the constant term; `ε⁻¹(2ℤ) ≠ ε⁻¹(3ℤ)`. (For `a = N`, `OH_{a,a} ≅ ℤ`.) -/
theorem oh_not_gradedLocal (n N : ℕ) (h : n+2 ≤ N) : ¬ IsGradedLocal (ohGrading n N) :=
  (ohAugmented n N h).not_gradedLocal

theorem oh_isMaxGraded_iff (n N : ℕ) (h : n+2 ≤ N) (I : Ideal (OH n N)) :
    IsMaxGradedIdeal (ohGrading n N) I ↔ ∃ p : ℤ, Prime p ∧ I = augIdeal (constOHN n N h) p :=
  (ohAugmented n N h).isMax_iff I

theorem ohSelf_not_gradedLocal (n : ℕ) : ¬ IsGradedLocal (ohGrading n (n+2)) :=
  oh_not_gradedLocal n (n+2) le_rfl

/-- `OH_{0,N} ≅ ℤ` is not graded local. -/
theorem ohZero_not_gradedLocal (N : ℕ) : ¬ IsGradedLocal (SmallRank.ohZeroGrading N) :=
  (ohZeroAugmented N).not_gradedLocal

/-- `OH_{1,N} ≅ ℤ[x]/(x^N)`, `N ≥ 1`, is not graded local. -/
theorem ohOne_not_gradedLocal {N : ℕ} (hN : 1 ≤ N) : ¬ IsGradedLocal (SmallRank.ohOneGrading N) :=
  (ohOneAugmented hN).not_gradedLocal

/-- For `a > N`, `OH_{a,N} = 0` has no proper ideal, so it is not graded local either. -/
theorem oh_not_gradedLocal_of_lt (n N : ℕ) (h : N < n+2) : ¬ IsGradedLocal (ohGrading n N) := by
  haveI := OH_subsingleton h
  exact not_gradedLocal_of_subsingleton

section FieldCase
variable {k : Type*} [Field k] {S : Type*} [Ring S] [Algebra k S]

/-- A graded `k`-algebra whose degree-`0` part is `k · 1`, with an augmentation `ε : S → k` killing
all nonzero degrees, and spanned by homogeneous elements. -/
structure FieldAugmented (A : ℤ → AddSubgroup S) (ε : S →ₐ[k] k) : Prop where
  zero : ∀ y ∈ A 0, algebraMap k S (ε y) = y
  vanish : ∀ d ≠ 0, ∀ y ∈ A d, ε y = 0
  span : ∀ y : S, ∃ f : ℤ →₀ S, (∀ d, f d ∈ A d) ∧ f.sum (fun _ z => z) = y

variable {A : ℤ → AddSubgroup S} {ε : S →ₐ[k] k} (h : FieldAugmented A ε)
include h

theorem FieldAugmented.eps_sum (f : ℤ →₀ S) (hf : ∀ d, f d ∈ A d) :
    ε (f.sum (fun _ y => y)) = ε (f 0) := by
  rw [Finsupp.sum, map_sum]
  by_cases h0 : (0 : ℤ) ∈ f.support
  · rw [Finset.sum_eq_single_of_mem 0 h0]
    intro d _ hd
    exact h.vanish d hd _ (hf d)
  · rw [Finsupp.not_mem_support_iff.mp h0, map_zero]
    exact Finset.sum_eq_zero fun d hd => h.vanish d (fun e => h0 (e ▸ hd)) _ (hf d)

/-- The augmentation ideal `ker ε`. -/
def augKer (ε : S →ₐ[k] k) : Ideal S := Ideal.comap ε (⊥ : Ideal k)

omit h in
theorem mem_augKer {y : S} : y ∈ augKer ε ↔ ε y = 0 := by
  rw [augKer, Ideal.mem_comap, Ideal.mem_bot]

theorem FieldAugmented.augKer_graded : IsGradedIdeal A (augKer ε) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := h.span x
  refine ⟨f, fun d => ⟨hf d, ?_⟩, rfl⟩
  rw [mem_augKer]
  by_cases hd : d = 0
  · subst hd
    rw [mem_augKer, h.eps_sum f hf] at hx
    exact hx
  · exact h.vanish d hd _ (hf d)

omit h in
theorem augKer_ne_top : augKer ε ≠ ⊤ := by
  intro e
  have h1 : (1 : S) ∈ augKer ε := e ▸ Submodule.mem_top
  rw [mem_augKer, map_one] at h1
  exact one_ne_zero h1

/-- **Graded local over a field**: `ker ε` is the unique maximal homogeneous left ideal. -/
theorem FieldAugmented.isMax_iff (I : Ideal S) : IsMaxGradedIdeal A I ↔ I = augKer ε := by
  have hmax : ∀ J : Ideal S, augKer ε ≤ J → J ≠ augKer ε → J = ⊤ := by
    intro J hJ hne
    obtain ⟨x, hxJ, hxI⟩ : ∃ x ∈ J, x ∉ augKer ε := by
      by_contra hc
      push_neg at hc
      exact hne (le_antisymm hc hJ)
    rw [mem_augKer] at hxI
    have hd : x - algebraMap k S (ε x) ∈ J := hJ (by
      rw [mem_augKer, map_sub, AlgHom.commutes, Algebra.id.map_eq_self, sub_self])
    have hc : algebraMap k S (ε x) ∈ J := by
      have := J.sub_mem hxJ hd
      rwa [sub_sub_cancel] at this
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : S) = algebraMap k S (ε x)⁻¹ * algebraMap k S (ε x) := by
      rw [← map_mul, inv_mul_cancel₀ hxI, map_one]
    rw [e1]
    exact J.mul_mem_left _ hc
  constructor
  · rintro ⟨hI, htop, hIm⟩
    have hle : I ≤ augKer ε := by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := hI x hx
      rw [mem_augKer, h.eps_sum f fun d => (hf d).1]
      by_contra hc
      apply htop
      rw [Ideal.eq_top_iff_one]
      have h0 := (hf 0).2
      rw [← h.zero _ (hf 0).1] at h0
      have e1 : (1 : S) = algebraMap k S (ε (f 0))⁻¹ * algebraMap k S (ε (f 0)) := by
        rw [← map_mul, inv_mul_cancel₀ hc, map_one]
      rw [e1]
      exact I.mul_mem_left _ h0
    rcases hIm _ h.augKer_graded hle with e | e
    · exact e.symm
    · exact absurd e augKer_ne_top
  · rintro rfl
    refine ⟨h.augKer_graded, augKer_ne_top, fun J _ hJ => ?_⟩
    by_cases hne : J = augKer ε
    · exact Or.inl hne
    · exact Or.inr (hmax J hJ hne)

theorem FieldAugmented.gradedLocal : IsGradedLocal A :=
  ⟨augKer ε, (h.isMax_iff _).2 rfl, fun I hI => (h.isMax_iff I).1 hI⟩

end FieldCase

/-! ### Base change to a field -/

section BaseChange
variable {R : Type*} [Ring R] (A : ℤ → AddSubgroup R) (k : Type*) [Field k]

/-- The grading of `k ⊗_ℤ R`: `(k ⊗ R)_d` is spanned by the `c ⊗ x`, `x ∈ R_d`. -/
def bcGrading (d : ℤ) : AddSubgroup (k ⊗[ℤ] R) :=
  AddSubgroup.closure {y | ∃ (c : k) (x : R), x ∈ A d ∧ y = c ⊗ₜ[ℤ] x}

variable {A} {k}

/-- The augmentation `k ⊗ R → k`, `c ⊗ x ↦ c ε(x)`. -/
def bcAug (ε : R →+* ℤ) : k ⊗[ℤ] R →ₐ[k] k :=
  Algebra.TensorProduct.lift (AlgHom.id k k) ((Int.castRingHom k).comp ε).toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem bcAug_tmul (ε : R →+* ℤ) (c : k) (x : R) : bcAug ε (c ⊗ₜ[ℤ] x) = c * (ε x : k) :=
  Algebra.TensorProduct.lift_tmul _ _ _ c x

theorem Augmented.baseChange {ε : R →+* ℤ} (h : Augmented A ε) :
    FieldAugmented (bcGrading A k) (bcAug ε) where
  zero y hy := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, x, hx, rfl⟩ := hy
      obtain ⟨z, rfl⟩ := h.conn.zero x hx
      rw [bcAug_tmul, map_intCast, Int.cast_id, Algebra.TensorProduct.algebraMap_apply,
        Algebra.id.map_eq_self, ← Int.smul_one_eq_cast (R := R) z, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', zsmul_eq_mul, mul_comm]
    | one => simp
    | mul y y' _ _ hy hy' => rw [map_add, map_add, hy, hy']
    | inv y _ hy => rw [map_neg, map_neg, hy]
  vanish d hd y hy := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, x, hx, rfl⟩ := hy
      rw [bcAug_tmul, h.vanish d hd x hx, Int.cast_zero, mul_zero]
    | one => simp
    | mul y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
    | inv y _ hy => rw [map_neg, hy, neg_zero]
  span y := by
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, fun d => zero_mem _, Finsupp.sum_zero_index⟩
    | tmul c x =>
      obtain ⟨f, hf, rfl⟩ := h.span x
      refine ⟨f.mapRange (fun r => c ⊗ₜ[ℤ] r) (TensorProduct.tmul_zero R c), fun d => ?_, ?_⟩
      · exact AddSubgroup.subset_closure ⟨c, f d, hf d, rfl⟩
      · rw [Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.sum, Finsupp.sum,
          TensorProduct.tmul_sum]
    | add y y' hy hy' =>
      obtain ⟨f, hf, rfl⟩ := hy
      obtain ⟨g, hg, rfl⟩ := hy'
      exact ⟨f + g, fun d => add_mem (hf d) (hg d),
        Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)⟩

/-- **`OH_{a,N}` is graded local after base change to any field `k`** (`2 ≤ a ≤ N`): the unique
maximal homogeneous left ideal of `k ⊗_ℤ OH_{a,N}` is the kernel of the augmentation. -/
theorem oh_baseChange_gradedLocal (n N : ℕ) (h : n+2 ≤ N) (k : Type*) [Field k] :
    IsGradedLocal (bcGrading (ohGrading n N) k) :=
  (ohAugmented n N h).baseChange.gradedLocal

theorem oh_baseChange_isMax_iff (n N : ℕ) (h : n+2 ≤ N) (k : Type*) [Field k]
    (I : Ideal (k ⊗[ℤ] OH n N)) :
    IsMaxGradedIdeal (bcGrading (ohGrading n N) k) I ↔ I = augKer (bcAug (constOHN n N h)) :=
  (ohAugmented n N h).baseChange.isMax_iff I

theorem ohZero_baseChange_gradedLocal (N : ℕ) (k : Type*) [Field k] :
    IsGradedLocal (bcGrading (SmallRank.ohZeroGrading N) k) :=
  (ohZeroAugmented N).baseChange.gradedLocal

theorem ohOne_baseChange_gradedLocal {N : ℕ} (hN : 1 ≤ N) (k : Type*) [Field k] :
    IsGradedLocal (bcGrading (SmallRank.ohOneGrading N) k) :=
  (ohOneAugmented hN).baseChange.gradedLocal

end BaseChange

/-! ### (5.8) -/

/-- `(M w)_j` for the printed matrix `M` of (5.4): `M_{j1} w_1 + w_{j+1}` (the last term absent for
`j = a`). -/
theorem printedMatrix_mulVec (n : ℕ) (w : Fin (n+2) → K n) (i : Fin (n+2)) :
    (printedMatrix n).mulVec w i =
      (-1 : ℤ)^(i.val.choose 2) • eK n (i.val+1) * w 0 +
        if h : i.val + 1 < n+2 then w ⟨i.val+1, h⟩ else 0 := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [printedMatrix, Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
    · simp only [if_true, one_mul]
      congr 1
    · intro b _ hb
      rw [if_neg (fun e => hb (Fin.ext (by simp; omega))), zero_mul]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (fun e => h (by have := b.isLt; omega)), zero_mul]

/-- **(5.8), corrected** (the matrix-multiplication step in the proof of Proposition 5.2):
let `M` be the matrix (5.4), `a = n+2`, `m = N-a`, and `f_{j,m}` the relations (5.6) for `N`.
If `w_j = (-1)^{C(m+j+1,2)} f_{j,m}` (the inductive hypothesis, `w = M^{m+1}v`), then
`(Mw)_j = (-1)^{C(j-1,2)+C(m+2,2)} ε_j f_{1,m} + (-1)^{C(m+j+2,2)} f_{j+1,m}` for `j ≤ a-1`, and
`(Mw)_a = (-1)^{C(a-1,2)+C(m+2,2)} ε_a f_{1,m}`. The printed exponent `C(N-a,2)` in place of
`C(N-a+2,2)` always has the opposite parity (`Cyclotomic.choose_two_parity`); the printed form is
refuted by `Cyclotomic.eq_5_8_false`. (0-based index `i = j-1`.) -/
theorem eq_5_8 (n m : ℕ) (w : Fin (n+2) → K n)
    (hw : ∀ i : Fin (n+2), w i =
      (-1 : ℤ)^((m + i.val + 2).choose 2) • grassmannRelation n (n+2+m) (m + i.val + 1))
    (i : Fin (n+2)) :
    (printedMatrix n).mulVec w i =
      if i.val + 1 < n+2 then
        (-1 : ℤ)^(i.val.choose 2 + (m+2).choose 2) •
            (eK n (i.val+1) * grassmannRelation n (n+2+m) (m+1)) +
          (-1 : ℤ)^((m + i.val + 3).choose 2) • grassmannRelation n (n+2+m) (m + i.val + 2)
      else (-1 : ℤ)^(i.val.choose 2 + (m+2).choose 2) •
            (eK n (i.val+1) * grassmannRelation n (n+2+m) (m+1)) := by
  rw [printedMatrix_mulVec, hw 0]
  simp only [Fin.val_zero, add_zero, smul_mul_smul_comm, ← pow_add]
  split_ifs with h
  · rw [hw]
    simp only
    rw [show m + (i.val + 1) + 2 = m + i.val + 3 by omega,
      show m + (i.val + 1) + 1 = m + i.val + 2 by omega]
  · rw [add_zero]

/-- (5.8) in the form used in the proof: from `(M^{m+1}v)_j = (-1)^{C(m+j+1,2)} f_{j,m}` for all `j`,
`(M^{m+2}v)_j` is given by the corrected (5.8). -/
theorem eq_5_8_step (n m : ℕ)
    (hw : ∀ i : Fin (n+2), ((printedMatrix n)^(m+1)).mulVec (Pi.single 0 1) i =
      (-1 : ℤ)^((m + i.val + 2).choose 2) • grassmannRelation n (n+2+m) (m + i.val + 1))
    (i : Fin (n+2)) :
    ((printedMatrix n)^(m+2)).mulVec (Pi.single 0 1) i =
      if i.val + 1 < n+2 then
        (-1 : ℤ)^(i.val.choose 2 + (m+2).choose 2) •
            (eK n (i.val+1) * grassmannRelation n (n+2+m) (m+1)) +
          (-1 : ℤ)^((m + i.val + 3).choose 2) • grassmannRelation n (n+2+m) (m + i.val + 2)
      else (-1 : ℤ)^(i.val.choose 2 + (m+2).choose 2) •
            (eK n (i.val+1) * grassmannRelation n (n+2+m) (m+1)) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  exact eq_5_8 n m _ hw i

theorem eK_zero_one_coeff :
    ((eK 0 1 : K 0) : OddMath.SkewPolynomial.SkewPolynomial 2) ![1, 0] = 1 := by
  rw [eK_val, EKLSectionTwo.elementary_one_eq, Fin.sum_univ_two]
  simp only [PlacticEvaluation.tildeGenerator, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, gen_eq, Finsupp.add_apply, Finsupp.neg_apply,
    OddMath.SkewPolynomial.monomial, Finsupp.single_apply]
  decide

/-- The inductive claim in the proof of Proposition 5.2,
`(M^{N-a+1}v)_j = (-1)^{C(N-a+j+1,2)} f_{j,N-a}` with `M` the printed matrix (5.4), already fails in
the base case `N = a = 2`, `j = 1`: the left side is `Mv_1 = ε_1`, the right side
`(-1)^{C(2,2)} f_{1,0} = -ε_1`. -/
theorem prop_5_2_claim_base_false :
    (printedMatrix 0).mulVec (Pi.single 0 1) 0 ≠
      (-1 : ℤ)^((2 : ℕ).choose 2) • grassmannRelation 0 2 1 := by
  rw [printedMatrix_mulVec, grassmannRelation_zero_two_one]
  simp only [Fin.val_zero, Pi.single_eq_same, mul_one, Nat.choose_zero_succ, pow_zero, one_smul]
  intro h
  have h2 := congrArg (fun k : K 0 => ((k : OddMath.SkewPolynomial.SkewPolynomial 2)) ![1, 0]) h
  simp only [Subring.coe_add, Finsupp.add_apply, eK_zero_one_coeff] at h2
  norm_num [Pi.single_apply, eK_zero_one_coeff] at h2
  have e : (FiniteCompleteElementary.elementaryPoly (0+2) 1) ![1, 0] = 1 := eK_zero_one_coeff
  rw [e] at h2
  norm_num at h2

end
end OddMath.Frontier.EKLGaps
