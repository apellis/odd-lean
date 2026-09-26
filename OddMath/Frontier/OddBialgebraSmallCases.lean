import OddMath.Frontier.OddBialgebraSmallBlocks
import OddMath.Frontier.OddBialgebraRestrict

/-!
# Restriction to `ONH_1 ⊗ ONH_b`, `ONH_a ⊗ ONH_1` and `ONH_1 ⊗ ONH_1`

EKL arXiv:1111.1320v1, §6, pp. 46–47: windows of size `1` (`ONH_1 = OPol_1`). Window data
(`WinData`) for the three inclusions

* `winL m'`: `OPol_1 ⊗ ONH_b ⊂ ONH_{1+b}`, `b = m'+2`, strands `{0}` and `[1, 1+b)`;
* `winR m`: `ONH_a ⊗ OPol_1 ⊂ ONH_{a+1}`, `a = m+2`, strands `[0, a)` and `{a}`;
* `win11`: `OPol_1 ⊗ OPol_1 ⊂ ONH_2`,

with factor data `opolFactor` (`e = 1`) and `onhFactor m` (`e = e_a`, the splitting (6.1)).
For each: `ONH_{a+b}` is free over `B` on the shuffles (`WinData.freeBasis`), with graded
coordinates (`WinData.coord_mem`), restriction `WinData.res`, `K₀(B) ≅ ℤ[q,q⁻¹]`
(`WinData.K0S.classify`), and

* `resL_exact`, `resR_exact`, `res11_exact`: `Res [E^{(a+b)}] = q^{-ab} [E^{(a)} ⊠ E^{(b)}]`;
* `coprodK0_coeff_eq_resL`, `coprodK0_coeff_eq_resR`, `coprodK0_coeff_eq_res11`: the
  `ϑ^{(a)} ⊗ ϑ^{(b)}`-coefficient of the coproduct of `K₀(ONH)` is the
  `[E^{(a)} ⊠ E^{(b)}]`-coordinate of restriction.
-/

noncomputable section
open LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords NilHeckeAction NilHeckeBasis GradedK0 OddCategorification QuantumSl2Plus
  OnhWindow OnhStructure ZeroHecke
open OddMath.SkewPolynomial (SkewPolynomial)

local notation "L" => LaurentPolynomial ℤ

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolRing'' (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ### Factor data -/

/-- `OPol_1` with `e = 1`. -/
def opolFactor : FactorCorner opolGrading where
  e := 1
  idem := one_mul 1
  mem := NilHeckeGradedEnd.one_mem 1
  I := Fin 1
  S :=
    { σ := fun _ => 1
      lam := fun _ => 1
      sum_eq := by simp
      orth := fun i j => by rw [if_pos (Subsingleton.elim i j), one_mul]
      mul_sigma := fun _ => one_mul 1
      lam_mul := fun _ => mul_one 1 }
  k := fun _ => 0
  sig := fun _ => mem_of_deg_eq (NilHeckeGradedEnd.one_mem 1) (by ring)
  lam := fun _ => mem_of_deg_eq (NilHeckeGradedEnd.one_mem 1) (by ring)
  neg := fun {d y} hy hd => by
    have h : y ∈ NilHeckeGradedEnd.polynomialPiece 1 d := hy
    rw [NilHeckeGradedEnd.polynomial_negative 1 d hd] at h
    rw [(Submodule.mem_bot ℤ).1 h]
    show OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.mul 1 0) 1 = 0
    rw [OddMath.SkewPolynomial.mul_zero, OddMath.SkewPolynomial.zero_mul]
  zero := fun {y} hy => ⟨y 0, by
    rw [one_mul, mul_one, zsmul_one]
    exact eq_intCast_of_mem hy⟩

/-- `ONH_{m+2}` with `e = e_a` and the splitting (6.1). -/
def onhFactor (m : ℕ) : FactorCorner (onhGrading m) where
  e := projector m
  idem := projector_mul_projector
  mem := projector_mem m
  I := BoxPartitionCount.Sq (m+2)
  S := Categorification.split61 m
  k ℓ := Categorification.deg61 ℓ.1
  sig := sig_mem
  lam := lam_mem
  neg := fun hy hd => projector_mul_mul_projector_neg hy hd
  zero := fun hy => projector_mul_mul_projector_zero hy

theorem opolFactor_class :
    K0.of (GIdem.single 0 : GIdem opolGrading) =
      (1 : L) • K0.of (gelem opolFactor.mem opolFactor.idem 0) := by
  rw [one_smul]
  rfl

theorem onhFactor_class (m : ℕ) :
    K0.of (GIdem.single 0 : GIdem (onhGrading m)) =
      qFact (m+2) • K0.of (gelem (onhFactor m).mem (onhFactor m).idem
        (((m+2).choose 2 : ℕ) : ℤ)) :=
  eq_6_1_qFact m

/-! ### Bases -/

/-- The monomial basis of `OPol_1`. -/
def opolBasis : Basis (Fin 1 → ℕ) ℤ (SkewPolynomial 1) := Finsupp.basisSingleOne

theorem opolBasis_apply (a : Fin 1 → ℕ) : opolBasis a = Finsupp.single a 1 :=
  congrFun (Finsupp.coe_basisSingleOne (R := ℤ) (ι := Fin 1 → ℕ)) a

theorem opolBasis_mem (a : Fin 1 → ℕ) : opolBasis a ∈ opolGrading (2 * (a 0 : ℤ)) := by
  rw [opolBasis_apply]
  have := NilHeckeGradedEnd.monomial_mem a 1
  simpa [NilHeckeGradedEnd.pdegree] using this

/-- Half the weight of a PBW index. -/
def hw {n : ℕ} (i : (Fin (n+2) → ℕ) × Perm n) : ℤ := (∑ j, i.1 j : ℕ) - (length i.2 : ℤ)

theorem basis_mem_hw {n : ℕ} (i : (Fin (n+2) → ℕ) × Perm n) :
    basis n i ∈ onhGrading n (2 * hw i) :=
  mem_of_deg_eq (NilHeckeBasis.basis_apply i ▸ NilHeckeGrading.basisElement_mem i)
    (by simp only [NilHeckeGrading.weight, hw]; ring)

theorem blockE_pair_ne_zero {n a b : ℕ} (hab : a + b = n+2) :
    ThickBubble.blockE n 0 a * ThickBubble.blockE n a b ≠ 0 := by
  intro h
  let S := Categorification.split62 hab
  have hα : (fun _ : Fin a => 0) ∈ BoxPartitionCount.box a b :=
    BoxPartitionCount.mem_box.2 ⟨fun _ _ _ => le_rfl, fun _ => Nat.zero_le _⟩
  let α : BoxPartitionCount.box a b := ⟨_, hα⟩
  have h1 : S.lam α = 0 :=
    ((S.lam_mul α).symm.trans (congrArg (S.lam α * ·) h)).trans (mul_zero _)
  have h2 := S.orth α α
  rw [if_pos rfl, h1, zero_mul] at h2
  exact OnhStructure.projector_ne_zero n h2.symm

theorem sum_append_one {k : ℕ} (a : Fin 1 → ℕ) (A : Fin k → ℕ) :
    ∑ j, (Fin.append a A : Fin (1 + k) → ℕ) j = a 0 + ∑ j, A j := by
  rw [Fin.sum_univ_add]
  simp

theorem sum_append_one' {k : ℕ} (A : Fin k → ℕ) (b : Fin 1 → ℕ) :
    ∑ j, (Fin.append A b : Fin (k + 1) → ℕ) j = ∑ j, A j + b 0 := by
  rw [Fin.sum_univ_add]
  simp

theorem append_injective {k l : ℕ} {a a' : Fin k → ℕ} {A A' : Fin l → ℕ}
    (h : (Fin.append a A : Fin (k + l) → ℕ) = Fin.append a' A') : a = a' ∧ A = A' :=
  ⟨funext fun i => by simpa using congrFun h (Fin.castAdd l i),
    funext fun j => by simpa using congrFun h (Fin.natAdd k j)⟩

/-! ### `OPol_1 ⊗ ONH_b ⊂ ONH_{1+b}` -/

section WinL

variable (m' : ℕ)

/-- Window data for `OPol_1 ⊗ ONH_{m'+2} ⊂ ONH_{1+m'+2}`. -/
def winL : WinData opolGrading (onhGrading m') (1 + m') 1 where
  P := pairOW m' (1 + m') (hR m')
  I₁ := Fin 1 → ℕ
  I₂ := (Fin (m'+2) → ℕ) × Perm m'
  b₁ := opolBasis
  b₂ := basis m'
  wt₁ a := (a 0 : ℤ)
  wt₂ := hw
  mem₁ := opolBasis_mem
  mem₂ := basis_mem_hw
  φ x := ((Fin.append x.1 x.2.1 : Fin (1 + (m'+2)) → ℕ), shiftR x.2.2)
  inj := by
    rintro ⟨a, A, v⟩ ⟨a', A', v'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, rfl⟩ := append_injective h1
    have hv : v = v' := Equiv.ext fun j => by
      have := congrArg (fun y : Perm (1 + m') => y (Fin.natAdd 1 j)) h2
      simpa using this
    rw [hv]
  weight := by
    rintro ⟨a, A, v⟩
    simp only [NilHeckeGrading.weight, hw, length_shiftR]
    rw [show (∑ x : Fin (1 + m' + 2), (Fin.append a A : Fin (1 + (m'+2)) → ℕ) x) =
      a 0 + ∑ j, A j from sum_append_one a A]
    push_cast
    ring
  young x := isYoung_shiftR x.2.2
  surj A y hy := by
    obtain ⟨v, rfl⟩ := young_shiftR hy
    exact ⟨(fun i => A (Fin.castAdd (m'+2) i), fun j => A (Fin.natAdd 1 j), v), by
      simp only [Fin.append_castAdd_natAdd]⟩
  sign a iv := by
    show Signed (dotHom (1 + m') 0 (opolBasis a) *
      windowHom m' (1 + m') 1 (hR m') (basis m' iv)) _
    rw [opolBasis_apply, NilHeckeBasis.basis_apply, NilHeckeBasis.basis_apply, basisElement,
      basisElement, map_mul,
      ← mul_assoc, dotHom_mul_windowHom_dotMonomial]
    exact (Signed.refl _).mul (windowHom_dividedR iv.2)

end WinL

/-! ### `ONH_a ⊗ OPol_1 ⊂ ONH_{a+1}` -/

section WinR

variable (m : ℕ)

/-- Window data for `ONH_{m+2} ⊗ OPol_1 ⊂ ONH_{m+2+1}`. -/
def winR : WinData (onhGrading m) opolGrading (m+1) (m+2) where
  P := pairWO m (m+1) (hL m) (lastFin m) rfl
  I₁ := (Fin (m+2) → ℕ) × Perm m
  I₂ := Fin 1 → ℕ
  b₁ := basis m
  b₂ := opolBasis
  wt₁ := hw
  wt₂ b := (b 0 : ℤ)
  mem₁ := basis_mem_hw
  mem₂ := opolBasis_mem
  φ x := ((Fin.append x.1.1 x.2 : Fin ((m+2) + 1) → ℕ), shiftL x.1.2)
  inj := by
    rintro ⟨⟨A, v⟩, b⟩ ⟨⟨A', v'⟩, b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, rfl⟩ := append_injective h1
    have hv : v = v' := Equiv.ext fun j => by
      have := congrArg (fun y : Perm (m+1) => y (Fin.castAdd 1 j)) h2
      simpa using this
    rw [hv]
  weight := by
    rintro ⟨⟨A, v⟩, b⟩
    simp only [NilHeckeGrading.weight, hw, length_shiftL]
    rw [show (∑ x : Fin (m + 1 + 2), (Fin.append A b : Fin ((m+2) + 1) → ℕ) x) =
      ∑ j, A j + b 0 from sum_append_one' A b]
    push_cast
    ring
  young x := isYoung_shiftL x.1.2
  surj A y hy := by
    obtain ⟨v, rfl⟩ := young_shiftL hy
    exact ⟨((fun i => A (Fin.castAdd 1 i), v), fun j => A (Fin.natAdd (m+2) j)), by
      simp only [Fin.append_castAdd_natAdd]⟩
  sign iv b := by
    show Signed (windowHom m (m+1) 0 (hL m) (basis m iv) *
      dotHom (m+1) (lastFin m) (opolBasis b)) _
    rw [opolBasis_apply, NilHeckeBasis.basis_apply, NilHeckeBasis.basis_apply, basisElement,
      basisElement, map_mul, mul_assoc, dotHom_single, one_smul]
    refine ((Signed.refl _).mul (windowHom_divided_mul_dot_pow iv.2 (b 0))).trans ?_
    rw [← mul_assoc, ← windowHom_dotMonomial_mul_dotHom, dotHom_single, one_smul]
    exact (Signed.refl _).mul (windowHom_dividedL iv.2)

end WinR

/-! ### `OPol_1 ⊗ OPol_1 ⊂ ONH_2` -/

theorem length_one' {n : ℕ} : length (1 : Perm n) = 0 := by
  unfold length
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    if_neg fun h => lt_asymm h.1 (by simpa using h.2)

theorem signed_dividedElement_one {n : ℕ} : Signed (1 : Presented n) (dividedElement 1) :=
  reduced_dividedElement [] (by simp [Reduced, permutation, length_one'])

theorem young_eq_one_11 {y : Perm 0} (hy : IsYoung 1 y) : y = 1 := by
  obtain ⟨a, b, h⟩ := exists_sumCongr_of_young (P := 1) (Q := 1) y hy
  obtain rfl : a = 1 := Subsingleton.elim _ _
  obtain rfl : b = 1 := Subsingleton.elim _ _
  rw [h]
  ext x
  simp

theorem dotHom_mul_dotHom (a b : Fin 1 → ℕ) :
    dotHom 0 0 (Finsupp.single a 1) * dotHom 0 1 (Finsupp.single b 1) =
      dotMonomial (Fin.append a b : Fin (1 + 1) → ℕ) := by
  rw [dotHom_single, dotHom_single, one_smul, one_smul, dotMonomial_eq_prod_ofFn,
    List.ofFn_add (m := 1) (n := 1), List.prod_append]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Fin.append_left, Fin.append_right]
  rfl

/-- Window data for `OPol_1 ⊗ OPol_1 ⊂ ONH_2`. -/
def win11 : WinData opolGrading opolGrading 0 1 where
  P := pairOO
  I₁ := Fin 1 → ℕ
  I₂ := Fin 1 → ℕ
  b₁ := opolBasis
  b₂ := opolBasis
  wt₁ a := (a 0 : ℤ)
  wt₂ b := (b 0 : ℤ)
  mem₁ := opolBasis_mem
  mem₂ := opolBasis_mem
  φ x := ((Fin.append x.1 x.2 : Fin (1 + 1) → ℕ), 1)
  inj := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := append_injective h
    rfl
  weight := by
    rintro ⟨a, b⟩
    simp only [NilHeckeGrading.weight, length_one']
    rw [show (∑ x : Fin (0 + 2), (Fin.append a b : Fin (1 + 1) → ℕ) x) = a 0 + ∑ j, b j from
      sum_append_one a b]
    simp
    ring
  young _ := isYoung_one
  surj A y hy := by
    obtain rfl := young_eq_one_11 hy
    exact ⟨(fun i => A (Fin.castAdd 1 i), fun j => A (Fin.natAdd 1 j)), by
      simp only [Fin.append_castAdd_natAdd]⟩
  sign a b := by
    show Signed (dotHom 0 0 (opolBasis a) * dotHom 0 1 (opolBasis b)) _
    rw [opolBasis_apply, opolBasis_apply, dotHom_mul_dotHom, NilHeckeBasis.basis_apply,
      basisElement]
    have := (Signed.refl (dotMonomial (Fin.append a b : Fin (1 + 1) → ℕ))).mul
      (signed_dividedElement_one (n := 0))
    rwa [mul_one] at this

/-! ### The Young sums -/

theorem sum_young_L (m' : ℕ) :
    ∑ y : YoungT (1 + m') 1, (T (-(2 * (length y.1 : ℤ))) : L) =
      ∑ v : Perm m', (T (-(2 * (length v : ℤ))) : L) := by
  refine (Fintype.sum_bijective (fun v : Perm m' => (⟨shiftR v, isYoung_shiftR v⟩ :
    YoungT (1 + m') 1)) ⟨fun v v' h => ?_, fun y => ?_⟩ _ _ fun v => ?_).symm
  · have h2 := congrArg Subtype.val h
    exact Equiv.ext fun j => by
      have := congrArg (fun y : Perm (1 + m') => y (Fin.natAdd 1 j)) h2
      simpa using this
  · obtain ⟨v, hv⟩ := young_shiftR y.2
    exact ⟨v, Subtype.ext hv.symm⟩
  · simp only [length_shiftR]

theorem sum_young_R (m : ℕ) :
    ∑ y : YoungT (m+1) (m+2), (T (-(2 * (length y.1 : ℤ))) : L) =
      ∑ v : Perm m, (T (-(2 * (length v : ℤ))) : L) := by
  refine (Fintype.sum_bijective (fun v : Perm m => (⟨shiftL v, isYoung_shiftL v⟩ :
    YoungT (m+1) (m+2))) ⟨fun v v' h => ?_, fun y => ?_⟩ _ _ fun v => ?_).symm
  · have h2 := congrArg Subtype.val h
    exact Equiv.ext fun j => by
      have := congrArg (fun y : Perm (m+1) => y (Fin.castAdd 1 j)) h2
      simpa using this
  · obtain ⟨v, hv⟩ := young_shiftL y.2
    exact ⟨v, Subtype.ext hv.symm⟩
  · simp only [length_shiftL]

theorem sum_young_11 : ∑ y : YoungT 0 1, (T (-(2 * (length y.1 : ℤ))) : L) = 1 := by
  rw [Finset.sum_eq_single ⟨1, isYoung_one⟩ (fun y _ hy => absurd (Subtype.ext
    (young_eq_one_11 y.2)) hy) (by simp)]
  simp [length_one']

/-! ### Exact restriction and the coproduct -/

section Main

variable (m m' : ℕ)

theorem eSL_ne_zero :
    ((winL m').eS opolFactor (onhFactor m') : Presented (1 + m')) ≠ 0 := by
  show dotHom (1 + m') 0 1 * windowHom m' (1 + m') 1 (hR m') (projector m') ≠ 0
  rw [map_one, one_mul, ← ThickBubble.blockE_eq (hR m'),
    ← one_mul (ThickBubble.blockE (1 + m') 1 (m'+2)), ← ThickBubble.blockE_one (n := 1 + m') 0]
  exact blockE_pair_ne_zero (show 1 + (m'+2) = (1 + m') + 2 by omega)

theorem eSR_ne_zero :
    ((winR m).eS (onhFactor m) opolFactor : Presented (m+1)) ≠ 0 := by
  show windowHom m (m+1) 0 (hL m) (projector m) * dotHom (m+1) (lastFin m) 1 ≠ 0
  rw [map_one, mul_one, ← ThickBubble.blockE_eq (hL m),
    ← mul_one (ThickBubble.blockE (m+1) 0 (m+2)), ← ThickBubble.blockE_one (n := m+1) (m+2)]
  exact blockE_pair_ne_zero (show (m+2) + 1 = (m+1) + 2 by omega)

theorem eS11_ne_zero : (win11.eS opolFactor opolFactor : Presented 0) ≠ 0 := by
  show dotHom 0 0 1 * dotHom 0 1 1 ≠ 0
  rw [map_one, map_one]
  exact blockE_pair_ne_zero (n := 0) (a := 1) (b := 1) rfl

theorem hsumL :
    (∑ u : ShufT (1 + m') 1, (T (-(2 * (length u.1 : ℤ))) : L)) * (1 * qFact (m'+2)) =
      T (-((1 * (m'+2) : ℕ) : ℤ)) * qFact (1 + m' + 2) := by
  have h := sum_length_young (1 + m') 1
  rw [sum_perm_length, sum_young_L, sum_perm_length] at h
  have hc : (((1 + m' + 2).choose 2 : ℕ) : ℤ) =
      (((m'+2).choose 2 : ℕ) : ℤ) + ((1 * (m'+2) : ℕ) : ℤ) := by
    rw [show 1 + m' + 2 = 1 + (m'+2) by omega, BoxComplement.choose_two_add]
    push_cast
    simp
  rw [hc, neg_add, T_add] at h
  refine mul_left_cancel₀ (isUnit_T (-(((m'+2).choose 2 : ℕ) : ℤ))).ne_zero ?_
  linear_combination -h

theorem hsumR :
    (∑ u : ShufT (m+1) (m+2), (T (-(2 * (length u.1 : ℤ))) : L)) * (qFact (m+2) * 1) =
      T (-(((m+2) * 1 : ℕ) : ℤ)) * qFact (m + 1 + 2) := by
  have h := sum_length_young (m+1) (m+2)
  rw [sum_perm_length, sum_young_R, sum_perm_length] at h
  have hc : (((m + 1 + 2).choose 2 : ℕ) : ℤ) =
      (((m+2).choose 2 : ℕ) : ℤ) + (((m+2) * 1 : ℕ) : ℤ) := by
    rw [show m + 1 + 2 = (m+2) + 1 by omega, BoxComplement.choose_two_add]
    push_cast
    simp
  rw [hc, neg_add, T_add] at h
  refine mul_left_cancel₀ (isUnit_T (-(((m+2).choose 2 : ℕ) : ℤ))).ne_zero ?_
  linear_combination -h

theorem hsum11 :
    (∑ u : ShufT 0 1, (T (-(2 * (length u.1 : ℤ))) : L)) * (1 * 1) =
      T (-((1 * 1 : ℕ) : ℤ)) * qFact (0 + 2) := by
  have h := sum_length_young 0 1
  rw [sum_perm_length, sum_young_11, one_mul] at h
  rw [mul_one, mul_one, ← h]
  simp

/-- **Restriction to `ONH_1 ⊗ ONH_b`**: `Res [E^{(1+b)}] = q^{-b} [E^{(1)} ⊠ E^{(b)}]`. -/
theorem resL_exact : (winL m').res (K0.of (divE (1 + m'))) =
    (T (-((1 * (m'+2) : ℕ) : ℤ)) : L) •
      K0.of ((winL m').boxS opolFactor (onhFactor m') 0 (((m'+2).choose 2 : ℕ) : ℤ)) :=
  (winL m').res_exact opolFactor (onhFactor m') (eSL_ne_zero m') _ _ _ 1 (qFact (m'+2))
    opolFactor_class (onhFactor_class m') (hsumL m')

/-- **Restriction to `ONH_a ⊗ ONH_1`**: `Res [E^{(a+1)}] = q^{-a} [E^{(a)} ⊠ E^{(1)}]`. -/
theorem resR_exact : (winR m).res (K0.of (divE (m+1))) =
    (T (-(((m+2) * 1 : ℕ) : ℤ)) : L) •
      K0.of ((winR m).boxS (onhFactor m) opolFactor (((m+2).choose 2 : ℕ) : ℤ) 0) :=
  (winR m).res_exact (onhFactor m) opolFactor (eSR_ne_zero m) _ _ _ (qFact (m+2)) 1
    (onhFactor_class m) opolFactor_class (hsumR m)

/-- **Restriction to `ONH_1 ⊗ ONH_1`**: `Res [E^{(2)}] = q^{-1} [E^{(1)} ⊠ E^{(1)}]`. -/
theorem res11_exact : win11.res (K0.of (divE 0)) =
    (T (-((1 * 1 : ℕ) : ℤ)) : L) • K0.of (win11.boxS opolFactor opolFactor 0 0) :=
  win11.res_exact opolFactor opolFactor eS11_ne_zero _ _ _ 1 1 opolFactor_class
    opolFactor_class hsum11

/-- The `[E^{(1)} ⊠ E^{(b)}]`-coordinate of restriction `K₀(ONH_{1+b}) → K₀(ONH_1 ⊗ ONH_b)`. -/
def resCoeffL : K0 (onhGrading (1 + m')) →ₗ[L] L :=
  (T (-(0 + (((m'+2).choose 2 : ℕ) : ℤ))) : L) •
    ((WinData.K0S.classify (winL m') opolFactor (onhFactor m') (eSL_ne_zero m')).toLinearMap ∘ₗ
      (winL m').res)

/-- The `[E^{(a)} ⊠ E^{(1)}]`-coordinate of restriction `K₀(ONH_{a+1}) → K₀(ONH_a ⊗ ONH_1)`. -/
def resCoeffR : K0 (onhGrading (m+1)) →ₗ[L] L :=
  (T (-((((m+2).choose 2 : ℕ) : ℤ) + 0)) : L) •
    ((WinData.K0S.classify (winR m) (onhFactor m) opolFactor (eSR_ne_zero m)).toLinearMap ∘ₗ
      (winR m).res)

/-- The `[E^{(1)} ⊠ E^{(1)}]`-coordinate of restriction `K₀(ONH_2) → K₀(ONH_1 ⊗ ONH_1)`. -/
def resCoeff11 : K0 (onhGrading 0) →ₗ[L] L :=
  (T (-(0 + 0)) : L) •
    ((WinData.K0S.classify win11 opolFactor opolFactor eS11_ne_zero).toLinearMap ∘ₗ win11.res)

theorem resCoeffL_divE : resCoeffL m' (K0.of (divE (1 + m'))) = T (-((1 * (m'+2) : ℕ) : ℤ)) := by
  rw [resCoeffL, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, resL_exact,
    map_smul, WinData.K0S.classify_boxS, smul_eq_mul, smul_eq_mul, ← T_add, ← T_add]
  congr 1
  ring

theorem resCoeffR_divE : resCoeffR m (K0.of (divE (m+1))) = T (-(((m+2) * 1 : ℕ) : ℤ)) := by
  rw [resCoeffR, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, resR_exact,
    map_smul, WinData.K0S.classify_boxS, smul_eq_mul, smul_eq_mul, ← T_add, ← T_add]
  congr 1
  ring

theorem resCoeff11_divE : resCoeff11 (K0.of (divE 0)) = T (-((1 * 1 : ℕ) : ℤ)) := by
  rw [resCoeff11, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, res11_exact,
    map_smul, WinData.K0S.classify_boxS, smul_eq_mul, smul_eq_mul, ← T_add, ← T_add]
  simp

/-- **The coproduct is induced by restriction, `a = 1`**: the coefficient of
`ϑ^{(1)} ⊗ ϑ^{(b)}` in `Δ(x)` is the `[E^{(1)} ⊠ E^{(b)}]`-coordinate of `Res(x_{1+b})`. -/
theorem coprodK0_coeff_eq_resL (x : K0ONH) :
    TwTensor.coeffAt (T (-2)) (1, m'+2) (coprodK0 x) = resCoeffL m' (x (1 + (m'+2))) := by
  have h : (TwTensor.coeffAt (T (-2)) (1, m'+2)).comp coprodK0.toLinearMap =
      (resCoeffL m').comp (DFinsupp.lapply (1 + (m'+2))) := by
    refine basisK0.ext fun k => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisK0_apply,
      coprodK0_single, coeffAt_coprodVal]
    erw [DFinsupp.lapply_apply]
    by_cases hk : k = 1 + (m'+2)
    · subst hk
      rw [if_pos rfl, DFinsupp.single_eq_same]
      exact (resCoeffL_divE m').symm
    · rw [if_neg (Ne.symm hk), DFinsupp.single_eq_of_ne hk, map_zero]
  exact DFunLike.congr_fun h x

/-- **The coproduct is induced by restriction, `b = 1`**. -/
theorem coprodK0_coeff_eq_resR (x : K0ONH) :
    TwTensor.coeffAt (T (-2)) (m+2, 1) (coprodK0 x) = resCoeffR m (x (m+2+1)) := by
  have h : (TwTensor.coeffAt (T (-2)) (m+2, 1)).comp coprodK0.toLinearMap =
      (resCoeffR m).comp (DFinsupp.lapply (m+2+1)) := by
    refine basisK0.ext fun k => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisK0_apply,
      coprodK0_single, coeffAt_coprodVal]
    erw [DFinsupp.lapply_apply]
    by_cases hk : k = m+2+1
    · subst hk
      rw [if_pos rfl, DFinsupp.single_eq_same]
      exact (resCoeffR_divE m).symm
    · rw [if_neg (Ne.symm hk), DFinsupp.single_eq_of_ne hk, map_zero]
  exact DFunLike.congr_fun h x

/-- **The coproduct is induced by restriction, `a = b = 1`**. -/
theorem coprodK0_coeff_eq_res11 (x : K0ONH) :
    TwTensor.coeffAt (T (-2)) (1, 1) (coprodK0 x) = resCoeff11 (x 2) := by
  have h : (TwTensor.coeffAt (T (-2)) (1, 1)).comp coprodK0.toLinearMap =
      resCoeff11.comp (DFinsupp.lapply 2) := by
    refine basisK0.ext fun k => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisK0_apply,
      coprodK0_single, coeffAt_coprodVal]
    erw [DFinsupp.lapply_apply]
    by_cases hk : k = 2
    · subst hk
      rw [if_pos rfl, DFinsupp.single_eq_same]
      exact resCoeff11_divE.symm
    · rw [if_neg (Ne.symm hk), DFinsupp.single_eq_of_ne hk, map_zero]
  exact DFunLike.congr_fun h x

end Main

end OddMath.Frontier.OddBialgebra
