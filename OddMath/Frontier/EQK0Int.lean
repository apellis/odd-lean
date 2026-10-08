import OddMath.Frontier.EQLimaAllRanks
import OddMath.Frontier.EQLimaLimit
import OddMath.Frontier.EQLimaCounting
import OddMath.Frontier.EQOnhDGZn
import OddMath.Frontier.PrefixEmbedding
import OddMath.Frontier.EQK0Field
import OddMath.Frontier.EQFunctorRingTensor
import DG.Derived.ConnectedK0
import DG.Derived.ConnectedTensor

/-!
# The Grothendieck groups of `OΛ_n` and `OΛ_{a,b}` over `ℤ`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
(printed numbering): §4.4 and its footnote 5 (the results of §4.4 hold over `ℤ`, by formality of `OΛ_n`
(Proposition A.3) and Theorem 2.7), Proposition A.2 (2),
Lemma 4.16 and the first line of the proof of Theorem 4.17.

Over a field `K` the computation `K₀(D(K ⊗ OΛ_n)) ≅ ℤ` uses Corollary 2.6 (`K₀(A) ≅ K₀(A⁰)` for `A`
positive), which needs `A⁰` semisimple; over `ℤ` the degree-`0` part is `ℤ`. This file proves the
integral statement from the low-degree cohomology of `OΛ_n` instead, with dg-lean's
`DG.DGRing.K0.equivIntOfIsConnectedInt`: for a dg ring concentrated in non-negative degrees with
degree-`0` part `ℤ · 1`, `H¹ = 0` and `H²` torsion-free, `K₀ ≃ ℤ`, `[A] ↦ 1` (every compact object
has a tower of shifted finitely generated abelian groups, the heart of a bounded t-structure).

* `EQSchur.untwisted_mem_grading`, `schurU_mem_grading`: the untwisted odd Schur polynomial `s_λ` is
  homogeneous of degree `|λ|`;
* `osym_eq_d_of_cocycle`: by Proposition A.2 (2) (Lima partitions have size divisible by `4`), every
  cocycle of `OΛ_N` of degree `k` with `4 ∤ k` is a coboundary; in particular `H¹(OΛ_N) = 0` and
  `H²(OΛ_N) = 0` (`osym_cocycle_one`, `osym_cocycle_two`);
* the same low-degree statements for `OΛ_{a,b} = OΛ_a ⊗ OΛ_b` (`osymAB_cocycle_one`,
  `osymAB_cohomology_two_torsionFree`), from dg-lean's `DG.ConnectedTensor` and
  `EQFunctor.tensorEquivOsymAB`;
* `baseK0OsymInt N : K₀(D(OΛ_N)^c) ≃ ℤ` and `baseK0OsymABInt a b : K₀(D(OΛ_{a,b})^c) ≃ ℤ`, the regular
  classes mapping to `1`, over `ℤ` (`*_self`).
-/

noncomputable section

open CategoryTheory DirectSum

namespace OddMath.Frontier.EQK0Int

open DG
open OddMath.SkewPolynomial (generator monomial)
open OddMath.Frontier.EQSkewDifferential (OPol osymDG osym grading totalDeg)
open OddMath.Frontier.EQFunctor (osymABDG)

/-! ### Homogeneity of the odd Schur polynomials -/

section Homogeneity

theorem theta_mem_grading {N : ℕ} {k : ℤ} {f : OddMath.SkewPolynomial.SkewPolynomial N}
    (hf : f ∈ grading N k) :
    EQSkewDifferential.theta N f ∈ grading N k :=
  EQSkewDifferential.ringHom_mem_grading _ (fun j => by
    rw [EQSkewDifferential.theta_generator]
    exact AddSubgroup.zsmul_mem _ (EQSkewDifferential.generator_mem_grading j) _) hf

theorem longestPerm_mem_grading {N : ℕ} {k : ℤ} {f : OddMath.SkewPolynomial.SkewPolynomial N}
    (hf : f ∈ grading N k) :
    EQSkewDifferential.longestPerm N f ∈ grading N k :=
  EQSkewDifferential.ringHom_mem_grading _ (fun j => by
    rw [EQSkewDifferential.longestPerm_generator]
    exact EQSkewDifferential.generator_mem_grading _) hf

theorem applyWord_mem_grading {n : ℕ} (w : List (Fin (n+1))) {k : ℤ}
    {f : OddMath.SkewPolynomial.SkewPolynomial (n+2)} (hf : f ∈ grading (n+2) k) :
    LongestDivided.applyWord w f ∈ grading (n+2) (k - w.length) := by
  induction w with
  | nil => simpa using hf
  | cons i w ih =>
    rw [LongestDivided.applyWord_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ← sub_sub]
    exact EQOnhDG.divided_mem_grading i ih

theorem D_mem_grading (N : ℕ) {k : ℤ} {f : OddMath.SkewPolynomial.SkewPolynomial N}
    (hf : f ∈ grading N k) :
    LongestDivided.D N f ∈ grading N (k - N.choose 2) := by
  rcases N with _ | _ | n
  · exact (show f ∈ grading 0 (k - (0 : ℕ).choose 2) by simpa using hf)
  · exact (show f ∈ grading 1 (k - (1 : ℕ).choose 2) by simpa using hf)
  · rw [LongestDivided.D_eq_inherited]
    have := applyWord_mem_grading (LongestDivided.wordIn n (n+2) le_rfl) hf
    rwa [PrefixEmbedding.wordIn_length] at this

theorem totalDeg_staircase (N : ℕ) : totalDeg (fun i : Fin N => N - 1 - i.val) = N.choose 2 := by
  rw [totalDeg]
  have h : ∑ i : Fin N, ((N - 1 - i.val : ℕ) : ℤ) = ∑ i ∈ Finset.range N, (i : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ((N - 1 - i : ℕ) : ℤ)) N]
    exact Finset.sum_range_reflect (fun i => (i : ℤ)) N
  rw [h, ← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]

theorem staircase_mem_grading (N : ℕ) :
    LongestDivided.staircase N ∈ grading N (N.choose 2) := by
  have := EQSkewDifferential.single_mem_grading (n := N) (fun i : Fin N => N - 1 - i.val) 1
  rwa [totalDeg_staircase] at this

theorem monomial_mem_grading {N : ℕ} (a : Fin N → ℕ) : monomial a 1 ∈ grading N (totalDeg a) :=
  EQSkewDifferential.single_mem_grading a 1

/-- **The untwisted odd Schur polynomial `s_a` is homogeneous of degree `|a|`.** -/
theorem untwisted_mem_grading (N : ℕ) (a : Fin N → ℕ) :
    EQSchur.untwisted N a ∈ grading N (totalDeg a) := by
  have h := EQSkewDifferential.mul_mem_grading' (theta_mem_grading (staircase_mem_grading N))
    (theta_mem_grading (monomial_mem_grading a))
  have h' := longestPerm_mem_grading (theta_mem_grading (D_mem_grading N h))
  rwa [show (N.choose 2 : ℤ) + totalDeg a - N.choose 2 = totalDeg a by ring] at h'

/-- `s_λ` is homogeneous of degree `|λ|` (for `ℓ(λ) ≤ N`). -/
theorem schurU_mem_grading {N : ℕ} {μ : YoungDiagram} (h : EQLima.LengthLE N μ) :
    EQLima.schurU N μ ∈ grading N μ.card := by
  have := untwisted_mem_grading N (EQLima.rowExp N μ)
  rwa [EQSkewDifferential.totalDeg, ← Nat.cast_sum, EQLima.sum_rowExp h] at this

end Homogeneity

/-! ### Low-degree cohomology of `OΛ_N` -/

section Osym

variable (N : ℕ)

/-- The Lima Schur polynomial `s_μ` as an element of `OΛ_N`. -/
def limaElt (μ : {μ : YoungDiagram // EQLima.IsLima μ ∧ EQLima.LengthLE N μ}) : osymDG N :=
  ⟨OPol.equiv N (EQLima.schurU N μ.1), EQSkewDifferential.mem_osymDG.mpr (by
    rw [RingEquiv.symm_apply_apply, ← EQLima.osymSchurBasisAll_apply N ⟨μ.1, μ.2.2⟩]
    exact (EQLima.osymSchurBasisAll N ⟨μ.1, μ.2.2⟩).2)⟩

theorem limaElt_mem_grading (μ : {μ : YoungDiagram // EQLima.IsLima μ ∧ EQLima.LengthLE N μ}) :
    limaElt N μ ∈ DG.grading (M := osymDG N) (μ.1.card : ℤ) :=
  (DGSubring.mem_grading_iff _).mpr (EQSkewDifferential.OPol.equiv_mem_grading_iff.mpr
    (schurU_mem_grading μ.2.2))

theorem four_dvd_card (μ : {μ : YoungDiagram // EQLima.IsLima μ ∧ EQLima.LengthLE N μ}) :
    (4 : ℤ) ∣ (μ.1.card : ℤ) := by
  have h : μ.1.card = 4 * (EQLima.limaEquiv ⟨μ.1, μ.2.1⟩).card :=
    EQLima.card_eq_four_mul_card_limaEquiv ⟨μ.1, μ.2.1⟩
  exact ⟨((EQLima.limaEquiv ⟨μ.1, μ.2.1⟩).card : ℤ), by rw [h]; push_cast; ring⟩

/-- **Proposition A.2 (2), graded**: every cocycle of `OΛ_N` of degree `k` with `4 ∤ k` is a
coboundary (the Lima partitions have size divisible by `4`). -/
theorem osym_eq_d_of_cocycle {k : ℤ} (hk : ¬ (4 : ℤ) ∣ k) {f : osymDG N}
    (hf : f ∈ DG.grading k) (hdf : DG.d f = 0) :
    ∃ g ∈ DG.grading (M := osymDG N) (k - 1), f = DG.d g := by
  set F : OddMath.SkewPolynomial.SkewPolynomial N := (OPol.equiv N).symm (f : OPol N) with hFdef
  have hF : F ∈ osym N := EQSkewDifferential.mem_osymDG.mp f.2
  have hdF : EQSkewDifferential.d N F = 0 := by
    rw [hFdef, ← EQSkewDifferential.OPol.symm_d, ← DGSubring.coe_d, hdf]
    rfl
  obtain ⟨G, hG, a, hFG⟩ := EQLima.cocycle_eq_all N hF hdF
  let G' : osymDG N := ⟨OPol.equiv N G, EQSkewDifferential.mem_osymDG.mpr (by simpa using hG)⟩
  let L : osymDG N := a.sum fun μ z => z • limaElt N μ
  let ψ : osymDG N →+ OddMath.SkewPolynomial.SkewPolynomial N :=
    (OPol.equiv N).symm.toAddMonoidHom.comp (DGSubring.subtype (osymDG N)).toAddMonoidHom
  have hψ : Function.Injective ψ := fun x y h =>
    Subtype.ext ((OPol.equiv N).symm.injective h)
  have hfL : f = DG.d G' + L := by
    apply hψ
    rw [map_add]
    change F = _ + _
    rw [hFG]
    congr 1
    simp only [L, map_finsuppSum, map_zsmul]
    rfl
  let π : osymDG N →+ osymDG N :=
    { toFun := fun x => (decompose (DG.grading (M := osymDG N)) x k : osymDG N)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hLk : (decompose (DG.grading (M := osymDG N)) L k : osymDG N) = 0 := by
    change π L = 0
    simp only [L, map_finsuppSum, map_zsmul]
    refine Finset.sum_eq_zero fun μ _ => ?_
    change a μ • (decompose (DG.grading (M := osymDG N)) (limaElt N μ) k : osymDG N) = 0
    have hne : (μ.1.card : ℤ) ≠ k := fun h => hk (h ▸ four_dvd_card N μ)
    rw [decompose_of_mem_ne _ (limaElt_mem_grading N μ) hne, smul_zero]
  refine ⟨decompose (DG.grading (M := osymDG N)) G' (k - 1),
    (decompose (DG.grading (M := osymDG N)) G' (k - 1)).2, ?_⟩
  have h := DG.decompose_d G' (k - 1)
  rw [sub_add_cancel] at h
  conv_lhs => rw [← decompose_of_mem_same _ hf, hfL]
  rw [decompose_add, DirectSum.add_apply, AddMemClass.coe_add, h, hLk, add_zero]

end Osym

/-! ### Connectedness, `H¹` and `H²` -/

/-- dg-lean's notion of a connected dg ring from the one of `EQK0`. -/
theorem isConnectedInt_of {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
    (h : EQK0.IsConnectedInt A) : DG.IsConnectedInt A where
  grading_neg := h.grading_neg
  exists_intCast := h.grading_zero
  intCast_injective m m' hm := by
    have := h.intCast_injective (m - m') (by rw [Int.cast_sub, hm, sub_self])
    omega

theorem isConnectedInt_osym (N : ℕ) : DG.IsConnectedInt (osymDG N) :=
  isConnectedInt_of (EQK0.isConnectedInt_dgSubring (osymDG N))

theorem isConnectedInt_osymAB (a b : ℕ) : DG.IsConnectedInt (osymABDG a b) :=
  isConnectedInt_of (EQK0.isConnectedInt_dgSubring (osymABDG a b))

/-- **`Z¹(OΛ_N) = 0`**, hence `H¹(OΛ_N) = 0`. -/
theorem osym_cocycle_one (N : ℕ) : ∀ x ∈ DG.grading (M := osymDG N) 1, DG.d x = 0 → x = 0 := by
  intro x hx hdx
  obtain ⟨g, hg, rfl⟩ := osym_eq_d_of_cocycle N (k := 1) (by decide) hx hdx
  obtain ⟨z, rfl⟩ := (isConnectedInt_osym N).exists_intCast g (by simpa using hg)
  exact DG.d_intCast z

/-- **Every degree-`2` cocycle of `OΛ_N` is a coboundary** (`H²(OΛ_N) = 0`). -/
theorem osym_cocycle_two (N : ℕ) :
    ∀ x ∈ DG.grading (M := osymDG N) 2, DG.d x = 0 →
      ∃ y ∈ DG.grading (M := osymDG N) 1, x = DG.d y := by
  intro x hx hdx
  obtain ⟨g, hg, rfl⟩ := osym_eq_d_of_cocycle N (k := 2) (by decide) hx hdx
  exact ⟨g, by simpa using hg, rfl⟩

theorem osym_cohomology_one (N : ℕ) (x : DG.cohomology (osymDG N) 1) : x = 0 := by
  induction x using DG.cohomology.induction_on with
  | h z =>
    rw [show z = 0 from Subtype.ext (osym_cocycle_one N _ (DG.cocycles.mem_grading z)
      (DG.cocycles.d_eq_zero z)), map_zero]

theorem osym_cohomology_two (N : ℕ) (x : DG.cohomology (osymDG N) 2) : x = 0 := by
  induction x using DG.cohomology.induction_on with
  | h z =>
    obtain ⟨y, hy, hzy⟩ := osym_cocycle_two N _ (DG.cocycles.mem_grading z)
      (DG.cocycles.d_eq_zero z)
    rw [DG.cohomology.mk_eq_zero_iff]
    exact DG.mem_coboundaries.mpr ⟨y, by simpa using hy, hzy.symm⟩

/-! ### A basis of `OΛ_b¹` -/

theorem exists_eq_single_of_totalDeg_eq_one {n : ℕ} {e : Fin n → ℕ} (h : totalDeg e = 1) :
    ∃ i, e = Pi.single i 1 := by
  have hsum : ∑ j, e j = 1 := by
    have := h
    rw [totalDeg] at this
    exact_mod_cast this
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, e i ≠ 0 := by
    by_contra hne
    push Not at hne
    rw [Finset.sum_eq_zero fun j _ => hne j (Finset.mem_univ j)] at hsum
    exact zero_ne_one hsum
  have hle : ∀ j, e j ≤ 1 := fun j => hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  have hi1 : e i = 1 := by have := hle i; omega
  refine ⟨i, funext fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, hi1]
  · rw [Pi.single_eq_of_ne hj]
    have h2 : e i + e j ≤ ∑ k, e k := by
      rw [← Finset.sum_pair (Ne.symm hj)]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

/-- The coefficients of the linear monomials. -/
def linCoeff (b : ℕ) : DG.grading (M := osymDG b) 1 →ₗ[ℤ] (Fin b → ℤ) where
  toFun x i := ((OPol.equiv b).symm ((x : osymDG b) : OPol b) :
    OddMath.SkewPolynomial.SkewPolynomial b) (Pi.single i 1)
  map_add' x y := by
    funext i
    simp only [AddMemClass.coe_add, map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' m x := by
    funext i
    change _ = m * _
    rw [show (((m • x : DG.grading (M := osymDG b) 1) : osymDG b) : OPol b) =
      m • (((x : osymDG b)) : OPol b) from rfl, map_zsmul, Finsupp.smul_apply, smul_eq_mul]

theorem linCoeff_injective (b : ℕ) : Function.Injective (linCoeff b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hgr : (OPol.equiv b).symm ((x : osymDG b) : OPol b) ∈ grading b 1 :=
    (DGSubring.mem_grading_iff _).mp x.2
  apply Subtype.ext
  apply Subtype.ext
  apply (OPol.equiv b).symm.injective
  rw [show (((0 : DG.grading (M := osymDG b) 1) : osymDG b) : OPol b) = 0 from rfl, map_zero]
  ext e
  by_cases he : e ∈ ((OPol.equiv b).symm ((x : osymDG b) : OPol b) :
      OddMath.SkewPolynomial.SkewPolynomial b).support
  · obtain ⟨i, rfl⟩ := exists_eq_single_of_totalDeg_eq_one (hgr e he)
    exact congrFun hx i
  · rw [Finsupp.notMem_support_iff] at he
    exact he

instance (b : ℕ) : Module.Finite ℤ (DG.grading (M := osymDG b) 1) :=
  Module.Finite.of_injective (linCoeff b) (linCoeff_injective b)

instance (b : ℕ) : Module.Free ℤ (DG.grading (M := osymDG b) 1) := by
  have : NoZeroSMulDivisors ℤ (DG.grading (M := osymDG b) 1) :=
    Function.Injective.noZeroSMulDivisors _ (linCoeff_injective b) (map_zero _)
      (fun m x => map_zsmul _ m x)
  exact Module.free_of_finite_type_torsion_free'

/-! ### `OΛ_{a,b} = OΛ_a ⊗ OΛ_b` -/

local notation "𝒜" a => DGAlgebra.gradingSubmodule ℤ (osymDG a)

/-- **`Z¹(OΛ_{a,b}) = 0`**. -/
theorem osymAB_cocycle_one (a b : ℕ) :
    ∀ x ∈ DG.grading (M := osymABDG a b) 1, DG.d x = 0 → x = 0 := by
  intro x hx hdx
  set e := EQFunctor.tensorEquivOsymAB a b
  have h := ConnectedTensor.cocycle_one_eq_zero (isConnectedInt_osym a) (isConnectedInt_osym b)
    (osym_cocycle_one a) (osym_cocycle_one b) (e.symm.map_mem hx)
    (by rw [← e.symm.map_d, hdx, map_zero])
  rw [← e.apply_symm_apply x, h, map_zero]

/-- **`H²(OΛ_{a,b})` is torsion-free.** -/
theorem osymAB_cohomology_two_torsionFree (a b : ℕ) (m : ℤ) (hm : m ≠ 0)
    (x : DG.cohomology (osymABDG a b) 2) (hx : m • x = 0) : x = 0 := by
  set e := EQFunctor.tensorEquivOsymAB a b
  induction x using DG.cohomology.induction_on with
  | h z =>
    rw [← map_zsmul, DG.cohomology.mk_eq_zero_iff] at hx
    obtain ⟨w, hw, hdw⟩ := DG.mem_coboundaries.mp hx
    have hmz : m • e.symm (z : osymABDG a b) = DG.d (e.symm w) := by
      rw [← e.symm.map_d, hdw, show ((m • z : DG.cocycles (osymABDG a b) 2) : osymABDG a b) =
        m • (z : osymABDG a b) from rfl, map_zsmul]
    obtain ⟨c, hc, hzc⟩ := ConnectedTensor.exists_eq_d_of_zsmul_eq_d (isConnectedInt_osym a)
      (isConnectedInt_osym b) (osym_cocycle_one a)
      (fun _ _ α hα hdα _ _ _ => osym_cocycle_two a α hα hdα)
      (fun _ _ β hβ hdβ _ _ _ => osym_cocycle_two b β hβ hdβ)
      (Module.Free.chooseBasis ℤ (DG.grading (M := osymDG b) 1)) hm
      (e.symm.map_mem (DG.cocycles.mem_grading z))
      (by rw [← e.symm.map_d, DG.cocycles.d_eq_zero z, map_zero])
      (e.symm.map_mem (by simpa using hw)) hmz
    rw [DG.cohomology.mk_eq_zero_iff]
    refine DG.mem_coboundaries.mpr ⟨e c, by simpa using e.map_mem hc, ?_⟩
    rw [← e.map_d, ← hzc, e.apply_symm_apply]

theorem osymAB_cohomology_one (a b : ℕ) (x : DG.cohomology (osymABDG a b) 1) : x = 0 := by
  induction x using DG.cohomology.induction_on with
  | h z =>
    rw [show z = 0 from Subtype.ext (osymAB_cocycle_one a b _ (DG.cocycles.mem_grading z)
      (DG.cocycles.d_eq_zero z)), map_zero]

/-! ### `K₀ ≃ ℤ` over `ℤ` -/

/-- **`K₀(D(OΛ_N)^c) ≃ ℤ`** over `ℤ`, `[OΛ_N] ↦ 1`. -/
def baseK0OsymInt (N : ℕ) [DG.HasDerivedCategory.{0, 0} (osymDG N)] :
    DGRing.K0.{0, 0} (osymDG N) ≃+ ℤ :=
  DGRing.K0.equivIntOfIsConnectedInt (isConnectedInt_osym N) (osym_cohomology_one N)
    (fun _ _ x _ => osym_cohomology_two N x)

theorem baseK0OsymInt_self (N : ℕ) [DG.HasDerivedCategory.{0, 0} (osymDG N)] :
    baseK0OsymInt N (DGRing.K0.self (osymDG N)) = 1 :=
  DGRing.K0.equivIntOfIsConnectedInt_self _ _ _

/-- **`K₀(D(OΛ_{a,b})^c) ≃ ℤ`** over `ℤ`, `[OΛ_{a,b}] ↦ 1`. -/
def baseK0OsymABInt (a b : ℕ) [DG.HasDerivedCategory.{0, 0} (osymABDG a b)] :
    DGRing.K0.{0, 0} (osymABDG a b) ≃+ ℤ :=
  DGRing.K0.equivIntOfIsConnectedInt (isConnectedInt_osymAB a b) (osymAB_cohomology_one a b)
    (osymAB_cohomology_two_torsionFree a b)

theorem baseK0OsymABInt_self (a b : ℕ) [DG.HasDerivedCategory.{0, 0} (osymABDG a b)] :
    baseK0OsymABInt a b (DGRing.K0.self (osymABDG a b)) = 1 :=
  DGRing.K0.equivIntOfIsConnectedInt_self _ _ _

end OddMath.Frontier.EQK0Int
