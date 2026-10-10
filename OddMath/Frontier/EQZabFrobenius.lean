import OddMath.Frontier.EQZabTrace
import OddMath.Frontier.EQThickSlider
import OddMath.Frontier.EQThickSplitters
import OddMath.Frontier.OddSymmetrizer
import OddMath.Frontier.EQInductionPoly
import OddMath.Frontier.EQK0Int

/-!
# The trace `z^∨` slides symmetric functions through the merger

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Definition 4.9 (printed numbering); the proof of Proposition 4.2 (`∂_{a,b}(∂_{w₀}' ⊗ ∂_{w₀}'') = ± ∂_{w₀}`).

Rank `n + 2 = a + b`, strands numbered from `0`, the left block `x` on `[0, a)`, the right block `y` on
`[a, a + b)`. `∂_{a,b} = EQZab.pdAB`, `∂_{w₀} = LongestDivided.D`, `D_x = ThickBubble.blockD n 0 a`,
`D_y = ThickBubble.blockD n a b`.

* `action_product_place_mul`: a product of crossings outside the window of a placed polynomial `P`
  moves past `P` at the cost of the parity involution.
* `blockD_pair_kernel_mul`: **the block longest divided differences are left semilinear over the joint
  kernel**: `(D_x D_y)(k X) = Γ(k) (D_x D_y)(X)` for `k ∈ OΛ̃_{a+b}`, with `Γ = ι^{binom(a,2)+binom(b,2)} ∘
  (w₀ × w₀)` (`gammaN`; `ι` the parity involution, `w₀ × w₀` the reversal of each block).
* `pdAB_gamma_mul`: hence, for `F` killed by the crossings inside the blocks,
  `∂_{a,b}(Γ(k) F) = w₀(k) ∂_{a,b}(F)` with `w₀` EKL's signed action of the longest element
  (`SignedPermutation.skewAction (LongestElementary.longest (n+2))`): Γ(k) slides through the merger.
* `RT` (`OΛ̃_a ⊠ OΛ̃_b` in rank `n + 2`): `RT_blocksym` (killed by the crossings inside the blocks),
  `kernel_le_RT` (`OΛ̃_{a+b} ⊆ RT`), `gammaN_mem_RT`, `rev_mem_RT`, `gammaN_gammaN`;
* `RT_left_span`: **left spanning**, every element of `OΛ̃_a ⊠ OΛ̃_b` is `Σ_μ Γ(k_μ) s̃_μ(y)` with
  `k_μ ∈ OΛ̃_{a+b}`, `μ` in the `b × a` box (from the right basis of Corollary 4.8 via `rev` and `Γ`).

Used for Definition 4.9 in `OddMath.Frontier.EQZabFree`.
-/

namespace OddMath.Frontier.EQFrob

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (parityInv parityInv_generator parityInv_parityInv longestPerm)
open NilHeckeAction NilCoxeterWords ThickBubble

noncomputable section

local instance (priority := high) frobNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) frobNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-! ### Placed polynomials and crossings outside their window -/

section Outside

variable {p k : ℕ} (h : p + k ≤ n + 2)

theorem parityInv_place (A : SkewPolynomial k) :
    parityInv (n+2) (ProjectorRank.place p h A) = ProjectorRank.place p h (parityInv k A) := by
  have e : (parityInv (n+2)).comp (ProjectorRank.place p h) =
      (ProjectorRank.place p h).comp (parityInv k) :=
    EQSkewDifferential.ringHom_ext fun j => by
      simp only [RingHom.comp_apply, ProjectorRank.place_generator, parityInv_generator, map_neg]
  exact RingHom.congr_fun e A

theorem s_place_outside (i : Fin (n+1)) (hi : i.val + 1 < p ∨ p + k ≤ i.val) (A : SkewPolynomial k) :
    AllRankDivided.s i (ProjectorRank.place p h A) = parityInv (n+2) (ProjectorRank.place p h A) := by
  have e : (AllRankDivided.s i).toRingHom.comp (ProjectorRank.place p h) =
      (parityInv (n+2)).comp (ProjectorRank.place p h) :=
    EQSkewDifferential.ringHom_ext fun j => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ProjectorRank.place_generator, AllRankDivided.s_generator, parityInv_generator]
      congr 2
      apply Equiv.swap_apply_of_ne_of_ne <;> intro e <;> have := congrArg Fin.val e <;>
        simp [ProjectorRank.shiftEmb_val] at this <;> omega
  exact RingHom.congr_fun e A

/-- A crossing outside the window of `P` moves past `P` at the cost of the parity involution. -/
theorem divided_place_mul (i : Fin (n+1)) (hi : i.val + 1 < p ∨ p + k ≤ i.val) (A : SkewPolynomial k)
    (Z : SkewPolynomial (n+2)) :
    AllRankDivided.divided i (ProjectorRank.place p h A * Z) =
      ProjectorRank.place p h (parityInv k A) * AllRankDivided.divided i Z := by
  rw [AllRankDivided.divided_mul, EQThick.divided_place_eq_zero h i hi, EQThick.sp_zero_mul, zero_add,
    s_place_outside h i hi, parityInv_place]

/-- **A product of crossings outside the window of `P` moves past `P`**, at the cost of the parity
involution once per crossing. -/
theorem action_product_place_mul (w : Word n) (hw : ∀ i ∈ w, i.val + 1 < p ∨ p + k ≤ i.val)
    (A : SkewPolynomial k) (Z : SkewPolynomial (n+2)) :
    action n (product w) (ProjectorRank.place p h A * Z) =
      ProjectorRank.place p h ((parityInv k)^[w.length] A) * action n (product w) Z := by
  induction w generalizing A with
  | nil => simp [product, map_one]
  | cons i w ih =>
    rw [product, action_mul_apply, action_mul_apply, ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)),
      action_crossing_apply, action_crossing_apply, divided_place_mul h i (hw i List.mem_cons_self),
      List.length_cons, Function.iterate_succ_apply']

end Outside

theorem mem_triWord {q k : ℕ} {i : Fin (n+1)} (hi : i ∈ StrandCrossing.triWord (n := n) q k) :
    q ≤ i.val ∧ i.val + 1 < q + k := by
  have hv : i.val ∈ StrandCrossing.triList q k := by
    have h := StrandCrossing.natWord_values (n := n) (StrandCrossing.triList q k)
    rcases List.mem_filterMap.mp hi with ⟨j, hj, he⟩
    split_ifs at he with hj'
    · cases he; exact hj
  refine ⟨?_, StrandCrossing.mem_triList hv⟩
  obtain ⟨j, _, e⟩ := List.mem_map.mp hv
  omega


/-! ### Block longest divided differences on placed polynomials -/

open OddMath.Frontier.EQSkewDifferential (grading)

theorem longestPerm_low {N : ℕ} (hN : N ≤ 1) (A : SkewPolynomial N) : longestPerm N A = A := by
  have e : longestPerm N = RingHom.id _ := EQSkewDifferential.ringHom_ext fun j => by
    rw [EQSkewDifferential.longestPerm_generator]
    congr 1
    exact Fin.ext (by simp [Fin.rev]; omega)
  rw [e]; rfl

/-- `D_N(A P) = (-1)^{binom(N,2) |i|} w₀(A) D_N(P)` for `A` of degree `i` in the joint kernel (EKL (2.64),
with the plain `w₀`). In ranks `N ≤ 1` nothing is required of `A`. -/
theorem D_kernel_mul (N : ℕ) {i : ℤ} {A : SkewPolynomial N} (hA : A ∈ grading N i)
    (hk : ∀ m, (h : N = m + 2) → EQZab.castHom h A ∈ OddSymmetricKernel.kernelSubring m)
    (P : SkewPolynomial N) :
    LongestDivided.D N (A * P) =
      ((-1 : ℤ) ^ (N.choose 2 * i.natAbs)) • (longestPerm N A * LongestDivided.D N P) := by
  match N, A, hA, hk with
  | 0, A, _, _ => simp [LongestDivided.D, longestPerm_low (le_of_lt Nat.zero_lt_one) A]
  | 1, A, _, _ => simp [LongestDivided.D, longestPerm_low le_rfl A]
  | m + 2, A, hA, hk =>
    have hk' := hk m rfl
    rw [EQZab.castHom_rfl] at hk'
    rw [OddSymmetrizer.D_left_kernel m A P hk',
      EQSchur.skewAction_longest A i.natAbs (by
        rw [EQSkewDifferential.parityInv_of_mem hA, EQFunctor.koszulSign_eq_neg_one_pow_natAbs]),
      smul_mul_assoc]

/-- The block longest divided difference on the window `[p, p+k)` acts on a placed polynomial times a
factor killed by the window's crossings through `D_k`. -/
theorem action_blockD_place_mul {p k : ℕ} (h : p + k ≤ n + 2) (P : SkewPolynomial k)
    (Z : SkewPolynomial (n+2))
    (hZ : ∀ i : Fin (n+1), p ≤ i.val → i.val + 1 < p + k → AllRankDivided.divided i Z = 0) :
    action n (blockD n p k) (ProjectorRank.place p h P * Z) =
      ProjectorRank.place p h (LongestDivided.D k P) * Z := by
  match k, h, P, hZ with
  | 0, h, P, _ => rw [blockD_zero, map_one]; rfl
  | 1, h, P, _ => rw [blockD_one, map_one]; rfl
  | m + 2, h, P, hZ =>
    rw [blockD_eq h, EQThick.action_windowHom_mul_kernel h _ _ Z (fun i =>
      hZ _ (by simp [OnhWindow.shiftIndex]) (by have := i.isLt; simp [OnhWindow.shiftIndex]; omega)),
      EQThick.action_windowHom_place, ZeroHecke.action_DElem]

/-- The block longest divided difference on `[q, q+k')` moves past a placed polynomial on a disjoint
window `[p, p+k)`, at the cost of `ι^{binom(k',2)}`. -/
theorem action_blockD_outside_mul {p k q k' : ℕ} (h : p + k ≤ n + 2) (h' : q + k' ≤ n + 2)
    (hdisj : p + k ≤ q ∨ q + k' ≤ p) (A : SkewPolynomial k) (Z : SkewPolynomial (n+2)) :
    action n (blockD n q k') (ProjectorRank.place p h A * Z) =
      ProjectorRank.place p h ((parityInv k)^[k'.choose 2] A) * action n (blockD n q k') Z := by
  rw [blockD, action_product_place_mul h _ (fun i hi => by
      have := mem_triWord hi
      omega), length_triWord h']


/-! ### Signs -/

theorem iterate_parityInv_of_mem {N : ℕ} (m : ℕ) {k : ℤ} {f : SkewPolynomial N} (hf : f ∈ grading N k) :
    (parityInv N)^[m] f = ((-1 : ℤ) ^ (m * k.natAbs)) • f := by
  rw [← RingHom.coe_pow, EQFunctor.pow_parityInv_of_mem m hf,
    EQFunctor.koszulSign_eq_neg_one_pow_natAbs, ← pow_mul, mul_comm]

theorem iterate_parityInv_mem {N : ℕ} (m : ℕ) {k : ℤ} {f : SkewPolynomial N} (hf : f ∈ grading N k) :
    (parityInv N)^[m] f ∈ grading N k := by
  rw [iterate_parityInv_of_mem m hf]
  exact AddSubgroup.zsmul_mem _ hf _

theorem iterate_parityInv_mul {N : ℕ} (m : ℕ) (f g : SkewPolynomial N) :
    (parityInv N)^[m] (f * g) = (parityInv N)^[m] f * (parityInv N)^[m] g := by
  rw [← RingHom.coe_pow, map_mul]

theorem iterate_parityInv_zsmul {N : ℕ} (m : ℕ) (c : ℤ) (f : SkewPolynomial N) :
    (parityInv N)^[m] (c • f) = c • (parityInv N)^[m] f := by
  rw [← RingHom.coe_pow, map_zsmul]

theorem neg_one_pow_congr {m m' : ℕ} (h : m % 2 = m' % 2) : (-1 : ℤ) ^ m = (-1 : ℤ) ^ m' := by
  rw [← Nat.mod_add_div m 2, ← Nat.mod_add_div m' 2, h, pow_add, pow_add, pow_mul, pow_mul]
  simp

/-! ### The block longest divided differences on products of placed polynomials -/

section Pair

variable {a b : ℕ} (hab : a + b = n + 2)

/-- `(D_x D_y)(P(x) Q(y)) = (D_a ι^{binom(b,2)} P)(x) (D_b Q)(y)`. -/
theorem blockD_pair_place (P : SkewPolynomial a) (Q : SkewPolynomial b) :
    action n (blockD n 0 a * blockD n a b)
        (ProjectorRank.place 0 (EQThick.left_le hab) P * ProjectorRank.place a (EQThick.right_le hab) Q) =
      ProjectorRank.place 0 (EQThick.left_le hab) (LongestDivided.D a ((parityInv a)^[b.choose 2] P)) *
        ProjectorRank.place a (EQThick.right_le hab) (LongestDivided.D b Q) := by
  have hy : action n (blockD n a b) (ProjectorRank.place a (EQThick.right_le hab) Q) =
      ProjectorRank.place a (EQThick.right_le hab) (LongestDivided.D b Q) := by
    have := action_blockD_place_mul (EQThick.right_le hab) Q 1 (fun i _ _ => AllRankDivided.divided_one i)
    rwa [mul_one, mul_one] at this
  rw [action_mul_apply, action_blockD_outside_mul (EQThick.left_le hab) (EQThick.right_le hab)
    (Or.inl (by omega)), hy, action_blockD_place_mul (EQThick.left_le hab) _ _ (fun i _ hi =>
      EQThick.divided_place_eq_zero (EQThick.right_le hab) i (Or.inl (by omega)) _)]

/-- Block supercommutation for placed polynomials: `Q(y) P(x) = P(x) (ι^{|i|} Q)(y)` for `P` of degree `i`. -/
theorem place_right_mul_place_left {i : ℤ} {P : SkewPolynomial a} (hP : P ∈ grading a i)
    (Q : SkewPolynomial b) :
    ProjectorRank.place a (EQThick.right_le hab) Q * ProjectorRank.place 0 (EQThick.left_le hab) P =
      ProjectorRank.place 0 (EQThick.left_le hab) P *
        ProjectorRank.place a (EQThick.right_le hab) ((parityInv b)^[i.natAbs] Q) := by
  have h := congrArg (EQZab.castHom hab) (EQFunctor.inclY_mul_inclX_pow_parityInv hP Q)
  rwa [map_mul, map_mul, EQZab.castHom_inclY, EQZab.castHom_inclX, EQZab.castHom_inclY,
    RingHom.coe_pow] at h

end Pair


/-! ### The automorphism `Γ` and the block left-kernel identity -/

section Gamma

variable {a b : ℕ} (hab : a + b = n + 2)

/-- `w₀ × w₀` (reversal of each block) on `OPol_{n+2}`, `a + b = n + 2`. -/
def blockRevN : SkewPolynomial (n+2) →+* SkewPolynomial (n+2) :=
  (EQZab.castHom hab).comp ((EQFunctor.blockRev a b).comp (EQZab.castHom hab.symm))

theorem castHom_castHom_symm (X : SkewPolynomial (n+2)) :
    EQZab.castHom hab (EQZab.castHom hab.symm X) = X :=
  EQZab.castHom_symm_castHom hab.symm X

theorem blockRevN_place_left (A : SkewPolynomial a) :
    blockRevN hab (ProjectorRank.place 0 (EQThick.left_le hab) A) =
      ProjectorRank.place 0 (EQThick.left_le hab) (longestPerm a A) := by
  rw [← EQZab.castHom_inclX hab, blockRevN, RingHom.comp_apply, RingHom.comp_apply,
    EQZab.castHom_symm_castHom, EQFunctor.blockRev_inclX, EQZab.castHom_inclX]

theorem blockRevN_place_right (B : SkewPolynomial b) :
    blockRevN hab (ProjectorRank.place a (EQThick.right_le hab) B) =
      ProjectorRank.place a (EQThick.right_le hab) (longestPerm b B) := by
  rw [← EQZab.castHom_inclY hab, blockRevN, RingHom.comp_apply, RingHom.comp_apply,
    EQZab.castHom_symm_castHom, EQFunctor.blockRev_inclY, EQZab.castHom_inclY]

theorem iterate_parityInv_place {p k : ℕ} (h : p + k ≤ n + 2) (m : ℕ) (A : SkewPolynomial k) :
    (parityInv (n+2))^[m] (ProjectorRank.place p h A) = ProjectorRank.place p h ((parityInv k)^[m] A) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, parityInv_place]

/-- **`Γ = ι^{binom(a,2) + binom(b,2)} ∘ (w₀ × w₀)`**. -/
def gammaN : SkewPolynomial (n+2) →+* SkewPolynomial (n+2) :=
  (parityInv (n+2) ^ (a.choose 2 + b.choose 2)).comp (blockRevN hab)

theorem gammaN_place_left (A : SkewPolynomial a) :
    gammaN hab (ProjectorRank.place 0 (EQThick.left_le hab) A) =
      ProjectorRank.place 0 (EQThick.left_le hab)
        ((parityInv a)^[a.choose 2 + b.choose 2] (longestPerm a A)) := by
  rw [gammaN, RingHom.comp_apply, blockRevN_place_left, RingHom.coe_pow, iterate_parityInv_place]

theorem gammaN_place_right (B : SkewPolynomial b) :
    gammaN hab (ProjectorRank.place a (EQThick.right_le hab) B) =
      ProjectorRank.place a (EQThick.right_le hab)
        ((parityInv b)^[a.choose 2 + b.choose 2] (longestPerm b B)) := by
  rw [gammaN, RingHom.comp_apply, blockRevN_place_right, RingHom.coe_pow, iterate_parityInv_place]

theorem elementaryPoly_mem_grading (N k : ℕ) :
    FiniteCompleteElementary.elementaryPoly N k ∈ grading N k := by
  rw [← EQFix.theta_elementary]
  exact EQK0Int.theta_mem_grading (EQSkewDifferential.elementary_mem_grading k)

theorem elementaryPoly_kernel_cond (N k : ℕ) (e : ℕ) :
    ∀ m, (h : N = m + 2) → EQZab.castHom h ((parityInv N)^[e] (FiniteCompleteElementary.elementaryPoly N k)) ∈
      OddSymmetricKernel.kernelSubring m := by
  intro m h
  rw [iterate_parityInv_of_mem e (elementaryPoly_mem_grading N k), map_zsmul,
    EQZab.castHom_elementaryPoly]
  exact Subring.zsmul_mem _ (OddSymmetricKernel.elementary_mem m k) _

/-- **The block left-kernel identity on products of elementary polynomials**:
`(D_x D_y)(ẽ_i(x) ẽ_j(y) X) = Γ(ẽ_i(x) ẽ_j(y)) (D_x D_y)(X)`. -/
theorem blockD_pair_elem_mul (i j : ℕ) (X : SkewPolynomial (n+2)) :
    action n (blockD n 0 a * blockD n a b)
        (ProjectorRank.place 0 (EQThick.left_le hab) (FiniteCompleteElementary.elementaryPoly a i) *
          ProjectorRank.place a (EQThick.right_le hab) (FiniteCompleteElementary.elementaryPoly b j) * X) =
      gammaN hab
          (ProjectorRank.place 0 (EQThick.left_le hab) (FiniteCompleteElementary.elementaryPoly a i) *
            ProjectorRank.place a (EQThick.right_le hab) (FiniteCompleteElementary.elementaryPoly b j)) *
        action n (blockD n 0 a * blockD n a b) X := by
  set A := FiniteCompleteElementary.elementaryPoly a i
  set B := FiniteCompleteElementary.elementaryPoly b j
  have hA : A ∈ grading a i := elementaryPoly_mem_grading a i
  have hB : B ∈ grading b j := elementaryPoly_mem_grading b j
  induction X using Finsupp.induction_linear with
  | zero => rw [EQThick.sp_mul_zero, map_zero, EQThick.sp_mul_zero]
  | add X Y hX hY => rw [mul_add, map_add, hX, hY, map_add, mul_add]
  | single ζ c =>
    -- `x^ζ c = P(x) Q(y)`
    have hζ : (Finsupp.single ζ c : SkewPolynomial (n+2)) =
        ProjectorRank.place 0 (EQThick.left_le hab) (monomial (ThickDecomposition.splitLeft hab ζ) c) *
          ProjectorRank.place a (EQThick.right_le hab) (monomial (ThickDecomposition.splitRight hab ζ) 1) := by
      have := ThickDecomposition.place_mul_place_monomial hab (ThickDecomposition.splitLeft hab ζ)
        (ThickDecomposition.splitRight hab ζ) c 1
      rw [ThickDecomposition.joinExp_split, mul_one] at this
      exact this.symm
    set P := monomial (ThickDecomposition.splitLeft hab ζ) c
    set Q := monomial (ThickDecomposition.splitRight hab ζ) (1 : ℤ)
    set p := EQSkewDifferential.totalDeg (ThickDecomposition.splitLeft hab ζ)
    have hP : P ∈ grading a p := EQSkewDifferential.single_mem_grading _ c
    rw [hζ]
    -- left side
    have hL : ProjectorRank.place 0 (EQThick.left_le hab) A * ProjectorRank.place a (EQThick.right_le hab) B *
        (ProjectorRank.place 0 (EQThick.left_le hab) P * ProjectorRank.place a (EQThick.right_le hab) Q) =
        ProjectorRank.place 0 (EQThick.left_le hab) (A * P) *
          ProjectorRank.place a (EQThick.right_le hab) ((parityInv b)^[p.natAbs] B * Q) := by
      rw [map_mul, map_mul, EQBorel.sp_mul_assoc, ← EQBorel.sp_mul_assoc (ProjectorRank.place a _ B),
        place_right_mul_place_left hab hP, EQBorel.sp_mul_assoc, ← EQBorel.sp_mul_assoc,
        ← EQBorel.sp_mul_assoc]
    rw [hL, blockD_pair_place hab, blockD_pair_place hab, iterate_parityInv_mul,
      D_kernel_mul a (iterate_parityInv_mem (b.choose 2) hA) (elementaryPoly_kernel_cond a i (b.choose 2)),
      D_kernel_mul b (iterate_parityInv_mem p.natAbs hB) (elementaryPoly_kernel_cond b j p.natAbs),
      map_mul, gammaN_place_left, gammaN_place_right]
    -- right side: move `Γ(B)(y)` past `D_a(ι^(b.choose 2) P)(x)`
    have hU : LongestDivided.D a ((parityInv a)^[(b.choose 2)] P) ∈ grading a (p - (a.choose 2)) :=
      EQK0Int.D_mem_grading a (iterate_parityInv_mem (b.choose 2) hP)
    rw [EQBorel.sp_mul_assoc, ← EQBorel.sp_mul_assoc (ProjectorRank.place a _ _),
      place_right_mul_place_left hab hU]
    simp only [iterate_parityInv_of_mem _ hA, iterate_parityInv_of_mem _ hB,
      iterate_parityInv_of_mem _ (EQK0Int.longestPerm_mem_grading hA),
      iterate_parityInv_of_mem _ (EQK0Int.longestPerm_mem_grading hB), iterate_parityInv_zsmul,
      map_zsmul, map_mul, smul_mul_assoc, mul_smul_comm, smul_smul, EQBorel.sp_mul_assoc]
    congr 1
    simp only [← pow_add]
    apply neg_one_pow_congr
    have hnat : ((p : ℤ) - ((a.choose 2) : ℤ)).natAbs % 2 = (p.natAbs + (a.choose 2)) % 2 := by omega
    simp only [Int.natAbs_natCast]
    have h1 : ((p : ℤ) - ((a.choose 2) : ℤ)).natAbs * j % 2 = (p.natAbs * j + (a.choose 2) * j) % 2 := by
      rw [Nat.mul_mod, hnat, ← Nat.mul_mod, Nat.add_mul]
    simp only [Nat.add_mul] at h1 ⊢
    omega


/-- **The block left-kernel identity**: `(D_x D_y)(k X) = Γ(k) (D_x D_y)(X)` for every `k ∈ OΛ̃_{a+b}`. -/
theorem blockD_pair_kernel_mul {k : SkewPolynomial (n+2)} (hk : k ∈ OddSymmetricKernel.kernelSubring n)
    (X : SkewPolynomial (n+2)) :
    action n (blockD n 0 a * blockD n a b) (k * X) =
      gammaN hab k * action n (blockD n 0 a * blockD n a b) X := by
  rw [ElementaryGeneration.kernel_eq_elementaryClosure] at hk
  induction hk using Subring.closure_induction generalizing X with
  | mem x hx =>
    obtain ⟨s, -, -, rfl⟩ := hx
    rw [EQThick.elementary_coproduct hab s, Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, map_zsmul, map_zsmul, smul_mul_assoc, blockD_pair_elem_mul hab]
  | zero => rw [EQThick.sp_zero_mul, map_zero, map_zero, EQThick.sp_zero_mul]
  | one => rw [map_one, one_mul, one_mul]
  | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]
  | neg x _ hx => rw [neg_mul, map_neg, hx, map_neg, neg_mul]
  | mul x y _ _ hx hy =>
    rw [EQBorel.sp_mul_assoc, hx, hy, ← EQBorel.sp_mul_assoc, (gammaN hab).map_mul]

/-- A list product of elements acting by left multiplication acts by left multiplication. -/
theorem action_list_prod_left (l : List (Presented n))
    (hl : ∀ x ∈ l, ∀ G : SkewPolynomial (n+2), action n x G = action n x 1 * G) (G : SkewPolynomial (n+2)) :
    action n l.prod G = action n l.prod 1 * G := by
  induction l with
  | nil => rw [List.prod_nil, map_one]; exact (one_mul G).symm
  | cons x l ih =>
    rw [List.prod_cons, action_mul_apply, action_mul_apply, ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)),
      hl x List.mem_cons_self, hl x List.mem_cons_self (action n l.prod 1), EQBorel.sp_mul_assoc]

theorem action_blockMono_left {p k : ℕ} (h : p + k ≤ n + 2) (A : Fin k → ℕ) (G : SkewPolynomial (n+2)) :
    action n (blockMono n p k h A) G = action n (blockMono n p k h A) 1 * G := by
  refine action_list_prod_left _ (fun x hx G => ?_) G
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  rw [OnhReflection.action_dot_pow_apply, OnhReflection.action_dot_pow_apply, mul_one]

/-- `∂_{a,b} = ` the action of `crossEQ`. -/
theorem pdAB_eq_crossEQ : EQZab.pdAB n a b = action n (EQThick.crossEQ n a b) := by
  rw [EQZab.pdAB, NilHeckeRightBasis.reverse_product]
  rfl

/-- **`Γ(k)` slides through the merger**: for `F` killed by the crossings inside the blocks and
`k ∈ OΛ̃_{a+b}`, `∂_{a,b}(Γ(k) F) = w₀(k) ∂_{a,b}(F)`, `w₀` EKL's signed action of the longest element. -/
theorem pdAB_gamma_mul {k : SkewPolynomial (n+2)} (hk : k ∈ OddSymmetricKernel.kernelSubring n)
    {F : SkewPolynomial (n+2)}
    (hF : ∀ i : Fin (n+1), (i.val + 1 < a ∨ a ≤ i.val) → AllRankDivided.divided i F = 0) :
    EQZab.pdAB n a b (gammaN hab k * F) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) k * EQZab.pdAB n a b F := by
  have hxF : action n (EQThick.eqBlock n 0 a (EQThick.left_le hab)) F = F := by
    have := EQThick.action_eqBlock_mul_kernel (EQThick.left_le hab) 1 F (fun i _ hi => hF i (Or.inl (by omega)))
    rwa [one_mul, EQThick.action_eqBlock_one, one_mul] at this
  have hyF : action n (EQThick.eqBlock n a b (EQThick.right_le hab)) F = F := by
    have := EQThick.action_eqBlock_mul_kernel (EQThick.right_le hab) 1 F (fun i hi _ => hF i (Or.inr hi))
    rwa [one_mul, EQThick.action_eqBlock_one, one_mul] at this
  set M := action n (EQThick.stairBlock n 0 a (EQThick.left_le hab) *
    EQThick.stairBlock n a b (EQThick.right_le hab)) 1 with hMdef
  have hM : ∀ G, action n (EQThick.stairBlock n 0 a (EQThick.left_le hab) *
      EQThick.stairBlock n a b (EQThick.right_le hab)) G = M * G := by
    intro G
    rw [hMdef, action_mul_apply, action_mul_apply, EQThick.stairBlock, EQThick.stairBlock,
      action_blockMono_left (EQThick.right_le hab) _ G,
      action_blockMono_left (EQThick.left_le hab) _ (action n (blockMono n a b _ _) 1 * G),
      action_blockMono_left (EQThick.left_le hab) _ (action n (blockMono n a b _ _) 1),
      EQBorel.sp_mul_assoc]
  -- `F = c (D_x D_y)(M F)`
  set c := (-1 : ℤ) ^ a.choose 3 * (-1 : ℤ) ^ b.choose 3 * (-1 : ℤ) ^ (a.choose 2 * b.choose 2)
  have hFD : F = c • action n (blockD n 0 a * blockD n a b) (M * F) := by
    have h := congrArg (fun z => action n z F) (EQThick.pair_eq hab)
    rw [action_mul_apply, hyF, hxF, map_zsmul, LinearMap.smul_apply,
      action_mul_apply n (blockD n 0 a * blockD n a b), hM] at h
    exact h
  obtain ⟨θ, hθ⟩ := EQThick.crossEQ_mul_blockD (n := n) hab
  have hcD : ∀ Y, action n (EQThick.crossEQ n a b) (action n (blockD n 0 a * blockD n a b) Y) =
      θ • LongestDivided.D (n+2) Y := by
    intro Y
    rw [← action_mul_apply, hθ, map_zsmul, LinearMap.smul_apply, ZeroHecke.action_DElem]
  have hGF : gammaN hab k * F = c • action n (blockD n 0 a * blockD n a b) (k * (M * F)) := by
    conv_lhs => rw [hFD]
    rw [mul_smul_comm, blockD_pair_kernel_mul hab hk]
  rw [hGF, pdAB_eq_crossEQ, map_zsmul, hcD, OddSymmetrizer.D_left_kernel n k _ hk]
  conv_rhs => rw [hFD, map_zsmul, hcD]
  rw [smul_smul, smul_smul, mul_smul_comm]

end Gamma


/-! ### The block symmetric polynomials `OΛ̃_a ⊠ OΛ̃_b` in rank `n + 2` -/

section Model

variable {a b : ℕ} (hab : a + b = n + 2)

/-- `OΛ̃_a ⊠ OΛ̃_b`, transported to rank `n + 2`. -/
def RT : Subring (SkewPolynomial (n+2)) := (EQZab.tosymAB a b).map (EQZab.castHom hab)

theorem place_left_elem_mem (k : ℕ) :
    ProjectorRank.place 0 (EQThick.left_le hab) (FiniteCompleteElementary.elementaryPoly a k) ∈ RT hab :=
  ⟨EQZab.tauAB a b (EQZab.inclX a b (EQSkewDifferential.elementary a k)),
    ⟨_, Subring.subset_closure (Or.inl ⟨k, rfl⟩), rfl⟩, by
      rw [EQZab.tauAB_inclX, EQFix.theta_elementary, EQZab.castHom_inclX]⟩

theorem place_right_elem_mem (k : ℕ) :
    ProjectorRank.place a (EQThick.right_le hab) (FiniteCompleteElementary.elementaryPoly b k) ∈ RT hab :=
  ⟨EQZab.tauAB a b (EQZab.inclY a b (EQSkewDifferential.elementary b k)),
    ⟨_, Subring.subset_closure (Or.inr ⟨k, rfl⟩), rfl⟩, by
      rw [EQZab.tauAB_inclY, EQFix.theta_elementary, EQZab.castHom_inclY]⟩

theorem RT_induction {P : SkewPolynomial (n+2) → Prop}
    (hx : ∀ k, P (ProjectorRank.place 0 (EQThick.left_le hab) (FiniteCompleteElementary.elementaryPoly a k)))
    (hy : ∀ k, P (ProjectorRank.place a (EQThick.right_le hab) (FiniteCompleteElementary.elementaryPoly b k)))
    (h0 : P 0) (h1 : P 1) (hadd : ∀ f g, P f → P g → P (f + g)) (hneg : ∀ f, P f → P (-f))
    (hmul : ∀ f g, P f → P g → P (f * g)) {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab) : P X := by
  obtain ⟨G, ⟨F, hF, rfl⟩, rfl⟩ := hX
  refine EQZab.osymAB_induction (P := fun F => P (EQZab.castHom hab (EQZab.tauAB a b F))) (fun k => ?_)
    (fun k => ?_) ?_ ?_ (fun f g hf hg => ?_) (fun f hf => ?_) (fun f g hf hg => ?_) hF
  · rw [EQZab.tauAB_inclX, EQFix.theta_elementary, EQZab.castHom_inclX]; exact hx k
  · rw [EQZab.tauAB_inclY, EQFix.theta_elementary, EQZab.castHom_inclY]; exact hy k
  · simpa using h0
  · simpa using h1
  · simpa only [map_add] using hadd _ _ hf hg
  · simpa only [map_neg] using hneg _ hf
  · simpa only [map_mul] using hmul _ _ hf hg

/-- A placed polynomial in the joint kernel of its block is killed by the crossings in the block. -/
theorem divided_place_elem {p k : ℕ} (h : p + k ≤ n + 2) (j : ℕ) (i : Fin (n+1)) (hi1 : p ≤ i.val)
    (hi2 : i.val + 1 < p + k) :
    AllRankDivided.divided i (ProjectorRank.place p h (FiniteCompleteElementary.elementaryPoly k j)) = 0 := by
  match k, h, hi2 with
  | 0, _, hi2 => omega
  | 1, _, hi2 => omega
  | m + 2, h, hi2 => exact EQZab.divided_place_kernel h (OddSymmetricKernel.elementary_mem m j) i hi1 hi2

/-- **Elements of `OΛ̃_a ⊠ OΛ̃_b` are killed by the crossings inside the blocks.** -/
theorem RT_blocksym {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab) :
    ∀ i : Fin (n+1), (i.val + 1 < a ∨ a ≤ i.val) → AllRankDivided.divided i X = 0 := by
  refine RT_induction hab (P := fun X => ∀ i : Fin (n+1), (i.val + 1 < a ∨ a ≤ i.val) →
    AllRankDivided.divided i X = 0) (fun k i hi => ?_) (fun k i hi => ?_) (fun i _ => map_zero _)
    (fun i _ => AllRankDivided.divided_one i) (fun f g hf hg i hi => ?_) (fun f hf i hi => ?_)
    (fun f g hf hg i hi => ?_) hX
  · rcases hi with hi | hi
    · exact divided_place_elem (EQThick.left_le hab) k i (Nat.zero_le _) (by omega)
    · exact EQThick.divided_place_eq_zero (EQThick.left_le hab) i (Or.inr (by omega)) _
  · rcases hi with hi | hi
    · exact EQThick.divided_place_eq_zero (EQThick.right_le hab) i (Or.inl hi) _
    · exact divided_place_elem (EQThick.right_le hab) k i hi (by have := i.isLt; omega)
  · rw [map_add, hf i hi, hg i hi, add_zero]
  · rw [map_neg, hf i hi, neg_zero]
  · rw [AllRankDivided.divided_mul, hf i hi, hg i hi, EQThick.sp_zero_mul, EQThick.sp_mul_zero, add_zero]

/-- `OΛ̃_{a+b} ⊆ OΛ̃_a ⊠ OΛ̃_b`. -/
theorem kernel_le_RT : OddSymmetricKernel.kernelSubring n ≤ RT hab := by
  rw [ElementaryGeneration.kernel_eq_elementaryClosure]
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨s, -, -, rfl⟩
  rw [EQThick.elementary_coproduct hab s]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (place_left_elem_mem hab _)
    (Subring.zsmul_mem _ (place_right_elem_mem hab _) _)

end Model


/-! ### `Γ` and `rev` on `OΛ̃_a ⊠ OΛ̃_b`; left spanning -/

section ModelGamma

variable {a b : ℕ} (hab : a + b = n + 2)

/-- The permutation of the strands underlying `w₀ × w₀` in rank `n + 2`. -/
def blockRevIdx (t : Fin (n+2)) : Fin (n+2) :=
  Fin.cast hab (EQFunctor.blockRevPerm a b (Fin.cast hab.symm t))

theorem blockRevN_generator (t : Fin (n+2)) :
    blockRevN hab (generator t) = generator (blockRevIdx hab t) := by
  simp [blockRevN, blockRevIdx, EQZab.castHom_generator, EQFunctor.blockRev_generator]

theorem gammaN_generator (t : Fin (n+2)) :
    gammaN hab (generator t) =
      ((-1 : ℤ) ^ (a.choose 2 + b.choose 2)) • generator (blockRevIdx hab t) := by
  rw [gammaN, RingHom.comp_apply, blockRevN_generator, EQFunctor.pow_parityInv_generator]

theorem blockRevN_blockRevN (X : SkewPolynomial (n+2)) : blockRevN hab (blockRevN hab X) = X := by
  simp only [blockRevN, RingHom.comp_apply, EQZab.castHom_symm_castHom, EQFunctor.blockRev_blockRev]

/-- `Γ = (w₀ × w₀) ∘ ι^{binom(a,2)+binom(b,2)}`. -/
theorem gammaN_eq (X : SkewPolynomial (n+2)) :
    gammaN hab X = blockRevN hab ((parityInv (n+2) ^ (a.choose 2 + b.choose 2)) X) := by
  have e : gammaN hab = (blockRevN hab).comp (parityInv (n+2) ^ (a.choose 2 + b.choose 2)) :=
    EQSkewDifferential.ringHom_ext fun t => by
      rw [gammaN_generator, RingHom.comp_apply, EQFunctor.pow_parityInv_generator, map_zsmul,
        blockRevN_generator]
  rw [e, RingHom.comp_apply]

theorem iterate_parityInv_iterate {N : ℕ} (m : ℕ) (X : SkewPolynomial N) :
    (parityInv N)^[m] ((parityInv N)^[m] X) = X := by
  rw [← Function.iterate_add_apply, ← two_mul, Function.iterate_mul]
  have h : (parityInv N)^[2] = id := funext fun Y => parityInv_parityInv Y
  rw [h, Function.iterate_id, id]

/-- `Γ` is an involution. -/
theorem gammaN_gammaN (X : SkewPolynomial (n+2)) : gammaN hab (gammaN hab X) = X := by
  conv_lhs => rw [gammaN_eq hab (gammaN hab X)]
  rw [gammaN, RingHom.comp_apply]
  simp only [RingHom.coe_pow]
  rw [iterate_parityInv_iterate, blockRevN_blockRevN]

theorem rev_place {p k : ℕ} (h : p + k ≤ n + 2) (A : SkewPolynomial k) :
    EQZab.rev (ProjectorRank.place p h A) = ProjectorRank.place p h (EQZab.rev A) := by
  induction A using EQSkewDifferential.induction_generator with
  | hgen j => rw [ProjectorRank.place_generator, EQZab.rev_generator, EQZab.rev_generator,
      ProjectorRank.place_generator]
  | h0 => simp [EQZab.rev]
  | h1 => rw [map_one, EQZab.rev_one, EQZab.rev_one, map_one]
  | hadd f g hf hg => rw [map_add, EQZab.rev_add, hf, hg, EQZab.rev_add, map_add]
  | hneg f hf => rw [map_neg, EQZab.rev_neg, hf, EQZab.rev_neg, map_neg]
  | hmul f g hf hg => rw [map_mul, EQZab.rev_mul, hf, hg, EQZab.rev_mul, map_mul]

/-- `rev ∘ Γ = Γ ∘ rev`. -/
theorem rev_gammaN (X : SkewPolynomial (n+2)) : EQZab.rev (gammaN hab X) = gammaN hab (EQZab.rev X) := by
  induction X using EQSkewDifferential.induction_generator with
  | hgen t => rw [gammaN_generator, EQZab.rev_zsmul, EQZab.rev_generator, EQZab.rev_generator,
      gammaN_generator]
  | h0 => simp [EQZab.rev]
  | h1 => rw [map_one, EQZab.rev_one, map_one]
  | hadd f g hf hg => rw [map_add, EQZab.rev_add, hf, hg, EQZab.rev_add, map_add]
  | hneg f hf => rw [map_neg, EQZab.rev_neg, hf, EQZab.rev_neg, map_neg]
  | hmul f g hf hg => rw [map_mul, EQZab.rev_mul, hf, hg, EQZab.rev_mul, map_mul]

theorem gammaN_mem_RT {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab) : gammaN hab X ∈ RT hab := by
  refine RT_induction hab (P := fun X => gammaN hab X ∈ RT hab) (fun k => ?_) (fun k => ?_)
    (by rw [map_zero]; exact zero_mem _) (by rw [map_one]; exact one_mem _)
    (fun f g hf hg => by rw [map_add]; exact add_mem hf hg) (fun f hf => by rw [map_neg]; exact neg_mem hf)
    (fun f g hf hg => by rw [map_mul]; exact mul_mem hf hg) hX
  · rw [gammaN_place_left, EQFix.eq_2_22_elementaryPoly, iterate_parityInv_zsmul,
      iterate_parityInv_of_mem _ (elementaryPoly_mem_grading a k), smul_smul, map_zsmul]
    exact Subring.zsmul_mem _ (place_left_elem_mem hab k) _
  · rw [gammaN_place_right, EQFix.eq_2_22_elementaryPoly, iterate_parityInv_zsmul,
      iterate_parityInv_of_mem _ (elementaryPoly_mem_grading b k), smul_smul, map_zsmul]
    exact Subring.zsmul_mem _ (place_right_elem_mem hab k) _

theorem rev_mem_RT {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab) : EQZab.rev X ∈ RT hab := by
  refine RT_induction hab (P := fun X => EQZab.rev X ∈ RT hab) (fun k => ?_) (fun k => ?_)
    (by simp [EQZab.rev]) (by rw [EQZab.rev_one]; exact one_mem _)
    (fun f g hf hg => by rw [EQZab.rev_add]; exact add_mem hf hg)
    (fun f hf => by rw [EQZab.rev_neg]; exact neg_mem hf)
    (fun f g hf hg => by rw [EQZab.rev_mul]; exact mul_mem hg hf) hX
  · rw [rev_place, EQZab.rev_elementaryPoly, map_zsmul]
    exact Subring.zsmul_mem _ (place_left_elem_mem hab k) _
  · rw [rev_place, EQZab.rev_elementaryPoly, map_zsmul]
    exact Subring.zsmul_mem _ (place_right_elem_mem hab k) _

theorem iterate_parityInv_of_parity {N : ℕ} (m k : ℕ) {f : SkewPolynomial N}
    (hf : parityInv N f = (-1 : ℤ) ^ k • f) : (parityInv N)^[m] f = ((-1 : ℤ) ^ (m * k)) • f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_zsmul, hf, smul_smul, ← pow_add]
    congr 1; ring

/-- `rev(Γ(s̃_μ(y))) = ± s̃_μ(y)`. -/
theorem rev_gammaN_twisted (μ : Fin b → ℕ) :
    ∃ ε : ℤ, EQZab.rev (gammaN hab (ProjectorRank.place a (EQThick.right_le hab) (EQSchur.twisted b μ))) =
      ε • ProjectorRank.place a (EQThick.right_le hab) (EQSchur.twisted b μ) := by
  obtain ⟨s, hs⟩ : ∃ s : ℤ, longestPerm b (EQSchur.twisted b μ) = s • EQZab.twistedHat b μ := by
    refine ⟨EQZab.hatCorr b μ * (-1) ^ (b.choose 3 + b.choose 2 * ∑ j, μ j + EQZab.pairSum μ), ?_⟩
    rw [EQZab.lemma_4_5_bottom, smul_smul]
    have hsq : (EQZab.hatCorr b μ * (-1) ^ (b.choose 3 + b.choose 2 * ∑ j, μ j + EQZab.pairSum μ)) *
        (EQZab.hatCorr b μ * (-1) ^ (b.choose 3 + b.choose 2 * ∑ j, μ j + EQZab.pairSum μ)) = 1 := by
      rw [mul_mul_mul_comm, EQZab.hatCorr, ← pow_add, ← pow_add, ← two_mul, ← two_mul, pow_mul, pow_mul]
      simp
    rw [hsq, one_smul]
  obtain ⟨s', hs'⟩ : ∃ s' : ℤ, EQZab.rev (EQZab.twistedHat b μ) = s' • EQSchur.twisted b μ := by
    refine ⟨(-1) ^ (b.choose 4 + (∑ j, μ j) * b.choose 2), ?_⟩
    have h := congrArg EQZab.rev (EQZab.rev_twisted_exact μ)
    rw [EQZab.rev_rev, EQZab.rev_zsmul] at h
    rw [h, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp
  have hpar : parityInv b (longestPerm b (EQSchur.twisted b μ)) =
      (-1 : ℤ) ^ (∑ j, μ j) • longestPerm b (EQSchur.twisted b μ) := by
    rw [EQSchur.parityInv_longestPerm, EQSchur.parityInv_twisted, map_zsmul]
  refine ⟨(-1) ^ ((a.choose 2 + b.choose 2) * ∑ j, μ j) * s * s', ?_⟩
  rw [gammaN_place_right, rev_place, iterate_parityInv_of_parity _ _ hpar, EQZab.rev_zsmul, hs,
    EQZab.rev_zsmul, hs', smul_smul, smul_smul, map_zsmul]

/-- **Left spanning**: every element of `OΛ̃_a ⊠ OΛ̃_b` is `Σ_μ Γ(k_μ) s̃_μ(y)` with `k_μ ∈ OΛ̃_{a+b}`. -/
theorem RT_left_span {X : SkewPolynomial (n+2)} (hX : X ∈ RT hab) :
    ∃ K : (Fin b → ℕ) → SkewPolynomial (n+2), (∀ μ, K μ ∈ OddSymmetricKernel.kernelSubring n) ∧
      X = ∑ μ ∈ BoxPartitionCount.box b a,
        gammaN hab (K μ) * ProjectorRank.place a (EQThick.right_le hab) (EQSchur.twisted b μ) := by
  have hV : gammaN hab (EQZab.rev X) ∈ RT hab := gammaN_mem_RT hab (rev_mem_RT hab hX)
  obtain ⟨G, hG, hGV⟩ := hV
  obtain ⟨c, hc, hGc⟩ := EQZab.zab_span_twisted hG
  have hX' : X = EQZab.rev (gammaN hab (gammaN hab (EQZab.rev X))) := by
    rw [gammaN_gammaN, EQZab.rev_rev]
  choose ε hε using fun μ => rev_gammaN_twisted hab μ
  refine ⟨fun μ => ε μ • EQZab.rev (EQZab.castHom hab (EQSkewDifferential.twistRev (a+b) (c μ))), fun μ =>
    Subring.zsmul_mem _ (EQZab.rev_mem_kernel (EQZab.castHom_twistRev_mem hab (hc μ))) _, ?_⟩
  rw [hX', ← hGV, hGc, map_sum, map_sum, EQZab.rev_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_mul, map_mul, EQZab.rev_mul, rev_gammaN, EQZab.castHom_inclY, hε μ, map_zsmul,
    mul_smul_comm, smul_mul_assoc]

end ModelGamma

end

end OddMath.Frontier.EQFrob
