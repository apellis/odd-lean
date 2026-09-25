import OddMath.Frontier.EKRestrictedPairing
import OddMath.Frontier.EKNondegeneracyControls

/-! EK Lemma 2.15 (1107.5610v2, p.18) restricted nondegeneracy — generic
machinery (run 2236; the two degree-6 closures live in
`EKNondegeneracyAudit.Hge33_nondeg` / `Egt222_nondeg`).

Target: for BOTH witness spaces `H≥(3,3)` and
`E>(2,2,2)` inside degree six, `x ∈ S`, `(∀ y ∈ S, (x,y) = 0) → x = 0`.

Proved here (no assumed conclusion):

* `restrictedNondeg_iff_injective`: for an ARBITRARY submodule `S` of the
  actual integral quotient `Q`, restricted nondegeneracy ↔ injectivity of the
  restricted pairing-to-dual map `S →ₗ[ℤ] Module.Dual ℤ S`.
* `nondeg_of_gram_det`, `nondeg_of_gram_right_inverse`, `nondeg_of_le_span`:
  Gram-certificate criteria on spans of finite families / on submodules that
  are exactly such spans.
* `pairing_word_ev`, `pairing_hL`, `pairing_eL`: a kernel-reducible integer
  evaluator of the ACTUAL `quotientPairing` on one-colour `h`/`e` products,
  proved sound from existing `EKMixedPairing.pairing_word_mul` /
  `pairing_gen_word` (EK Prop 2.6 coproduct/adjointness + Prop 3.1 cells).
* `rowLens_mem_parts`: every Young diagram of size `d` has its row list in
  the exhaustive kernel-reducible enumeration `partsF d d d` (completeness).

The refuted middle equality `(H≥λ)⊥ = E>λᵀ` is NOT used in either direction;
no perfectness, direct-sum exhaustion, positivity, Gram–Schmidt or
determinant (3.4) input is used.
-/
namespace OddMath.Frontier.EKNondegeneracy
open EKSemiorthogonality EKRadicalQuotient
open scoped BigOperators

/-- The exact restricted-nondegeneracy predicate of the specification. -/
def RestrictedNondeg (S : Submodule ℤ Q) : Prop :=
  ∀ x ∈ S, (∀ y ∈ S, quotientPairing x y = 0) → x = 0

/-- Restricted pairing-to-dual map on an arbitrary submodule of `Q`. -/
noncomputable def restrictedDual (S : Submodule ℤ Q) : S →ₗ[ℤ] Module.Dual ℤ S :=
  quotientPairing.compl₁₂ S.subtype S.subtype

@[simp] theorem restrictedDual_apply (S : Submodule ℤ Q) (x y : S) :
    restrictedDual S x y = quotientPairing (x : Q) (y : Q) := rfl

/-- Genuine arbitrary-element consumer: restricted nondegeneracy is exactly
injectivity of the restricted pairing-to-dual map. -/
theorem restrictedNondeg_iff_injective (S : Submodule ℤ Q) :
    RestrictedNondeg S ↔ Function.Injective (restrictedDual S) := by
  constructor
  · intro h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply h x.1 x.2
    intro y hy
    have hxy := LinearMap.congr_fun hx ⟨y, hy⟩
    simpa using hxy
  · intro h x hx hy
    have hz : restrictedDual S ⟨x, hx⟩ = 0 := by
      apply LinearMap.ext
      intro y
      simpa using hy y.1 y.2
    have he := h (hz.trans (map_zero (restrictedDual S)).symm)
    simpa using congrArg Subtype.val he

/-- Orthogonality of a span element to every generator, as a row-vector
identity for the actual Gram matrix. -/
theorem gram_vecMul_zero {ι : Type*} [Fintype ι] (g : ι → Q) (c : ι → ℤ)
    (horth : ∀ y ∈ Submodule.span ℤ (Set.range g),
      quotientPairing (∑ i, c i • g i) y = 0) :
    Matrix.vecMul c (Matrix.of fun i j => quotientPairing (g i) (g j)) = 0 := by
  funext j
  have hj := horth (g j) (Submodule.subset_span ⟨j, rfl⟩)
  simp only [map_sum, map_smul, LinearMap.coeFn_sum, Finset.sum_apply,
    LinearMap.smul_apply, smul_eq_mul] at hj
  simpa [Matrix.vecMul, dotProduct] using hj

/-- Gram-determinant criterion on the span of an arbitrary finite family. -/
theorem nondeg_of_gram_det {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Q)
    (hdet : (Matrix.of fun i j => quotientPairing (g i) (g j)).det ≠ 0) :
    RestrictedNondeg (Submodule.span ℤ (Set.range g)) := by
  intro x hx horth
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have hc := Matrix.eq_zero_of_vecMul_eq_zero hdet (gram_vecMul_zero g c horth)
  subst hc
  simp

/-- Determinant-free criterion: an explicit integer right inverse `N` of the
actual Gram matrix (`G * N = 1`) forces restricted nondegeneracy. -/
theorem nondeg_of_gram_right_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → Q) (N : Matrix ι ι ℤ)
    (hN : (Matrix.of fun i j => quotientPairing (g i) (g j)) * N = 1) :
    RestrictedNondeg (Submodule.span ℤ (Set.range g)) := by
  intro x hx horth
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have hv := congrArg (fun v => Matrix.vecMul v N) (gram_vecMul_zero g c horth)
  simp only [Matrix.vecMul_vecMul, hN, Matrix.vecMul_one, Matrix.zero_vecMul] at hv
  subst hv
  simp

/-- Transfer to an arbitrary submodule `S` that is exactly the span of a
finite family of its own elements (both inclusions are hypotheses). -/
theorem nondeg_of_le_span {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Submodule ℤ Q)
    (g : ι → Q) (N : Matrix ι ι ℤ) (hg : ∀ i, g i ∈ S)
    (hle : S ≤ Submodule.span ℤ (Set.range g))
    (hN : (Matrix.of fun i j => quotientPairing (g i) (g j)) * N = 1) :
    RestrictedNondeg S := by
  have hge : Submodule.span ℤ (Set.range g) ≤ S :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hg)
  have heq : S = Submodule.span ℤ (Set.range g) := le_antisymm hle hge
  rw [heq]
  exact nondeg_of_gram_right_inverse g N hN

/-! ### Kernel-reducible evaluator of the ACTUAL pairing (run 2236)

`ev b e r β c α` is a structurally recursive integer evaluator.  Its soundness
theorem `pairing_word_ev` is proved from the existing EK Prop 2.6/3.1
ingredients `EKMixedPairing.pairing_word_mul` (actual adjointness/coproduct)
and `EKMixedPairing.pairing_gen_word` (single-platform pairing).  The value of
`quotientPairing` on one-colour words is therefore machine-derived; no table is
assumed. -/

section Evaluator
open EKMixedPairing EKPairingMatrices

def sumF : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + sumF n (fun i => f i.succ)

theorem sumF_eq : ∀ (n : ℕ) (f : Fin n → ℕ), ∑ i, f i = sumF n f
  | 0, f => by simp [sumF]
  | n+1, f => by rw [Fin.sum_univ_succ, sumF_eq n]; rfl

def prodF : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 1
  | n+1, f => f 0 * prodF n (fun i => f i.succ)

theorem prodF_eq : ∀ (n : ℕ) (f : Fin n → ℤ), ∏ i, f i = prodF n f
  | 0, f => by simp [prodF]
  | n+1, f => by rw [Fin.prod_univ_succ, prodF_eq n]; rfl

def crossF : (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → ℕ
  | 0, _, _ => 0
  | n+1, u, v => sumF n (fun j => u j.succ) * v 0 +
      crossF n (fun j => u j.succ) (fun j => v j.succ)

theorem crossF_eq : ∀ (n : ℕ) (u v : Fin n → ℕ), crossCols u v = crossF n u v
  | 0, u, v => by simp [crossCols, crossF]
  | n+1, u, v => by rw [EKPairingAdjoint.crossCols_succ, crossF_eq n, sumF_eq]; rfl

def sumTo : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n+1, f => sumTo n f + f n

theorem sumTo_eq : ∀ (n : ℕ) (f : ℕ → ℤ), ∑ i : Fin n, f i = sumTo n f
  | 0, f => by simp [sumTo]
  | n+1, f => by simp [Fin.sum_univ_castSucc, sumTo, sumTo_eq n]

def sumSplits : (c : ℕ) → (Fin c → ℕ) → ((Fin c → ℕ) → ℤ) → ℤ
  | 0, _, F => F Fin.elim0
  | c+1, α, F => sumTo (α 0 + 1) (fun i =>
      sumSplits c (fun j => α j.succ) (fun v => F (Fin.cons i v)))

theorem sumSplits_eq : ∀ (c : ℕ) (α : Fin c → ℕ) (F : (Fin c → ℕ) → ℤ),
    ∑ u : Splits α, F (fun j => (u j : ℕ)) = sumSplits c α F
  | 0, α, F => by
      rw [Fintype.sum_unique]
      simp only [sumSplits]
      congr 1; funext j; exact Fin.elim0 j
  | c+1, α, F => by
      rw [← (Fin.consEquiv (fun j => Fin (α j + 1))).sum_comp, Fintype.sum_prod_type]
      simp only [sumSplits]
      rw [← sumTo_eq]
      apply Finset.sum_congr rfl; intro i _
      rw [← sumSplits_eq c]
      apply Finset.sum_congr rfl; intro w _
      congr 1; funext j
      refine Fin.cases ?_ ?_ j <;> simp [Fin.consEquiv]

/-- Kernel-reducible one-colour evaluator (top colour `b`, bottom colour `e`). -/
def ev (b e : Bool) : (r : ℕ) → (Fin r → ℕ) → (c : ℕ) → (Fin c → ℕ) → ℤ
  | 0, _, c, α => if 0 = sumF c α then prodF c (fun j => cell b e (α j)) else 0
  | r+1, β, c, α => sumSplits c α (fun v =>
      (-1 : ℤ) ^ crossF c v (fun j => α j - v j) *
      (if β 0 = sumF c v then prodF c (fun j => cell b e (v j)) else 0) *
      ev b e r (fun i => β i.succ) c (fun j => α j - v j))

/-- Soundness of the evaluator against the actual free-algebra pairing. -/
theorem pairing_word_ev (b e : Bool) : ∀ (r : ℕ) (β : Fin r → ℕ) (c : ℕ) (α : Fin c → ℕ),
    EKPairingAdjoint.pairing (word β (fun _ => b)) (word α (fun _ => e)) = ev b e r β c α
  | 0, β, c, α => by
      rw [word_zero, ← gen_zero b, pairing_gen_word]
      simp only [ev, sumF_eq, prodF_eq]
  | r+1, β, c, α => by
      rw [word_succ, pairing_word_mul]
      simp only [ev]
      rw [← sumSplits_eq]
      apply Finset.sum_congr rfl; intro u _
      rw [pairing_gen_word, pairing_word_ev b e r, crossF_eq, sumF_eq, prodF_eq]

/-- Ordered `h`/`e` products of a list of parts, in the actual `Q`. -/
def hL (l : List ℕ) : Q := (l.map EKElementaryQuotient.h).prod
def eL (l : List ℕ) : Q := (l.map EKElementaryQuotient.e).prod

theorem hL_eq (l : List ℕ) :
    hL l = pi (word (fun i : Fin l.length => l.get i) (fun _ => false)) := by
  rw [← mixed_eq_pi]
  simp [hL, mixed, List.ofFn_getElem_eq_map]

theorem eL_eq (l : List ℕ) :
    eL l = pi (word (fun i : Fin l.length => l.get i) (fun _ => true)) := by
  rw [← mixed_eq_pi]
  simp [eL, mixed, List.ofFn_getElem_eq_map]

def evL (b e : Bool) (l l' : List ℕ) : ℤ := ev b e l.length l.get l'.length l'.get

theorem pairing_hL (l l' : List ℕ) :
    quotientPairing (hL l) (hL l') = evL false false l l' := by
  rw [hL_eq, hL_eq, quotientPairing_pi, pairing_word_ev]; rfl

theorem pairing_eL (l l' : List ℕ) :
    quotientPairing (eL l) (eL l') = evL true true l l' := by
  rw [eL_eq, eL_eq, quotientPairing_pi, pairing_word_ev]; rfl

end Evaluator

/-! ### Exhaustive partition enumeration (for exact-lex shape classification) -/

/-- Fuel-bounded partitions of `n` with all parts `≤ m` (kernel-reducible). -/
def partsF : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, n, _ => if n = 0 then [[]] else []
  | f+1, n, m => if n = 0 then [[]] else
      (List.range m).flatMap (fun k => if k + 1 ≤ n then
        (partsF f (n - (k+1)) (k+1)).map ((k+1) :: ·) else [])

/-- Completeness: every weakly decreasing positive list of sum `n`, parts `≤ m`,
is enumerated (for all such lists, not a sample). -/
theorem mem_partsF : ∀ (l : List ℕ) (f n m : ℕ), l.Sorted (· ≥ ·) → (∀ x ∈ l, 0 < x) →
    (∀ x ∈ l, x ≤ m) → l.sum = n → n ≤ f → l ∈ partsF f n m
  | [], f, n, m, _, _, _, hs, _ => by
      cases f <;> simp_all [partsF]
  | a :: t, f, n, m, hl, hp, hm, hs, hf => by
      have ha : 0 < a := hp a (by simp)
      have ham : a ≤ m := hm a (by simp)
      simp only [List.sum_cons] at hs
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      have hn : n ≠ 0 := by omega
      have ht := mem_partsF t f (n - a) a (List.sorted_cons.mp hl).2
        (fun x hx => hp x (by simp [hx]))
        (fun x hx => (List.sorted_cons.mp hl).1 x hx) (by omega) (by omega)
      simp only [partsF, if_neg hn, List.mem_flatMap, List.mem_range]
      refine ⟨a - 1, by omega, ?_⟩
      have e : a - 1 + 1 = a := by omega
      rw [e, if_pos (by omega)]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩

/-- Every Young diagram of size `d` has its row list in `partsF d d d`. -/
theorem rowLens_mem_parts (d : ℕ) (ν : YoungDiagram) (h : ν.card = d) :
    ν.rowLens ∈ partsF d d d := by
  have hs : ν.rowLens.sum = d := by rw [EKIntegralBases.rowLens_sum, h]
  apply mem_partsF _ _ _ _ ν.rowLens_sorted ν.pos_of_mem_rowLens _ hs le_rfl
  intro x hx
  rw [← hs]
  exact List.le_sum_of_mem hx

end OddMath.Frontier.EKNondegeneracy
