import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-!
# EK odd pairing: nonnegative matrices and row splitting

EK arXiv:1107.5610v2 §2.1 (2.1), Prop. 2.2, pp.6–8.
Rows are top platforms β, columns bottom platforms α. Crossing pairs have
row i < k and column l < j, with weight M i j * M k l. Zero parts are allowed
as empty platforms. This is the q=-1 integer specialization.

PARTIAL source premise: this file proves the matrix convolution, not the
equivalence with minimal double-coset permutations or the full algebra-level
Proposition 2.2. The source bridge remains an explicit separate obligation.
-/
namespace OddMath.Frontier.EKPairingMatrices
open scoped BigOperators

abbrev Raw (r c : ℕ) := Fin r → Fin c → ℕ

def rowSum {r c : ℕ} (M : Raw r c) (i : Fin r) : ℕ := ∑ j, M i j
def colSum {r c : ℕ} (M : Raw r c) (j : Fin c) : ℕ := ∑ i, M i j

def Mat {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :=
  {M : Raw r c // rowSum M = β ∧ colSum M = α}

instance {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    CoeFun (Mat β α) (fun _ => Raw r c) := ⟨Subtype.val⟩

 theorem entry_le {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (M : Mat β α) (i : Fin r) (j : Fin c) : M i j ≤ α j := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (M k j))
    (Finset.mem_univ i)
  change M i j ≤ colSum M j at h
  simpa only [M.property.2] using h

noncomputable instance {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    Fintype (Mat β α) := Fintype.ofInjective
  (fun M : Mat β α => fun i j => (⟨M i j, Nat.lt_succ_of_le (entry_le M i j)⟩ : Fin (α j + 1)))
  (by intro M N h; apply Subtype.ext; funext i j
      exact congrArg Fin.val (congrFun (congrFun h i) j))

def crossing {r c : ℕ} (M : Raw r c) : ℕ :=
  ∑ i, ∑ k, if i < k then ∑ j, ∑ l, if l < j then M i j * M k l else 0 else 0

/-- Crossings from the first row block to the second. -/
def crossCols {c : ℕ} (u v : Fin c → ℕ) : ℕ :=
  ∑ j, ∑ l, if l < j then u j * v l else 0

def join {r s c : ℕ} (U : Raw r c) (V : Raw s c) : Raw (r+s) c := Fin.addCases U V

@[simp] theorem join_left {r s c : ℕ} (U : Raw r c) (V : Raw s c) (i : Fin r) :
    join U V (Fin.castAdd s i) = U i := by simp [join]
@[simp] theorem join_right {r s c : ℕ} (U : Raw r c) (V : Raw s c) (i : Fin s) :
    join U V (Fin.natAdd r i) = V i := by simp [join]

@[simp] theorem colSum_join {r s c : ℕ} (U : Raw r c) (V : Raw s c) :
    colSum (join U V) = fun j => colSum U j + colSum V j := by
  funext j; simp [colSum, Fin.sum_univ_add]

 theorem cross_blocks {r s c : ℕ} (U : Raw r c) (V : Raw s c) :
    (∑ i, ∑ k, ∑ j, ∑ l, if l < j then U i j * V k l else 0) =
      crossCols (colSum U) (colSum V) := by
  unfold crossCols colSum
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_irrel]
  conv_lhs =>
    arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1; funext j
  conv_lhs =>
    arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1; funext l
  rw [Finset.sum_comm]
  split_ifs <;> simp_all

 theorem crossing_join {r s c : ℕ} (U : Raw r c) (V : Raw s c) :
    crossing (join U V) = crossing U + crossing V +
      crossCols (colSum U) (colSum V) := by
  have lr (i : Fin r) (k : Fin s) : Fin.castAdd s i < Fin.natAdd r k := by
    simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega
  have rl (i : Fin s) (k : Fin r) : ¬ Fin.natAdd r i < Fin.castAdd s k := by
    simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega
  have ll (i k : Fin r) : (Fin.castAdd s i < Fin.castAdd s k) = (i < k) := rfl
  have rr (i k : Fin s) : (Fin.natAdd r i < Fin.natAdd r k) = (i < k) := by
    simp only [Fin.lt_def, Fin.coe_natAdd, Nat.add_lt_add_iff_left]
  simp only [crossing, Fin.sum_univ_add, join_left, join_right,
    ll, rr, lr, rl, if_true, if_false,
    Finset.sum_add_distrib, Finset.sum_const_zero, zero_add]
  rw [cross_blocks]
  omega

noncomputable def pairing {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) : ℤ :=
  ∑ M : Mat β α, (-1 : ℤ) ^ crossing M

 theorem total_eq {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ} (M : Mat β α) :
    ∑ i, β i = ∑ j, α j := by
  calc
    _ = ∑ i, rowSum M i := by simp only [M.property.1]
    _ = ∑ j, colSum M j := Finset.sum_comm
    _ = _ := by simp only [M.property.2]

 theorem pairing_degree_mismatch {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (h : (∑ i, β i) ≠ ∑ j, α j) : pairing β α = 0 := by
  haveI : IsEmpty (Mat β α) := ⟨fun M => h (total_eq M)⟩
  exact Finset.sum_eq_zero (fun M _ => isEmptyElim M)

/-- Every coordinate split 0 ≤ u_j ≤ α_j, including zero and empty cases. -/
abbrev Splits {c : ℕ} (α : Fin c → ℕ) := (j : Fin c) → Fin (α j + 1)
abbrev upper {c : ℕ} {α : Fin c → ℕ} (u : Splits α) (j : Fin c) : ℕ := u j
abbrev lower {c : ℕ} {α : Fin c → ℕ} (u : Splits α) (j : Fin c) : ℕ := α j - u j

abbrev SplitMatrices {r s c : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :=
  Σ u : Splits α, Mat β (upper u) × Mat γ (lower u)

def joinMat {r s c : ℕ} {β : Fin r → ℕ} {γ : Fin s → ℕ} {α : Fin c → ℕ}
    (z : SplitMatrices β γ α) : Mat (Fin.addCases β γ) α :=
  ⟨join z.2.1 z.2.2, by
    constructor
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro k
        simpa only [rowSum, join_left, Fin.addCases_left] using congrFun z.2.1.property.1 k
      · intro k
        simpa only [rowSum, join_right, Fin.addCases_right] using congrFun z.2.2.property.1 k
    · rw [colSum_join, z.2.1.property.2, z.2.2.property.2]
      funext j
      exact Nat.add_sub_of_le (Nat.le_of_lt_succ (z.1 j).isLt)⟩

def top {r s c : ℕ} (M : Raw (r+s) c) : Raw r c := fun i => M (Fin.castAdd s i)
def bottom {r s c : ℕ} (M : Raw (r+s) c) : Raw s c := fun i => M (Fin.natAdd r i)

@[simp] theorem join_top_bottom {r s c : ℕ} (M : Raw (r+s) c) :
    join (top M) (bottom M) = M := by
  funext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp [top, bottom]

 theorem split_col {r s c : ℕ} {β : Fin r → ℕ} {γ : Fin s → ℕ} {α : Fin c → ℕ}
    (M : Mat (Fin.addCases β γ) α) (j : Fin c) :
    colSum (top M) j + colSum (bottom M) j = α j := by
  have h := congrFun (colSum_join (top M) (bottom M)) j
  simpa only [join_top_bottom, M.property.2] using h.symm

 def splitMat {r s c : ℕ} {β : Fin r → ℕ} {γ : Fin s → ℕ} {α : Fin c → ℕ}
    (M : Mat (Fin.addCases β γ) α) : SplitMatrices β γ α :=
  ⟨(fun j => ⟨colSum (top M) j, by have := split_col M j; omega⟩),
    ⟨top M, by
      constructor
      · funext i
        simpa only [rowSum, top, Fin.addCases_left] using congrFun M.property.1 (Fin.castAdd s i)
      · rfl⟩,
    ⟨bottom M, by
      constructor
      · funext i
        simpa only [rowSum, bottom, Fin.addCases_right] using congrFun M.property.1 (Fin.natAdd r i)
      · funext j; change colSum (bottom M) j = α j - colSum (top M) j
        have := split_col M j; omega⟩⟩

 theorem joinMat_injective {r s c : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    Function.Injective (@joinMat r s c β γ α) := by
  rintro ⟨u, U, V⟩ ⟨v, W, X⟩ h
  have ht : (U : Raw r c) = W := by
    funext i j
    have := congrArg (fun M : Mat (Fin.addCases β γ) α => M (Fin.castAdd s i) j) h
    simpa only [joinMat, join_left] using this
  have hb : (V : Raw s c) = X := by
    funext i j
    have := congrArg (fun M : Mat (Fin.addCases β γ) α => M (Fin.natAdd r i) j) h
    simpa only [joinMat, join_right] using this
  have huv : u = v := by
    funext j; apply Fin.ext
    have := congrArg (fun M : Raw r c => colSum M j) ht
    simpa only [U.property.2, W.property.2] using this
  subst v
  have hu : U = W := Subtype.ext ht
  have hv : V = X := Subtype.ext hb
  subst W; subst X; rfl

/-- Actual bijection, not a decomposition certificate supplied by callers. -/
noncomputable def matrixEquivSplit {r s c : ℕ}
    (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    Mat (Fin.addCases β γ) α ≃ SplitMatrices β γ α :=
  (Equiv.ofBijective joinMat ⟨joinMat_injective β γ α, by
    intro M; refine ⟨splitMat M, ?_⟩
    apply Subtype.ext; exact join_top_bottom M⟩).symm

 theorem crossing_joinMat {r s c : ℕ}
    {β : Fin r → ℕ} {γ : Fin s → ℕ} {α : Fin c → ℕ}
    (z : SplitMatrices β γ α) :
    crossing (joinMat z) = crossing z.2.1 + crossing z.2.2 +
      crossCols (upper z.1) (lower z.1) := by
  change crossing (join z.2.1 z.2.2) = _
  rw [crossing_join, z.2.1.property.2, z.2.2.property.2]

/-- Word-level q=-1 convolution underlying EK Proposition 2.2. -/
theorem pairing_convolution {r s c : ℕ}
    (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    pairing (Fin.addCases β γ) α =
      ∑ u : Splits α, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
        pairing β (upper u) * pairing γ (lower u) := by
  classical
  unfold pairing
  rw [← (matrixEquivSplit β γ α).symm.sum_comp (fun M => (-1 : ℤ) ^ crossing M)]
  change (∑ z : SplitMatrices β γ α, (-1 : ℤ) ^ crossing (joinMat z)) = _
  simp only [crossing_joinMat, pow_add, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro U _
  apply Finset.sum_congr rfl; intro V _
  ring

def transpose {r c : ℕ} (M : Raw r c) : Raw c r := fun j i => M i j

/-- Four-index version exposes the symmetry (i,k,j,l) ↔ (l,j,k,i). -/
theorem crossing_expanded {r c : ℕ} (M : Raw r c) :
    crossing M = ∑ i, ∑ k, ∑ j, ∑ l,
      if i < k ∧ l < j then M i j * M k l else 0 := by
  unfold crossing
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  by_cases h : i < k <;> simp [h]

theorem crossing_transpose {r c : ℕ} (M : Raw r c) :
    crossing (transpose M) = crossing M := by
  simp only [crossing_expanded]
  conv_lhs =>
    arg 2; ext i
    arg 2; ext k
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  simp only [transpose, and_comm, mul_comm]

def transposeEquiv {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    Mat β α ≃ Mat α β where
  toFun M := ⟨transpose M, M.property.2, M.property.1⟩
  invFun M := ⟨transpose M, M.property.2, M.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pairing_transpose {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    pairing β α = pairing α β := by
  unfold pairing
  apply Fintype.sum_equiv (transposeEquiv β α)
  intro M
  exact congrArg (fun n => (-1 : ℤ) ^ n) (crossing_transpose M).symm

/-- Empty/zero-degree matrices are literally the unique zero matrix. -/
theorem zero_columns_unique {r c : ℕ} {β : Fin r → ℕ} (M : Mat β (fun _ : Fin c => 0)) :
    (M : Raw r c) = fun _ _ => 0 := by
  funext i j; have := entry_le M i j; omega

theorem pairing_zero_zero (r c : ℕ) :
    pairing (fun _ : Fin r => 0) (fun _ : Fin c => 0) = 1 := by
  classical
  let Z : Mat (fun _ : Fin r => 0) (fun _ : Fin c => 0) :=
    ⟨fun _ _ => 0, by constructor <;> funext i <;> simp [rowSum, colSum]⟩
  have hz (M : Mat (fun _ : Fin r => 0) (fun _ : Fin c => 0)) : M = Z :=
    Subtype.ext (zero_columns_unique M)
  unfold pairing
  rw [Finset.sum_eq_single Z]
  · simp [Z, crossing]
  · intro M _ h; exact (h (hz M)).elim
  · simp

/-- Deleting any zero platform respects the source convention h₀ = 1. -/
theorem zero_row {r c : ℕ} {β : Fin r → ℕ} {α : Fin c → ℕ}
    (M : Mat β α) (p : Fin r) (hp : β p = 0) (j : Fin c) : M p j = 0 := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (M p k))
    (Finset.mem_univ j)
  change M p j ≤ rowSum M p at h
  rw [M.property.1, hp] at h
  omega

def eraseRow {r c : ℕ} (p : Fin (r+1)) (M : Raw (r+1) c) : Raw r c :=
  fun i => M (p.succAbove i)

theorem crossing_erase_zero {r c : ℕ} (p : Fin (r+1)) (M : Raw (r+1) c)
    (hz : ∀ j, M p j = 0) : crossing (eraseRow p M) = crossing M := by
  unfold crossing
  rw [Fin.sum_univ_succAbove _ p]
  simp only [hz, zero_mul, Finset.sum_const_zero, ite_self, zero_add]
  apply Finset.sum_congr rfl; intro i _
  rw [Fin.sum_univ_succAbove _ p]
  simp only [hz, mul_zero, Finset.sum_const_zero, ite_self, zero_add,
    Fin.succAbove_lt_succAbove_iff, eraseRow]

def eraseMat {r c : ℕ} {β : Fin (r+1) → ℕ} {α : Fin c → ℕ}
    (p : Fin (r+1)) (hp : β p = 0) (M : Mat β α) : Mat (fun i => β (p.succAbove i)) α :=
  ⟨eraseRow p M, by
    constructor
    · funext i; exact congrFun M.property.1 (p.succAbove i)
    · funext j
      have h := congrFun M.property.2 j
      unfold colSum at h ⊢
      rw [Fin.sum_univ_succAbove _ p, zero_row M p hp j, zero_add] at h
      exact h⟩

def insertZeroMat {r c : ℕ} {β : Fin (r+1) → ℕ} {α : Fin c → ℕ}
    (p : Fin (r+1)) (hp : β p = 0) (M : Mat (fun i => β (p.succAbove i)) α) : Mat β α :=
  ⟨Fin.insertNth p (fun _ => 0) M, by
    constructor
    · funext i
      refine Fin.succAboveCases p ?_ ?_ i
      · simp [rowSum, hp]
      · intro k
        simpa only [rowSum, Fin.insertNth_apply_succAbove] using congrFun M.property.1 k
    · funext j
      unfold colSum
      rw [Fin.sum_univ_succAbove _ p]
      simpa only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_add]
        using congrFun M.property.2 j⟩

def eraseZeroEquiv {r c : ℕ} (β : Fin (r+1) → ℕ) (α : Fin c → ℕ)
    (p : Fin (r+1)) (hp : β p = 0) : Mat β α ≃ Mat (fun i => β (p.succAbove i)) α where
  toFun := eraseMat p hp
  invFun := insertZeroMat p hp
  left_inv M := by
    apply Subtype.ext; funext i j
    refine Fin.succAboveCases p ?_ ?_ i
    · simpa only [insertZeroMat, Fin.insertNth_apply_same] using (zero_row M p hp j).symm
    · intro k; simp [insertZeroMat, eraseMat, eraseRow]
  right_inv M := by
    apply Subtype.ext; funext i j
    simp [insertZeroMat, eraseMat, eraseRow]

theorem pairing_erase_zero_row {r c : ℕ} (β : Fin (r+1) → ℕ) (α : Fin c → ℕ)
    (p : Fin (r+1)) (hp : β p = 0) :
    pairing β α = pairing (fun i => β (p.succAbove i)) α := by
  unfold pairing
  apply Fintype.sum_equiv (eraseZeroEquiv β α p hp)
  intro M
  exact congrArg (fun n => (-1 : ℤ) ^ n)
    (crossing_erase_zero p M (zero_row M p hp)).symm

theorem pairing_erase_zero_column {r c : ℕ} (β : Fin r → ℕ) (α : Fin (c+1) → ℕ)
    (p : Fin (c+1)) (hp : α p = 0) :
    pairing β α = pairing β (fun j => α (p.succAbove j)) := by
  rw [pairing_transpose β α, pairing_erase_zero_row α β p hp,
    pairing_transpose (fun j => α (p.succAbove j)) β]

theorem pairing_single_row {c : ℕ} (α : Fin c → ℕ) :
    pairing (fun _ : Fin 1 => ∑ j, α j) α = 1 := by
  classical
  let Z : Mat (fun _ : Fin 1 => ∑ j, α j) α :=
    ⟨fun _ j => α j, by constructor <;> funext i <;> simp [rowSum, colSum]⟩
  have hz (M : Mat (fun _ : Fin 1 => ∑ j, α j) α) : M = Z := by
    apply Subtype.ext; funext i j
    have h := congrFun M.property.2 j
    simpa [colSum, Subsingleton.elim i 0] using h
  unfold pairing
  rw [Finset.sum_eq_single Z]
  · simp [Z, crossing]
  · intro M _ h; exact (h (hz M)).elim
  · simp

theorem pairing_single_column {r : ℕ} (β : Fin r → ℕ) :
    pairing β (fun _ : Fin 1 => ∑ i, β i) = 1 := by
  rw [pairing_transpose, pairing_single_row]

/-- Exhaustiveness is for all natural matrices, not a bounded sample. -/
theorem enumeration_complete {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (M : Raw r c) (h : rowSum M = β ∧ colSum M = α) :
    (⟨M, h⟩ : Mat β α) ∈ (Finset.univ : Finset (Mat β α)) := @Finset.mem_univ (Mat β α) _ ⟨M, h⟩

/-- Multiplicity matrix of actual labelled strands (not a chosen matrix). -/
def strandMatrix {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) : Raw r c :=
  fun i j => ∑ a, if T a = i ∧ B a = j then 1 else 0

private theorem sum_strandMatrix {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c)
    (f : Fin r → Fin c → ℕ) :
    ∑ i, ∑ j, strandMatrix T B i j * f i j = ∑ a, f (T a) (B a) := by
  unfold strandMatrix
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp [ite_and]

/-- Source diagrams have actual ordered endpoints and a genuine permutation.
The last field is exactly EK p.6: strands starting OR ending in the same
platform do not cross. No matrix decomposition or length certificate is assumed. -/
structure PlatformDiagram (n r c : ℕ) where
  topPlatform : Fin n → Fin r
  bottomPlatform : Fin n → Fin c
  top_monotone : Monotone topPlatform
  bottom_monotone : Monotone bottomPlatform
  perm : Equiv.Perm (Fin n)
  noWithin : ∀ a b, a < b →
    (bottomPlatform a = bottomPlatform b ∨ topPlatform (perm a) = topPlatform (perm b)) →
      perm a < perm b

def PlatformDiagram.matrix {n r c : ℕ} (D : PlatformDiagram n r c) : Raw r c :=
  strandMatrix (fun a => D.topPlatform (D.perm a)) D.bottomPlatform

def PlatformDiagram.length {n r c : ℕ} (D : PlatformDiagram n r c) : ℕ :=
  ∑ a, ∑ b, if a < b ∧ D.perm b < D.perm a then 1 else 0

/-- The source no-within-platform criterion reduces permutation inversions
precisely to opposite strict platform orders. -/
theorem PlatformDiagram.inversion_iff {n r c : ℕ} (D : PlatformDiagram n r c) (a b : Fin n) :
    (a < b ∧ D.perm b < D.perm a) ↔
      (D.bottomPlatform a < D.bottomPlatform b ∧
       D.topPlatform (D.perm b) < D.topPlatform (D.perm a)) := by
  constructor
  · rintro ⟨hab, hba⟩
    have hB := D.bottom_monotone (le_of_lt hab)
    have hT := D.top_monotone (le_of_lt hba)
    have neB : D.bottomPlatform a ≠ D.bottomPlatform b := by
      intro h; exact (not_lt_of_gt hba) (D.noWithin a b hab (Or.inl h))
    have neT : D.topPlatform (D.perm b) ≠ D.topPlatform (D.perm a) := by
      intro h; exact (not_lt_of_gt hba) (D.noWithin a b hab (Or.inr h.symm))
    exact ⟨lt_of_le_of_ne hB neB, lt_of_le_of_ne hT neT⟩
  · rintro ⟨hB, hT⟩
    constructor
    · by_contra h; exact (not_le_of_gt hB) (D.bottom_monotone (le_of_not_gt h))
    · by_contra h; exact (not_le_of_gt hT) (D.top_monotone (le_of_not_gt h))

theorem crossing_strandMatrix {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) :
    crossing (strandMatrix T B) =
      ∑ a, ∑ b, if T a < T b ∧ B b < B a then 1 else 0 := by
  have heq : crossing (strandMatrix T B) =
      ∑ i, ∑ j, strandMatrix T B i j *
        (∑ k, ∑ l, strandMatrix T B k l * (if i < k ∧ l < j then 1 else 0)) := by
    rw [crossing_expanded]
    conv_lhs =>
      arg 2; ext i
      rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [heq, sum_strandMatrix]
  apply Finset.sum_congr rfl; intro a _
  exact sum_strandMatrix T B _

/-- General source crossing-length equality, without a matrix↔diagram
bijection claim. The still-missing converse must construct and uniquely recover
such a permutation for every prescribed-margin matrix. -/
theorem PlatformDiagram.crossing_eq_length {n r c : ℕ} (D : PlatformDiagram n r c) :
    crossing D.matrix = D.length := by
  rw [PlatformDiagram.matrix, crossing_strandMatrix, PlatformDiagram.length, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  simp only [D.inversion_iff, and_comm]

theorem strandMatrix_rowSum {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) (i : Fin r) :
    rowSum (strandMatrix T B) i = ∑ a, if T a = i then 1 else 0 := by
  have h := sum_strandMatrix T B (fun k _ => if k = i then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, rowSum] using h

theorem strandMatrix_colSum {n r c : ℕ} (T : Fin n → Fin r) (B : Fin n → Fin c) (j : Fin c) :
    colSum (strandMatrix T B) j = ∑ a, if B a = j then 1 else 0 := by
  have h := sum_strandMatrix T B (fun _ l => if l = j then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, colSum] using h

/-- Actual endpoint platform cardinalities; the row count is independent of σ. -/
def PlatformDiagram.toMat {n r c : ℕ} (D : PlatformDiagram n r c) :
    Mat (fun i => ∑ a, if D.topPlatform a = i then 1 else 0)
      (fun j => ∑ a, if D.bottomPlatform a = j then 1 else 0) :=
  ⟨D.matrix, by
    constructor
    · funext i
      rw [PlatformDiagram.matrix, strandMatrix_rowSum]
      exact Equiv.sum_comp D.perm (fun a => if D.topPlatform a = i then 1 else 0)
    · funext j; exact strandMatrix_colSum _ _ j⟩

end OddMath.Frontier.EKPairingMatrices
