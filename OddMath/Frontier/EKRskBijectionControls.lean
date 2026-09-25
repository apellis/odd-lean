import OddMath.Frontier.TableauInsertion

/-!
# EK Thm 4.3 / (4.4) controls, compiled before production

Source: Ellis–Khovanov arXiv:1107.5610v2, §4.1, pp. 32–33, Theorem 4.3, (4.4), Examples 4.4, 4.5.

Frozen RSK definition (the fixed specification): read the two-line array lexicographically
(row index `u` weakly increasing, column index `v` weakly increasing on ties),
`P_k := TableauInsertion.insert P_{k-1} v_k` and `Q_k := Q_{k-1}` with `u_k` placed in the unique
new cell of `P_k`.  `TableauInsertion.insert` is *defined* from the list-level row recursion
`TableauRowRecursion.runRows` (its `tableau` is `TableauOfRows.tableau` of `runRows … .output`,
`insert_rows`) and its `newCell` is literally `TableauRowRecursion.newCell` (`insert_newCell`, rfl).
The computable mirror below runs exactly these existing list-level functions, so the kernel can
evaluate the printed examples by `decide`.  Conventions: English zero-based cells; a `Fin n` letter
`a` is the paper label `a.val + 1`; matrix row `i : Fin m` is the paper label `i.val + 1`.
These are CONTROLS only; nothing here is the production theorem.
-/

namespace OddMath.Frontier.EKRskBijection
open TableauRowRecursion

/-- The weakly increasing word of a matrix row: `r j` copies of the letter `j`, `j` ascending. -/
def rowWord {n : ℕ} (r : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun j => List.replicate (r j) j

/-- EK's two-line array, read "as if reading a book": pairs `(u, v)` = (row index, column letter)
in lexicographic order; each entry `k` contributes `k` equal columns. -/
def twoLine {m n : ℕ} (A : Fin m → Fin n → ℕ) : List (ℕ × Fin n) :=
  (List.finRange m).flatMap fun i => (rowWord (A i)).map fun j => (i.val, j)

/-- One frozen RSK step at list level: row-insert `v` (existing `runRows`), record the paper
label `u + 1` at the existing `newCell`. -/
def mirrorStep {n : ℕ} (s : List (List (Fin n)) × List ((ℕ × ℕ) × ℕ)) (x : ℕ × Fin n) :
    List (List (Fin n)) × List ((ℕ × ℕ) × ℕ) :=
  ((runRows n s.1 x.2).output, s.2 ++ [(newCell n s.1 x.2, x.1 + 1)])

/-- The frozen RSK map at list level: rows of `P` and the recorded `Q` cells. -/
def rskMirror {m n : ℕ} (A : Fin m → Fin n → ℕ) :
    List (List (Fin n)) × List ((ℕ × ℕ) × ℕ) :=
  (twoLine A).foldl mirrorStep ([], [])

/-- `P` rows in paper labels. -/
def pRows {m n : ℕ} (A : Fin m → Fin n → ℕ) : List (List ℕ) :=
  (rskMirror A).1.map fun w => w.map fun a => a.val + 1

/-- Recorded label at a cell (latest record wins; `0` off the recorded cells). -/
def qLook (cs : List ((ℕ × ℕ) × ℕ)) (p : ℕ × ℕ) : ℕ :=
  ((cs.reverse.find? fun e => e.1 = p).map Prod.snd).getD 0

/-- `Q` rows in paper labels, read off the recorded cells on the shape of `P`. -/
def qRows {m n : ℕ} (A : Fin m → Fin n → ℕ) : List (List ℕ) :=
  let s := rskMirror A
  (List.range s.1.length).map fun r =>
    (List.range (s.1.getD r []).length).map fun c => qLook s.2 (r, c)

/-! ## Example 4.5 (EK p.33): μ = (2,2) (row sums), ρ = (2,1,1) (column sums), all four matrices -/

def ex45a : Fin 2 → Fin 3 → ℕ := ![![2, 0, 0], ![0, 1, 1]]
def ex45b : Fin 2 → Fin 3 → ℕ := ![![1, 1, 0], ![1, 0, 1]]
def ex45c : Fin 2 → Fin 3 → ℕ := ![![1, 0, 1], ![1, 1, 0]]
def ex45d : Fin 2 → Fin 3 → ℕ := ![![0, 1, 1], ![2, 0, 0]]

theorem ex45a_rsk : pRows ex45a = [[1, 1, 2, 3]] ∧ qRows ex45a = [[1, 1, 2, 2]] := by decide
theorem ex45b_rsk : pRows ex45b = [[1, 1, 3], [2]] ∧ qRows ex45b = [[1, 1, 2], [2]] := by decide
theorem ex45c_rsk : pRows ex45c = [[1, 1, 2], [3]] ∧ qRows ex45c = [[1, 1, 2], [2]] := by decide
theorem ex45d_rsk : pRows ex45d = [[1, 1], [2, 3]] ∧ qRows ex45d = [[1, 1], [2, 2]] := by decide

/-- Row sums (2,2) and column sums (2,1,1) of all four printed matrices. -/
theorem ex45_margins :
    (∀ A ∈ [ex45a, ex45b, ex45c, ex45d],
      (∀ i, ∑ j, A i j = ![2, 2] i) ∧ (∀ j, ∑ i, A i j = ![2, 1, 1] j)) := by decide

/-! ## Example 4.4 (EK p.33): μ = (1,1,1) (row sums), ρ = (2,1) (column sums) -/

def ex44a : Fin 3 → Fin 2 → ℕ := ![![1, 0], ![1, 0], ![0, 1]]
def ex44b : Fin 3 → Fin 2 → ℕ := ![![1, 0], ![0, 1], ![1, 0]]
def ex44c : Fin 3 → Fin 2 → ℕ := ![![0, 1], ![1, 0], ![1, 0]]

theorem ex44a_rsk : pRows ex44a = [[1, 1, 2]] ∧ qRows ex44a = [[1, 2, 3]] := by decide
theorem ex44b_rsk : pRows ex44b = [[1, 1], [2]] ∧ qRows ex44b = [[1, 2], [3]] := by decide
theorem ex44c_rsk : pRows ex44c = [[1, 1], [2]] ∧ qRows ex44c = [[1, 3], [2]] := by decide

/-! ## Content control: in the printed Example 4.5 the `P` tableau has content ρ = col(A) = (2,1,1)
and `Q` has content μ = row(A) = (2,2); the printed (4.3) codomain asks for cont(P) = μ. -/

theorem ex45a_P_content_is_columns :
    ((pRows ex45a).flatten.count 1, (pRows ex45a).flatten.count 2,
      (pRows ex45a).flatten.count 3) = (2, 1, 1) ∧
    ((qRows ex45a).flatten.count 1, (qRows ex45a).flatten.count 2) = (2, 2) := by decide

/-! ## Small exhaustive control: all 81 2×2 matrices with entries ≤ 2 have pairwise distinct
list-level RSK images (injectivity across all their margins).  The |µ| ≤ 4 exhaustive bijection
control is the exact-integer script an unpublished script. -/

def allSmall : List (Fin 2 → Fin 2 → ℕ) :=
  (List.range 81).map fun k => ![![k % 3, k / 3 % 3], ![k / 9 % 3, k / 27 % 3]]

theorem allSmall_images_nodup : ((allSmall.map fun A => (pRows A, qRows A))).Nodup := by decide

#print axioms ex45a_rsk
#print axioms ex45b_rsk
#print axioms ex45c_rsk
#print axioms ex45d_rsk
#print axioms ex45_margins
#print axioms ex44a_rsk
#print axioms ex44b_rsk
#print axioms ex44c_rsk
#print axioms ex45a_P_content_is_columns
#print axioms allSmall_images_nodup

end OddMath.Frontier.EKRskBijection
