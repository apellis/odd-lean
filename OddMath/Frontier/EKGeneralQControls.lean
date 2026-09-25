import OddMath.Frontier.EKPairingAdjoint

/-!
# Controls for EK §2.1 at generic q (compiled BEFORE `EKGeneralQ`)

Source: Ellis–Khovanov arXiv:1107.5610v2, §2.1, pp.5–8: the q-twisted product
`(x₁⊗x₂)(y₁⊗y₂) = q^{deg x₂ deg y₁} x₁y₁⊗x₂y₂`, `Δ(hₙ) = Σ hₘ⊗h_{n-m}`, the form (2.1)
as a sum over minimal double-coset representatives of `q^{ℓ(c)}`, the tensor form
(2.2) and Proposition 2.2 (2.3).

CONTROL ONLY.  This is an independent, computable model of `ℤ[q]` (coefficient
lists; index = power of `q`), NOT the production objects.  The form here is computed
from EK's own p.6 characterization of minimal representatives (strands that start or
end on a common platform do not cross), by brute force over all permutations of the
strands, with `ℓ` = the inversion count.  Every check below is kernel-evaluated by
`decide` (no `native_decide`), exhaustively over all compositions of degree `≤ 3`
(and the printed four-strand Example 2.1).  Finite checks are controls; they prove
nothing about general degree.

The last section compares, at q = -1 over ℤ, with the EXISTING objects
`EKFreeCoproduct.coproduct` / `EKPairingAdjoint.pairing` (theorems, not evaluation).
-/
namespace OddMath.Frontier.EKGeneralQControls

/-- `ℤ[q]` as coefficient lists. -/
abbrev P := List Int

def padd : P → P → P
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: padd a b

def pscale (c : Int) (a : P) : P := a.map (c * ·)

def pmul : P → P → P
  | [], _ => []
  | x :: a, b => padd (pscale x b) (0 :: pmul a b)

/-- `q ^ n`. -/
def ppow : Nat → P
  | 0 => [1]
  | n + 1 => 0 :: ppow n

def pnorm (a : P) : P := (a.reverse.dropWhile (· == 0)).reverse

/-- Exact equality in `ℤ[q]`. -/
def peq (a b : P) : Bool := pnorm (padd a (pscale (-1) b)) == []

/-- Evaluation at an integer. -/
def peval (a : P) (x : Int) : Int := a.foldr (fun c acc => c + x * acc) 0

def lflat {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: l => f a ++ lflat f l

def insertAll (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertAll a l).map (b :: ·)

/-- All permutations (structural recursion, kernel-reducible). -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => lflat (insertAll a) (perms l)

/-- Platform label of each endpoint for a composition, left to right. -/
def blocks : Nat → List Nat → List Nat
  | _, [] => []
  | i, a :: l => List.replicate a i ++ blocks (i + 1) l

def lsum : List Nat → Nat
  | [] => 0
  | a :: l => a + lsum l

/-- EK p.6: `s` (bottom point `a` ↦ top point `s a`) is a minimal double-coset
representative iff strands starting or ending on a common platform do not cross. -/
def minimalRep (bot top s : List Nat) : Bool :=
  (List.range s.length).all fun a => (List.range s.length).all fun b =>
    !(decide (a < b)) ||
    !(bot.getD a 0 == bot.getD b 0 || top.getD (s.getD a 0) 0 == top.getD (s.getD b 0) 0) ||
    decide (s.getD a 0 < s.getD b 0)

def inversions (s : List Nat) : Nat :=
  ((List.range s.length).map fun a => ((List.range s.length).filter fun b =>
    decide (a < b) && decide (s.getD b 0 < s.getD a 0)).length).foldr (· + ·) 0

/-- EK (2.1) with `β` on top, `α` at the bottom. -/
def form (β α : List Nat) : P :=
  if lsum β = lsum α then
    (perms (List.range (lsum α))).foldr (fun s acc =>
      if minimalRep (blocks 0 α) (blocks 0 β) s then padd (ppow (inversions s)) acc else acc) []
  else []

/-- Words use positive parts; `h₀ = 1` is the empty word. -/
def hw (n : Nat) : List Nat := if n = 0 then [] else [n]

abbrev Tensor := List (P × List Nat × List Nat)

def delta1 (n : Nat) : Tensor := (List.range (n + 1)).map fun m => ([1], hw m, hw (n - m))

/-- The q-twisted product on `Λ'⊗Λ'`. -/
def tmul (x y : Tensor) : Tensor :=
  lflat (fun t => y.map fun u =>
    (pmul (pmul t.1 u.1) (ppow (lsum t.2.2 * lsum u.2.1)), t.2.1 ++ u.2.1, t.2.2 ++ u.2.2)) x

/-- Δ extended multiplicatively for the q-twisted product. -/
def delta : List Nat → Tensor
  | [] => [([1], [], [])]
  | n :: w => tmul (delta1 n) (delta w)

/-- (2.2): `(y₁⊗y₂, x₁⊗x₂) = (y₁,x₁)(y₂,x₂)`, extended linearly. -/
def tform (y1 y2 : List Nat) (t : Tensor) : P :=
  t.foldr (fun u acc => padd (pmul u.1 (pmul (form y1 u.2.1) (form y2 u.2.2))) acc) []

def coeff2 (t : Tensor) (w1 w2 : List Nat) : P :=
  t.foldr (fun u acc => if u.2.1 == w1 && u.2.2 == w2 then padd u.1 acc else acc) []

abbrev Tensor3 := List (P × List Nat × List Nat × List Nat)

def leftDelta (t : Tensor) : Tensor3 :=
  lflat (fun u => (delta u.2.1).map fun v => (pmul u.1 v.1, v.2.1, v.2.2, u.2.2)) t

def rightDelta (t : Tensor) : Tensor3 :=
  lflat (fun u => (delta u.2.2).map fun v => (pmul u.1 v.1, u.2.1, v.2.1, v.2.2)) t

def coeff3 (t : Tensor3) (a b c : List Nat) : P :=
  t.foldr (fun u acc => if u.2.1 == a && u.2.2.1 == b && u.2.2.2 == c then padd u.1 acc else acc) []

/-- Compositions of `n` (positive parts), with structural fuel. -/
def compsF : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | f + 1, n => if n = 0 then [[]] else
      lflat (fun a => (compsF f (n - (a + 1))).map ((a + 1) :: ·)) (List.range n)

def comps (n : Nat) : List (List Nat) := compsF n n

def words3 : List (List Nat) := lflat comps [0, 1, 2, 3]

/-- Pairs `(y₁, y₂)` of words with `deg y₁ + deg y₂ = n`. -/
def splits (n : Nat) : List (List Nat × List Nat) :=
  lflat (fun i => lflat (fun a => (comps (n - i)).map fun b => (a, b)) (comps i)) (List.range (n + 1))

/-! ## Printed example and sanity values -/

/-- EK Example 2.1 exactly as printed: `(h₂h₂, h₁h₂h₁) = 1 + 2q² + q³`. -/
theorem example_2_1 : form [2, 2] [1, 2, 1] = [1, 0, 2, 1] := by decide

theorem form_h1h1 : form [1, 1] [1, 1] = [1, 1] := by decide
theorem form_h111 : form [1, 1, 1] [1, 1, 1] = [1, 2, 2, 1] := by decide

/-! ## Exhaustive degree ≤ 3 checks in `ℤ[q]` -/

/-- (2.1) symmetry, all compositions of degree ≤ 3 (unequal degrees included). -/
theorem symmetry_le3 :
    (words3.all fun b => words3.all fun a => peq (form b a) (form a b)) = true := by decide

/-- Proposition 2.2 (2.3), all `x` of degree ≤ 3 and all `y₁,y₂` with matching degree. -/
theorem adjointness_le3 :
    ([0, 1, 2, 3].all fun n => (comps n).all fun x => (splits n).all fun y =>
      peq (tform y.1 y.2 (delta x)) (form (y.1 ++ y.2) x)) = true := by decide

/-- Adjointness also holds (both sides 0) when the degrees differ. -/
theorem adjointness_mismatch_le3 :
    ([0, 1, 2, 3].all fun n => (comps n).all fun x => (splits ((n + 1) % 4)).all fun y =>
      peq (tform y.1 y.2 (delta x)) (form (y.1 ++ y.2) x)) = true := by decide

/-- Counit laws: `(ε⊗id)Δx = x = (id⊗ε)Δx`, degree ≤ 3. -/
theorem counit_le3 :
    ([0, 1, 2, 3].all fun n => (comps n).all fun x => (comps n).all fun w =>
      peq (coeff2 (delta x) [] w) (if w == x then [1] else []) &&
      peq (coeff2 (delta x) w []) (if w == x then [1] else [])) = true := by decide

/-- Coassociativity, degree ≤ 3, every coefficient of every word triple. -/
theorem coassoc_le3 :
    ([0, 1, 2, 3].all fun n => (comps n).all fun x => (splits n).all fun p =>
      (comps (n - lsum p.1 - lsum p.2)).all fun c =>
        peq (coeff3 (leftDelta (delta x)) p.1 p.2 c) (coeff3 (rightDelta (delta x)) p.1 p.2 c))
      = true := by decide

/-- EK p.5 displayed formula `Δ(hₙhₖ) = Σ q^{(n-m)r} hₘhᵣ ⊗ h_{n-m}h_{k-r}`, n,k ≤ 2. -/
theorem coproduct_two_le2 :
    ([1, 2].all fun n => [1, 2].all fun k => (splits (n + k)).all fun p =>
      peq (coeff2 (delta [n, k]) p.1 p.2)
        ((List.range (n + 1)).foldr (fun m acc => (List.range (k + 1)).foldr (fun r acc' =>
          if hw m ++ hw r == p.1 && hw (n - m) ++ hw (k - r) == p.2
          then padd (ppow ((n - m) * r)) acc' else acc') acc) [])) = true := by decide

/-- Non-vacuity: the q-twisted coproduct is NOT cocommutative at generic q (EK p.5). -/
theorem not_cocommutative : peq (coeff2 (delta [1, 1]) [1] [1]) [2] = false := by decide

/-! ## Specialization q = -1 against the existing objects -/

theorem form_h1h1_at_neg_one : peval (form [1, 1] [1, 1]) (-1) = 0 := by decide
theorem form_h2_at_neg_one : peval (form [2] [2]) (-1) = 1 := by decide

open CompleteElementary EKFreeCoproduct EKPairingAdjoint in
/-- Existing q=-1 form: `(h₁h₁, h₁h₁) = 0`, matching `(1+q)|_{q=-1}` above. -/
theorem integrated_h1h1 : pairing (h 1 * h 1) (h 1 * h 1) =
    peval (form [1, 1] [1, 1]) (-1) := by
  have h01 : pairing (h 1) 1 = 0 := by rw [pairing_right_one]; exact counit_h_succ 0
  have h10 : pairing 1 (h 1) = 0 := by rw [pairing_one]; exact counit_h_succ 0
  have h11 : pairing (h 1) (h 1 * h 1) = 0 := by
    have := pairing_vWord_degree_mismatch (fun _ : Fin 1 => 1) ![1, 1] (by decide)
    simpa [vWord, List.ofFn_succ, hWord] using this
  have h11' : pairing (h 1) (h 1) = 1 := pairing_h_self 1
  rw [form_h1h1_at_neg_one, ← adjointness, coproduct_two]
  simp [Fin.sum_univ_succ, h01, h10, h11, h11', -zsmul_eq_mul, neg_smul, one_smul]

open CompleteElementary EKPairingAdjoint in
/-- Existing q=-1 form: `(h₂, h₂) = 1`. -/
theorem integrated_h2 : pairing (h 2) (h 2) = peval (form [2] [2]) (-1) := by
  rw [form_h2_at_neg_one]; exact pairing_h_self 2

end OddMath.Frontier.EKGeneralQControls
