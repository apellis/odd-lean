import OddMath.SKM.MixedCrossingLocal
import OddMath.SKM.PositivePointGradingExamples

/-! Nonempty odd/odd tests of the local Claim 4 calculations.
These do not supply the missing global representative-family transport. -/
namespace OddMath.SKM.MixedCrossingLocalExamples
open StringDiagrams StringDiagrams.Chord DTMove

def oddDatum : Datum Bool (Bool → ℤ) where
  cd := PositivePointGradingExamples.twoColourDatum.cd
  isGCM := PositivePointGradingExamples.twoColourDatum.isGCM
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

def oddSymmetrizer : Symmetrizer oddDatum where
  d := fun i => if i then 2 else 1
  pos := by intro i; cases i <;> decide
  symm := by intro i j; cases i <;> cases j <;> rfl

def A : List (Letter Bool) := [(true, false), (false, true), (false, false), (true, true)]
def B : List (Letter Bool) := [(false, true), (true, false), (false, false), (true, true)]
def S : List (TMove (Letter Bool)) := [.cap 1, .cap 0]
def R : List (TMove (Letter Bool)) := [.mv (.cross 0), .cap 1, .cap 0]
def raw : List (TMove (Letter Bool)) := [.mv (.cross 0), .mv (.cross 0), .cap 1, .cap 0]

theorem colours_distinct : (false : Bool) ≠ true := by decide

theorem source_matching : IsMatching₂ A [] R := by
  refine ⟨⟨by change 5 < 8; decide, ?_⟩, rfl⟩
  refine ⟨⟨(6, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(4, (false, true)), (0, (true, true)), rfl, rfl, rfl, by decide⟩, trivial⟩

theorem target_matching : IsMatching₂ B [] S := by
  refine ⟨?_, rfl⟩
  refine ⟨⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩, ?_⟩
  exact ⟨⟨(6, (false, true)), (0, (true, true)), rfl, rfl, rfl, by decide⟩, trivial⟩

theorem source_reduced : StrictReduced₂ A R := by
  change (([s(6, 4)] : List (Sym2 ℕ)).Nodup ∧
    (∀ z ∈ ([s(6, 4)] : List (Sym2 ℕ)), ¬ z.IsDiag)) ∧ ([6, 4] : List ℕ).Nodup
  simp

theorem target_reduced : StrictReduced₂ B S := by
  change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
    ([4, 6] : List ℕ).Nodup
  simp

/-- Raw attachment can violate the hypothesis required by the existing
reduced comparison theorem, even at two distinct odd colours and empty target. -/
theorem raw_not_reduced : ¬ Reduced₂ B raw := by
  change ¬ (([s(6, 4), s(4, 6)] : List (Sym2 ℕ)).Nodup ∧ _)
  simp [Sym2.eq_swap]

/-- One dot lies on the upward false-coloured strand before the inner cap. -/
def targetDots : List (DTMove Bool) := [.dt 1, .tm (.cap 1), .tm (.cap 0)]
def sourceDots : List (DTMove Bool) := .tm (.mv (.cross 0)) :: targetDots

theorem rightward_dot_transport :
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) =
      tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) ∧
    xpar oddDatum 0 (dLay A sourceDots) = xpar oddDatum 0 (dLay B targetDots) + 1 := by
  simpa only [A, B, sourceDots, List.nil_append, List.length_nil, oddDatum, one_mul] using
    right_cross_attach_degree_parity oddDatum oddSymmetrizer 0 []
      [(false, false), (true, true)] false true targetDots

theorem dot_values :
    tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) = 5 ∧
    xpar oddDatum 0 (dLay B targetDots) = 0 := by
  norm_num [B, targetDots, dLay, dotOn, tmLay, tLet, xDotL, xCapL,
    tableDegree, xpar, xlpar, ofL, gdeg, Shape.parity, xwhL, wt, sh, ipar,
    oddDatum, oddSymmetrizer, Datum.h, Datum.α,
    PositivePointGradingExamples.twoColourDatum]
  rfl

/-- A negative specialization detects omitting the odd/odd crossing factor. -/
theorem signs_detect_factor :
    (1 : ℚ) ^ (xpar oddDatum 0 (dLay A sourceDots)).val = 1 ∧
    (-1 : ℚ) ^ (xpar oddDatum 0 (dLay A sourceDots)).val = -1 ∧
    (-1 : ℚ) ^ (xpar oddDatum 0 (dLay B targetDots)).val = 1 := by
  rw [rightward_dot_transport.2, dot_values.2]
  norm_num
  rfl

/-- The local source bigon removal works with a nonzero dot after the bigon. -/
theorem dotted_bigon :
    tableDegree oddDatum oddSymmetrizer 0
      (dLay B (.tm (.mv (.cross 0)) :: sourceDots)) =
        tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) ∧
    xpar oddDatum 0 (dLay B (.tm (.mv (.cross 0)) :: sourceDots)) =
      xpar oddDatum 0 (dLay B targetDots) :=
  opposite_bigon_degree_parity oddDatum oddSymmetrizer 0 []
    [(false, false), (true, true)] true false false targetDots

end OddMath.SKM.MixedCrossingLocalExamples
