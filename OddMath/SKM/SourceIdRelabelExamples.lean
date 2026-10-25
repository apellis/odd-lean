import OddMath.SKM.SourceIdRelabel

/-! Cap-containing source transport with a relabelling that moves ID zero. -/
namespace OddMath.SKM.SourceIdRelabelExamples
open StringDiagrams StringDiagrams.Chord
private def T : TState (Letter Bool) := tStart [up false, dn false]
private def R : List (TMove (Letter Bool)) := [.cap 0]
private def ρ : Equiv.Perm ℕ := Equiv.swap 0 2
private theorem fits : TFits flipL 2 T R := by
  exact ⟨⟨(2, up false), (0, dn false), rfl, rfl, rfl, by decide⟩, trivial⟩
private theorem fresh : ∀ n, T.nxt ≤ n → ρ n = n := by
  intro n hn
  change 4 ≤ n at hn
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- Relabelling moves ID zero, so no artificial `f 0 = 0` premise is available. -/
theorem moves_zero : ρ 0 = 2 := by decide

theorem actual_cap_state :
    tRun flipL 2 (SourceIdRelabel.rename ρ T) R =
      SourceIdRelabel.rename ρ (tRun flipL 2 T R) :=
  SourceIdRelabel.run flipL ρ ρ.injective 2 T fresh R fits

theorem actual_cap_critical :
    tCrit flipL 2 (SourceIdRelabel.rename ρ T) [] R = [0] := by
  have H := SourceIdRelabel.crit flipL ρ ρ.injective 2 T fresh R fits []
  exact H.trans (by decide)

theorem frozen_cap_critical :
    tCrit flipL 2 (SourceFrozenSwap.frozen 0 T) [] R = tCrit flipL 2 T [] R :=
  SourceFrozenSwap.crit flipL (by decide) T R fits []

theorem frozen_cap_renaming (x : ℕ) :
    tRen 2 (SourceFrozenSwap.frozen 0 T) R x = tRen 2 T R x :=
  SourceFrozenSwap.ren (by decide) T R fits x

theorem actual_cap_renaming (x : ℕ) :
    tRen 2 (SourceIdRelabel.rename ρ T) R (ρ x) = ρ (tRen 2 T R x) :=
  SourceIdRelabel.ren ρ ρ.injective 2 T fresh R fits x

#print axioms actual_cap_renaming
#print axioms actual_cap_state
#print axioms actual_cap_critical
#print axioms frozen_cap_critical
#print axioms frozen_cap_renaming
end OddMath.SKM.SourceIdRelabelExamples
