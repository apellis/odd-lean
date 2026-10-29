import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortWord
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentShortWord then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open OddMath.QuiverHecke Categorification.TypeA Equiv
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace AppendContentShortWordConsumer

def identityShuffle (n : ℕ) : PrependShuffle (n + 1) := ⟨1, isShuffle_one _⟩

theorem identity_short (n : ℕ) : identityShuffle n ≠ longPrependShuffle (n + 1) := by
  intro h
  have he := congrArg (fun u : PrependShuffle (n + 1) => (u.1 (Fin.last (n + 1))).val) h
  change n + 1 = (finRotate (n + 1 + 1) (Fin.last (n + 1))).val at he
  rw [finRotate_last] at he
  simp at he

/-- The boundary content index is positive old height one, not affine height zero. -/
example (u : PrependShuffle 1) (hu : u ≠ longPrependShuffle 1) :
    canWord 2 u.1⁻¹ = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have := canWord_prependShort_lt 0 u hu x hx
  omega

example (n : ℕ) (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1)) :
    canWord (n + 1) (wordProd (n + 1) (canWord (n + 2) u.1⁻¹)) =
      canWord (n + 2) u.1⁻¹ := canWord_prependShort_restrict n u hu

open CategoryTheory StringDiagrams MonoidalCategory

/-- Both colours and a concrete short shuffle at every positive old height. -/
theorem identityDiagram (n : ℕ) (i : Bool) (s : List Bool) (hs : s.length = n + 1) :
    ∃ h : SChain (s ++ [i])
        (pl (s ++ [i]) (cw (canWord (n + 2) (identityShuffle n).1⁻¹)))
        (tgt s (cw (canWord (n + 2) (identityShuffle n).1⁻¹)) ++ [i]),
      cl datum scalars (s ++ [i]) _ (cw (canWord (n + 2) (identityShuffle n).1⁻¹)) h =
        cl datum scalars s _ (cw (canWord (n + 2) (identityShuffle n).1⁻¹))
          (sChain_pl _ _) ▷ (pres datum scalars).obj (ob datum [i]) :=
  prependShort_cl_whiskerRight datum scalars n (identityShuffle n) (identity_short n) s hs i

#print axioms OddMath.QuiverHecke.canWord_prependShort_restrict
#print axioms OddMath.QuiverHecke.prependShort_cl_whiskerRight
end AppendContentShortWordConsumer
