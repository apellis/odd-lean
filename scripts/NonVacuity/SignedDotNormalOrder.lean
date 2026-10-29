import OddMath.QuiverHecke.CyclotomicAction.SignedDotNormalOrder
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.SignedDotNormalOrder then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke Categorification.TypeA
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace SignedDotNormalOrderConsumer

def mixedDatum : OddMath.SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

def mixedScalars : OddMath.SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

/-- Both parities at arbitrary height, arbitrary crossing words and contexts. -/
example {t t' : List Bool} (P : List PG) (σ : List ℕ)
    (hv : ValidWord t.length σ) (p : ℕ) (hp : p < t.length) (R : List PG)
    (h : SChain t (pl t (P ++ cw σ ++ [.dot p] ++ R)) t') :
    ∃ h' : SChain t (pl t (P ++ [.dot (sourceDotPosition σ p)] ++ cw σ ++ R)) t',
      cl mixedDatum mixedScalars t t' (P ++ cw σ ++ [.dot p] ++ R) h -
        sourceDotSign mixedDatum (k := ℚ) (tgt t P) σ p •
          cl mixedDatum mixedScalars t t' (P ++ [.dot (sourceDotPosition σ p)] ++ cw σ ++ R) h' ∈
        Low mixedDatum mixedScalars t t' (crossCount P + σ.length + crossCount R) :=
  dot_down_signed mixedDatum mixedScalars P rfl σ hv p hp R h

example {n : ℕ} {σ : List ℕ} (hv : ValidWord n σ) (p : Fin n) :
    sourceDotPosition σ p = ((wordProd n σ)⁻¹ p : ℕ) := sourceDotPosition_eq hv p

/-- Arbitrarily many interleaved decorations, in a genuinely mixed-parity datum. -/
example {t t' : List Bool} (P R : List PG) (bs : List (ℕ × List ℕ))
    (hv : ValidWord t.length (bs.map Prod.fst))
    (hp : ∀ b ∈ bs, ∀ p ∈ b.2, p < t.length)
    (h : SChain t (pl t (P ++ decoratedCrossingGens bs ++ R)) t') :
    ∃ h' : SChain t
        (pl t (P ++ (collectedSourceDots bs).map PG.dot ++ cw (bs.map Prod.fst) ++ R)) t',
      cl mixedDatum mixedScalars t t' (P ++ decoratedCrossingGens bs ++ R) h -
        collectedSourceSign mixedDatum (k := ℚ) (tgt t P) bs •
          cl mixedDatum mixedScalars t t'
            (P ++ (collectedSourceDots bs).map PG.dot ++ cw (bs.map Prod.fst) ++ R) h' ∈
        Low mixedDatum mixedScalars t t' (crossCount P + bs.length + crossCount R) :=
  decorated_crossings_normal_order mixedDatum mixedScalars P rfl bs hv hp R h

#print axioms OddMath.QuiverHecke.cross_dot_move_signed
#print axioms OddMath.QuiverHecke.dot_down_signed
#print axioms OddMath.QuiverHecke.dots_down_signed
#print axioms OddMath.QuiverHecke.decorated_crossings_normal_order
end SignedDotNormalOrderConsumer
