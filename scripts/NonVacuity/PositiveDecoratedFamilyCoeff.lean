import OddMath

/-! Non-vacuity checks in `PositiveDecoratedFamilyCoeffNonVacuity`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace PositiveDecoratedFamilyCoeffNonVacuity
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open scoped BigOperators
attribute [local instance] Classical.propDecidable
private abbrev Q := oddDatum
private abbrev μ : ℤ := 0
private abbrev π : ℤ := -1
private abbrev n : ℕ := 2
private abbrev I := Unit
private abbrev a : Fin n → I := fun _ => ()
private abbrev b : Fin n → I := fun _ => ()
private abbrev M := repeatedFamily
local notation "A" => (List.ofFn fun r => (true, a r))
local notation "B" => (List.ofFn fun r => (true, b r))

example : let C := Q.toSuperCartanDatum
  let κ : Equiv.Perm (Fin n) → ℤ := fun w =>
    ∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s)
  let ε : Equiv.Perm (Fin n) → ZMod 2 := fun w =>
    ∑ r, ∑ s with r < s ∧ w s < w r, Q.parity (a r) * Q.parity (a s)
  ∃ p : ∀ R : {R // R ∈ M}, MatchingStrand A R.val ≃ Fin n,
    (∀ R (j : MatchingStrand A R.val),
      OnStrand₂ A R.val j.val (R.val.length, (p R j).val)) ∧
    (let family := decoratedFamily₂ A M
       (fun R c => topDotMoves A R (topPositionExtension M p R) (fun j => c j))
     let G := {D // D ∈ family}
     ∃ (L : G → List (LayerData I)) (hL : ∀ D, SChain A (L D) B),
       (∀ D, (L D).map ofL = D.val) ∧
       ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
         Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
           (mkD Q.toSKM μ (L D) (hL D)) = z},
         (∑ D ∈ hf.toFinset, π ^ (xpar Q.toSKM μ D.val).val) =
           ∑ w : Equiv.Perm (Fin n), if ∀ r, a r = b (w r) then
             if κ w ≤ z then π ^ (ε w).val *
               PowerSeries.coeff (z - κ w).toNat (C.dotSeries π b)
             else 0
           else 0) := by
  obtain ⟨p, hp, L, hL, hm, h⟩ :=
    positive_decorated_family_coeff Q μ π (by norm_num [π]) a b M
      family_matching family_coverage family_unique
  refine ⟨p, hp, L, hL, hm, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, hc.trans ?_⟩
  apply Finset.sum_congr rfl
  intro w _
  have hcol : ∀ r, a r = b (w r) := fun _ => rfl
  rw [ite_eq_left hcol, ite_eq_left hcol]

end PositiveDecoratedFamilyCoeffNonVacuity
