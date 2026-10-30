import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence

noncomputable section
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Finite I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

include sy hc in
example (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff N (ν : Multiset I),
      (show End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M) from
        (contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M) ^ e = 0 :=
  contentInductionDot_module_pow_zero D Sc cutoff sy hc N ν i

include sy hc in
example (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (c : k) (M : ContentModules D Sc cutoff N (ν : Multiset I)),
      (c • (show End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M) from
        (contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M)) ^ e = 0 :=
  contentInductionDot_smul_pow_zero D Sc cutoff sy hc N ν i

include sy hc in
example (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (M : ContentModules D Sc cutoff N (ν : Multiset I))
      (w : ContentCategory D Sc cutoff N ((ν : Multiset I) + ([i] : Multiset I))),
      let f : End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M |>.obj w) :=
        ((contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M).app
          (D.parity i) w
      f ^ e = 0 :=
  contentInductionDot_pow_zero D Sc cutoff sy hc N ν i

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
