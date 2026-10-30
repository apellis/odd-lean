import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (i j : I) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 0 = contentEPairInnerDot D Sc cutoff N β i j M w :=
  contentEPairDot_zero_eq_inner D Sc cutoff N β i j M w

example (β : Multiset I) (i j : I) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) :
    contentEPairDot D Sc cutoff N β i j M w 1 = contentEPairOuterDot D Sc cutoff N β i j M w :=
  contentEPairDot_one_eq_outer D Sc cutoff N β i j M w

example (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    let A := contentEPairInnerDot D (parameterTwist D Sc) cutoff N β i j M w
    let B := contentEPairOuterDot D (parameterTwist D Sc) cutoff N β i j M w
    (contentEPairCross D (parameterTwist D Sc) cutoff N β i j _ rfl
        (content_pair_swap β i j) M w).comp
      (contentEPairCross D (parameterTwist D Sc) cutoff N β j i _
        (content_pair_swap β i j) rfl M w) =
    if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
      ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j r s • (B ^ s * A ^ r) +
      ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i) :=
  contentEPair_whiskered_quadratic D Sc cutoff N β hij M w

#print axioms contentEPairDot_zero_eq_inner
#print axioms contentEPairDot_one_eq_outer
#print axioms contentEPair_whiskered_quadratic
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
