import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVContentModuleTransformConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (i : I) :
    SuperNatTrans k (contentE D Sc cutoff N β i) (contentE D Sc cutoff N β i) :=
  contentInductionDot D Sc cutoff N β i

example (β : Multiset I) (i j : I) : SuperNatTrans k
    (contentInductionTo D Sc cutoff N β [j, i] (β + ([i, j] : Multiset I))
      (content_pair_swap β i j))
    (contentInductionTo D Sc cutoff N β [i, j] (β + ([i, j] : Multiset I)) rfl) :=
  contentInductionCross D Sc cutoff N β i j

example (β : Multiset I) (i : I) (M L : ContentModules D Sc cutoff N β)
    {q : ZMod 2} (f : M ⟶ L) (hf : f ∈ parity (R := k) _ _ q) :
    (contentE D Sc cutoff N β i).map f ≫
      (contentInductionDot D Sc cutoff N β i).app (D.parity i) L =
    sign k (D.parity i * q) •
      ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M ≫
        (contentE D Sc cutoff N β i).map f) :=
  ((contentInductionDot D Sc cutoff N β i).isSupernatural (D.parity i)).naturality hf

example (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppend D Sc cutoff N β [i]).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionDot D Sc cutoff N β i).app (D.parity i) M).app (D.parity i) w
      (BalancedInduction.tensor (contentAppend D Sc cutoff N β [i]) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl rfl (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h) m :=
  contentInductionDot_tensor D Sc cutoff N β i M w v h m

example (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i)).obj v ⟶ w)
    (m : M.obj v) :
    ((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i) M).app
      (D.parity i * D.parity i) w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, i] _
        (content_pair_swap β i i)) M.toFunctor v h m) =
    -BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, i] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
        (crossTwo D Sc i i) v ≫ twist k (D.parity i * D.parity i) h) m :=
  contentInductionCross_equal_tensor D Sc cutoff N β i M w v h m

example (β : Multiset I) (i j : I) (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)).obj v ⟶ w)
    (m : M.obj v) :
    ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [j, i] _
        (content_pair_swap β i j)) M.toFunctor v h m) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i, j] _ rfl) M.toFunctor v
      (contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v ≫ twist k (D.parity i * D.parity j) h) m :=
  contentInductionCross_distinct_tensor D Sc cutoff N β i j hij M w v h m

end ELVContentModuleTransformConsumer

#print axioms contentInductionDot_tensor
#print axioms contentInductionCross_equal_tensor
#print axioms contentInductionCross_distinct_tensor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations audited"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
