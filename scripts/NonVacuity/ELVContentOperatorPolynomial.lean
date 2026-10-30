import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorPolynomial
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (i j : I) (r s : ℕ)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    (Sc.s i j r s •
      ((contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w ^ s) *
       (contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (firstDot_parity D (parameterTwist D Sc) i [j]) M w ^ r)))
      (BalancedInduction.tensor
        (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        ((OddMath.SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (s / 2 : ℕ)) *
          Sc.s i j r s) •
          (dotE D (parameterTwist D Sc) [i,j] 0 ^ r *
           dotE D (parameterTwist D Sc) [i,j] 1 ^ s)) v ≫ h) m :=
  contentInduction_dot_monomial D Sc cutoff N β i j r s M w v h m

#print axioms contentInduction_dot_monomial
#print axioms contentInductionEndLinear_pow_tensor
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorPolynomial
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
