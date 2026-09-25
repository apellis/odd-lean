import OddMath.Frontier.EKAutomorphismsControls

noncomputable section
open scoped BigOperators TensorProduct
open OddMath.Frontier EKRadicalQuotient EKElementaryQuotient EKAutomorphisms

namespace OddMath.Frontier.EKAutomorphismsAudit

-- Literal carrier, map types, order, and general consumer identities.
example : Q = (CompleteElementary.A ⧸ EKRadicalQuotient.radical) := rfl
example : Q ≃+* Q := psi2
example : Q ≃ₗ[ℤ] Q := psi3
example (x : Q) : psi12 x = EKPresentation.psi1 (psi2 x) := rfl
example (n : ℕ) : psi2 (h n) = (-1 : ℤ)^((n+1).choose 2) • h n := psi2_h n
example (n : ℕ) : psi3 (h n) = h n := psi3_h n
example (x : Q) : psi2 (psi2 x) = x := psi2_involutive x
example (x : Q) : psi3 (psi3 x) = x := psi3_involutive x
example (x : Q) : psi12 (psi12 x) = x := psi12_involutive x
example (a b : ℕ) (x y : Q)
    (hx : x ∈ EKIntegralBases.degreePiece a) (hy : y ∈ EKIntegralBases.degreePiece b) :
    psi3 (x*y) = (-1 : ℤ)^(a*b) • (psi3 y*psi3 x) := psi3_mul hx hy
example (r : ℤ) (x y : Q) : psi3 (r • x + y) = r • psi3 x + psi3 y := by
  rw [map_add, map_smul]
example (x : Q) : EKCoideal.quotientCoproduct (EKPresentation.psi1 x) =
    TensorProduct.map psi1L psi1L (EKCoideal.quotientCoproduct x) := psi1_coproduct x
example (x : Q) : quotientCounit (EKPresentation.psi1 x) = quotientCounit x := psi1_counit x
example (w : List ℕ) : psi12 ((w.map h).prod) =
    (-1 : ℤ)^((w.map (fun n => (n+1).choose 2)).sum) • (w.map e).prod := psi12_hWord_source w
example (w : List ℕ) : psi12 ((w.map e).prod) =
    (-1 : ℤ)^((w.map (fun n => (n+1).choose 2)).sum) • (w.map h).prod := psi12_eWord_source w
example (w : List ℕ) : psi3 ((w.map h).prod) =
    (-1 : ℤ)^(∑ i : Fin w.length, ∑ j : Fin w.length,
      if i < j then w.get i * w.get j else 0) • (w.reverse.map h).prod := psi3_hWord_source w
example (x : Q) : psi2 (EKPresentation.psi1 (psi2 x)) = EKPresentation.psi1.symm x := psi2_psi1_psi2 x
example (x : Q) : EKPresentation.psi1 (psi2 (EKPresentation.psi1 x)) = psi2 x := psi1_psi2_psi1 x

end OddMath.Frontier.EKAutomorphismsAudit

#check psi2
#check psi3
#check psi12
#check psi2_h
#check psi2_degree
#check psi3_degree
#check psi1_degree
#check psi1_inverse_degree
#check psi3_mul
#check psi3_hWord_source
#check psi12_hWord_source
#check psi12_eWord_source
#check psi12_involutive
#check psi2_psi1_psi2
#check psi1_psi2_psi1
#check psi1_coproduct
#check psi1_counit

-- Enumerate by actual defining module, not namespace or theorem-name heuristics.
-- Every SAFE generated declaration is included in the logical closure audit.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKAutomorphisms,
        `OddMath.Frontier.EKAutomorphismsControls,
        `OddMath.Frontier.EKAutomorphismsAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``psi2, ``psi3, ``psi12, ``descend, ``psi2_h, ``psi3_h,
      ``psi2_involutive, ``psi3_involutive, ``psi12_involutive,
      ``psi2_degree, ``psi3_degree, ``psi1_degree, ``psi1_inverse_degree,
      ``psi3_mul, ``psi3_hWord_source, ``psi12_hWord_source, ``psi12_eWord_source,
      ``psi2_psi1_psi2, ``psi1_psi2_psi1, ``psi1_coproduct, ``psi1_counit,
      ``EKAutomorphismsControls.ordinary_reversal_rejected,
      ``EKAutomorphismsControls.psi3_reverses_noncommuting_word,
      ``EKAutomorphismsControls.psi12_noncommuting_product,
      ``EKAutomorphismsControls.general_consumer,
      ``EKAutomorphismsControls.literal_printed_224_counterexample,
      ``EKAutomorphismsControls.psi3_e_two_not_fixed,
      ``EKAutomorphismsControls.direct_226_term_mismatch] do
    unless owned.any (fun (name,_) => name == required) do
      throwError "Missing acceptance declaration {required}"
  let mut logical := 0
  let mut stages := 0
  for (name, info) in owned do
    let axioms ← Lean.collectAxioms name
    let compiler := (name.toString.splitOn ".").any (fun s =>
      s == "_cstage1" || s == "_cstage2" || s.startsWith "_elambda_" || s.startsWith "_spec_")
    if compiler && info.isUnsafe then
      stages := stages + 1
      Lean.logInfo m!"COMPILER '{name}' unsafe=true depends on axioms: {axioms.toList}"
    else
      if info.isUnsafe then throwError "Unexpected unsafe logical declaration {name}"
      unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "Nonstandard owned axioms {name}: {axioms}"
      logical := logical + 1
      Lean.logInfo m!"OWNED '{name}' unsafe=false depends on axioms: {axioms.toList}"
  Lean.logInfo m!"AUDIT logical={logical} compiler-stages={stages}"
