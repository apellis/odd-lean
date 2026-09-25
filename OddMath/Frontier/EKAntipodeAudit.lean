import OddMath.Frontier.EKAntipodeControls

noncomputable section
open scoped BigOperators TensorProduct
open OddMath.Frontier EKRadicalQuotient EKElementaryQuotient EKAntipode
namespace OddMath.Frontier.EKAntipodeAudit

-- Exact exported types, no substituted carrier or assumed antipode property.
example : Q = (CompleteElementary.A ⧸ EKRadicalQuotient.radical) := rfl
example (x : Q) : S x = EKPresentation.psi1 (EKAutomorphisms.psi2 (EKAutomorphisms.psi3 x)) := rfl
example : S (1 : Q) = 1 := S_one
example (d : ℕ) (x : Q) (hx : x ∈ EKIntegralBases.degreePiece d) :
    S x ∈ EKIntegralBases.degreePiece d := S_degree hx
example (a b : ℕ) (x y : Q)
    (hx : x ∈ EKIntegralBases.degreePiece a) (hy : y ∈ EKIntegralBases.degreePiece b) :
    S (x*y) = (-1 : ℤ)^(a*b) • (S y*S x) := S_mul hx hy
example (w : List ℕ) : S ((w.map h).prod) =
    (-1 : ℤ)^((w.sum+1).choose 2) • (w.reverse.map e).prod := S_hWord w
example (x : Q) :
    multiplication (TensorProduct.map S (LinearMap.id : Q →ₗ[ℤ] Q) (EKCoideal.quotientCoproduct x)) =
      quotientCounit x • (1 : Q) := convolution_left x
example (x : Q) :
    multiplication (TensorProduct.map (LinearMap.id : Q →ₗ[ℤ] Q) S (EKCoideal.quotientCoproduct x)) =
      quotientCounit x • (1 : Q) := convolution_right x
example : S (S (h 2)) = h 2 - (2 : ℤ) • (h 1*h 1) := S_square_h_two
example : S (S (h 2)) ≠ h 2 := S_not_involutive
end OddMath.Frontier.EKAntipodeAudit

#check S
#check S_apply
#check S_one
#check S_degree
#check S_mul
#check S_hWord
#check multiplication
#check convolution_left
#check convolution_right
#check antipode_identities
#check S_square_h_two
#check S_not_involutive
#check EKAntipodeControls.general_consumer

-- All owned safe declarations are audited, INCLUDING compiler-named helpers.
-- Unsafe compiler artifacts are enumerated individually; names alone never
-- exempt a safe declaration from the transitive standard-axiom check.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.EKAntipode,
        `OddMath.Frontier.EKAntipodeControls,
        `OddMath.Frontier.EKAntipodeAudit].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``S, ``S_apply, ``S_one, ``S_degree, ``S_mul, ``S_hWord,
      ``multiplication, ``convolution_left, ``convolution_right, ``antipode_identities,
      ``S_square_h_two, ``S_not_involutive,
      ``EKAntipodeControls.unit_both, ``EKAntipodeControls.h_one_both,
      ``EKAntipodeControls.h_two_both, ``EKAntipodeControls.square_both,
      ``EKAntipodeControls.mixed_both, ``EKAntipodeControls.coproduct_square,
      ``EKAntipodeControls.coproduct_mixed, ``EKAntipodeControls.ordinary_antihom_rejected,
      ``EKAntipodeControls.zero_parts, ``EKAntipodeControls.general_consumer] do
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
