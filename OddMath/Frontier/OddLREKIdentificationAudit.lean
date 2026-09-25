import OddMath.Frontier.OddLREKIdentification
import OddMath.Frontier.OddLREKIdentificationControls

open scoped BigOperators
open OddMath.Frontier OddMath.SkewPolynomial EKRadicalQuotient OddLREKIdentification

-- Definitional checks: the map is the h-presentation descent of the literal complete evaluation,
-- and the EK Schur family is the literal signed-Kostka inverse of the actual complete basis.
example (N : ℕ) : piN N = (completeDescent N).comp EKPresentation.presentationEquiv.symm.toRingHom := rfl
example (N : ℕ) : completeDescent N = Ideal.Quotient.lift EKPresentation.relIdeal
    (FiniteCompleteElementary.completeEvaluation N)
    (killed_of_relators _ (fun _ hr => complete_relator N hr)) := rfl
example (d : ℕ) : schurK d = KostkaModuleInversion.recover d (EKIntegralBases.degreeHBasis d) := rfl
example (N k : ℕ) : FiniteCompleteElementary.completePoly N k =
    ∑ f : Fin k → Fin N, if Monotone f then
      (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f i))).prod else 0 := rfl
example (N : ℕ) (lam : YoungDiagram) : CompleteTableauExpansion.sp N lam =
    (-1 : ℤ) ^ (TableauStripSigns.directNorth lam + TableauStripSigns.north lam) •
      TableauPolynomial.tableauPolynomial N lam := rfl
example (lam mu : YoungDiagram) : TableauDominance.signedKostka lam mu =
    TableauDominance.tableauSign (TableauDominance.canonicalTableau lam) *
      ∑ T ∈ TableauContent.tableauxOfContent lam (TableauDominance.shapeContent mu),
        TableauDominance.tableauSign T := rfl
example (d : ℕ) (mu : DegreeShapes.DegreeShape d) :
    (EKIntegralBases.degreeHBasis d mu : Q) = (mu.val.rowLens.map EKElementaryQuotient.h).prod :=
  EKIntegralBases.degreeHBasis_apply d mu
example (k : ℕ) : EKElementaryQuotient.h k = pi (CompleteElementary.h k) := rfl

-- The acceptance statements, restated.
example (N k : ℕ) : piN N (EKElementaryQuotient.h k) = FiniteCompleteElementary.completePoly N k :=
  piN_h N k
example (N d : ℕ) (lam : DegreeShapes.DegreeShape d) :
    piN N (schurK d lam : Q) = CompleteTableauExpansion.sp N lam.val := piN_schurK N d lam
example (N : ℕ) (lam : YoungDiagram) : piN N (sK lam) = CompleteTableauExpansion.sp N lam :=
  piN_sK N lam
example (d : ℕ) : KostkaModuleInversion.transform d (schurK d) = EKIntegralBases.degreeHBasis d :=
  schurK_defining d

#check @complete_even
#check @complete_odd
#check @piN_unique
#check @piN_schurK
#check @thm38_conditional
#print axioms piN
#print axioms complete_even
#print axioms complete_odd
#print axioms piN_h
#print axioms piN_e
#print axioms piN_unique
#print axioms piN_mem_kernel
#print axioms piN_schurK
#print axioms piN_sK
#print axioms thm38_conditional
#print axioms OddLREKIdentificationControls.recover_natural

-- Audit all owned constants, including SAFE compiler-named generated helpers.
run_cmd do
  let env ← Lean.getEnv
  let owned := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => [`OddMath.Frontier.OddLREKIdentification,
        `OddMath.Frontier.OddLREKIdentificationControls].contains env.header.moduleNames[idx.toNat]!
    | none => true
  for required in [``piN, ``piN_pi, ``piN_h, ``piN_e, ``piN_eq_ePi, ``piN_unique,
      ``piN_hPartition, ``piN_mem_kernel, ``complete_relator, ``complete_even, ``complete_odd,
      ``elementary_relator, ``elementaryEvaluation_eq, ``ePi, ``ePi_pi,
      ``schurK, ``schurK_defining, ``schurK_unique, ``sK, ``recover_natural,
      ``piN_schurK, ``piN_sK, ``toExponent, ``EliminationC, ``thm38_conditional,
      ``OddLREKIdentificationControls.recover_natural,
      ``OddLREKIdentificationControls.unsigned_recover_natural,
      ``OddLREKIdentificationControls.complete_one_eq_elementary_one,
      ``OddLREKIdentificationControls.evaluation_on_elementary,
      ``OddLREKIdentificationControls.elementary_fixture_03] do
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
