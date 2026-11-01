# Denominator units from probe units in shifted ELV postcomposition

Status: proposed source, pending CI; depends on contentwise ELV denominator units.

For an arbitrary PiSCat source A and functor F into the existing ELV source
weight category, take the probe-precomposition map α : End F. The probe dot
on postinduction is its literal postcomposition by elvE, and its unit property
is the image of IsUnit α under homPost.mapEnd. The reservoir dot is exactly
whiskerLeft F elvActionDot. Their component commutation/anticommutation is
proved from elvActionDot.naturality; it is not an input of the final producer.

The difference and odd square difference/sum are units by the existing
contentwise dot bound. The same homPiLeft structure as GlobalFactorNondegeneracy
is used locally, and the prescribed homParityShift functor maps these units.
The shifted-dot formula is literal, preserving the chosen contentInductionDot
normalization, all coefficient parities and the original weight categories.

A closed even-parity asymmetric datum consumer supplies every unit and
homogeneity premise and checks the nontrivial parity shift. The generic odd
norm algebra is tested by the infinite product of rational matrix modules
in ProductDenominatorUnits. All owned declarations are axiom audited.

No full RouquierFamily, swapped mate inverse or nondegeneracy conclusion is
claimed. Final factor assembly must instantiate the generic algebra parameter
with parameterTwist Sc and retain Sc as the action parameter. The mate's
transposed source denominator units remain separate work.
