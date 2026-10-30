import OddMath.QuiverHecke.CyclotomicAction.ELVAppendKernel

noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke.ELVOld

universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k)
  (cutoff : I → ℕ) (N : ℕ) (sy : OddMath.SKM.Symmetrizer D) (hc : Sc.Homogeneous)
  (v σ : List I)

example : GradedSuperBimodule
    (truncatedEndGSuperAlg D Sc cutoff N sy hc (v ++ σ)).gsa
    (truncatedEndGSuperAlg D Sc cutoff N sy hc v).gsa :=
  truncatedAppendInduction D Sc cutoff N sy hc v σ

example : GradedSuperBimodule
    (truncatedEndGSuperAlg D Sc cutoff N sy hc v).gsa
    (truncatedEndGSuperAlg D Sc cutoff N sy hc (v ++ σ)).gsa :=
  truncatedAppendRestriction D Sc cutoff N sy hc v σ

example (a : TruncatedEnd D Sc cutoff N v)
    (z : TruncatedEnd D Sc cutoff N (v ++ σ)) :
    (truncatedAppendInduction D Sc cutoff N sy hc v σ).toSuperBimodule.ract a z =
      z * truncatedAppendAlgHom D Sc cutoff N v σ a :=
  truncatedAppendInduction_ract D Sc cutoff N sy hc v σ a z

example (a : TruncatedEnd D Sc cutoff N v)
    (z : TruncatedEnd D Sc cutoff N (v ++ σ)) :
    (truncatedAppendRestriction D Sc cutoff N sy hc v σ).toSuperBimodule.lact a z =
      truncatedAppendAlgHom D Sc cutoff N v σ a * z :=
  truncatedAppendRestriction_lact D Sc cutoff N sy hc v σ a z
