/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Algebra
import OddMath.QuiverHecke.AlphaPrime
import OddMath.QuiverHecke.MatrixMap
import OddMath.QuiverHecke.MatrixSuperop
import OddMath.QuiverHecke.PresentationGrading
import StringDiagrams.Super.SOpGraded

/-!
# BE2 (11.7) and (11.8): homomorphisms of graded superalgebras

Finite-support Hom matrices give the locally unital algebras for arbitrary
colour sets. Their grading is the independent integer/parity bigrading.
The downward source is realized by matrices in the super-opposite category;
`FiniteHomMatrix.unsopEquiv` and `unsopLinear_mul` identify this with the
super-opposite algebra, including the Koszul multiplication sign.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The upward fixed-length Hom algebra at rightmost weight `μ`. -/
abbrev UpAlgebra (μ : X) (n : ℕ) :=
  FiniteHomMatrix.Mat (fun a : Word I n => (alpha D Sc μ).obj (wordObj D Sc a))

/-- The super-opposite of `H_n`, realized as Hom matrices with reversed Hom spaces. -/
abbrev SopAlgebra (n : ℕ) :=
  FiniteHomMatrix.Mat (fun a : Word I n => (SOp.mk (wordObj D Sc a) : SOp k (H D Sc)))

/-- The downward fixed-length Hom algebra at rightmost weight `μ`. -/
abbrev DownAlgebra (μ : X) (n : ℕ) :=
  FiniteHomMatrix.Mat (fun a : Word I n =>
    (alphaPrime D Sc μ).obj (SOp.mk (wordObj D Sc a)))

/-- Equation (11.7), on the full locally unital fixed-length algebra. -/
def alphaN (n : ℕ) (μ : X) : Hn D Sc n →ₙ+* UpAlgebra D Sc μ n :=
  FiniteHomMatrix.map (k := k) (alpha D Sc μ)

/-- Equation (11.8), with the super-opposite source and the rightmost weight `μ`. -/
def alphaPrimeN (n : ℕ) (μ : X) : SopAlgebra D Sc n →ₙ+* DownAlgebra D Sc μ n :=
  FiniteHomMatrix.map (k := k) (alphaPrime D Sc μ)

@[simp] theorem alphaN_smul (n : ℕ) (μ : X) (r : k) (a : Hn D Sc n) :
    alphaN D Sc n μ (r • a) = r • alphaN D Sc n μ a :=
  FiniteHomMatrix.map_smul _ _ _

@[simp] theorem alphaPrimeN_smul (n : ℕ) (μ : X) (r : k) (a : SopAlgebra D Sc n) :
    alphaPrimeN D Sc n μ (r • a) = r • alphaPrimeN D Sc n μ a :=
  FiniteHomMatrix.map_smul _ _ _

/-- The upward map acts on each matrix entry by weight labelling. -/
@[simp] theorem alphaN_single (n : ℕ) (μ : X) (a b : Word I n)
    (f : wordObj D Sc b ⟶ wordObj D Sc a) :
    alphaN D Sc n μ (Hn.single a b f) =
      FiniteHomMatrix.single a b ((alpha D Sc μ).map f) :=
  FiniteHomMatrix.map_single _ _ _ _

/-- The downward map is the entrywise Chevalley image of the upward map at `-μ`. -/
@[simp] theorem alphaPrimeN_single (n : ℕ) (μ : X) (a b : Word I n)
    (f : (SOp.mk (wordObj D Sc b) : SOp k (H D Sc)) ⟶ SOp.mk (wordObj D Sc a)) :
    alphaPrimeN D Sc n μ (FiniteHomMatrix.single a b f) =
      FiniteHomMatrix.single a b ((alphaPrime D Sc μ).map f) :=
  FiniteHomMatrix.map_single _ _ _ _

@[simp] theorem alphaN_wordIdempotent (n : ℕ) (μ : X) (a : Word I n) :
    alphaN D Sc n μ (Hn.wordIdempotent a) = FiniteHomMatrix.idem a := by
  change FiniteHomMatrix.map (alpha D Sc μ) (FiniteHomMatrix.single a a (𝟙 _)) =
    FiniteHomMatrix.single a a (𝟙 _)
  rw [FiniteHomMatrix.map_single]
  exact congrArg (FiniteHomMatrix.single a a) ((alpha D Sc μ).map_id _)

@[simp] theorem alphaPrimeN_wordIdempotent (n : ℕ) (μ : X) (a : Word I n) :
    alphaPrimeN D Sc n μ (FiniteHomMatrix.idem a) = FiniteHomMatrix.idem a := by
  change FiniteHomMatrix.map (alphaPrime D Sc μ) (FiniteHomMatrix.single a a (𝟙 _)) =
    FiniteHomMatrix.single a a (𝟙 _)
  rw [FiniteHomMatrix.map_single]
  exact congrArg (FiniteHomMatrix.single a a) ((alphaPrime D Sc μ).map_id _)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The target's grading, inherited from the original SKM presentation. -/
@[instance_reducible]
def skmPresentedGrading : GradedSupercategory k (SKM.pres D Sc).Presented :=
  presentedGrading (SKM.pres D Sc) (SKM.isParityHomogeneous D Sc) (SKM.gdeg D sy)
    (SKM.isHomogeneous_gdeg D sy Sc hc)

/-- The target of (11.7), with its integer/parity decomposition. -/
def upBidegree (n : ℕ) (μ : X) (d : ℤ × ZMod 2) : Submodule k (UpAlgebra D Sc μ n) :=
  letI := skmPresentedGrading D Sc sy hc
  FiniteHomMatrix.bidegree d

/-- The source of (11.8) has unchanged integer degree and parity. -/
def sopBidegree (n : ℕ) (d : ℤ × ZMod 2) : Submodule k (SopAlgebra D Sc n) :=
  letI := gradedSupercategory D sy Sc hc
  FiniteHomMatrix.bidegree d

/-- The target of (11.8), with its integer/parity decomposition. -/
def downBidegree (n : ℕ) (μ : X) (d : ℤ × ZMod 2) : Submodule k (DownAlgebra D Sc μ n) :=
  letI := skmPresentedGrading D Sc sy hc
  FiniteHomMatrix.bidegree d

/-- Both target gradings are internal direct sums, as is the super-opposite source grading. -/
theorem algebraMapGradings_internal (n : ℕ) (μ : X) :
    DirectSum.IsInternal (upBidegree D Sc sy hc n μ) ∧
    DirectSum.IsInternal (sopBidegree D Sc sy hc n) ∧
    DirectSum.IsInternal (downBidegree D Sc sy hc n μ) := by
  let := skmPresentedGrading D Sc sy hc
  let := gradedSupercategory D sy Sc hc
  exact ⟨FiniteHomMatrix.isInternal_bidegree, FiniteHomMatrix.isInternal_bidegree,
    FiniteHomMatrix.isInternal_bidegree⟩

/-- Equation (11.7) preserves both gradings. -/
theorem alphaN_mem_bidegree {n : ℕ} (μ : X) {d : ℤ × ZMod 2} {a : Hn D Sc n}
    (ha : a ∈ Hn.bidegree D Sc sy hc n d) :
    alphaN D Sc n μ a ∈ upBidegree D Sc sy hc n μ d := by
  intro p
  exact ⟨alpha_mem_degree D Sc sy μ (ha p).1, alpha_mem_parity D Sc μ (ha p).2⟩

/-- Equation (11.8) preserves both gradings. -/
theorem alphaPrimeN_mem_bidegree {n : ℕ} (μ : X) {d : ℤ × ZMod 2} {a : SopAlgebra D Sc n}
    (ha : a ∈ sopBidegree D Sc sy hc n d) :
    alphaPrimeN D Sc n μ a ∈ downBidegree D Sc sy hc n μ d := by
  intro p
  exact ⟨alphaPrime_mem_degree D Sc sy μ (ha p).1,
    alphaPrime_mem_parity D Sc μ (ha p).2⟩

instance (n : ℕ) (μ : X) : SetLike.GradedMul (upBidegree D Sc sy hc n μ) where
  mul_mem := by
    intro d e a b ha hb
    let := skmPresentedGrading D Sc sy hc
    exact FiniteHomMatrix.mul_mem_bidegree ha hb

instance (n : ℕ) : SetLike.GradedMul (sopBidegree D Sc sy hc n) where
  mul_mem := by
    intro d e a b ha hb
    let := gradedSupercategory D sy Sc hc
    exact FiniteHomMatrix.mul_mem_bidegree ha hb

instance (n : ℕ) (μ : X) : SetLike.GradedMul (downBidegree D Sc sy hc n μ) where
  mul_mem := by
    intro d e a b ha hb
    let := skmPresentedGrading D Sc sy hc
    exact FiniteHomMatrix.mul_mem_bidegree ha hb

end OddMath.QuiverHecke
