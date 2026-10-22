/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Algebra
import OddMath.QuiverHecke.Basis

/-!
# The basis theorem for the quiver Hecke superalgebra `H_n`

`H_n = ⊕_{a,b} Hom_H(b, a)` (BE2, arXiv:1701.04133v2, (11.1)) has the basis of the matrix
entries `x^l ψ_w` at `(a, b)`, where `x^l ψ_w : b → a` runs over the normal forms of
`basisNF` (Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Corollary 3.15). Any colour set, any
super Kac–Moody datum and scalars, any commutative ring.
-/

noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The normal forms of `H_n`: a pair of words `(a, b)` and a normal form `b → a`. -/
abbrev HnIdx (I : Type u) (n : ℕ) := Σ p : Word I n × Word I n, NFIdx p.2.val p.1.val

/-- **The basis theorem for `H_n`**: the matrix entries `x^l ψ_w` at `(a, b)`. -/
def Hn.basis (n : ℕ) : Module.Basis (HnIdx I n) k (Hn D Sc n) :=
  DFinsupp.basis fun p => basisNF D Sc p.2.val p.1.val

@[simp] theorem Hn.basis_apply (n : ℕ) (a b : Word I n) (i : NFIdx b.val a.val) :
    Hn.basis D Sc n ⟨(a, b), i⟩ = Hn.single a b i.nf := by
  classical
  simp only [Hn.basis, DFinsupp.basis, Module.Basis.coe_ofRepr, LinearEquiv.symm_trans_apply]
  simp [sigmaFinsuppEquivDFinsupp_single, Hn.single, FiniteHomMatrix.single]
  congr 1 <;> first | exact Subsingleton.elim _ _ | exact basisNF_apply D Sc b.val a.val i

end OddMath.QuiverHecke
