import OddMath.Frontier.ZeroHecke
import OddMath.Frontier.OnhReflection
import OddMath.Frontier.StrandCrossing
import OddMath.Frontier.ThickDots

/-! Audit for EKL arXiv:1111.1320v1 §3.2–§3.3 and §4.1–§4.2: headline statements restated on the
presented ring `NilHeckeAction.Presented n` (= ONH_{n+2}), plus transitive axioms. -/
namespace OddMath.Frontier.ThickCalculusAudit
open NilHeckeAction NilCoxeterWords NilHeckeRightBasis

/-- (3.17)–(3.18): the 0-Hecke generators `∂̄_r = x_r ∂_r`. -/
example (n : ℕ) (i j : Fin (n+1)) (h : j.val = i.val+1) :
    ZeroHecke.zeroHecke n i * ZeroHecke.zeroHecke n i = ZeroHecke.zeroHecke n i ∧
    ZeroHecke.zeroHecke n i * ZeroHecke.zeroHecke n j * ZeroHecke.zeroHecke n i =
      ZeroHecke.zeroHecke n j * ZeroHecke.zeroHecke n i * ZeroHecke.zeroHecke n j :=
  ⟨ZeroHecke.zeroHecke_sq i, ZeroHecke.zeroHecke_braid i j h⟩

/-- `e_a = ∂̄_{w_0}` does not depend on the reduced word. -/
example (n : ℕ) (w : Word n) (hw : Reduced w) (hp : permutation w = LongestElementary.longest (n+2)) :
    ZeroHecke.projector n = ZeroHecke.zeroHeckeProduct w :=
  ZeroHecke.projector_eq_of_reduced w hw hp

/-- Prop 3.5. -/
example (n : ℕ) : ZeroHecke.projector n =
    (-1 : ℤ)^((n+2).choose 3) • (ZeroHecke.staircaseElem n * ZeroHecke.DElem n) :=
  ZeroHecke.prop_3_5

/-- Prop 3.6 (1) (every 0-Hecke generator), (2), (3). -/
example (n : ℕ) (i : Fin (n+1)) :
    ZeroHecke.DElem n * ZeroHecke.zeroHecke n i = ZeroHecke.DElem n ∧
    ZeroHecke.DElem n * ZeroHecke.projector n = ZeroHecke.DElem n ∧
    ZeroHecke.projector n * ZeroHecke.projector n = ZeroHecke.projector n :=
  ⟨ZeroHecke.DElem_mul_zeroHecke i, ZeroHecke.DElem_mul_projector,
    ZeroHecke.projector_mul_projector⟩

/-- (3.51), corrected: `D_a = σ(D_a) = (−1)^{C(a,4)} ψ(D_a) = (−1)^{C(a,4)} ψσ(D_a)`. -/
example (n : ℕ) :
    ZeroHecke.DElem n = OnhReflection.sigma n (ZeroHecke.DElem n) ∧
    ZeroHecke.DElem n = (-1 : ℤ)^((n+2).choose 4) •
      MulOpposite.unop (reverseHom n (ZeroHecke.DElem n)) ∧
    ZeroHecke.DElem n = (-1 : ℤ)^((n+2).choose 4) •
      MulOpposite.unop (reverseHom n (OnhReflection.sigma n (ZeroHecke.DElem n))) :=
  OnhReflection.eq_3_51 n

/-- Prop 3.7. -/
example (n a b : ℕ) (hab : a+b = n+2) :
    product (LongestDivided.wordIn n (n+2) le_rfl) =
        product (StrandCrossing.triWord n 0 a) * product (StrandCrossing.triWord n a b) *
          product (StrandCrossing.crossWord n 0 a b) ∧
    product (LongestDivided.wordIn n (n+2) le_rfl) = (-1 : ℤ)^(a.choose 2 * b.choose 2) •
        (product (StrandCrossing.triWord n a b) * product (StrandCrossing.triWord n 0 a) *
          product (StrandCrossing.crossWord n 0 a b)) :=
  StrandCrossing.prop_3_7 (n := n) a b hab

#print axioms ZeroHecke.zeroHecke_braid
#print axioms ZeroHecke.zeroHeckeProduct_reduced_eq
#print axioms ZeroHecke.prop_3_5
#print axioms ZeroHecke.projector_mul_projector
#print axioms OnhReflection.eq_3_51
#print axioms OnhReflection.eq_3_51_printed_false
#print axioms OnhReflection.eq_3_52
#print axioms OnhReflection.eq_3_53
#print axioms OnhReflection.eq_3_54
#print axioms StrandCrossing.prop_3_7
#print axioms StrandCrossing.crossing_3_42
#print axioms ThickDots.schur_eq
#print axioms ThickDots.projector_poly_projector_eq
#print axioms ThickDots.thick_mul
#print axioms ThickDots.projector_schur_projector
#print axioms ThickDots.projector_dualSchur_projector

end OddMath.Frontier.ThickCalculusAudit
