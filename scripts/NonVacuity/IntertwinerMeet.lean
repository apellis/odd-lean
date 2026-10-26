import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChain
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! The three-strand identity on `i, j, i` (KKO arXiv:1206.5933v2, Lemma 8.3 and (8.13)) for the
two distinct odd colours of the all-odd two-colour datum, and the resulting unconditional first
identity of (8.13) for an old crossing of the colours `true, true` under the moving strand. -/
noncomputable section
open CategoryTheory OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

example : meetLeft datum scalars [] [] true false true = meetRight datum scalars [] [] true false true :=
  meetLeft_eq_meetRight_iji datum scalars [] [] (by decide)

example : meetLeft datum scalars [false] [true] false true false =
    meetRight datum scalars [false] [true] false true false :=
  meetLeft_eq_all datum scalars [false] [true] false true false

/-- The moving strand of colour `true` passes an old crossing of `false, true`. -/
example := cross_comp_moveHom_all datum scalars [] true false true [] []

/-- The balance for the positioned word "cross, then dot" on `false, true`. -/
example := cl_comp_moveHom datum scalars true [PG.cross 0, PG.dot 1] (sChain_pl [false, true] _)
  (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp [PG.pos, PG.width])
