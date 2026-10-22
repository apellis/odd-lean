import OddMath

/-! # Consumers of the KKT twisted module and the operators `σ_a` -/

noncomputable section
open OddMath.QuiverHecke.Realization

/-- The parity with `true` odd. -/
def parB : Bool → ZMod 2 := fun b => if b then 1 else 0

/-- A non-constant `Q̃`: `u² + v²` for all colours. -/
def sqSum : PairFn Bool ℚ where
  toFun _ _ u v := u ^ 2 + v ^ 2
  map' e _ _ u v := by simp
  symm' _ _ u v := add_comm _ _

theorem sqSum_isEven : sqSum.IsEven parB := fun _ _ u v _ => by simp [sqSum]

example (a : ℕ) : sig parB sqSum a * sig parB sqSum a = mulK (sqSum.val a (a + 1)) :=
  sig_mul_self parB sqSum sqSum_isEven a

example (a : ℕ) :
    sig parB sqSum (a + 1) * sig parB sqSum a * sig parB sqSum (a + 1) -
        sig parB sqSum a * sig parB sqSum (a + 1) * sig parB sqSum a =
      fpq parB a (a + 2) * mulK (sqSum.val (a + 1) (a + 2) - sqSum.val a (a + 1)) :=
  sig_braid parB sqSum sqSum_isEven a

example : sig parB sqSum 0 * sig parB sqSum 2 = sig parB sqSum 2 * sig parB sqSum 0 :=
  sig_comm parB sqSum sqSum_isEven (by omega)

example (a p : ℕ) : sig parB sqSum a * clif parB p = clif parB (sw a p) * sig parB sqSum a :=
  sig_clif parB sqSum sqSum_isEven a p

example (a : ℕ) :
    sig parB sqSum a * mulK (fun _ => y a) - mulK (fun _ => y (a + 1)) * sig parB sqSum a =
      mulK (eqv a) + clif parB a * clif parB (a + 1) * mulK (eqv a) :=
  sig_dot_left parB sqSum a

example : IsUnit (y (k := ℤ) 0 + y 1) := isUnit_y_add (by decide)

example : IsUnit (y (k := ZMod 2) 0 - y 1) := isUnit_y_sub (by decide)

#print axioms OddMath.QuiverHecke.Realization.sig_braid
#print axioms OddMath.QuiverHecke.Realization.sig_dot_right
#print axioms OddMath.QuiverHecke.Realization.twist_twist

/-! ## The representation of the quiver Hecke supercategory

The relations (1.7)–(1.9) hold for all colours, including the extra dotted terms of (1.9) when
the outer colours agree, for countably many odd colours over `ℚ`. -/

section Representation
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

example (u : StringDiagrams.Obj (OddMath.QuiverHecke.sig datum)) (v : List (OddMath.QuiverHecke.sig datum).Colour) :
    (interp datum scalars).evalW (seqOf (I := ℕ) (wI u ++ [0, 1, 0] ++ cI v))
      (seqOf (I := ℕ) (wI u ++ [0, 1, 0] ++ cI v)) u v
      (relation datum scalars (.braidEq 0 1 (by decide))) = 0 :=
  interp_rel datum scalars (.braidEq 0 1 (by decide)) u v

example : (pres datum scalars).Respects (interp datum scalars).functor :=
  respects datum scalars

example : (rep datum scalars).obj ((pres datum scalars).obj (ob datum [0, 1])) =
    (interp datum scalars).functor.obj (ob datum [0, 1]) :=
  rfl

end Representation

#print axioms OddMath.QuiverHecke.Realization.interp_rel
#print axioms OddMath.QuiverHecke.Realization.respects
