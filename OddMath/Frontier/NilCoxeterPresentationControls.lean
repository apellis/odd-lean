import OddMath.Frontier.NilCoxeterPresentation

namespace OddMath.Frontier.NilCoxeterPresentation.Controls
open NilCoxeterWords (Word Reduced permutation)
open OddMath.SkewPolynomial (SkewPolynomial generator)
open AllRankDivided LongestDivided

 theorem literal_generator (n : ℕ) (i : Fin (n+1)) :
    toNilHecke n (crossing n i) = NilHeckeAction.crossing n i := toNilHecke_crossing n i

 theorem empty_control (n : ℕ) : product ([] : Word n) = 1 := rfl

 theorem unit_action (n : ℕ) (f : SkewPolynomial (n+2)) : action n 1 f = f := by
  rw [map_one]; rfl

 theorem square_control {n : ℕ} (i : Fin (n+1)) : product [i,i] = 0 := by
  simpa [product] using crossing_square i

 theorem braid_control : product ([0,1,0] : Word 1) = product [1,0,1] := by
  simpa [product,mul_assoc] using crossing_braid (0 : Fin 2) 1 (by decide)

 theorem distant_negative : product ([0,2] : Word 2) = -product [2,0] := by
  simpa [product] using crossing_distant (0 : Fin 3) 2 (by decide)

 theorem hidden_square_zero : product ([0,1,0,1] : Word 1) = 0 :=
  nonreduced_zero _ (by decide)

 theorem distant_forward : applyWord ([0,2] : Word 2) (generator 0 * generator 2) = -1 := by
  simp only [applyWord_cons,applyWord_nil]
  rw [divided_spectator_mul (2 : Fin 3) 0 (by decide) (by decide)]
  norm_num [divided_generator,Fin.ext_iff]

 theorem distant_reverse : applyWord ([2,0] : Word 2) (generator 0 * generator 2) = 1 := by
  simp only [applyWord_cons,applyWord_nil]
  change divided (2 : Fin 3) (divided (0 : Fin 3)
    (generator (0 : Fin 3).castSucc * generator 2)) = 1
  rw [divided_left_mul]
  norm_num [divided_generator,Fin.ext_iff]

 theorem distant_not_positive : product ([0,2] : Word 2) ≠ product [2,0] := by
  intro h
  have he := congrArg (fun a : Presented 2 => action 2 a (generator 0 * generator 2)) h
  simp only [action_product,distant_forward,distant_reverse] at he
  have hc := congrArg (fun f : SkewPolynomial 4 => f (0 : Fin 4 → ℕ)) he
  change -(Finsupp.single (0 : Fin 4 → ℕ) (1 : ℤ)) 0 =
    (Finsupp.single (0 : Fin 4 → ℕ) (1 : ℤ)) 0 at hc
  norm_num at hc

 theorem faithful_consumer (n : ℕ) (a b : Presented n)
    (h : ∀ f : SkewPolynomial (n+2), action n a f = action n b f) : a = b :=
  action_injective n (LinearMap.ext h)

 theorem quotient_relation_consumer (n : ℕ) (a b : Presented n)
    (h : toNilHecke n a = toNilHecke n b) : a = b := toNilHecke_injective n h

end OddMath.Frontier.NilCoxeterPresentation.Controls
