import OddMath.Frontier.GradedK0Basic
import OddMath.Frontier.GradedK0Connected
import OddMath.Frontier.GradedK0Morita

/-!
# Graded `K₀` via graded idempotent matrices

Grothendieck groups of graded finitely generated projective modules over a `ℤ`-graded ring
`R` (grading `A : ℤ → AddSubgroup R`, `SetLike.GradedMonoid A`), modelled by graded
idempotent matrices up to Murray–von Neumann equivalence; used for EKL arXiv:1111.1320v1 §6.

Conventions: `R{k}` has its generator in degree `k`; a graded idempotent `(n, s, e)` has
`e i j ∈ A (s i - s j)` and represents `R^n{s} · e`; `T k ∈ ℤ[T;T⁻¹]` acts on `K₀`
by `{k}`.

* `GradedK0Basic`: `IsHom`, `MvN` (an equivalence relation), `GIdem`, block sum and shift,
  the commutative monoid `GProj A`, the Grothendieck group `K0 A` and its
  `ℤ[T;T⁻¹]`-module structure.
* `GradedK0Connected`: for a connected grading (`A d = 0` for `d < 0`, `A 0 = ℤ · 1`,
  `ℤ ↪ R`), every graded idempotent is equivalent to a graded free module `R^m{t}`
  (`GIdem.exists_free`), the multiplicity of each shift is the rank of the corresponding
  block of the degree-zero reduction (`GIdem.card_shift_eq`), and
  `K0 A ≃ₗ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹]` with `[R{k}] ↦ T k` (`K0.classify`, `K0.basis`).
* `GradedK0Morita`: for `Mat_κ(R)` graded by `deg (E_ab r) = deg r + d a - d b`,
  `K0 (matGrading A d) ≃ₗ[ℤ[T;T⁻¹]] K0 A` with `[E_aa] ↦ [R{-d a}]` (`K0.morita`,
  `K0.morita_corner`).
-/
