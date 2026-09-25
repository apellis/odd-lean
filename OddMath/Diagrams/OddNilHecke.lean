import OddMath.Diagrams.OddNilHecke.Basic
import OddMath.Diagrams.OddNilHecke.Relations
import OddMath.Diagrams.OddNilHecke.Action
import OddMath.Diagrams.OddNilHecke.Comparison

/-!
# The diagrammatic odd nilHecke category

EKL, arXiv:1111.1320v1, Proposition 2.1 and §2.2, via the diagram library
`string-diagrams-lean`:

* `OddMath.Diagrams.OddNilHecke.Basic`: the presented super 2-category with odd dots and
  crossings; only the square, braid and mixed relations are imposed.
* `OddMath.Diagrams.OddNilHecke.Relations`: the seven relation families of Prop. 2.1 at every
  width and position, the anticommutations coming from the Koszul-signed interchange law.
* `OddMath.Diagrams.OddNilHecke.Action`: the polynomial representation (dots by
  multiplication, crossings by odd divided differences), with width-dependent objects.
* `OddMath.Diagrams.OddNilHecke.Comparison`: `presentedEquivEnd n`, a ring isomorphism from
  odd-lean's presented ring `NilHeckeAction.Presented n` to the endomorphism ring of `n + 2`
  strands, compatible with the polynomial actions.
-/
