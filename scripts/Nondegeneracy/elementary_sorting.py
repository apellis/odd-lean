"""Typed local word checks, not an SKM action or matching-independence test."""

from collections import defaultdict
from functools import lru_cache

Token = tuple[str, int]
Word = tuple[Token, ...]
Polynomial = dict[Word, int]
ENDS = {
    "u": ("A", "A"), "d": ("A", "A"), "P": ("A", "A"),
    "x": ("B", "B"), "v": ("B", "B"), "S": ("A", "B"),
    "e": ("A", "O"), "H": ("O", "B"), "D": ("O", "A"),
    "q": ("O", "O"),
}


def t(name: str, n: int = 0) -> Token:
    return name, n


def power(name: str, n: int) -> Word:
    return (t(name),) * n


def typed(word: Word, source: str, target: str) -> None:
    current = source
    for name, _ in word:
        dom, cod = ENDS[name]
        assert current == dom, (word, current, dom)
        current = cod
    assert current == target, (word, current, target)


def rule(word: Word, pos: int, wrong_down_sign: bool):
    first = word[pos]
    if first == t("q", 0):
        return 1, ((1, ()),)
    if pos + 1 == len(word):
        return None
    second = word[pos + 1]
    if first == t("u") and second[0] == "e":
        return 2, ((1, (t("e", second[1] + 1),)),)
    if first == t("d") and second[0] == "e":
        return 2, (((-1) ** second[1], (t("e", second[1] + 1),)),)
    if first[0] == "H" and second == t("x"):
        return 2, ((1, (t("H", first[1] + 1),)),)
    if first == t("u") and second == t("S"):
        return 2, ((-1, (t("S"), t("x"))), (1, (t("e"), t("H"))))
    if first == t("d") and second == t("S"):
        correction = 1 if wrong_down_sign else -1
        return 2, ((-1, (t("S"), t("v"))), (correction, (t("e"), t("H"))))
    if first == t("D") and second == t("S"):
        return 2, ()
    if first == t("D") and second[0] == "e":
        return 2, ((1, (t("q", second[1]),)),)
    return None


@lru_cache(None)
def normal(word: Word, wrong_down_sign: bool = False) -> Polynomial:
    for pos in range(len(word)):
        replacement = rule(word, pos, wrong_down_sign)
        if replacement is None:
            continue
        count, terms = replacement
        old = word[pos:pos + count]
        source, target = ENDS[old[0][0]][0], ENDS[old[-1][0]][1]
        typed(old, source, target)
        out: dict[Word, int] = defaultdict(int)
        for coefficient, piece in terms:
            typed(piece, source, target)
            for reduced, value in normal(word[:pos] + piece + word[pos + count:], wrong_down_sign).items():
                out[reduced] += coefficient * value
        return {key: value for key, value in out.items() if value}
    return {word: 1}


def expand(terms: list[tuple[int, Word]], prefix: Word = ()) -> Polynomial:
    out: dict[Word, int] = defaultdict(int)
    for coefficient, word in terms:
        for reduced, value in normal(prefix + word).items():
            out[reduced] += coefficient * value
    return {key: value for key, value in out.items() if value}


def chi(n: int) -> int:
    return n * (n - 1) // 2


def through_cross(a: int, b: int) -> list[tuple[int, Word]]:
    terms = [((-1) ** (a + b), (t("S"),) + power("x", a) + power("v", b))]
    terms += [
        ((-1) ** (a + b + 1 + s), (t("e", s), t("H", a - 1 - s)) + power("v", b))
        for s in range(a)
    ]
    terms += [
        (-(-1) ** (r + chi(b - 1 - r)), (t("e", a + b - 1 - r), t("H")) + power("v", r))
        for r in range(b)
    ]
    return terms


def cap_cross(a: int, b: int) -> list[tuple[int, Word]]:
    # The common unit c has been factored out: this is c^{-1} K_ab.
    return [
        ((-1) ** (b + 1 + r), (t("e", a), t("q", r), t("H", b - 1 - r)))
        for r in range(b)
    ]


def main() -> None:
    checked = 0
    for a in range(7):
        for b in range(7):
            through = power("u", a) + power("d", b)
            cap_cup = (t("e", a), t("D")) + power("u", b)
            cases = [
                (through + (t("e"),), [((-1) ** chi(b), (t("e", a + b),))], "O"),
                (through + (t("S"),), through_cross(a, b), "B"),
                (cap_cup + (t("e"),), [(1, (t("e", a), t("q", b)))], "O"),
                (cap_cup + (t("S"),), cap_cross(a, b), "B"),
            ]
            for prefix in ((), (t("P"),)):
                for word, expected, target in cases:
                    typed(prefix + word, "A", target)
                    for _, term in expected:
                        typed(prefix + term, "A", target)
                    result = normal(prefix + word)
                    assert result == expand(expected, prefix), (a, b, word)
                    for term in result:
                        typed(term, "A", target)
                    checked += 1

    # Corruptions with explicit nonzero discrepancies in these word normal forms.
    assert normal((t("d"), t("S")), True) != expand(through_cross(0, 1))
    assert normal(power("d", 2) + (t("e"),)) != {(t("e", 2),): 1}
    assert expand(cap_cross(0, 2)) != expand([(-1, (t("e"), t("H", 1)))])
    assert normal((t("e"), t("D"), t("S"))) == {}
    assert normal((t("e"), t("D"), t("e"))) != {}
    print({"typed_component_checks": checked, "mutation_rejections": 4})
    print("PASS: both components, both matching types, dot exponents 0..6, source prefix retained.")
    print("Not tested: all SKM relations, right-adjunction closures, full SYM transport, or independence.")


if __name__ == "__main__":
    main()
