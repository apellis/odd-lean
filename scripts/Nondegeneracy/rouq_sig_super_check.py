# /// script
# requires-python = ">=3.10"
# dependencies = ["sympy==1.14.0"]
# ///
"""Exact cup--crossing--cap tests in cutoff-two separated towers.

The optional connected slice has reservoir content (a,1_j), probe (b,0_j),
and Q_ij=x^2-y^4. It does not enumerate other multicolour contents.
Induction and constrained-Hom coinduction use nonvacuum_rankone's algebra
coordinates. Mixed mates are computed from adjunctions, never from the
proposed expansion. The even control distinguishes the raw source mate
from sigma=-q*sigma_src. By default it checks all 27 projective-generator
instances (equivalently --all-contents --connected). Use --middle-only for
the three middle-content cases, --regular to retain redundant regular
matrix-algebra copies, or --exterior for the nonzero delta_i middle-content
rank-one control.
"""

import argparse
import importlib.util
from functools import lru_cache
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import sympy as S


def model(odd, exterior=False, regular=False):
    name = "nonvacuum_exterior" if exterior else "nonvacuum_rankone"
    spec = importlib.util.spec_from_file_location(
        name, Path(__file__).with_name(name + ".py")
    )
    assert spec is not None and spec.loader is not None
    m: Any = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)

    def sparse_kron(a, b):
        return S.SparseMatrix(
            a.rows * b.rows,
            a.cols * b.cols,
            {
                (i * b.rows + k, j * b.cols + l): v * w
                for (i, j), v in a.todok().items()
                for (k, l), w in b.todok().items()
            },
        )

    m.kron = sparse_kron

    if not odd:
        assert not exterior
        m.A = [
            m.Alg([S.eye(1)], [0]),
            m.Alg([S.eye(2), m.e10], [0, 0]),
            m.Alg([m.e00, m.e11, m.e01, m.e10], [0] * 4),
        ]
        m.B = [
            m.Alg([S.eye(1)], [0]),
            m.Alg([S.eye(2), m.e01 + m.e10], [0, 0]),
            m.Alg([m.e00, m.e11, m.e01, m.e10], [0] * 4),
        ]
        m.C = {(a, b): m.TensorAlg(m.A[a], m.B[b]) for a in range(3) for b in range(3)}
    oldEm, oldFm = m.Em, m.Fm
    oldunit, oldcap, olddot, oldT = m.unit, m.counit, m.dot, m.T

    def zero(idx):
        return m.Mod(idx, [], [], "zero")

    @lru_cache(None)
    def E(v, t):
        a, b = v.idx
        idx = (a + 1, b) if t == 0 else (a, b - 1)
        if not v.n or idx not in m.C:
            return zero(idx)
        return m.ind(v, idx) if t == 0 else m.shift(m.res(v, idx), a % 2 if odd else 0)

    @lru_cache(None)
    def F(v, t):
        a, b = v.idx
        idx = (a - 1, b) if t == 0 else (a, b + 1)
        if not v.n or idx not in m.C:
            return zero(idx)
        return (
            m.res(v, idx) if t == 0 else m.coind(m.shift(v, a % 2 if odd else 0), idx)
        )

    def Em(f, v, w, t, p=0):
        if not E(v, t).n or not E(w, t).n:
            return S.zeros(E(w, t).n, E(v, t).n)
        if not odd and t == 1:
            return f
        return oldEm(f, v, w, t, p)

    def Fm(f, v, w, t, p=0):
        if not F(v, t).n or not F(w, t).n:
            return S.zeros(F(w, t).n, F(v, t).n)
        return oldFm(f, v, w, t, p if odd else 0)

    def unit(v, t):
        if not E(v, t).n:
            return S.zeros(0, v.n)
        return oldunit(v, t)

    def cap(v, t):
        if not F(v, t).n:
            return S.zeros(v.n, 0)
        return oldcap(v, t)

    def dot(v, t):
        if not E(v, t).n:
            return S.zeros(0)
        if odd:
            return olddot(v, t)
        a, b = v.idx
        if t == 0:
            e = E(v, t)
            d = m.C[e.idx]
            xi = m.kron(m.A[a + 1].coord(m.e10 if a == 0 else -m.e10), m.B[b].one)
            return e.Q * m.kron(S.eye(v.n), m.lmul(d, xi)) * e.sec
        eta = m.kron(m.A[a].one, m.B[b].coord((1 if b == 1 else -1) * (m.e01 + m.e10)))
        return v.action(eta)

    @lru_cache(None)
    def T(v, p, q, s, r):
        src = E(E(v, q), p)
        tar = E(E(v, r), s)
        if not src.n or not tar.n:
            return S.zeros(tar.n, src.n)
        if odd:
            return oldT(v, p, q, s, r)
        if p == q == s == r == 0:
            K, direct = m.collapseAA(v)
            d = m.C[direct.idx]
            tau = m.kron(m.A[2].coord(-m.e01), m.B[v.idx[1]].one)
            return (
                K.inv() * direct.Q * m.kron(S.eye(v.n), m.lmul(d, tau)) * direct.sec * K
            )
        if p == q == s == r == 1:
            return v.action(m.kron(m.A[v.idx[0]].one, m.B[2].coord(m.e01)))
        J = m.mixedJ(v)
        b = E(v, 1)
        X = dot(b, 0)
        Y = Em(dot(v, 1), b, b, 0)
        a = (X - Y).inv()
        return {
            (0, 1, 0, 1): a,
            (0, 1, 1, 0): J,
            (1, 0, 0, 1): -a * a * J.inv(),
            (1, 0, 1, 0): -J * a * J.inv(),
        }[p, q, s, r]

    def mate(v, p, q, s, r):
        fr = F(v, r)
        src = E(fr, q)
        tar = F(E(v, s), p)
        ep = E(src, p)
        etarget = E(E(fr, r), s)
        if not ep.n or not etarget.n:
            return S.zeros(tar.n, src.n)
        cup = unit(src, p)
        cross = Fm(T(fr, p, q, s, r), ep, etarget, p, int(odd))
        counit = Em(cap(v, r), E(fr, r), v, s)
        finish = Fm(counit, etarget, E(v, s), p)
        return finish * cross * cup

    m.Ei, m.Fi, m.Em, m.Fm = E, F, Em, Fm
    m.unit, m.counit, m.dot, m.T, m.mate = unit, cap, dot, T, mate
    m.odd, m.exterior, m.connected = odd, exterior, False
    full_regular = m.regular

    @lru_cache(None)
    def generator(idx):
        v = full_regular(idx)
        if regular:
            return v
        # e_00 A_2 and e_00 B_2 are graded projective generators.
        # Remove redundant matrix-algebra copies, not spectral sectors.
        a, b = idx
        selected = [
            k
            for k, (i, j) in enumerate(
                (i, j) for i in range(m.A[a].n) for j in range(m.B[b].n)
            )
            if (a != 2 or i // (2 if exterior else 1) in (0, 2))
            and (b != 2 or j in (0, 2))
        ]
        H = S.eye(v.n)[:, selected]
        actions = [H.T * f * H for f in v.act]
        assert all(f * H == H * g for f, g in zip(v.act, actions))
        return m.Mod(idx, [v.ps[k] for k in selected], actions, "projective generator")

    m.regular = generator
    return m


def connected_slice(base):
    """Transport the ji^a corner tower, retaining the occupied-j parity line.

    f_i=1, f_j=y^2+y delta; Q_ij=x^2-y^4. Only ji^a survives.
    Mixed crossings vanish and their square forces x_1^2=y^4=0.
    Hence this corner tower is R tensor ONH_a^2, not an independent
    disconnected datum. All functor and adjunction maps below are transported
    along this algebra isomorphism. G_(a,b)=Pi^b accounts for the extra
    occupied odd j strand in the B-sector parity line.
    """
    assert base.odd and not base.exterior
    # Left multiplication in the basis (1,y,delta,y delta).
    y = S.Matrix([[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, -1, 1, 0]])
    delta = S.Matrix([[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, -1, 0, 0]])
    P = S.diag(1, -1, -1, 1)
    assert delta**2 == S.zeros(4) and delta.rank() == 2
    assert y**2 + y * delta == S.zeros(4) and y**3 == S.zeros(4)
    assert y * delta + delta * y == S.zeros(4)
    assert P * y == -y * P and P * delta == -delta * P
    assert y**2 != S.zeros(4)

    @lru_cache(None)
    def wrap(v):
        return SimpleNamespace(
            base=v,
            idx=v.idx,
            n=4 * v.n,
            ps=[(r + p + v.idx[1]) % 2 for r in (0, 1, 1, 0) for p in v.ps],
        )

    def lift(f, p, idx):
        return (-1) ** ((idx[1] * p) % 2) * base.kron(P if p % 2 else S.eye(4), f)

    def unlift(f, p, idx, rows, cols):
        raw = (-1) ** ((idx[1] * p) % 2) * f[:rows, :cols]
        assert f == lift(raw, p, idx), "map outside the transported tensor subspace"
        return raw

    def E(v, t):
        return wrap(base.Ei(v.base, t))

    def F(v, t):
        return wrap(base.Fi(v.base, t))

    def Em(f, v, w, t, p=0):
        raw = unlift(f, p, v.idx, w.base.n, v.base.n)
        return lift(base.Em(raw, v.base, w.base, t, p), p, E(w, t).idx)

    def Fm(f, v, w, t, p=0):
        raw = unlift(f, p, v.idx, w.base.n, v.base.n)
        return lift(base.Fm(raw, v.base, w.base, t, p), p, F(w, t).idx)

    def unit(v, t):
        return lift(base.unit(v.base, t), 0, v.idx)

    def cap(v, t):
        return lift(base.counit(v.base, t), 0, v.idx)

    def dot(v, t):
        return lift(base.dot(v.base, t), 1, E(v, t).idx)

    def T(v, p, q, s, r):
        return lift(base.T(v.base, p, q, s, r), 1, E(E(v, r), s).idx)

    def mate(v, p, q, s, r):
        # Recompute the whole transported composite, not a tensor of a mate.
        fr = F(v, r)
        src = E(fr, q)
        tar = F(E(v, s), p)
        ep = E(src, p)
        etarget = E(E(fr, r), s)
        if not ep.n or not etarget.n:
            return S.zeros(tar.n, src.n)
        cup = unit(src, p)
        cross = Fm(T(fr, p, q, s, r), ep, etarget, p, 1)
        evaluation = Em(cap(v, r), E(fr, r), v, s)
        finish = Fm(evaluation, etarget, E(v, s), p)
        return finish * cross * cup

    print(
        "PASS connected ji^a corner presentation: delta!=0, y^2!=0, y^3=0; "
        "Q_ij=x^2-y^4; probe j-content=0",
        flush=True,
    )
    return SimpleNamespace(
        regular=lambda idx: wrap(base.regular(idx)),
        Ei=E,
        Fi=F,
        Em=Em,
        Fm=Fm,
        unit=unit,
        counit=cap,
        dot=dot,
        T=T,
        mate=mate,
        odd=True,
        exterior=False,
        connected=True,
    )


def check(m, idx):
    v = m.regular(idx)
    q = -1 if m.odd else 1
    E, F = m.Ei, m.Fi
    branches = [(a, b) for a in (0, 1) for b in (0, 1)]
    src = [E(F(v, r), s) for s, r in branches]
    tar = [F(E(v, s), r) for r, s in branches]
    for t in (0, 1):
        e, f = E(v, t), F(v, t)
        assert m.counit(e, t) * m.Em(m.unit(v, t), v, F(e, t), t) == S.eye(e.n)
        assert m.Fm(m.counit(v, t), E(f, t), v, t) * m.unit(f, t) == S.eye(f.n)
    for r in (0, 1):
        n = F(v, r)
        for words in ([(0, 1), (1, 0)], [(r, r)]):
            X = S.diag(*[m.dot(E(n, b), a) for a, b in words])
            Y = S.diag(
                *[m.Em(m.dot(n, b), E(n, b), E(n, b), a, int(m.odd)) for a, b in words]
            )
            T = S.BlockMatrix(
                [[m.T(n, a, b, c, d) for a, b in words] for c, d in words]
            ).as_explicit()
            assert X * Y == q * Y * X
            assert T * X - q * Y * T == S.eye(X.rows)
            assert X * T - q * T * Y == S.eye(X.rows)
            assert T * T == S.zeros(X.rows)
    blocks = [
        [
            m.mate(v, p, a, s, b)
            if sorted((p, a)) == sorted((s, b))
            else S.zeros(tar[j].n, src[k].n)
            for k, (a, b) in enumerate(branches)
        ]
        for j, (p, s) in enumerate(branches)
    ]
    raw = S.BlockMatrix(blocks).as_explicit()
    sig = -q * raw

    def u(t, r):
        e = E(v, t)
        if not e.n:
            return S.zeros(0, v.n)
        return m.Fm(m.dot(v, t) ** r, e, e, t, (r * int(m.odd)) % 2) * m.unit(v, t)

    def cap(t, r):
        f = F(v, t)
        if not f.n:
            return S.zeros(v.n, 0)
        return m.counit(v, t) * m.dot(f, t) ** r

    bound = 3 if m.exterior else 2
    assert m.dot(v, 0) ** bound == S.zeros(E(v, 0).n)
    assert m.dot(F(v, 0), 0) ** bound == S.zeros(src[0].n)
    C = -q * blocks[0][3]
    D = -q * blocks[3][0]
    cp = sum((q**r * u(0, r) * cap(1, -r - 1) for r in range(bound)), S.zeros(*C.shape))
    dp = -sum(
        (q ** (r + 1) * u(1, -r - 1) * cap(0, r) for r in range(bound)),
        S.zeros(*D.shape),
    )
    assert C == cp and D == dp, "ordered expansion"
    hA = 2 * idx[0] - 2
    hB = 2 - 2 * idx[1]
    h = hA + hB
    if h > 0:
        rows = [
            S.Matrix.hstack(
                *[
                    cap(a, r) if a == b else S.zeros(v.n, n.n)
                    for (a, b), n in zip(branches, src)
                ]
            )
            for r in range(h)
        ]
        total = S.Matrix.vstack(sig, *rows)
    elif h < 0:
        columns = [
            S.Matrix.vstack(
                *[
                    u(a, r) if a == b else S.zeros(n.n, v.n)
                    for (a, b), n in zip(branches, tar)
                ]
            )
            for r in range(-h)
        ]
        total = S.Matrix.hstack(sig, *columns)
    else:
        total = sig
    assert total.rows == total.cols, ("height dimension", total.shape, h)
    total = S.SparseMatrix(total)
    inv = S.SparseMatrix(S.Matrix(total).inv())
    assert total * inv == inv * total == S.eye(total.rows)

    def common_inverse(t, height):
        s = -q * blocks[3 * t][3 * t]
        if height > 0:
            factor = S.Matrix.vstack(s, *[cap(t, r) for r in range(height)])
            inverse = factor.inv()
            return inverse[:, : s.rows]
        if height < 0:
            factor = S.Matrix.hstack(s, *[u(t, r) for r in range(-height)])
            inverse = factor.inv()
            return inverse[: s.cols, :]
        return s.inv()

    rA = common_inverse(0, hA)
    rB = common_inverse(1, hB)
    feedback = D * rA * C * rB
    power = S.eye(feedback.rows)
    nilindex = None
    for n in range(1, max(1, feedback.rows) + 1):
        power = power * feedback
        if power == S.zeros(feedback.rows):
            nilindex = n
            break
    assert nilindex is not None, "whole feedback not nilpotent"
    feedback_note = f"rank={feedback.rank()}, nilpotence index={nilindex}"
    print(
        f"PASS {'connected odd slice' if m.connected else 'odd exterior' if m.exterior else 'odd' if m.odd else 'even control'}"
        f" content={idx} heights={(hA, hB, h)} total={total.rows}x{total.cols}"
        f" C,D=ordered expansions; inverse=two-sided; feedback={feedback_note}",
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exterior", action="store_true")
    parser.add_argument("--all-contents", action="store_true")
    parser.add_argument("--connected", action="store_true")
    parser.add_argument("--middle-only", action="store_true", help="test only a=b=1")
    parser.add_argument(
        "--regular",
        action="store_true",
        help="retain redundant regular matrix-algebra copies",
    )
    args = parser.parse_args()
    all_contents = args.all_contents or (not args.middle_only and not args.exterior)
    cases = [(a, b) for a in range(3) for b in range(3)] if all_contents else [(1, 1)]
    for odd in (False, True):
        m = model(odd, exterior=args.exterior and odd, regular=args.regular)
        for idx in cases:
            try:
                check(m, idx)
            except Exception:
                print(
                    f"FAIL parity={int(odd)} exterior={m.exterior} content={idx}",
                    flush=True,
                )
                raise
    if args.connected or not args.exterior:
        connected = connected_slice(
            m if not args.exterior else model(True, regular=args.regular)
        )
        for idx in cases:
            try:
                check(connected, idx)
            except Exception:
                print(f"FAIL connected occupied-j slice content={idx}", flush=True)
                raise
    print(
        "NOT TESTED: other multicolour contents or simultaneous independent delta_i,delta_j.",
        flush=True,
    )


if __name__ == "__main__":
    main()
