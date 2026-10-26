# /// script
# requires-python = ">=3.10"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Super rouqSig projection formula on genuine two-colour cyclotomic reservoirs.

Reservoir tower A_a = R^Lambda(a i + m j) (exact KKO cyclotomic quotients built
by klr_cyclotomic.py from the presentation, verified against the dimension
formula, all relations and associativity).  E^A = induction along the
non-unital inclusion R(beta) -> R(beta+i) (new i strand on the right), F^A =
restriction to M e(beta,i).  Probe tower B_b = the single-colour cutoff-two
probe of rouq_sig_super_check.py (f_i = y^2-1), E^B = Pi^{s(a)} restriction,
F^B = constrained-Hom coinduction.  The separated algebra is A_a (x) B_b with
the Koszul sign.  Everything is exact over Q (python-flint fmpq matrices).

Induction is computed from an explicit presentation of e(beta,i)A_{a+1} as a
left A_a-module (generators t_k, left kernel generators kappa_r, a linear
section), so M (x)_{A_a} e A_{a+1} = M^K / span{(m kappa_{r,k})_k}.  The
crossing on E^A E^A is computed after collapsing to M (x) e(beta,i,i)A_{a+2}.
Mates are cup-crossing-cap composites as in rouq_sig_super_check.py; nothing
is assumed about their blocks.  For each content and each projective test
module e(nu)A_a (x) e'B_b we check: both adjunction triangles, the upward
relations on every two-letter word, the ordered C/D expansions for
sigma = -q sigma_src, the two-sided inverse of the total map, and nilpotence of
the whole feedback D r_A C r_B.
"""
from __future__ import annotations

import argparse
import itertools
import sys
import time
from functools import lru_cache
from pathlib import Path

import flint

sys.path.insert(0, str(Path(__file__).parent))
from klr_cyclotomic import KLR, build, fq, sgn  # noqa: E402

F = flint.fmpq_mat


# ---------------------------------------------------------------- matrices
def Z(r, c):
    return F(r, c)


def eye(n):
    M = F(n, n)
    for i in range(n):
        M[i, i] = 1
    return M


def hstack(ms, r):
    ms = [m for m in ms if m.ncols()]
    if not ms:
        return F(r, 0)
    Ls = [m.tolist() for m in ms]
    c = sum(m.ncols() for m in ms)
    if r == 0:
        return F(0, c)
    return F(r, c, [x for i in range(r) for L in Ls for x in L[i]])


def vstack(ms, c):
    ms = [m for m in ms if m.nrows()]
    if not ms:
        return F(0, c)
    r = sum(m.nrows() for m in ms)
    if c == 0:
        return F(r, 0)
    return F(r, c, [x for m in ms for row in m.tolist() for x in row])


def blocks(rows, rdims, cdims):
    out = F(sum(rdims), sum(cdims))
    r0 = 0
    for i, row in enumerate(rows):
        c0 = 0
        for j, b in enumerate(row):
            if b is not None and b.nrows() and b.ncols():
                L = b.tolist()
                for a in range(b.nrows()):
                    for c in range(b.ncols()):
                        if L[a][c] != 0:
                            out[r0 + a, c0 + c] = L[a][c]
            c0 += cdims[j]
        r0 += rdims[i]
    return out


def bdiag(ms):
    n = len(ms)
    return blocks([[ms[i] if i == j else None for j in range(n)] for i in range(n)],
                  [m.nrows() for m in ms], [m.ncols() for m in ms])


def iszero(M):
    return all(x == 0 for row in M.tolist() for x in row)


def rref_rows(M):
    R, rk = M.rref()
    L = R.tolist()
    piv = []
    for i in range(rk):
        for j, x in enumerate(L[i]):
            if x != 0:
                piv.append(j)
                break
    return L[:rk], piv


def nullspace(M):
    """Columns spanning {v : M v = 0}; returns (N, free) with N[free,:] = I."""
    n = M.ncols()
    if M.nrows() == 0:
        return eye(n), list(range(n))
    rows, piv = rref_rows(M)
    free = [j for j in range(n) if j not in set(piv)]
    N = F(n, len(free))
    for c, f in enumerate(free):
        N[f, c] = 1
        for i, p in enumerate(piv):
            if rows[i][f] != 0:
                N[p, c] = -rows[i][f]
    return N, free


def colspace(M):
    """Columns H spanning the column space with H[piv,:]=I (rref of M^T)."""
    n = M.nrows()
    if M.ncols() == 0:
        return F(n, 0), []
    rows, piv = rref_rows(M.transpose())
    H = F(n, len(rows), [rows[c][i] for i in range(n) for c in range(len(rows))]) if rows else F(n, 0)
    return H, piv


def select_rows(idx, n):
    S = F(len(idx), n)
    for i, j in enumerate(idx):
        S[i, j] = 1
    return S


def quotient(R, N):
    """Q (q x N), sec (N x q): ker Q = colspace R, Q sec = I, sec standard vectors."""
    if R.ncols() == 0:
        return eye(N), eye(N), list(range(N))
    Y, _ = nullspace(R.transpose())  # columns y with y^T R = 0
    Qm = Y.transpose()
    if Qm.nrows() == 0:
        return F(0, N), F(N, 0), []
    _, piv = rref_rows(Qm)
    sec = select_rows(piv, N).transpose()
    Q = (Qm * sec).inv() * Qm
    return Q, sec, piv


def pdiag(ps):
    M = F(len(ps), len(ps))
    for i, p in enumerate(ps):
        M[i, i] = sgn(p)
    return M


def mpow(M, r):
    if r < 0:
        M = M.inv()
        r = -r
    out = eye(M.nrows())
    for _ in range(r):
        out = out * M
    return out


# ---------------------------------------------------------------- algebras
class AlgA:
    """Wrap a verified Cyclotomic quotient (or the zero algebra)."""

    def __init__(self, R, parity_of_colour, a):
        self.R = R
        self.a = a
        if R is None or R.dim == 0:
            self.dim = 0
            self.zero = True
            return
        self.zero = False
        self.dim = R.dim
        self.basis = R.basis
        self.ps = R.ps
        self.n = R.n
        self.words = R.words
        self.letters = list(R.L.keys())
        self.p = parity_of_colour
        self.one = R.one
        self.Ls = R.Ls
        self.cg = {g: R.L[g] * R.one for g in self.letters}
        # right multiplication by generators: column j = Ls[j] * cg
        self.Rg = {g: hstack([self.Ls[j] * self.cg[g] for j in range(self.dim)], self.dim)
                   for g in self.letters}

    def par(self, g, nu):
        if g[0] == "x":
            return self.p[nu[g[1]]]
        if g[0] == "t":
            return self.p[nu[g[1]]] * self.p[nu[g[1] + 1]]
        if g[0] == "d":
            return 1
        return 0

    def word(self, j):
        return self.R.word_of(self.basis[j])

    def left_word(self, j):
        return self.R.E.left_word(self.basis[j])


class AlgB:
    """Probe tower level from explicit matrices (rouq_sig_super_check)."""

    def __init__(self, mats, ps):
        self.mats, self.ps, self.dim = mats, ps, len(ps)
        s = mats[0].nrows()
        flat = F(s * s, self.dim, [mats[j][i // s, i % s] for i in range(s * s) for j in range(self.dim)])
        self.flat = flat
        self.size = s

        def coord(m):
            v = F(s * s, 1, [m[i // s, i % s] for i in range(s * s)])
            sol = solve_exact(flat, v)
            return sol

        self.coord = coord
        self.mul = [[coord(u * v) for v in mats] for u in mats]
        self.one = coord(eye(s))

    def rmul(self, j):
        """right multiplication by basis j: column i = coord(b_i b_j)."""
        return hstack([self.mul[i][j] for i in range(self.dim)], self.dim)

    def lmul(self, i):
        return hstack([self.mul[i][j] for j in range(self.dim)], self.dim)

    def elem_rmul(self, v):
        out = Z(self.dim, self.dim)
        for j in range(self.dim):
            if v[j, 0] != 0:
                out += v[j, 0] * self.rmul(j)
        return out


def solve_exact(A, b):
    """Unique solution of A x = b for full column rank A (exact)."""
    rows, piv = rref_rows(hstack([A, b], A.nrows()))
    n = A.ncols()
    assert n not in piv, "inconsistent"
    x = F(n, 1)
    for i, p in enumerate(piv):
        x[p, 0] = rows[i][n]
    return x


def probe_tower(odd):
    e00 = F(2, 2, [1, 0, 0, 0]); e11 = F(2, 2, [0, 0, 0, 1])
    e01 = F(2, 2, [0, 1, 0, 0]); e10 = F(2, 2, [0, 0, 1, 0])
    one1 = F(1, 1, [1])
    y = e01 + e10
    if odd:
        B = [AlgB([one1], [0]), AlgB([eye(2), y], [0, 1]), AlgB([e00, e11, e01, e10], [0, 0, 1, 1])]
        dots = {1: B[1].coord(e01 + e10), 2: B[2].coord(-1 * e01 + e10)}
    else:
        B = [AlgB([one1], [0]), AlgB([eye(2), y], [0, 0]), AlgB([e00, e11, e01, e10], [0] * 4)]
        dots = {1: B[1].coord(e01 + e10), 2: B[2].coord(-1 * (e01 + e10))}
    tau = B[2].coord(e01)

    def inc(b):  # B_b -> B_{b+1}
        if b == 0:
            return B[1].one
        return hstack([B[b + 1].coord(m) for m in B[b].mats], B[b + 1].dim)

    incs = {b: inc(b) for b in (0, 1)}
    e00c = B[2].coord(e00)
    return B, dots, tau, incs, e00c


# ---------------------------------------------------------------- modules
class Mod:
    def __init__(self, tw, idx, ps, gA, gB, name=""):
        self.tw, self.idx, self.ps, self.n = tw, idx, list(ps), len(ps)
        self.gA, self.gB, self.name = gA, gB, name
        self._rA = {}

    def rA_word(self, letters):
        key = tuple(letters)
        if key in self._rA:
            return self._rA[key]
        if not key:
            M = eye(self.n)
        else:
            M = self.gA[key[-1]] * self.rA_word(key[:-1])
        self._rA[key] = M
        return M

    def rA(self, j):
        A = self.tw.A(self.idx[0])
        return self.rA_word(A.word(j))

    def rAvec(self, v):
        A = self.tw.A(self.idx[0])
        out = Z(self.n, self.n)
        for j in range(A.dim):
            if v[j, 0] != 0:
                out += v[j, 0] * self.rA(j)
        return out

    def rB(self, j):
        return self.gB[j]

    def rBvec(self, v):
        out = Z(self.n, self.n)
        for j in range(v.nrows()):
            if v[j, 0] != 0:
                out += v[j, 0] * self.gB[j]
        return out

    def signed_gA(self, g, p):
        """sum_nu (-1)^{p |g e(nu)|} rho(e(nu)) rho(g)."""
        A = self.tw.A(self.idx[0])
        if not p:
            return self.gA[g]
        out = Z(self.n, self.n)
        for nu in A.words:
            out += sgn(A.par(g, nu)) * (self.gA[("e", nu)] * self.gA[g])
        return out


class Tower:
    def __init__(self, D, Lam, m, levels, odd_i, Bdata, twist="a", label=""):
        self.D, self.Lam, self.m = D, Lam, m
        self.odd = bool(odd_i)
        self.label = label
        self.twist = twist
        self.Bt, self.ydot, self.btau, self.binc, self.e00 = Bdata
        self._A = {}
        for a, R in levels.items():
            self._A[a] = AlgA(R, D.par, a)
        self.pres = {}
        self.cache = {}

    def A(self, a):
        if a not in self._A:
            return AlgA(None, self.D.par, a)
        return self._A[a]

    def B(self, b):
        return self.Bt[b] if 0 <= b <= 2 else None

    def s(self, a):
        if not self.odd:
            return 0
        return {"a": a, "a+1": a + 1, "0": 0, "nosign": a}[self.twist] % 2

    # ----- inclusion data A_a -> A_{a+s}
    def apply_iota_word(self, a, steps, letters, T):
        """iota^steps(g1...gk) T for T a matrix of columns in A_{a+steps}."""
        A2 = self.A(a + steps)
        for g in reversed(letters):
            if g[0] == "e":
                g2 = ("e", g[1] + (0,) * steps)
            else:
                g2 = g
            T = A2.R.L[g2] * T
        return T

    def presentation(self, a, steps):
        key = (a, steps)
        if key in self.pres:
            return self.pres[key]
        A, A2 = self.A(a), self.A(a + steps)
        assert not A.zero and not A2.zero
        # epsilon = iota^steps(1)
        eps = F(A2.dim, 1)
        for nu in A.words:
            eps += A2.R.L[("e", nu + (0,) * steps)] * A2.one
        cand = [j for j in range(A2.dim) if A2.left_word(j)[-steps:] == (0,) * steps]
        cand.sort(key=lambda j: (A2.R.E.degree(A2.basis[j]), len(A2.basis[j][1]), j))
        ts, cols = [], []
        span_rows, span_piv = [], []

        def in_span(v):
            v = [v[i, 0] for i in range(v.nrows())]
            for row, p in zip(span_rows, span_piv):
                if v[p] != 0:
                    c = v[p]
                    v = [x - c * y for x, y in zip(v, row)]
            return all(x == 0 for x in v)

        for j in cand:
            ej = F(A2.dim, 1)
            ej[j, 0] = 1
            if in_span(ej):
                continue
            ts.append(j)
            block = hstack([self.apply_iota_word(a, steps, A.word(al), ej) for al in range(A.dim)], A2.dim)
            cols.append(block)
            allc = hstack(cols, A2.dim)
            span_rows, span_piv = rref_rows(allc.transpose())
            if len(span_rows) == len(cand):
                break
        K = len(ts)
        Pi = hstack(cols, A2.dim)  # columns (k, alpha)
        assert len(span_rows) == len(cand), "presentation does not span"
        # section via pivot columns
        rowsP, pivc = rref_rows(Pi)
        Pp = hstack([col_of(Pi, c) for c in pivc], A2.dim)
        _, pivr = rref_rows(Pp.transpose())
        Sq = (select_rows(pivr, A2.dim) * Pp).inv()

        def section(y):
            c = Sq * (select_rows(pivr, A2.dim) * y)
            out = F(K * A.dim, 1)
            for i, cc in enumerate(pivc):
                out[cc, 0] = c[i, 0]
            assert Pi * out == y, "section"
            return out

        # kernel and left generators
        Nk, _ = nullspace(Pi)
        gens = []
        srows, spiv = [], []

        def leftmul(al, kv):
            return vstack([A.Ls[al] * sub(kv, k * A.dim, A.dim) for k in range(K)], 1)

        for c in range(Nk.ncols()):
            kv = col_of(Nk, c)
            v = [kv[i, 0] for i in range(kv.nrows())]
            for row, p in zip(srows, spiv):
                if v[p] != 0:
                    cc = v[p]
                    v = [x - cc * y for x, y in zip(v, row)]
            if all(x == 0 for x in v):
                continue
            gens.append(kv)
            allk = hstack([leftmul(al, g) for g in gens for al in range(A.dim)], K * A.dim)
            srows, spiv = rref_rows(allk.transpose())
            if len(srows) == Nk.ncols():
                break
        assert len(srows) == Nk.ncols(), "kernel generators"
        tpar = [A2.ps[j] for j in ts]
        tvec = []
        for j in ts:
            ej = F(A2.dim, 1)
            ej[j, 0] = 1
            tvec.append(ej)
        P = dict(K=K, ts=ts, tpar=tpar, tvec=tvec, section=section, kappa=gens, eps=eps, Pi=Pi)
        self.pres[key] = P
        return P

    # ----- modules
    def zero(self, idx):
        return Mod(self, idx, [], {}, {}, "zero")

    def exists(self, idx):
        a, b = idx
        return not self.A(a).zero and self.B(b) is not None

    def projective(self, idx, nu, half):
        """e(nu)A_a (x) e' B_b, e' = e00 when b = 2 and half."""
        a, b = idx
        A, B = self.A(a), self.B(b)
        rowsA = [j for j in range(A.dim) if A.left_word(j) == nu]
        if b == 2 and half:
            # e00 B_2 spanned by e00, e01 (basis 0 and 2)
            rowsB = [0, 2]
        else:
            rowsB = list(range(B.dim))
        idxs = [(i, j) for i in rowsA for j in rowsB]
        pos = {p: k for k, p in enumerate(idxs)}
        n = len(idxs)
        ps = [(A.ps[i] + B.ps[j]) % 2 for i, j in idxs]
        gA = {}
        for g in A.letters:
            M = F(n, n)
            for nu2 in A.words:
                Rg = A.Rg[("e", nu2)] * A.Rg[g]  # alpha -> alpha g e(nu2)
                par = A.par(g, nu2)
                L = Rg.tolist()
                for (i, j), k in pos.items():
                    s = sgn(B.ps[j] * par)
                    for i2 in rowsA:
                        if L[i2][i] != 0:
                            M[pos[(i2, j)], k] += s * L[i2][i]
            gA[g] = M
        gB = {}
        for jb in range(B.dim):
            Rb = B.rmul(jb).tolist()
            M = F(n, n)
            for (i, j), k in pos.items():
                for j2 in rowsB:
                    if Rb[j2][j] != 0:
                        M[pos[(i, j2)], k] += Rb[j2][j]
            gB[jb] = M
        return Mod(self, idx, ps, gA, gB, f"P{nu}")

    def check_module(self, M):
        """Right-module sanity on generators: idempotents sum to one."""
        A = self.A(M.idx[0])
        tot = Z(M.n, M.n)
        for nu in A.words:
            tot += M.gA[("e", nu)]
        assert tot == eye(M.n), "A unit"

    # restriction along A_{a-1} -> A_a
    def resA(self, M):
        a, b = M.idx
        idx = (a - 1, b)
        if not M.n or not self.exists(idx):
            return self.zero(idx)
        A0 = self.A(a - 1)
        Peps = Z(M.n, M.n)
        for nu in A0.words:
            Peps += M.gA[("e", nu + (0,))]
        H, piv = colspace(Peps)
        if not H.ncols():
            return self.zero(idx)
        ext = select_rows(piv, M.n)
        gA = {}
        for g in A0.letters:
            if g[0] == "e":
                gA[g] = ext * M.gA[("e", g[1] + (0,))] * H
            else:
                gA[g] = ext * Peps * M.gA[g] * H
        gB = {j: ext * M.gB[j] * H for j in M.gB}
        out = Mod(self, idx, [M.ps[p] for p in piv], gA, gB, "resA " + M.name)
        out.H, out.ext, out.base = H, ext, M
        return out

    def indA(self, M, steps=1):
        a, b = M.idx
        idx = (a + steps, b)
        if not M.n or not self.exists(idx):
            return self.zero(idx)
        P = self.presentation(a, steps)
        A, A2 = self.A(a), self.A(a + steps)
        K, n = P["K"], M.n
        N = K * n
        rel = []
        for kv in P["kappa"]:
            rel.append(vstack([M.rAvec(sub(kv, k * A.dim, A.dim)) for k in range(K)], n))
        R = hstack(rel, N)
        Q, sec, piv = quotient(R, N)
        psraw = [(P["tpar"][k] + M.ps[i]) % 2 for k in range(K) for i in range(n)]
        ps = [psraw[p] for p in piv]

        def leftop(yvec, signed):
            """(m_k) -> sum_k m_k (x) y t_k, optionally with (-1)^{|m|}."""
            rows = []
            for l in range(K):
                rows.append([None] * K)
            for k in range(K):
                c = P["section"](yvec(P["tvec"][k]))
                for l in range(K):
                    blk = M.rAvec(sub(c, l * A.dim, A.dim))
                    if signed:
                        blk = blk * pdiag(M.ps)
                    rows[l][k] = blk
            return blocks(rows, [n] * K, [n] * K)

        gA = {}
        for g in A2.letters:
            # (m_k) . g : t_k g = sum_l iota(c_lk) t_l
            rows = [[None] * K for _ in range(K)]
            for k in range(K):
                c = P["section"](A2.Rg[g] * P["tvec"][k])
                for l in range(K):
                    rows[l][k] = M.rAvec(sub(c, l * A.dim, A.dim))
            gA[g] = Q * blocks(rows, [n] * K, [n] * K) * sec
        Bm = self.B(b)
        gB = {}
        for j in range(Bm.dim):
            gB[j] = Q * bdiag([sgn(Bm.ps[j] * P["tpar"][k]) * M.gB[j] for k in range(K)]) * sec
        out = Mod(self, idx, ps, gA, gB, f"ind{steps} " + M.name)
        out.Q, out.sec, out.base, out.K, out.P, out.steps = Q, sec, M, K, P, steps
        out.leftop = lambda yvec, signed: Q * leftop(yvec, signed) * sec
        return out

    # B sector
    def resB(self, M):
        a, b = M.idx
        idx = (a, b - 1)
        if not M.n or not self.exists(idx):
            return self.zero(idx)
        Bs = self.B(b - 1)
        inc = self.binc[b - 1]
        gB = {j: M.rBvec(col_of(inc, j)) for j in range(Bs.dim)}
        sh = self.s(a)
        out = Mod(self, idx, [(p + sh) % 2 for p in M.ps], dict(M.gA), gB, "resB " + M.name)
        out.base = M
        return out

    def coindB(self, M):
        """Pi^{s(a)} applied first, then Hom_{C(a,b)}(C(a,b+1), -)."""
        a, b = M.idx
        idx = (a, b + 1)
        if not M.n or not self.exists(idx):
            return self.zero(idx)
        sh = self.s(a)
        mps = [(p + sh) % 2 for p in M.ps]
        Bs, Bt = self.B(b), self.B(b + 1)
        inc = self.binc[b]
        n, r = M.n, Bt.dim
        eqs = []
        for g in range(r):
            for beta in range(Bs.dim):
                # phi_{g . iota(beta)} - phi_g . beta = 0
                prod = Bt.elem_rmul(col_of(inc, beta)) * col_of(eye(r), g)
                row = []
                for d in range(r):
                    blk = prod[d, 0] * eye(n)
                    if d == g:
                        blk = blk - M.gB[beta]
                    row.append(blk)
                eqs.append(hstack(row, n))
        E = vstack(eqs, r * n)
        H, free = nullspace(E)
        psraw = [(Bt.ps[g] + mps[i]) % 2 for g in range(r) for i in range(n)]
        ps = [psraw[f] for f in free]
        ext = select_rows(free, r * n)
        A = self.A(a)
        gA = {}
        for g in A.letters:
            gA[g] = ext * bdiag([M.signed_gA(g, Bt.ps[d]) for d in range(r)]) * H
        gB = {}
        for j in range(r):
            Lj = Bt.lmul(j)  # gamma -> b_j gamma
            rows = [[Lj[d, g] * eye(n) if Lj[d, g] != 0 else None for d in range(r)] for g in range(r)]
            # (phi.b_j)_g = phi(b_j g) = sum_d Lj[d,g] phi_d
            gB[j] = ext * blocks(rows, [n] * r, [n] * r) * H
        out = Mod(self, idx, ps, gA, gB, "coindB " + M.name)
        out.H, out.ext, out.base, out.r = H, ext, M, r
        return out


def col_of(M, j):
    out = F(M.nrows(), 1)
    for i in range(M.nrows()):
        out[i, 0] = M[i, j]
    return out


def sub(v, start, length):
    out = F(length, 1)
    for i in range(length):
        out[i, 0] = v[start + i, 0]
    return out


# ---------------------------------------------------------------- 2-representation
class Rep:
    def __init__(self, tw: Tower):
        self.tw = tw
        self.odd = tw.odd
        self._E, self._F = {}, {}

    def E(self, v, t):
        k = (id(v), t)
        if k not in self._E:
            self._E[k] = (v, self.tw.indA(v) if t == 0 else self.tw.resB(v))
        return self._E[k][1]

    def F(self, v, t):
        k = (id(v), t)
        if k not in self._F:
            self._F[k] = (v, self.tw.resA(v) if t == 0 else self.tw.coindB(v))
        return self._F[k][1]

    def Em(self, f, v, w, t, p=0):
        e1, e2 = self.E(v, t), self.E(w, t)
        if not e1.n or not e2.n:
            return Z(e2.n, e1.n)
        if t == 0:
            K = e1.K
            return e2.Q * bdiag([f] * K) * e1.sec
        if not self.odd:
            return f
        return sgn(self.tw.s(v.idx[0]) * p) * f

    def Fm(self, f, v, w, t, p=0):
        f1, f2 = self.F(v, t), self.F(w, t)
        if not f1.n or not f2.n:
            return Z(f2.n, f1.n)
        if t == 0:
            return f2.ext * f * f1.H
        s = sgn(self.tw.s(v.idx[0]) * p) if self.odd else 1
        return s * f2.ext * bdiag([f] * f1.r) * f1.H

    def unit(self, v, t):
        e = self.E(v, t)
        if not e.n:
            return Z(0, v.n)
        fe = self.F(e, t)
        if t == 0:
            P = e.P
            A = self.tw.A(v.idx[0])
            c = P["section"](P["eps"])
            raw = vstack([v.rAvec(sub(c, k * A.dim, A.dim)) for k in range(P["K"])], v.n)
            return fe.ext * (e.Q * raw)
        Bt = self.tw.B(v.idx[1])
        raw = vstack([v.gB[g] for g in range(Bt.dim)], v.n)
        return fe.ext * raw

    def counit(self, v, t):
        f = self.F(v, t)
        if not f.n:
            return Z(v.n, 0)
        ef = self.E(f, t)
        if t == 0:
            P = ef.P
            cols = [v.rAvec(P["tvec"][k]) * f.H for k in range(P["K"])]
            return hstack(cols, v.n) * ef.sec
        Bt = self.tw.B(v.idx[1] + 1)
        one = Bt.one
        return hstack([one[g, 0] * eye(v.n) for g in range(Bt.dim)], v.n) * f.H

    def dot(self, v, t):
        e = self.E(v, t)
        if not e.n:
            return Z(0, 0)
        a, b = v.idx
        if t == 0:
            A2 = self.tw.A(a + 1)
            g = ("x", A2.n - 1)
            return e.leftop(lambda T: A2.R.L[g] * T, self.odd)
        y = self.tw.ydot[b]
        act = v.rBvec(y)
        if not self.odd:
            return act
        sh = self.tw.s(a) if self.tw.twist != "nosign" else 0
        return sgn(sh) * act * pdiag(v.ps)

    def collapse(self, v):
        e = self.E(v, 0)
        ee = self.E(e, 0)
        direct = self.tw.indA(v, 2)
        P1, P2, Pd = e.P, ee.P, direct.P
        A, A1, A2 = self.tw.A(v.idx[0]), self.tw.A(v.idx[0] + 1), self.tw.A(v.idx[0] + 2)
        n, K1, K2, Kd = v.n, P1["K"], P2["K"], Pd["K"]
        # ee coords -> (e)^{K2} -> (v^{K1})^{K2} -> v^{Kd}
        S1 = bdiag([e.sec] * K2) * ee.sec
        rows = [[None] * (K2 * K1) for _ in range(Kd)]
        for l in range(K2):
            for k in range(K1):
                # iota(t_k) t'_l in A2
                tk = A1.basis[P1["ts"][k]]
                prod = self.tw.apply_iota_word(v.idx[0] + 1, 1, A1.word(P1["ts"][k]), P2["tvec"][l])
                c = Pd["section"](prod)
                for j in range(Kd):
                    rows[j][l * K1 + k] = v.rAvec(sub(c, j * A.dim, A.dim))
        G = blocks(rows, [n] * Kd, [n] * (K2 * K1))
        Kmat = direct.Q * G * S1
        assert Kmat.nrows() == Kmat.ncols() and Kmat.det() != 0, "collapse"
        return Kmat, direct

    def mixedJ(self, v):
        b = self.E(v, 1)
        ab = self.E(b, 0)
        a = self.E(v, 0)
        ba = self.E(a, 1)
        J = a.Q * ab.sec
        assert J.nrows() == J.ncols() and J.det() != 0, "mixed J"
        return J

    def T(self, v, p, q, s, r):
        key = (id(v), p, q, s, r)
        if not hasattr(self, "_Tc"):
            self._Tc = {}
        if key in self._Tc:
            return self._Tc[key][1]
        src = self.E(self.E(v, q), p)
        tar = self.E(self.E(v, r), s)
        if not src.n or not tar.n:
            out = Z(tar.n, src.n)
        elif p == q == s == r == 0:
            Kmat, direct = self.collapse(v)
            A2 = self.tw.A(v.idx[0] + 2)
            g = ("t", A2.n - 2)
            raw = direct.leftop(lambda T: A2.R.L[g] * T, self.odd)
            out = Kmat.inv() * raw * Kmat
        elif p == q == s == r == 1:
            act = v.rBvec(self.tw.btau)
            out = (-1 * act * pdiag(v.ps)) if self.odd else act
        else:
            J = self.mixedJ(v)
            b = self.E(v, 1)
            X = self.dot(b, 0)
            Y = self.Em(self.dot(v, 1), b, b, 0, 1)
            if self.odd:
                Dm = X * X - Y * Y
                Di = Dm.inv()
                aa = (X - Y) * Di
                qq = (X * X + Y * Y) * Di * Di
                out = {(0, 1, 0, 1): aa, (0, 1, 1, 0): J, (1, 0, 0, 1): -1 * qq * J.inv(),
                       (1, 0, 1, 0): -1 * J * aa * J.inv()}[p, q, s, r]
            else:
                aa = (X - Y).inv()
                out = {(0, 1, 0, 1): aa, (0, 1, 1, 0): J, (1, 0, 0, 1): -1 * aa * aa * J.inv(),
                       (1, 0, 1, 0): -1 * J * aa * J.inv()}[p, q, s, r]
        if self.odd and src.n and tar.n:
            assert pdiag(tar.ps) * out == -1 * out * pdiag(src.ps), ("crossing parity", p, q, s, r)
        self._Tc[key] = (v, out)
        return out

    def mate(self, v, p, q, s, r):
        fr = self.F(v, r)
        src = self.E(fr, q)
        tar = self.F(self.E(v, s), p)
        ep = self.E(src, p)
        etarget = self.E(self.E(fr, r), s)
        if not ep.n or not etarget.n or not src.n or not tar.n:
            return Z(tar.n, src.n)
        cup = self.unit(src, p)
        cross = self.Fm(self.T(fr, p, q, s, r), ep, etarget, p, int(self.odd))
        counit = self.Em(self.counit(v, r), self.E(fr, r), v, s)
        finish = self.Fm(counit, etarget, self.E(v, s), p)
        return finish * cross * cup


def nil_index(M, cap=64):
    if M.nrows() == 0:
        return 0
    P = eye(M.nrows())
    for k in range(1, cap + 1):
        P = P * M
        if iszero(P):
            return k
    return None


def check(rep: Rep, v, hA, hB, log):
    tw = rep.tw
    q = -1 if rep.odd else 1
    E, Fn = rep.E, rep.F
    branches = [(a, b) for a in (0, 1) for b in (0, 1)]
    src = [E(Fn(v, r), s) for s, r in branches]
    tar = [Fn(E(v, s), r) for r, s in branches]
    for t in (0, 1):
        e, f = E(v, t), Fn(v, t)
        if e.n:
            assert rep.counit(e, t) * rep.Em(rep.unit(v, t), v, Fn(e, t), t) == eye(e.n), "triangle E"
        if f.n:
            assert rep.Fm(rep.counit(v, t), E(f, t), v, t) * rep.unit(f, t) == eye(f.n), "triangle F"
    for r in (0, 1):
        n = Fn(v, r)
        for words in ([(0, 1), (1, 0)], [(r, r)]):
            mods = [E(E(n, b), a) for a, b in words]
            if not all(m.n for m in mods):
                continue
            X = bdiag([rep.dot(E(n, b), a) for a, b in words])
            Y = bdiag([rep.Em(rep.dot(n, b), E(n, b), E(n, b), a, int(rep.odd)) for a, b in words])
            dims = [m.n for m in mods]
            T = blocks([[rep.T(n, a, b, c, d) for a, b in words] for c, d in words], dims, dims)
            I_ = eye(X.nrows())
            assert X * Y == q * Y * X, ("dots supercommute", words)
            assert T * X - q * Y * T == I_, ("slide 1", words)
            assert X * T - q * T * Y == I_, ("slide 2", words)
            assert iszero(T * T), ("crossing square", words)
    bl = []
    for j, (p, s) in enumerate(branches):
        row = []
        for k, (a, b) in enumerate(branches):
            if sorted((p, a)) == sorted((s, b)):
                row.append(rep.mate(v, p, a, s, b))
            else:
                row.append(Z(tar[j].n, src[k].n))
        bl.append(row)
    tdims = [m.n for m in tar]
    sdims = [m.n for m in src]
    raw = blocks(bl, tdims, sdims)
    sig = -q * raw

    def u(t, r):
        e = E(v, t)
        if not e.n:
            return Z(0, v.n)
        return rep.Fm(mpow(rep.dot(v, t), r), e, e, t, (r * int(rep.odd)) % 2) * rep.unit(v, t)

    def cap(t, r):
        f = Fn(v, t)
        if not f.n:
            return Z(v.n, 0)
        return rep.counit(v, t) * mpow(rep.dot(f, t), r)

    n1 = nil_index(rep.dot(v, 0)) if E(v, 0).n else 0
    n2 = nil_index(rep.dot(Fn(v, 0), 0)) if src[0].n else 0
    assert n1 is not None and n2 is not None, "reservoir dot not nilpotent"
    bound = max(n1, n2, 1)
    C = -q * bl[0][3]
    Dm = -q * bl[3][0]
    cp = Z(C.nrows(), C.ncols())
    dp = Z(Dm.nrows(), Dm.ncols())
    for r in range(bound):
        if E(v, 0).n and Fn(v, 1).n:
            cp += q ** r * (u(0, r) * cap(1, -r - 1))
        if E(v, 1).n and Fn(v, 0).n:
            dp += -(q ** (r + 1)) * (u(1, -r - 1) * cap(0, r))
    okC, okD = C == cp, Dm == dp
    assert okC and okD, f"ordered expansion C={okC} D={okD}"
    h = hA + hB
    if h > 0:
        rows = [hstack([cap(a, r) if a == b else Z(v.n, nn.n) for (a, b), nn in zip(branches, src)], v.n)
                for r in range(h)]
        total = vstack([sig] + rows, sig.ncols())
    elif h < 0:
        cols = [vstack([u(a, r) if a == b else Z(nn.n, v.n) for (a, b), nn in zip(branches, tar)], v.n)
                for r in range(-h)]
        total = hstack([sig] + cols, sig.nrows())
    else:
        total = sig
    assert total.nrows() == total.ncols(), ("height dimension", total.nrows(), total.ncols(), h)
    if total.nrows():
        assert total.det() != 0, "total map singular"
        inv = total.inv()
        assert total * inv == eye(total.nrows()) and inv * total == eye(total.nrows())

    def common_inverse(t, height):
        s_ = -q * bl[3 * t][3 * t]
        if height > 0:
            fac = vstack([s_] + [cap(t, r) for r in range(height)], s_.ncols())
            return sub_cols(fac.inv(), s_.nrows()) if fac.nrows() else fac
        if height < 0:
            fac = hstack([s_] + [u(t, r) for r in range(-height)], s_.nrows())
            return sub_rows(fac.inv(), s_.ncols()) if fac.nrows() else fac
        return s_.inv() if s_.nrows() else s_

    rA = common_inverse(0, hA)
    rB = common_inverse(1, hB)
    fb = Dm * rA * C * rB if Dm.nrows() else Z(0, 0)
    ni = nil_index(fb, cap=max(1, fb.nrows())) if fb.nrows() else 0
    assert ni is not None, "feedback not nilpotent"
    rk = fb.rank() if fb.nrows() else 0
    log(f"PASS [{tw.label}] content={v.idx} module={v.name} heights={(hA, hB, h)} "
        f"total={total.nrows()} dims EF={sdims} FE={tdims} dot-nil={bound} "
        f"C,D=ordered expansions; inverse two-sided; feedback rank={rk} nil={ni}")
    return True


def sub_cols(M, k):
    return F(M.nrows(), k, [M[i, j] for i in range(M.nrows()) for j in range(k)])


def sub_rows(M, k):
    return F(k, M.ncols(), [M[i, j] for i in range(k) for j in range(M.ncols())])


# ---------------------------------------------------------------- data
CARTAN = [[2, -2], [-4, 2]]
DEGX = (4, 2)  # (alpha_i|alpha_i) = 4, (alpha_j|alpha_j) = 2, (alpha_i|alpha_j) = -4
Q_TRUE = {(2, 0): 1, (0, 4): -1}  # Q_ij(x, y) = x^2 - y^4


def datum(case, par, mut=frozenset(), Q=None):
    """case 'beside': Lambda = Lambda_i + Lambda_j, content a i + j, f_i = x (+delta_i if i odd),
    f_j = y (+delta_j if j odd and i even);  case 'twoj': Lambda = Lambda_j, content a i + 2 j, f_j = y."""
    Q = Q_TRUE if Q is None else Q
    pi, pj = par
    if case == "beside":
        deltas, fi, fj = [], [(1, 1, ())], [(1, 1, ())]
        if pi:
            deltas.append(DEGX[0])
            fi = [(1, 1, ()), (1, 0, (len(deltas) - 1,))]
        elif pj:
            deltas.append(DEGX[1])
            fj = [(1, 1, ()), (1, 0, (len(deltas) - 1,))]
        D = KLR(par, CARTAN, Q, DEGX, {0: fi, 1: fj}, deltas, mut=mut, name=f"beside{par}")
        return D, (1, 1), 1, [0, 1, 2, 3, 4]
    if case == "twoj":
        D = KLR(par, CARTAN, Q, DEGX, {0: [], 1: [(1, 1, ())]}, [], mut=mut, name=f"twoj{par}")
        return D, (0, 1), 2, [0, 1, 2, 3, 4]
    raise ValueError(case)


def Cyclotomic_formula(D, Lam, content):
    from klr_cyclotomic import bk_dim, words_of
    W = words_of(content)
    return sum(bk_dim(D, Lam, u, v) for u in W for v in W) * 2 ** len(D.deltas)


def build_levels(D, Lam, m, alist, log):
    levels, report = {}, []
    for a in alist:
        t0 = time.time()
        if Cyclotomic_formula(D, Lam, (a, m)) == 0:
            log(f"  level a={a}: formula dimension 0 (zero algebra; not built)")
            continue
        R = build(D, Lam, (a, m), cap0=8, step=4, capmax=40, verbose=False)
        tot, _ = R.expected()
        err = R.verify() if R.dim else (None if tot == 0 else f"dimension 0 != formula {tot}")
        log(f"  level a={a}: dim {R.dim} (formula x 2^#delta: {tot}) cap={R.cap} "
            f"verify={'OK' if err is None else err} assoc={getattr(R, 'assoc_mode', '-')} "
            f"[{time.time() - t0:.1f}s]")
        if err is not None:
            report.append((a, err))
        if R.dim:
            levels[a] = R
    return levels, report


def run_case(case, par, contents, mut=frozenset(), twist="a", Q=None, log=print, half=True, levels=None):
    D, Lam, m, alist = datum(case, par, mut, Q)
    label = f"{case} par={par} mut={sorted(mut)} twist={twist}" + (" Q=" + str(Q) if Q else "")
    log(f"== {label}")
    if levels is None:
        need = sorted({x for a, _ in contents for x in (a - 1, a, a + 1) if x in alist})
        levels, bad = build_levels(D, Lam, m, need, log)
        if bad:
            log(f"FAIL-ALGEBRA [{label}] {bad}")
            return False, levels
    tw = Tower(D, Lam, m, levels, par[0], probe_tower(par[0]), twist=twist, label=label)
    ok = True
    for a, b in contents:
        if a not in levels:
            continue
        A = tw.A(a)
        hA = 2 * a - Lam[0] - 2 * m
        hB = 2 - 2 * b
        for nu in A.words:
            if not any(A.left_word(j) == nu for j in range(A.dim)):
                continue
            rep = Rep(tw)
            v = tw.projective((a, b), nu, half)
            t0 = time.time()
            try:
                check(rep, v, hA, hB, log)
            except AssertionError as e:
                ok = False
                log(f"FAIL [{label}] content={(a, b)} module=P{nu}: {e}")
            except (ZeroDivisionError, ValueError) as e:
                ok = False
                log(f"FAIL [{label}] content={(a, b)} module=P{nu}: {type(e).__name__} {e}")
            log(f"     [{time.time() - t0:.1f}s]")
    return ok, levels


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", default="beside")
    ap.add_argument("--par", default="11")
    ap.add_argument("--contents", default="")
    ap.add_argument("--mut", default="")
    ap.add_argument("--twist", default="a")
    ap.add_argument("--Qsym", action="store_true", help="legitimate datum Q = x^2 + y^4")
    args = ap.parse_args()
    par = (int(args.par[0]), int(args.par[1]))
    contents = [tuple(int(c) for c in x.split(",")) for x in args.contents.split(";") if x]
    mut = frozenset(x for x in args.mut.split(",") if x)
    Q = {(2, 0): 1, (0, 4): 1} if args.Qsym else None

    def log(s):
        print(s, flush=True)

    ok, _ = run_case(args.case, par, contents, mut, args.twist, Q, log)
    print("RESULT", "PASS" if ok else "FAIL", flush=True)


if __name__ == "__main__":
    main()
