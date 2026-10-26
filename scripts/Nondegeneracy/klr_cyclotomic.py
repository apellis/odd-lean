# /// script
# requires-python = ">=3.10"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Exact two-colour cyclotomic quiver Hecke superalgebras from the KKO presentation.

R(beta) is presented by e(nu), x_k, tau_a with the KKO relations (R1)-(R8)
(Kang-Kashiwara-Oh, Supercategorification I, Def. 4.1) over Q adjoined odd
supercommuting coefficients delta_s (exterior, degree given).  Normal forms are
tau_{c(w)} x^a delta^S e(nu), with c(w) the canonical reduced word obtained by
repeatedly taking the smallest left descent.  Products are computed by
rewriting with the defining relations only (no polynomial representation).

The cyclotomic quotient R^Lambda(beta) = R/(R a^Lambda(x_1) R) is computed
exactly as follows.  Out = span of normal monomials whose polynomial part
x^a delta^S has degree > cap is a left ideal (left multiplication never lowers
the polynomial part).  If cap is at least the top degree of R^Lambda, Out lies
in the cyclotomic ideal J, and J/Out is the left closure of {a^Lambda m :
m in Box}.  A too small cap only produces a smaller quotient; we raise cap
until the quotient dimension equals the Brundan-Kleshchev/Kang-Kashiwara
dimension formula (times 2^#delta), and then verify exactly:
  * block dimensions dim e(mu) R^Lambda e(nu) against the formula;
  * every defining relation (R1)-(R8) and a^Lambda(x_1)=0 on the left regular
    representation;
  * associativity: L_g L_b = L_{g b} for every generator g and basis element b
    (with L_b the product of generator matrices along b's word), and
    L_b(1) = b.
Mutations (presentation errors) are switched on by flags.
"""
from __future__ import annotations

import itertools
from collections import deque
from fractions import Fraction
from functools import lru_cache

import flint


def fq(c):
    c = Fraction(c)
    return flint.fmpq(c.numerator, c.denominator)


def sgn(p):
    return -1 if p % 2 else 1


class KLR:
    """Two colours 0 (=i) and 1 (=j)."""

    def __init__(self, par, cartan, Q01, degx, cyc, deltas, mut=frozenset(), name=""):
        self.par = par
        self.cartan = cartan
        self.Q01 = dict(Q01)
        self.degx = degx
        self.cyc = cyc  # colour -> list of (coef, xpow, tuple of delta indices); [] means f=1
        self.deltas = deltas  # list of degrees
        self.mut = frozenset(mut)
        self.name = name
        self._cache = {}

    # ---------- basic data
    def Q(self, c, d):
        if c == d:
            return {}
        if (c, d) == (0, 1):
            q = dict(self.Q01)
        else:
            q = {(s, r): t for (r, s), t in self.Q01.items()}
            if "Qasym" in self.mut:
                # flip the sign of one coefficient in one orientation only
                k = max(q)
                q[k] = -q[k]
        return q

    def p(self, c):
        return self.par[c]


@lru_cache(None)
def perm_of(word, n):
    """Tuple p with (s_{w0}...s_{wL-1} nu)[k] = nu[p[k]]."""
    p = list(range(n))
    for a in reversed(word):
        pass
    # apply rightmost first: start with identity for nu, each s_a on the left
    p = list(range(n))
    for a in reversed(word):
        # new word = s_a(old): new[k] = old[s_a(k)] -> p'[k] = p[s_a(k)]
        p[a], p[a + 1] = p[a + 1], p[a]
    return tuple(p)


def act(p, nu):
    return tuple(nu[p[k]] for k in range(len(nu)))


@lru_cache(None)
def canon(p):
    p = list(p)
    out = []
    while True:
        d = [a for a in range(len(p) - 1) if p[a] > p[a + 1]]
        if not d:
            return tuple(out)
        b = d[0]
        out.append(b)
        p[b], p[b + 1] = p[b + 1], p[b]


@lru_cache(None)
def path_to_start(word, b):
    """Braid/commutation moves taking reduced word to one starting with b."""
    if word and word[0] == b:
        return ()
    seen = {word: None}
    dq = deque([word])
    while dq:
        u = dq.popleft()
        if u[0] == b:
            moves = []
            while seen[u] is not None:
                prev, mv = seen[u]
                moves.append(mv)
                u = prev
            return tuple(reversed(moves))
        for i in range(len(u) - 1):
            if abs(u[i] - u[i + 1]) > 1:
                v = u[:i] + (u[i + 1], u[i]) + u[i + 2:]
                if v not in seen:
                    seen[v] = (u, ("c", i))
                    dq.append(v)
            if i + 2 < len(u) and u[i] == u[i + 2] and abs(u[i] - u[i + 1]) == 1:
                v = u[:i] + (u[i + 1], u[i], u[i + 1]) + u[i + 3:]
                if v not in seen:
                    seen[v] = (u, ("b", i))
                    dq.append(v)
    raise ValueError("no path", word, b)


class Engine:
    """Rewriting in R(beta) tensor Lambda(delta) for a fixed number n of strands."""

    def __init__(self, D: KLR, n):
        self.D, self.n = D, n
        self.memo = {}
        self.tnf = {}

    def addto(self, out, vec, c):
        for k, v in vec.items():
            w = out.get(k, 0) + c * v
            if w:
                out[k] = w
            else:
                out.pop(k, None)

    def parity(self, key):
        nu, w, a, S = key
        p = len(S)
        D = self.D
        cur = nu
        for b in reversed(w):
            p += D.p(cur[b]) * D.p(cur[b + 1])
            cur = cur[:b] + (cur[b + 1], cur[b]) + cur[b + 2:]
        p += sum(a[k] * D.p(nu[k]) for k in range(self.n))
        return p % 2

    def left_word(self, key):
        nu, w, a, S = key
        return act(perm_of(w, self.n), nu)

    def polydeg(self, key):
        nu, w, a, S = key
        D = self.D
        return sum(a[k] * D.degx[nu[k]] for k in range(self.n)) + sum(D.deltas[s] for s in S)

    def degree(self, key):
        nu, w, a, S = key
        D = self.D
        d = self.polydeg(key)
        cur = nu
        for b in reversed(w):
            c, e = cur[b], cur[b + 1]
            d += -self.ip(c, e)
            cur = cur[:b] + (e, c) + cur[b + 2:]
        return d

    def ip(self, c, e):
        # (alpha_c|alpha_e) = d_c a_ce with d_c = degx[c]/2
        return self.D.degx[c] // 2 * self.D.cartan[c][e]

    # ---------- elementary multiplications
    def lmul_word(self, letters, vec):
        for g in reversed(letters):
            new = {}
            for k, c in vec.items():
                self.addto(new, self.lmul(g, k), c)
            vec = new
        return vec

    def lmul(self, g, key):
        mk = (g, key)
        r = self.memo.get(mk)
        if r is None:
            if g[0] == "d":
                r = self._lmul_d(g[1], key)
            elif g[0] == "x":
                r = self._lmul_x(g[1], key)
            elif g[0] == "t":
                r = self._lmul_t(g[1], key)
            elif g[0] == "e":
                r = {key: 1} if self.left_word(key) == g[1] else {}
            else:
                raise ValueError(g)
            self.memo[mk] = r
        return r

    def _lmul_d(self, s, key):
        nu, w, a, S = key
        if s in S:
            return {}
        sign = sgn(self.parity((nu, w, a, ())) + sum(1 for t in S if t < s))
        return {(nu, w, a, tuple(sorted(S + (s,)))): sign}

    def _lmul_x(self, k, key):
        nu, w, a, S = key
        D = self.D
        if not w:
            # x_k x^a delta^S: delta's to the right; sort x_k into position k
            sign = sgn(sum(D.p(nu[k]) * D.p(nu[l]) * a[l] for l in range(k)))
            a2 = list(a)
            a2[k] += 1
            return {(nu, w, tuple(a2), S): sign}
        a0 = w[0]
        rest = (nu, w[1:], a, S)
        mu = self.left_word(rest)
        pa, pb = D.p(mu[a0]), D.p(mu[a0 + 1])
        out = {}
        if k not in (a0, a0 + 1):
            sign = sgn(D.p(mu[k]) * pa * pb)
            for kk, c in self.lmul(("x", k), rest).items():
                self.addto(out, self.lmul(("t", a0), kk), sign * c)
            return out
        sg = self.r5sign(mu[a0], mu[a0 + 1])
        eq = 1 if mu[a0] == mu[a0 + 1] else 0
        if k == a0 + 1:
            for kk, c in self.lmul(("x", a0), rest).items():
                self.addto(out, self.lmul(("t", a0), kk), sg * c)
            if eq:
                self.addto(out, {rest: 1}, 1)
        else:
            for kk, c in self.lmul(("x", a0 + 1), rest).items():
                self.addto(out, self.lmul(("t", a0), kk), sg * c)
            if eq:
                self.addto(out, {rest: 1}, -sg)
        return out

    def r5sign(self, c, d):
        D = self.D
        sg = sgn(D.p(c) * D.p(d))
        if "R5mixed" in D.mut and c != d:
            sg = 1
        if "R5same" in D.mut and c == d:
            sg = 1
        return sg

    def xpoly(self, terms, vec):
        """Apply sum coef * (letters) to vec, letters a list of x-letters (leftmost first)."""
        out = {}
        for coef, letters in terms:
            self.addto(out, self.lmul_word([("x", k) for k in letters], dict(vec)), coef)
        return out

    def quad(self, b, mu):
        q = self.D.Q(mu[b], mu[b + 1])
        return [(t, [b] * r + [b + 1] * s) for (r, s), t in q.items()]

    def braid_corr(self, a, mu):
        """R(mu) for (tau_{a+1}tau_a tau_{a+1}-tau_a tau_{a+1}tau_a)e(mu)."""
        D = self.D
        c, d = mu[a], mu[a + 2]
        if c != d or mu[a + 1] == c:
            return []
        q = D.Q(c, mu[a + 1])
        terms = []
        if D.p(c) == 0:
            for (r, s), t in q.items():
                for k in range(r):
                    terms.append((t, [a + 2] * k + [a] * (r - 1 - k) + [a + 1] * s))
        else:
            sign = sgn(D.p(mu[a + 1]))
            if "braidsign" in D.mut:
                sign = -sign
            for (r, s), t in q.items():
                assert r % 2 == 0
                m = r // 2
                for k in range(m):
                    body = [a + 2] * (2 * k) + [a] * (2 * (m - 1 - k)) + [a + 1] * s
                    terms.append((sign * t, [a + 2] + body))
                    terms.append((-sign * t, [a] + body))
        return terms

    def to_nf(self, word, tail):
        """Normal form of tau_word x^a delta^S e(nu) for a REDUCED word."""
        mk = (word, tail)
        r = self.tnf.get(mk)
        if r is not None:
            return r
        n = self.n
        nu, a, S = tail
        p = perm_of(word, n)
        c = canon(p)
        if word == c:
            r = {(nu, word, a, S): 1}
            self.tnf[mk] = r
            return r
        b = c[0]
        out = {}
        coef, word2 = self.transform(word, b, tail, out)
        # word2 starts with b and [b]+canon(rest) = canon(p)
        for kk, cc in self.to_nf(word2[1:], tail).items():
            self.addto(out, self.lmul(("t", b), kk), coef * cc)
        self.tnf[mk] = out
        return out

    def transform(self, word, b, tail, out):
        """tau_word T = coef * tau_word2 T + (corrections added to out); word2 starts with b."""
        D = self.D
        n = self.n
        nu, a, S = tail
        coef = 1
        for kind, i in path_to_start(word, b):
            mu = act(perm_of(word[i + (2 if kind == "c" else 3):], n), nu)
            if kind == "c":
                x, y = word[i], word[i + 1]
                coef *= sgn(D.p(mu[x]) * D.p(mu[x + 1]) * D.p(mu[y]) * D.p(mu[y + 1]))
                word = word[:i] + (y, x) + word[i + 2:]
            else:
                lo = min(word[i], word[i + 1])
                # word[i:i+3] is (lo+1,lo,lo+1) -> (lo,lo+1,lo) + R, or reverse with -R
                s = 1 if word[i] == lo + 1 else -1
                R = self.braid_corr(lo, mu)
                if R:
                    suffix = self.to_nf(word[i + 3:], tail)
                    vec = self.xpoly(R, suffix)
                    vec = self.lmul_word([("t", t) for t in word[:i]], vec)
                    self.addto(out, vec, coef * s)
                word = word[:i] + (word[i + 1], word[i], word[i + 1]) + word[i + 3:]
        return coef, word

    def _lmul_t(self, b, key):
        nu, w, a, S = key
        n = self.n
        p = perm_of(w, n)
        tail = (nu, a, S)
        if p[b] > p[b + 1]:
            out = {}
            coef, w2 = self.transform(w, b, tail, out)
            # tau_b out-corrections
            corr = out
            out = {}
            for kk, cc in corr.items():
                self.addto(out, self.lmul(("t", b), kk), cc)
            rest = w2[1:]
            mu = act(perm_of(rest, n), nu)
            restnf = self.to_nf(rest, tail)
            self.addto(out, self.xpoly(self.quad(b, mu), restnf), coef)
            return out
        return self.to_nf((b,) + w, tail)


def words_of(content):
    a, m = content
    return sorted(set(itertools.permutations([0] * a + [1] * m)))


def bk_dim(D, Lam, nu2, nu):
    n = len(nu)
    tot = 0
    for w in itertools.permutations(range(n)):
        wn = [None] * n
        for k in range(n):
            wn[w[k]] = nu[k]
        if tuple(wn) != tuple(nu2):
            continue
        prod = 1
        for m in range(n):
            N = Lam[nu[m]] - sum(D.cartan[nu[m]][nu[k]] for k in range(m) if w[k] < w[m])
            prod *= N
            if prod == 0:
                break
        tot += prod
    return tot


def monomials(n, degs, cap):
    out = []

    def rec(k, cur, d):
        if k == n:
            out.append(tuple(cur))
            return
        e = 0
        while d + e * degs[k] <= cap:
            rec(k + 1, cur + [e], d + e * degs[k])
            e += 1

    rec(0, [], 0)
    return out


class Cyclotomic:
    """Exact R^Lambda(content) with verified basis and left-regular matrices."""

    full_assoc_dim = 260

    def __init__(self, D: KLR, Lam, content, cap, verbose=False):
        self.D, self.Lam, self.content = D, Lam, content
        a_, m_ = content
        n = a_ + m_
        self.n = n
        self.E = E = Engine(D, n)
        self.words = words_of(content)
        nd = len(D.deltas)
        subsets = [S for r in range(nd + 1) for S in itertools.combinations(range(nd), r)]
        self.cap = cap
        # Box per right word nu
        box = {}
        for nu in self.words:
            degs = [D.degx[c] for c in nu]
            ms = monomials(n, degs, cap)
            keys = []
            for p in itertools.permutations(range(n)):
                w = canon(p)
                for a in ms:
                    for S in subsets:
                        k = (nu, w, a, S)
                        if E.polydeg(k) <= cap:
                            keys.append(k)
            box[nu] = keys
        self.boxsize = sum(len(v) for v in box.values())
        gens = [("x", k) for k in range(n)] + [("t", b) for b in range(n - 1)] + [
            ("d", s) for s in range(nd)
        ]
        self.gens = gens
        # left closure per right word
        rows = {}  # pivot key -> row dict (pivot coefficient 1)
        order = lambda k: (E.polydeg(k), len(k[1]), k)

        def drop(vec):
            return {k: c for k, c in vec.items() if E.polydeg(k) <= cap}

        def reduce(vec):
            vec = dict(vec)
            while True:
                piv = [k for k in vec if k in rows]
                if not piv:
                    return vec
                k = max(piv, key=order)
                c = vec[k]
                for kk, cc in rows[k].items():
                    v = vec.get(kk, 0) - c * cc
                    if v:
                        vec[kk] = v
                    else:
                        vec.pop(kk, None)

        def add(vec):
            vec = reduce(vec)
            if not vec:
                return False
            lead = max(vec, key=order)
            c = Fraction(vec[lead])
            rows[lead] = {k: Fraction(v) / c for k, v in vec.items()}
            queue.append(rows[lead])
            return True

        queue = deque()
        for nu in self.words:
            for m2 in box[nu]:
                mu = E.left_word(m2)
                f = D.cyc[mu[0]]
                if not f:
                    add({m2: 1})
                    continue
                vec = {}
                for coef, xp, ds in f:
                    v = {m2: 1}
                    v = E.lmul_word([("d", s) for s in ds], v)
                    v = E.lmul_word([("x", 0)] * xp, v)
                    E.addto(vec, v, coef)
                add(drop(vec))
        while queue:
            r = queue.popleft()
            for g in gens:
                v = {}
                for k, c in r.items():
                    E.addto(v, E.lmul(g, k), c)
                add(drop(v))
        self.rows = rows
        self.reduce = lambda v: reduce(drop(v))
        basis = [k for nu in self.words for k in box[nu] if k not in rows]
        basis.sort(key=lambda k: (k[0], E.left_word(k), E.degree(k), len(k[1]), k))
        self.basis = basis
        self.pos = {k: i for i, k in enumerate(basis)}
        self.dim = len(basis)
        self.ps = [E.parity(k) for k in basis]
        self.deg = [E.degree(k) for k in basis]
        if verbose:
            print(f"  R^L{Lam}{content} [{D.name}] box={self.boxsize} J-rows={len(rows)} dim={self.dim} cap={cap}", flush=True)

    # ---------- coordinates
    def coords(self, vec):
        v = self.reduce(vec)
        out = [Fraction(0)] * self.dim
        for k, c in v.items():
            out[self.pos[k]] += c
        return out

    def expected(self):
        nd = len(self.D.deltas)
        tot = 0
        blocks = {}
        for u in self.words:
            for v in self.words:
                d = bk_dim(self.D, self.Lam, u, v) * 2 ** nd
                blocks[u, v] = d
                tot += d
        return tot, blocks

    def blockdims(self):
        bd = {}
        for k in self.basis:
            key = (self.E.left_word(k), k[0])
            bd[key] = bd.get(key, 0) + 1
        return bd

    def build_matrices(self):
        n, dim = self.n, self.dim
        E = self.E
        self.L = {}
        for g in self.gens + [("e", nu) for nu in self.words]:
            M = flint.fmpq_mat(dim, dim)
            for j, b in enumerate(self.basis):
                col = self.coords(E.lmul(g, b))
                for i, c in enumerate(col):
                    if c:
                        M[i, j] = fq(c)
            self.L[g] = M
        # x_k, tau_b as sums over idempotents are already the full generators
        self.one = flint.fmpq_mat(dim, 1)
        for nu in self.words:
            k = (nu, (), (0,) * n, ())
            for i, c in enumerate(self.coords({k: 1})):
                if c:
                    self.one[i, 0] += fq(c)
        return self

    def word_of(self, key):
        nu, w, a, S = key
        letters = [("t", b) for b in w]
        for k in range(self.n):
            letters += [("x", k)] * a[k]
        letters += [("d", s) for s in S]
        letters.append(("e", nu))
        return letters

    def Lb(self, key):
        M = flint.fmpq_mat(self.dim, self.dim)
        for i in range(self.dim):
            M[i, i] = 1
        for g in self.word_of(key):
            M = M * self.L[g]
        return M

    def verify(self):
        """Dimension formula, relations and associativity; raises AssertionError."""
        tot, blocks = self.expected()
        bd = self.blockdims()
        if self.dim != tot:
            return f"dimension {self.dim} != formula {tot}"
        for key, d in blocks.items():
            if bd.get(key, 0) != d:
                return f"block {key} dim {bd.get(key,0)} != formula {d}"
        self.build_matrices()
        err = self.check_relations()
        if err:
            return err
        err = self.check_assoc()
        if err:
            return err
        return None

    def check_assoc(self):
        dim = self.dim
        Ls = [self.Lb(k) for k in self.basis]
        for i, k in enumerate(self.basis):
            col = Ls[i] * self.one
            for r in range(dim):
                if col[r, 0] != (1 if r == i else 0):
                    return f"L_b(1) != b for {k}"
        if dim <= self.full_assoc_dim:
            tests = None  # full matrix identity
        else:
            # randomized exact identity test on 3 random integer vectors
            import random
            rnd = random.Random(20261026)
            W = flint.fmpq_mat(dim, 3, [rnd.randint(-10**6, 10**6) for _ in range(3 * dim)])
            LW = [L_ * W for L_ in Ls]
            tests = W
        self.assoc_mode = "full" if tests is None else "randomized(3 vectors)"
        for g in self.gens:
            Lg = self.L[g]
            for i, k in enumerate(self.basis):
                if tests is None:
                    v = Lg * Ls[i]
                    w = flint.fmpq_mat(dim, dim)
                    for r in range(dim):
                        c = Lg[r, i]
                        if c:
                            w += c * Ls[r]
                else:
                    v = Lg * LW[i]
                    w = flint.fmpq_mat(dim, 3)
                    for r in range(dim):
                        c = Lg[r, i]
                        if c:
                            w += c * LW[r]
                if v != w:
                    return f"associativity fails: g={g} b={k}"
        self.Ls = Ls
        return None

    def idem(self, nu):
        return self.L[("e", nu)]

    def check_relations(self):
        D, n, dim = self.D, self.n, self.dim
        L = self.L
        I = flint.fmpq_mat(dim, dim)
        for i in range(dim):
            I[i, i] = 1
        Z = flint.fmpq_mat(dim, dim)
        e = {nu: L[("e", nu)] for nu in self.words}
        if sum((e[nu] for nu in self.words), Z) != I:
            return "sum of idempotents"
        for nu in self.words:
            for mu in self.words:
                if e[nu] * e[mu] != (e[nu] if nu == mu else Z):
                    return "orthogonal idempotents"
        x = [L[("x", k)] for k in range(n)]
        t = [L[("t", b)] for b in range(n - 1)]
        d = [L[("d", s)] for s in range(len(D.deltas))]
        P = lambda nu, k: D.p(nu[k])

        def polyop(terms, nu):
            out = flint.fmpq_mat(dim, dim)
            for coef, letters in terms:
                M = flint.fmpq_mat(I)
                for k in letters:
                    M = M * x[k]
                out += coef * M
            return out * e[nu]

        for nu in self.words:
            E_ = e[nu]
            for k in range(n):
                if x[k] * E_ != E_ * x[k]:
                    return "x commutes with e"
            for b in range(n - 1):
                snu = nu[:b] + (nu[b + 1], nu[b]) + nu[b + 2:]
                if t[b] * E_ != e[snu] * t[b]:
                    return "tau e"
            for k in range(n):
                for l in range(n):
                    if k != l and x[k] * x[l] * E_ != sgn(P(nu, k) * P(nu, l)) * x[l] * x[k] * E_:
                        return f"R2 {nu} {k} {l}"
            for b in range(n - 1):
                s = self.E.r5sign(nu[b], nu[b + 1])  # the presentation actually used
                dl = I if nu[b] == nu[b + 1] else Z
                for k in range(n):
                    if k not in (b, b + 1):
                        if t[b] * x[k] * E_ != sgn(P(nu, k) * P(nu, b) * P(nu, b + 1)) * x[k] * t[b] * E_:
                            return f"R4 {nu} {b} {k}"
                if (t[b] * x[b + 1] - s * x[b] * t[b]) * E_ != dl * E_:
                    return f"R5a {nu} {b}"
                if (x[b + 1] * t[b] - s * t[b] * x[b]) * E_ != dl * E_:
                    return f"R5b {nu} {b}"
                Qt = [(c, [b] * r + [b + 1] * s_) for (r, s_), c in D.Q(nu[b], nu[b + 1]).items()]
                if t[b] * t[b] * E_ != polyop(Qt, nu):
                    return f"R6 {nu} {b}"
                for c in range(n - 1):
                    if abs(b - c) > 1:
                        sg = sgn(P(nu, b) * P(nu, b + 1) * P(nu, c) * P(nu, c + 1))
                        if t[b] * t[c] * E_ != sg * t[c] * t[b] * E_:
                            return f"R7 {nu} {b} {c}"
            for b in range(n - 2):
                lhs = (t[b + 1] * t[b] * t[b + 1] - t[b] * t[b + 1] * t[b]) * E_
                R = self.E.braid_corr(b, nu)
                if lhs != polyop(R, nu):
                    return f"R8 {nu} {b}"
            for s_ in range(len(D.deltas)):
                for k in range(n):
                    if d[s_] * x[k] * E_ != sgn(P(nu, k)) * x[k] * d[s_] * E_:
                        return "delta x"
                for b in range(n - 1):
                    if d[s_] * t[b] * E_ != sgn(P(nu, b) * P(nu, b + 1)) * t[b] * d[s_] * E_:
                        return "delta tau"
                if d[s_] * d[s_] != Z:
                    return "delta^2"
            f = D.cyc[nu[0]]
            if not f:
                if E_ != Z:
                    return "f=1 idempotent survives"
            else:
                M = flint.fmpq_mat(dim, dim)
                for coef, xp, ds in f:
                    T = flint.fmpq_mat(I)
                    for _ in range(xp):
                        T = T * x[0]
                    for s_ in ds:
                        T = T * d[s_]
                    M += coef * T
                if M * E_ != Z:
                    return "cyclotomic"
        return None


def build(D, Lam, content, cap0=4, step=2, capmax=40, verbose=True):
    """Raise the cap until the dimension formula is met (computed dim is monotone).

    For a (mutated) presentation whose quotient stays below the formula, stop
    once the dimension is stable over two further steps; verify() then reports
    the deficit.
    """
    cap = cap0
    hist = []
    while True:
        R = Cyclotomic(D, Lam, content, cap, verbose=verbose)
        tot, _ = R.expected()
        hist.append(R.dim)
        if R.dim >= tot:
            return R
        if cap >= capmax or (len(hist) >= 3 and hist[-1] == hist[-2] == hist[-3]):
            return R
        cap += step
