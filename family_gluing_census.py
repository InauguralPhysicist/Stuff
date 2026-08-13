#!/usr/bin/env python3
"""Census pipeline for the wall-gluing invariant (FAMILY_GLUING.md).

Computes the G1 component census and the G2 labeled incidence graph
for a family member and implements the validation gates V1-V4, V5, V6a.
THE A-vs-B COMPARISON IS GATED: it runs only after every gate passed in
the same invocation (V5 and V6a are blocking per the pre-registration).

Design (all exact; algebraic numbers only as sympy real roots compared
via exact arithmetic):

* 2D strip-sweep census engine (PlaneCensus): partition of R^2 by a
  squarefree curve S(u,v) = 0 with integer labels. Critical u-values =
  roots of Res_v(S, S_v) (plus leading-coefficient vanishing). Between
  them the curve is a union of graphs over u (delineability), so cells
  are (strip, slot); strips are glued across each critical line with
  order/count/label consistency asserted at every step. Critical line
  points are classified: smooth folds (S_u != 0) are presentation
  artifacts and are coarsened away; singular points are strata whose
  labels come from a caller-supplied theorem oracle (for our curves:
  4 incident arc-ends = node -> n = 0 [E a perfect square, both double
  roots real by L6, both on the guard]; 2 incident arc-ends at a
  singular point = cusp -> n = 1 [a triple root of a real quartic is
  real and sits on the guard; the remaining simple root is real]).
  Arc labels = min of the two flanking chamber labels (exact for this
  family: L6 rules out phantom arcs, so every arc is a genuine +/-2
  jump and the on-curve count is the lower side).

* Canonical member census: S = D(P,R) = disc_w E, labels =
  count_roots(E) at rational samples. 3D assembly per L1 (two
  half-space copies of the plane complex, dimensions shifted by one)
  plus the wall complex per L3/L4/L7.

* V5 negative control: the same engine run on a MOVED presentation
  (wall-preserving affine target move mixing A,B and rescaling C,
  plus a source move) where the slice curves are genuine degree-8
  curves and the (P,R) product shortcut is unavailable; the abstract
  censuses must tie the canonical ones exactly.
"""
import argparse
import sys

import sympy as sp
from sympy import Rational as Q

from family_hunt import member_kit, n1_exact, n1_wall, x, y, z, w

Ps, Rs, Aw, Bw = sp.symbols('Ps Rs Aw Bw')


class CensusError(AssertionError):
    pass


def fail(msg):
    raise CensusError(msg)


# ---------------------------------------------------------------------------
# exact numeric helpers

def rational_between(a, b):
    """A rational strictly between exact reals a < b."""
    prec = 30
    while prec < 4000:
        mid = sp.Rational(sp.Float((a.evalf(prec) + b.evalf(prec))/2,
                                   prec))
        if bool(sp.simplify(a - mid) < 0) and bool(sp.simplify(mid - b) < 0):
            return Q(mid)
        prec *= 2
    fail("rational_between failed to separate %s, %s" % (a, b))


def real_roots_exact(expr, var):
    """Sorted distinct real roots of a univariate QQ polynomial."""
    P = sp.Poly(expr, var)
    if P.degree() < 1:
        return []
    return sorted(set(P.real_roots()), key=lambda r: r.evalf(60))


def sorted_reals(vals):
    return sorted(vals, key=lambda r: r.evalf(60))


# ---------------------------------------------------------------------------
# abstract labeled complex

class Complex:
    """Cells: id -> (dim, label). Edges: unordered closure-incidence
    pairs. Supports census, intrinsic coarsening and labeled iso."""

    def __init__(self):
        self.cells = {}
        self.edges = set()

    def add(self, cid, dim, label):
        self.cells[cid] = (dim, label)

    def connect(self, a, b):
        if a != b:
            self.edges.add(tuple(sorted((a, b), key=str)))

    def neighbors(self, i):
        out = set()
        for a, b in self.edges:
            if a == i:
                out.add(b)
            elif b == i:
                out.add(a)
        return out

    def merge(self, keep, drop):
        """Identify two cells (labels must agree)."""
        if self.cells[keep] != self.cells[drop]:
            fail("merging cells with different (dim,label): %s %s"
                 % (self.cells[keep], self.cells[drop]))
        for a, b in list(self.edges):
            if drop in (a, b):
                self.edges.discard((a, b))
                other = b if a == drop else a
                if other != keep:
                    self.connect(keep, other)
        del self.cells[drop]

    def census(self):
        out = {}
        for _, (d, lab) in self.cells.items():
            out[(d, lab)] = out.get((d, lab), 0) + 1
        return dict(sorted(out.items()))

    def iso(self, other):
        if self.census() != other.census():
            return False

        def key(C, i):
            return (C.cells[i],
                    tuple(sorted(C.cells[j] for j in C.neighbors(i))))

        buckets = {}
        for j in other.cells:
            buckets.setdefault(key(other, j), []).append(j)
        mine = sorted(self.cells, key=lambda i: (len(self.neighbors(i)),
                                                 str(i)), reverse=True)

        def extend(assign):
            if len(assign) == len(mine):
                return True
            i = mine[len(assign)]
            for j in buckets.get(key(self, i), []):
                if j in assign.values():
                    continue
                good = True
                for i2, j2 in assign.items():
                    if (i in self.neighbors(i2)) != (j in other.neighbors(j2)):
                        good = False
                        break
                if good:
                    assign[i] = j
                    if extend(assign):
                        return True
                    del assign[i]
            return False

        return extend({})


# ---------------------------------------------------------------------------
# the strip-sweep plane census engine

class PlaneCensus:
    """Exact census of R^2 partitioned by squarefree S(u,v) = 0.

    label(u0, v0): exact integer label at a rational point.
    point_oracle(n_arc_ends, arc_label, singular): label for a critical
    line point given its incident arc-end count, the common arc label,
    and whether the point is singular (S_u = S_v = 0). Smooth folds
    (singular=False) return the arc label and are coarsened away."""

    def __init__(self, S, u, v, label, point_oracle):
        self.S = sp.expand(S)
        self.u, self.v = u, v
        self.label = label
        self.point_oracle = point_oracle
        self.cx = Complex()
        self._alias = {}
        self._build()

    def rep(self, i):
        while i in self._alias:
            i = self._alias[i]
        return i

    def _build(self):
        u, v = self.u, self.v
        Sv = sp.diff(self.S, v)
        res = sp.expand(sp.resultant(self.S, Sv, v))
        lc = sp.Poly(self.S, v).LC()
        crit = set(real_roots_exact(res, u))
        if lc.free_symbols:
            crit |= set(real_roots_exact(lc, u))
        crit = sorted_reals(crit)
        self.crit = crit
        # rational sample per open strip
        samples = []
        for i in range(len(crit) + 1):
            if not crit:
                samples.append(Q(0))
            elif i == 0:
                samples.append(Q(sp.floor(crit[0].evalf(50))) - 1)
            elif i == len(crit):
                samples.append(Q(sp.ceiling(crit[-1].evalf(50))) + 1)
            else:
                samples.append(rational_between(crit[i - 1], crit[i]))
        self.samples = samples
        # strip cells
        self.roots = []
        for i, u0 in enumerate(samples):
            rr = real_roots_exact(self.S.subs(u, u0), v)
            self.roots.append(rr)
            for slot in range(len(rr) + 1):
                v0 = self._slot_sample(rr, slot)
                self.cx.add(('C', i, slot), 2, self.label(u0, v0))
            for j in range(len(rr)):
                lo = self.cx.cells[('C', i, j)][1]
                hi = self.cx.cells[('C', i, j + 1)][1]
                if abs(lo - hi) != 2:
                    fail("arc (%s,%s): flanking labels %s,%s not +/-2"
                         % (i, j, lo, hi))
                self.cx.add(('A', i, j), 1, min(lo, hi))
                self.cx.connect(('A', i, j), ('C', i, j))
                self.cx.connect(('A', i, j), ('C', i, j + 1))
        # glue strips across critical lines
        for k, uc in enumerate(crit):
            self._glue(k, uc)

    def _slot_sample(self, rr, slot):
        if not rr:
            return Q(0)
        if slot == 0:
            return Q(sp.floor(rr[0].evalf(50))) - 1
        if slot == len(rr):
            return Q(sp.ceiling(rr[-1].evalf(50))) + 1
        return rational_between(rr[slot - 1], rr[slot])

    def _line_roots(self, uc):
        u, v = self.u, self.v
        Sc = self.S.subs(u, uc)
        if uc.is_rational:
            return real_roots_exact(Sc, v)
        mpu = sp.minimal_polynomial(uc, u)
        elim = sp.resultant(mpu, self.S, u)
        cand = real_roots_exact(elim, v)
        out = []
        for r in cand:
            val = Sc.subs(v, r)
            if sp.simplify(val) == 0:
                out.append(r)
        return sorted_reals(out)

    def _singular_set(self):
        """Real singular points of the curve, solved once from
        {S, S_u, S_v}; cached as 80-digit approximations (the set is
        finite and separations are far above the ambiguity band)."""
        if not hasattr(self, '_sing'):
            Su = sp.diff(self.S, self.u)
            Sv = sp.diff(self.S, self.v)
            G = sp.groebner([self.S, Su, Sv], self.u, self.v,
                            order='lex', domain='QQ')
            self._sing = []
            if list(G.exprs) != [sp.Integer(1)]:
                for s in sp.solve(G.exprs, [self.u, self.v], dict=True):
                    su, sv2 = s[self.u], s[self.v]
                    if su.is_real and sv2.is_real:
                        self._sing.append((su.evalf(80), sv2.evalf(80)))
        return self._sing

    def _is_singular(self, uc, vt):
        pu, pv = uc.evalf(80), vt.evalf(80)
        best = None
        for su, sv2 in self._singular_set():
            d = max(abs(pu - su), abs(pv - sv2))
            best = d if best is None or d < best else best
        if best is None:
            return False
        if best < sp.Float(10)**-40:
            return True
        if best < sp.Float(10)**-10:
            fail("singularity test ambiguous (distance %s)" % best)
        return False

    def _match(self, strip_idx, uc, line_roots, from_left):
        """Order-preserving map (branch index in the strip) -> (line
        root index), computed at rational points adaptively refined
        toward the critical line, where each branch is within a quarter
        line-root gap of its limit. Branch order is constant within a
        strip (disjoint graphs), so indices transport from the strip
        sample."""
        n = len(self.roots[strip_idx])
        if n == 0:
            return {}
        lv = [r.evalf(80) for r in line_roots]
        gaps = [abs(lv[i + 1] - lv[i]) for i in range(len(lv) - 1)]
        tol = (min(gaps)/4) if gaps else sp.Float(1)
        # start one unit from the line, refine toward it
        h = Q(1)
        for _ in range(200):
            u1 = Q(sp.Rational(sp.Float(uc.evalf(60), 60))) + \
                (-h if from_left else h)
            # u1 must stay inside the strip
            if not self._inside_strip(strip_idx, u1):
                h /= 2
                continue
            rr = real_roots_exact(self.S.subs(self.u, u1), self.v)
            if len(rr) != n:
                h /= 2
                continue
            rv = [r.evalf(80) for r in rr]
            ok = True
            mapping = {}
            for j, a in enumerate(rv):
                dists = [abs(b - a) for b in lv]
                k = min(range(len(lv)), key=lambda i: dists[i])
                if dists[k] > tol:
                    ok = False
                    break
                mapping[j] = k
            if ok:
                vals = [mapping[j] for j in range(n)]
                if vals != sorted(vals):
                    fail("branch matching lost order at u=%s" % u1)
                return mapping
            h /= 2
        fail("branch matching did not stabilize approaching u=%s" % uc)

    def _inside_strip(self, strip_idx, u1):
        lo = self.crit[strip_idx - 1] if strip_idx >= 1 else None
        hi = self.crit[strip_idx] if strip_idx < len(self.crit) else None
        if lo is not None and not bool(sp.simplify(u1 - lo) > 0):
            return False
        if hi is not None and not bool(sp.simplify(u1 - hi) < 0):
            return False
        return True

    def _glue(self, k, uc):
        L, R = k, k + 1
        rc = self._line_roots(uc)
        mapL = self._match(L, uc, rc, from_left=True)
        mapR = self._match(R, uc, rc, from_left=False)
        nl, nr = len(self.roots[L]), len(self.roots[R])
        for t, vt in enumerate(rc):
            jl = [j for j in range(nl) if mapL[j] == t]
            jr = [j for j in range(nr) if mapR[j] == t]
            ends = len(jl) + len(jr)
            labs = {self.cx.cells[self.rep(('A', L, j))][1] for j in jl} | \
                   {self.cx.cells[self.rep(('A', R, j))][1] for j in jr}
            if ends == 2 and len(jl) == 1 and len(jr) == 1 \
                    and not self._is_singular(uc, vt):
                # regular continuation: fuse the two arcs
                a = self.rep(('A', L, jl[0]))
                b = self.rep(('A', R, jr[0]))
                if a != b:
                    self.cx.merge(a, b)
                    self._alias[b] = a
                continue
            singular = self._is_singular(uc, vt)
            if not singular and len(labs) != 1:
                fail("smooth critical point at u=%s with mixed arc "
                     "labels %s" % (uc, labs))
            lab = self.point_oracle(ends, min(labs), singular)
            pid = ('P', k, t)
            self.cx.add(pid, 0, lab)
            for j in jl:
                self.cx.connect(pid, self.rep(('A', L, j)))
            for j in jr:
                self.cx.connect(pid, self.rep(('A', R, j)))
        # chambers: glue across the line by open overlap of line spans
        spans = {}
        for side, n, mp_ in (('L', nl, mapL), ('R', nr, mapR)):
            idx = L if side == 'L' else R
            for slot in range(n + 1):
                lo = mp_[slot - 1] if slot >= 1 else -1
                hi = mp_[slot] if slot < n else len(rc)
                spans[(side, slot)] = (lo, hi, idx)
        for slotL in range(nl + 1):
            loL, hiL, _ = spans[('L', slotL)]
            for slotR in range(nr + 1):
                loR, hiR, _ = spans[('R', slotR)]
                if max(loL, loR) < min(hiL, hiR):
                    a = self.rep(('C', L, slotL))
                    b = self.rep(('C', R, slotR))
                    if a != b:
                        self.cx.merge(a, b)
                        self._alias[b] = a
        # chamber-point incidence: slot closures reaching a line root
        for t in range(len(rc)):
            pid = ('P', k, t)
            if pid not in self.cx.cells:
                continue
            for (side, slot), (lo, hi, idx) in spans.items():
                if lo == t or hi == t or (lo < t < hi):
                    self.cx.connect(pid, self.rep(('C', idx, slot)))

    # -- exact point location (for 3D assembly) ------------------------
    def strip_of(self, u0):
        """Index of the open strip containing rational u0 (fails loudly
        if u0 is a critical value)."""
        for i, uc in enumerate(self.crit):
            d = sp.simplify(u0 - uc)
            if d == 0:
                fail("strip_of called on a critical value")
            if bool(d < 0):
                return i
        return len(self.crit)

    def locate_chamber(self, u0, v0):
        """Coarsened chamber id containing rational (u0, v0): walk the
        branch structure from the strip sample to u0 (no critical
        values in between, so slot indices transport verbatim)."""
        i = self.strip_of(u0)
        rr = real_roots_exact(self.S.subs(self.u, u0), self.v)
        slot = 0
        for r in rr:
            d = sp.simplify(v0 - r)
            if d == 0:
                fail("locate_chamber called on the curve")
            if bool(d > 0):
                slot += 1
        if len(rr) != len(self.roots[i]):
            fail("root count changed inside a strip (delineability "
                 "violated)")
        return self.rep(('C', i, slot))

    def locate_arc(self, u0, v_root):
        """Coarsened arc id of the branch passing through (u0, v_root),
        where u0 is rational and non-critical and v_root is an exact
        root of S(u0, .)."""
        i = self.strip_of(u0)
        rr = real_roots_exact(self.S.subs(self.u, u0), self.v)
        if len(rr) != len(self.roots[i]):
            fail("root count changed inside a strip")
        idx = None
        for j, r in enumerate(rr):
            if sp.simplify(r - v_root) == 0:
                idx = j
        if idx is None:
            fail("locate_arc: point is not on the curve")
        return self.rep(('A', i, idx))

    def result(self):
        """Coarsened abstract complex: remove presentation-only fold
        points (0-cells whose label equals that of their exactly-two
        incident arcs and which are non-strata by construction --
        the point_oracle marks them by returning the arc label; genuine
        strata points have a different label or >2 arc ends)."""
        cx = self.cx
        for i in [i for i, (d, _) in list(cx.cells.items()) if d == 0]:
            arcs = [j for j in cx.neighbors(i) if cx.cells[j][0] == 1]
            if len(arcs) != 2:
                continue
            lab = cx.cells[i][1]
            l1 = cx.cells[arcs[0]][1]
            l2 = cx.cells[arcs[1]][1]
            if lab == l1 == l2:
                # fold: fuse arcs, drop the point
                if arcs[0] != arcs[1]:
                    cx.merge(arcs[0], arcs[1])
                cx.edges = {e for e in cx.edges if i not in e}
                del cx.cells[i]
        return cx


# ---------------------------------------------------------------------------
# canonical member: plane data and census

def plane_data(M):
    H, Hp0 = M['H'], M['Hp0']
    EPR = sp.expand(-H + w*(Hp0 + Ps) - Rs)
    D = sp.expand(sp.discriminant(EPR, w))

    def label(p0, r0):
        return sp.count_roots(sp.Poly(EPR.subs({Ps: p0, Rs: r0}), w))

    return EPR, D, label


def point_oracle_factory(degree, allow_folds):
    """Labels for critical points of a discriminant-type curve of an
    E of the given degree (or a diffeomorphic image of one):
      - smooth fold (not singular): presentation artifact of the moved
        frame; labeled with the arc label and coarsened away. On a
        canonical curve folds contradict L5, so allow_folds=False
        turns them into loud failures.
      - singular, 2 arc-ends: cusp -> real triple root (automatic for
        a real polynomial) on the guard; the remaining degree-3 simple
        roots are real for our quartic (one root) and absent for the
        cubic: n = degree - 3.
      - singular, 4 arc-ends: node -> two double roots, both real (L6)
        and on the guard: n = degree - 4."""
    def oracle(ends, arc_label, singular):
        if not singular:
            if not allow_folds:
                fail("smooth vertical tangent on a canonical curve "
                     "(contradicts L5)")
            return arc_label
        if ends == 2:
            return degree - 3
        if ends == 4:
            return degree - 4
        fail("unclassified singular point with %d arc ends" % ends)
    return oracle


def canonical_plane_census(M):
    """Returns (engine, coarsened complex); the engine is kept for
    exact point location during 3D assembly."""
    EPR, D, label = plane_data(M)
    deg = sp.Poly(EPR, w).degree()
    pc = PlaneCensus(D, Ps, Rs, label,
                     point_oracle_factory(deg, allow_folds=False))
    return pc, pc.result()


# ---------------------------------------------------------------------------
# wall data

def wall_delta(M):
    """Sign-faithful polynomial with the sign of delta(A,B)."""
    a = M['a']
    F1, F2 = M['F'][0], M['F'][1]
    zg = -(1 + a*x*y)/x**2
    eqs = []
    for Fi, ti in ((F1, Aw), (F2, Bw)):
        num = sp.fraction(sp.cancel(Fi.subs(z, zg) - ti))[0]
        eqs.append(sp.expand(num))
    G = sp.groebner(eqs, y, x, order='lex', domain='QQ(Aw,Bw)')
    uni = [e for e in G.exprs if e.free_symbols <= {x, Aw, Bw}]
    P = sp.Poly(uni[-1], x)
    while P.coeff_monomial(1) == 0:
        P = sp.Poly(sp.cancel(P.as_expr()/x), x)
    delta = sp.factor(sp.discriminant(P.as_expr(), x))
    num, den = sp.fraction(delta)
    return sp.expand(num*den)


# ---------------------------------------------------------------------------
# 3D assembly (G1 + G2)

def assemble_3d(M, pc, plane_cx):
    """Two half-space copies of the plane complex (dims shifted by 1)
    plus the wall complex, per L1/L3/L4/L7."""
    EPR, D, label = plane_data(M)
    dn = wall_delta(M)
    cx = Complex()
    for side in ('+', '-'):
        for i, (d, lab) in plane_cx.cells.items():
            cx.add((side, i), d + 1, lab)
        for a, b in plane_cx.edges:
            cx.connect((side, a), (side, b))
    # wall 2-strata: the two delta-sign regions with exact labels
    for tag, (av, bv) in (('dpos', (Q(-3), Q(2, 3))),
                          ('dneg', (Q(4), Q(1, 5)))):
        sgn = dn.subs({Aw: av, Bw: bv})
        if (tag == 'dpos') != (sgn > 0):
            fail("wall sample signs inverted")
        cx.add(('W', tag), 2, n1_wall(M, (av, bv, Q(0))))
    # parabola stratum (one intrinsic stratum through the vertex;
    # halves verified to carry equal labels)
    labs = []
    for bval in (Q(2), Q(-2)):
        sols = sp.solve(sp.Eq(dn.subs(Bw, bval), 0), Aw)
        avs = [s for s in sols if s.is_rational]
        if not avs:
            fail("parabola point not rational at B=%s" % bval)
        labs.append(n1_wall(M, (Q(avs[0]), bval, Q(0))))
    if labs[0] != labs[1]:
        fail("parabola halves carry different labels: %s" % labs)
    cx.add(('W', 'parab'), 1, labs[0])
    # vertex
    cx.add(('W', 'vertex'), 0, n1_wall(M, (Q(0), Q(0), Q(0))))
    # locate the origin-local plane cells exactly: the origin is a
    # regular curve point (L7); pick a non-critical rational u* near 0
    # and find the branch through the origin plus its flanking chambers
    ustar = Q(0)
    if any(sp.simplify(uc) == 0 for uc in pc.crit):
        fail("P = 0 is a critical value (unexpected for these curves)")
    rr0 = real_roots_exact(D.subs(Ps, ustar), Rs)
    zero_idx = [j for j, r in enumerate(rr0) if sp.simplify(r) == 0]
    if len(zero_idx) != 1:
        fail("origin is not a simple curve point on the line P=0")
    j0 = zero_idx[0]
    above = rational_between(rr0[j0], rr0[j0 + 1]) if j0 + 1 < len(rr0) \
        else Q(sp.ceiling(rr0[-1].evalf(50))) + 1
    below = rational_between(rr0[j0 - 1], rr0[j0]) if j0 >= 1 \
        else Q(sp.floor(rr0[0].evalf(50))) - 1
    lab_up, lab_dn = label(ustar, above), label(ustar, below)
    if {lab_up, lab_dn} != {4, 2}:
        fail("origin-flanking chambers are not the 4/2 pair: %s"
             % {lab_up, lab_dn})
    ch4 = pc.locate_chamber(ustar, above if lab_up == 4 else below)
    ch2 = pc.locate_chamber(ustar, above if lab_up == 2 else below)
    arc0 = pc.locate_arc(ustar, rr0[j0])
    # incidence per L3/L7:
    for side in ('+', '-'):
        # crack: both wall 2-strata attach to both half-space copies of
        # their near-wall chamber (N=4 over dpos, N=2 over dneg)
        cx.connect(('W', 'dpos'), (side, ch4))
        cx.connect(('W', 'dneg'), (side, ch2))
        # jump stratum: the parabola touches all four chamber copies
        cx.connect(('W', 'parab'), (side, ch4))
        cx.connect(('W', 'parab'), (side, ch2))
        # closure(Sigma) /\ wall = parabola: the Sigma copy through the
        # origin arc limits onto the parabola (and the vertex)
        cx.connect(('W', 'parab'), (side, arc0))
        cx.connect(('W', 'vertex'), (side, arc0))
        cx.connect(('W', 'vertex'), (side, ch4))
        cx.connect(('W', 'vertex'), (side, ch2))
    cx.connect(('W', 'parab'), ('W', 'dpos'))
    cx.connect(('W', 'parab'), ('W', 'dneg'))
    cx.connect(('W', 'vertex'), ('W', 'parab'))
    cx.connect(('W', 'vertex'), ('W', 'dpos'))
    cx.connect(('W', 'vertex'), ('W', 'dneg'))
    return cx


# ---------------------------------------------------------------------------
# gates

def gate_V1(M, name):
    """Independent-oracle grid: plane labels vs the certified n1_exact
    (through the C=1 section: n(R, P, 1) = N(P, R)), wall labels vs
    n1_wall, jump points on the parabola."""
    EPR, D, label = plane_data(M)
    ok = True
    for p0, r0 in [(Q(3), Q(1)), (Q(-3), Q(1)), (Q(3), Q(-1)),
                   (Q(-3), Q(-1)), (Q(0), Q(5)), (Q(0), Q(-5)),
                   (Q(10), Q(2)), (Q(-10), Q(-3)), (Q(1), Q(100)),
                   (Q(1), Q(-100)), (Q(1, 7), Q(-1, 9))]:
        via_map = n1_exact(M, (r0, p0, Q(1)))
        if via_map is None:
            continue
        if label(p0, r0) != via_map:
            print("  V1 mismatch at (P,R)=(%s,%s)" % (p0, r0))
            ok = False
    dn = wall_delta(M)
    for av, bv in [(Q(-3), Q(2, 3)), (Q(4), Q(1, 5)), (Q(1, 4), Q(5, 2)),
                   (Q(6, 5), Q(-1))]:
        want = 3 if dn.subs({Aw: av, Bw: bv}) > 0 else 1
        if n1_wall(M, (av, bv, Q(0))) != want:
            print("  V1 wall mismatch at (%s,%s)" % (av, bv))
            ok = False
    # node label theorem check at the rational node (if rational)
    node = rational_node(M)
    if node is not None:
        pv, rv = node
        E = sp.Poly(EPR.subs({Ps: pv, Rs: rv}), w)
        g = sp.gcd(E, sp.Poly(sp.diff(E.as_expr(), w), w))
        simple = sp.count_roots(sp.Poly(sp.cancel(E.as_expr()/g.as_expr()),
                                        w)) - sp.count_roots(g)
        if simple != 0:
            print("  V1 node-label theorem violated: n = %s" % simple)
            ok = False
    print("[%s] V1 independent-oracle grid: %s"
          % (name, "PASS" if ok else "FAIL"))
    return ok


def rational_node(M):
    EPR, D, _ = plane_data(M)
    G = sp.groebner([D, sp.diff(D, Ps), sp.diff(D, Rs)], Ps, Rs,
                    order='lex', domain='QQ')
    sols = sp.solve(G.exprs, [Ps, Rs], dict=True)
    for s in sols:
        if s[Ps].is_rational and s[Rs].is_rational:
            return (s[Ps], s[Rs])
    return None


def gate_V2(cxA, cxB):
    M3 = member_kit([0, -1, 2])       # degree-3 member: roots sum to 1
    _, cx3 = canonical_plane_census(M3)
    da = cx3.census() != cxA.census() or not cx3.iso(cxA)
    db = cx3.census() != cxB.census() or not cx3.iso(cxB)
    print("V2 planted difference (degree-3 member, census %s): %s"
          % (cx3.census(), "PASS" if (da and db) else "FAIL"))
    return da and db


def gate_V3(M, name):
    EPR, D, _ = plane_data(M)
    lc = sp.Poly(EPR, w).LC()
    D2 = sp.expand(sp.resultant(EPR, sp.diff(EPR, w), w)/lc)
    same = {f for f, _ in sp.factor_list(D)[1]} == \
           {f for f, _ in sp.factor_list(D2)[1]}
    print("[%s] V3 two-route D: %s" % (name, "PASS" if same else "FAIL"))
    return same


def gate_V4(M, name):
    """Transformation law: count fibers of the COMPOSED map psi o F
    from scratch (Groebner, shape-lemma verified) and compare with
    n1_exact at psi^{-1}(y). psi = elementary o affine:
    psi(a,b,c) = (a + c**2, b - c, 2*c); psi^{-1}(y) =
    (y1 - y3**2/4, y2 + y3/2, y3/2)."""
    F1, F2, F3 = M['F']
    comp = (sp.expand(F1 + F3**2), sp.expand(F2 - F3), sp.expand(2*F3))
    ok = True
    for yv in [(Q(1), Q(2), Q(2)), (Q(-2), Q(1), Q(4)),
               (Q(3), Q(-1), Q(-2)), (Q(0), Q(4), Q(6))]:
        y1, y2, y3 = yv
        pre = (y1 - y3**2/4, y2 + y3/2, y3/2)
        want = n1_exact(M, pre)
        if want is None:
            continue
        got = groebner_fiber_count(comp, yv)
        if got != want:
            print("  V4 mismatch at %s: composed %s vs law %s"
                  % (yv, got, want))
            ok = False
    print("[%s] V4 transformation law (composed-map oracle): %s"
          % (name, "PASS" if ok else "FAIL"))
    return ok


def groebner_fiber_count(F, tgt):
    """Exact fiber count of a polynomial map by lex Groebner with
    shape-lemma verification and substitution check."""
    eqs = [sp.expand(f - t) for f, t in zip(F, tgt)]
    G = sp.groebner(eqs, z, y, x, order='lex', domain='QQ')
    exprs = list(G.exprs)
    if exprs == [sp.Integer(1)]:
        return 0
    uni = [e for e in exprs if e.free_symbols <= {x}]
    if not uni:
        fail("fiber oracle: no eliminant")
    g = sp.Poly(uni[-1], x)
    gsf = sp.Poly(sp.prod([b for b, _ in
                           sp.factor_list(g.as_expr())[1]]), x)
    subs_chain = {}
    for var in (y, z):
        lin = None
        for e in exprs:
            if var in e.free_symbols and sp.degree(e, var) == 1:
                c = sp.Poly(e, var)
                cn1 = sp.simplify(c.nth(1).subs(subs_chain))
                cn0 = sp.simplify(c.nth(0).subs(subs_chain))
                if cn1.free_symbols <= {x} and cn0.free_symbols <= {x}:
                    cand = sp.cancel(-cn0/cn1)
                    den = sp.fraction(cand)[1]
                    if sp.gcd(sp.Poly(den, x), gsf).total_degree() == 0:
                        lin = cand
                        break
        if lin is None:
            fail("fiber oracle: not shape lemma")
        subs_chain[var] = lin
    for f, t in zip(F, tgt):
        expr = sp.cancel(f.subs(subs_chain, simultaneous=True) - t)
        num = sp.fraction(expr)[0]
        if sp.rem(sp.expand(num), gsf.as_expr(), x) != 0:
            fail("fiber oracle: candidate verification failed")
    return gsf.count_roots()


def gate_V5(M, name, canonical_cx):
    """Negative control: plane censuses of a moved presentation.
    Target move psi (affine, wall-preserving, mixes A,B, rescales C):
      psi(a,b,c) = (2a - b + c, a + b - 3c, c/2)
    Source move phi: any affine automorphism (does not change n; the
    composed map's fiber counts are n1_exact at psi^{-1}, which the
    slice labels use through exact rational arithmetic only).
    Slice curves in the moved frame are degree-8 images of D = 0; the
    engine must reproduce the canonical abstract census on every
    sampled slice, with slice-family criticality excluded exactly."""
    y1, y2, y3 = sp.symbols('y1 y2 y3')
    EPR, D, _ = plane_data(M)
    Mmat = sp.Matrix([[2, -1, 1], [1, 1, -3], [0, 0, Q(1, 2)]])
    inv = Mmat.inv()
    av_, bv_, cv_ = (inv * sp.Matrix([y1, y2, y3]))
    Smoved = sp.expand(D.subs({Ps: sp.expand(bv_*cv_),
                               Rs: sp.expand(av_*cv_**2)}))
    ok = True
    for c0 in (Q(2), Q(-2), Q(6)):
        Sc = sp.expand(Smoved.subs(y3, c0))
        fl = [f for f, _ in sp.factor_list(Sc)[1]]
        Sc = sp.expand(sp.prod(fl))          # squarefree part

        def lab(u0, v0, c0=c0):
            # evaluate ALL target coordinates through the same psi^{-1}
            # expressions the slice curve was built from (a hand-derived
            # C here caused the first V5 failure -- labels from a wrong
            # slice produce non-jumping arcs)
            sub = {y1: u0, y2: v0, y3: c0}
            vals = [av_.subs(sub), bv_.subs(sub), cv_.subs(sub)]
            for vv in vals:
                if not vv.is_rational:
                    fail("V5 slice sample not rational: %s" % vv)
            r = n1_exact(M, tuple(Q(vv) for vv in vals))
            if r is None:
                fail("V5 slice sample on a guarded stratum")
            return r

        cx = PlaneCensus(Sc, y1, y2, lab,
                         point_oracle_factory(4, allow_folds=True)).result()
        if cx.census() != canonical_cx.census() or \
                not cx.iso(canonical_cx):
            print("  V5 slice c=%s census %s != canonical %s"
                  % (c0, cx.census(), canonical_cx.census()))
            ok = False
    print("[%s] V5 moved-presentation slice censuses: %s"
          % (name, "PASS" if ok else "FAIL"))
    return ok


def gate_V6a(cxA):
    fake = Complex()
    fake.cells = dict(cxA.cells)
    fake.edges = set(cxA.edges)
    two = sorted([i for i, (d, _) in fake.cells.items() if d == 2],
                 key=str)[0]
    fake.cells[('X', 'plant')] = fake.cells[two]
    detected = fake.census() != cxA.census()
    print("V6a synthetic same-G0 plant detected: %s"
          % ("PASS" if detected else "FAIL"))
    return detected


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true',
                    help='plane censuses and cheap gates only (V5 '
                         'skipped => comparison locked)')
    args = ap.parse_args()

    A = member_kit([0, -1, 3, 4])
    B = member_kit([0, -1, -2, Q(3, 2)])

    print("== plane censuses (canonical) ==")
    pcA, cxA = canonical_plane_census(A)
    pcB, cxB = canonical_plane_census(B)
    print("  A plane census:", cxA.census())
    print("  B plane census:", cxB.census())

    print("== gates ==")
    gates = True
    gates &= gate_V1(A, 'A')
    gates &= gate_V1(B, 'B')
    gates &= gate_V2(cxA, cxB)
    gates &= gate_V3(A, 'A')
    gates &= gate_V3(B, 'B')
    gates &= gate_V4(A, 'A')
    gates &= gate_V4(B, 'B')
    gates &= gate_V6a(cxA)
    if args.quick:
        print("V5 SKIPPED (--quick) => comparison locked")
        gates = False
    else:
        gates &= gate_V5(A, 'A', cxA)

    if not gates:
        print("\nGATES NOT GREEN -- no A-vs-B comparison performed "
              "(pre-registration lock)")
        return 1

    print("== G1/G2 (gates green) ==")
    gA = assemble_3d(A, pcA, cxA)
    gB = assemble_3d(B, pcB, cxB)
    print("  G1(A):", gA.census())
    print("  G1(B):", gB.census())
    if gA.census() != gB.census():
        print("  -> G1 DIFFERENCE: anomaly protocol (assume bug; "
              "independent recomputation required before banking)")
        return 2
    print("  G1 tie.")
    if not gA.iso(gB):
        print("  -> G2 DIFFERENCE: anomaly protocol applies")
        return 2
    print("  G2 tie (labeled incidence graphs isomorphic).")
    print("  G0-G2 TIE: escalation to G3 per pre-registration")
    return 0


if __name__ == '__main__':
    sys.exit(main())
