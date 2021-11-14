"""
Instanton moduli space and its associated objects.
"""
from sage.combinat.sf.sfa import SymmetricFunctionAlgebra_generic
from sage.categories.morphism import SetMorphism
from sage.rings.fraction_field import is_FractionField
from sage.structure.element import is_Matrix

load("partition_3d.sage")
load("quantum_toroidal.sage")

load("setup.sage") # contains Default and KTheory

class Instantons(UniqueRepresentation):
    """
    Instanton moduli space (mostly only implemented for the rank 1 case
    where it is the Hilbert scheme).
    """
    def __init__(self, r, t1, t2, u=None):
        self.r = r

        self.t1 = t1
        self.t2 = t2
        if t1.parent() != t2.parent():
            raise ValueError("%s and %s not in same ring" % (t1, t2))
        self._wR = t1.parent()

        if r > 1:
            if not u:
                raise ValueError("must specify framing variables u")
            self.u = u
        else:
            self.u = [self._wR.one()]
        self._uR = self.u[0].parent()

        self.QTA = QuantumToroidalAlgebra(self.t1, self.t2)

        self.sym = SymmetricFunctions(self._wR.fraction_field())
        self.sym_mcd = self.sym.macdonald(q=self.t1, t=self.t2)

    def __repr__(self):
        return "Rank %s instanton moduli space in x=%s, y=%s, u=%s" % \
            (self.r, self.t1, self.t2, self.u)

    def fixed_points(self, n):
        """
        Lists fixed points of instanton number `n` as r-tuples of
        partitions, in ascending dominance order.
        """
        L = PartitionTuples(self.r, n).list()
        return sorted(L, key=lambda pt: len(self.full_attracting_set(pt)))
            
    def fixed_points_nested(self, n, descending_flag=True):
        """
        Lists only the fixed points of instanton number `n` which are
        descending flags of `r` partitions, in ascending dominance order.
        """
        def flags(r, n, mu):
            if r == 1:
                return [[nu] for nu in Partitions(n, outer=mu)]
            else:
                return [p+[nu] for k in range(n+1)
                        for nu in Partitions(k, outer=mu)
                        for p in flags(r-1, n-nu.size(), nu)]
        L = flags(self.r, n, [n+1] * (n+1))
        if descending_flag:
            L = [PartitionTuple(list(reversed(p))) for p in L]
        else:
            L = [PartitionTuple(p) for p in L]

        return sorted(L, key=lambda pt: len(self.full_attracting_set(pt)))

    def full_attracting_set(self, p, chamber=1):
        """
        Returns all fixed points in the full attracting set of the
        fixed point `p`, aside from `p` itself.
        """
        if chamber == 1:
            comparison = lambda p, q: p.dominates(q)
        elif chamber == -1:
            comparison = lambda p, q: q.dominates(p)
        return [q for q in PartitionTuples(p.level(), p.size())
                if q != p and comparison(p, q)]

    def _polarization(self, lamb, mu):
        r"""
        Computes the polarization at `(\lambda, \mu)`.
        """
        t1, t2 = self.t1, self.t2
        V_lamb_inv = character_2d_partition(lamb, 1/t1, 1/t2)
        V_mu = character_2d_partition(mu, t1, t2)

        return V_mu - (1-1/t1)*V_lamb_inv*V_mu
    
    def _tangent_space(self, lamb, mu):
        r"""
        Computes the tangent character at `(\lambda, \mu)`.
        """
        t1, t2 = self.t1, self.t2
        V_lamb_inv = character_2d_partition(lamb, 1/t1, 1/t2)
        V_mu = character_2d_partition(mu, t1, t2)

        return V_mu + V_lamb_inv/(t1*t2) - (1-1/t1)*(1-1/t2)*V_mu*V_lamb_inv

    def _tangent_space_weights(self, lamb, mu):
        r"""
        Computes the weights in the tangent space at `(\lambda, \mu)`
        using the formula in terms of arm and leg lengths.

        Returns the weights as a list of pairs `(w_1, w_2)`, representing
        weights `t_1^{w_1} t_2^{w_2}`.
        """
        arm = lambda lamb, c: lamb.get_part(c[0]) - c[1] - 1
        leg = lambda mu, c: mu.conjugate().get_part(c[1]) - c[0] - 1
        return [[(-arm(lamb,c)-1, leg(mu,c)) for c in lamb.cells()],
                [(arm(mu,c), -leg(lamb,c)-1) for c in mu.cells()]]

    def _tangent_space_half(self, lamb):
        r"""
        Computes half the tangent character at `\lambda` using
        the formula in terms of arm and leg lengths.
        """
        weights = self._tangent_space_weights(lamb, lamb)
        return sum( (self.t1^w1*self.t2^w2 for w1,w2 in weights[0]),
                    self._wR.zero() )
    
    def _sum_over_lamb_mu(self, f, p, strict=False):
        r"""
        Given a functional `f(\lambda, \mu)`, return the weighted sum
        `\sum_{i,j} u_j/u_i f(\lambda_i, \lambda_j)`, where the partitions
        `\lambda` are taken to be the ones in the fixed point `p`.
        """
        if p.level() == 1:
            p = [p] # otherwise enumerate(p) is bad
        return sum(self.u[j]/self.u[i] * f(lamb, mu)
                   for i, lamb in enumerate(p)
                   for j, mu in enumerate(p) if not strict or strict and i<j)

    def polarization(self, p):
        """
        Returns the polarization `T^{1/2}` at the fixed point `p`.
        """
        return self._sum_over_lamb_mu(self._polarization, p)

    def tangent_space(self, p):
        """
        Returns the character of the tangent space at the fixed point `p`.
        """
        return self._sum_over_lamb_mu(self._tangent_space, p)

    def tangent_space_nested(self, p):
        """
        Returns the character of the tangent space of the nested Hilbert
        scheme at the fixed point `p` (assuming `p` is a point in it).
        """
        return (sum(self._tangent_space(lamb, lamb) for lamb in p) -
                sum(self._tangent_space(p[i], p[i+1]) for i in range(len(p)-1)))

    def _attracting(self, f, wts):
        r"""
        Returns the *attracting* part of `f`, using ``wts`` for
        how much to weigh each equiariant variable by.
        """
        vars = [self.t1, self.t2]
        if self.r > 1:
            vars += self.u

        # Maybe some variables are powers of generators.
        vars = [x.variables()[0] for x in vars if hasattr(x, 'variables')]

        is_attracting = lambda mon: sum(mon.degree(x)*wts[i]
                                        for i,x in enumerate(vars)) > 0
        return sum( (coeff*mon for coeff, mon in f if is_attracting(mon) ),
                    f.parent().zero() )

    def attracting(self, f, chamber=1):
        r"""
        Returns the *attracting* part of `f`, using ``chamber``.
        """
        N = 10000 # must exceed any n in M(r, n)
        wts = [N, -N] # degree of t = sqrt(t1/t2)
        wts += [j*N^2 for j in range(len(self.u)+1, 1, -1)]
        if chamber == -1:
            wts = [-w for w in wts]
        return self._attracting(f, wts)

    def walls(self, n):
        """
        Lists all walls for instanton number `n` in `[0, 1)`.
        """
        rats = [0] + sum(([ZZ(a)/b for a in range(1, b)]
                          for b in range(1, n+1)), [])
        return sorted(list(set(rats)))

    def tautological_bundle(self, p):
        """
        Returns the weight of the tautological bundle at fixed point `p`.
        """
        if p.level() == 1:
            p = [p] # otherwise enumerate(fp) is bad
        return sum((u*sum(self.t1^i*self.t2^j for i, j in partition.cells())
                    for u,partition in zip(self.u,p)), self._wR.zero())

    def O1_at(self, p):
        r"""
        Returns the weight of `\mathcal{O}(1)` at fixed point `p`.
        """
        return KTheory.determinant(self.tautological_bundle(p))

    def O(self, d, n):
        r"""
        Returns the matrix for multiplication by `\mathcal{O}(d)`.
        """
        return diagonal_matrix([self.O1_at(p)^d for p in self.fixed_points(n)])

    def stab(self, s):
        """
        Returns the K-theoretic stable basis of slope `s`.
        """
        return Instanton_StableBasis(self.sym, self.t1, self.t2, s)

    def _qde_wall_func_monomial(self, n, w, mu, q, z, B):
        r"""
        Computes the action of the operator `\mathbf{B}_w`
        (eq 66 in Smirnov-Okounkov) with quasimap `q` and Kahler parameter
        `z`, on the monomial `B[\mu]`, where `B` is some basis for
        symmetric functions.
        """
        w = QQ(w) # just in case
        numer, denom = w.numerator(), w.denominator()

        # Can discard all terms containing alpha_k for k > n.
        h, r = self.t1*self.t2, self.r
        coeffs = [0] # deg 0 term
        coeffs += [self.QTA.n(k) * h^(-k*r*denom/2) /
                   (1 - z^(-k*denom) * q^(k*numer) * h^(-k*r*denom/2))
                   for k in range(1, n+1)]

        res = B.zero()
        for k in range(n+1):
            for L in Compositions(k): # monomial of total degree k
                term = B(mu)
                for m in L:
                    term = self.QTA.alpha(w, m).fock(term, 1) # annihilate
                for m in L:
                    term = self.QTA.alpha(w, -m).fock(term, 1) # create
                res += prod(coeffs[m] for m in L) * term / factorial(len(L))
        return res

    def _qde_wall_func(self, n, w, f, q, z):
        r"""
        Computes the action of the operator `\mathbf{B}_w`
        (eq 66 in Smirnov-Okounkov), with quasimap `q` and Kahler parameter
        `z`, on the symmetric function `f`.
        """
        B = f.parent()
        return sum((cmu * self._qde_wall_func_monomial(n, w, mu, q, z, B)
                    for mu, cmu in f), B.zero())

    @cached_method
    def qde_wall(self, n, w, q, z, B=None):
        r"""
        Computes the operator `\mathbf{B}_w` (eq 66 in Smirnov-Okounkov)
        as a matrix in the specified basis `B` (default: fixed points),
        with quasimap `q` and Kahler parameter `z`.
        """
        if self.r != 1:
            raise NotImplementedError("only rank 1 implemented so far")
        if B is None:
            B = self.sym_mcd.Ht()
        fps = self.fixed_points(n)
        res = [self._qde_wall_func(n, w, B(lamb), q, z) for lamb in fps]
        return matrix([[elt.coefficient(lamb) for lamb in fps]
                       for elt in res]).transpose()

    @cached_method
    def qde(self, n, q, z):
        r"""
        Quantum difference operator for `\mathcal{O}(1)`, as a matrix
        in the fixed point basis, with Kahler parameter `z`.
        """
        return prod((self.qde_wall(n, w, q*z) for w in self.walls(n)),
                    self.O(1))

def quo_rem_with_slope(f, g, x, s):
    r"""
    Finds `r` such that `f = rg + q` where the degree of q lies within
    the degree of `g` shifted by the vector `s`. Degree is measured
    with respect to the variable `x`.

    Returns the pair `(r, q)`.
    """
    R = x.parent()
    deg = lambda mon: _nongen_degree(mon, x)
    terms = lambda h: [R(coeff*mon) for coeff, mon in h]

    r, q = R.zero(), R(f)
    if f == 0:
        return r, q

    g_terms = sorted(terms(g), key=lambda h: deg(h))
    g_min, g_max = g_terms[0], g_terms[-1]
    d_min, d_max = deg(g_min)+s, deg(g_max)+s
    while True:
        term = next((term for term in terms(q)
                     if deg(term) < d_min or deg(term) >= d_max), None)
        if not term:
            break
        d = deg(term)
        if d < d_min:
            adjustment = term / g_min
        elif d >= d_max:
            adjustment = term / g_max
        r += adjustment
        q -= adjustment * g

    return r, q

class Instanton_StableBasis(SymmetricFunctionAlgebra_generic):
    """
    K-theoretic stable basis for the Hilbert scheme.
    """
    def __init__(self, Sym, q, t, s):
        """
        Creates the ring of symmetric functions in the stable basis
        with slope `s`.
        """
        name = "Stable envelope in q=%s, t=%s with slope %s" % (q, t, s)
        SymmetricFunctionAlgebra_generic.__init__(self, Sym, basis_name=name,
                                                  prefix='Stab^{%s}'%s)
        self.q = q
        self.t = t
        if q.parent() != t.parent():
            raise ValueError("%s and %s not in same ring" % (q, t))
        self._wR = q.parent()

        self._Hilb = Instantons(1, q, t)
        self.slope = s

        self._s = Sym.s()
        self._Ht = Sym.macdonald(q=self.q, t=self.t).Ht()

        cat = HopfAlgebras(Sym.base_ring()).WithBasis()
        self.register_coercion(SetMorphism(Hom(self._Ht, self, cat), self._Ht_to_self))
        self._Ht.register_coercion(SetMorphism(Hom(self, self._Ht, cat), self._self_to_Ht))

    def polarization(self, mu):
        r"""
        Computes the polarization contribution to the diagonal at `\mu`.
        """
        h = self.q * self.t
        Thalf_plus = self._Hilb.attracting(self._Hilb.polarization(mu))
        return ((-1/sqrt(h))^(KTheory.rank(Thalf_plus)) /
                KTheory.determinant(Thalf_plus))
    
    @cached_method
    def _plethystic_schur(self, mu):
        r"""
        Computes the plethystically modified Schur function

        .. MATH::

            s_\mu\left[\frac{X}{1 - t^{-1}}\right]

        normalized to be precisely the slope zero stable envelope.
        """
        q, t, h = self.q, self.t, self.q*self.t

        res = self._s(mu).theta_qt(0, 1/t)
        diagonal = self._Ht(res).coefficient(mu)

        Tplus = self._Hilb.attracting(self._Hilb.tangent_space(mu))
        wanted_diagonal = self.polarization(mu) * \
                          KTheory.measure_unsymmetrized(Tplus)

        c = wanted_diagonal / diagonal
        normalization = self._wR(c.numerator()) / self._wR(c.denominator())
        if not normalization.is_unit():
            raise ValueError("something went very wrong")

        return normalization * res

    def _apply_to_func(self, F, f):
        """
        Applies a functional `F`, which acts on monomials, to the
        polynomial or matrix of polynomials `f`.
        """
        if is_Matrix(f):
            return f.apply_map(lambda g: self._apply_to_func(F, g))
        elif f in ZZ:
            return f * F(1)
        else:
            return sum(coeff * F(mon) for coeff, mon in f)

    def _q1q2_to_qt(self, f):
        """
        Converts `f` from the coordinate basis `q_1` and `q_2`. to the
        `q=sqrt(q_1q_2)` and `t=sqrt(q_1/q_2)` basis.
        """
        def to_qt(mon):
            q, t = self.q, self.t
            a, b = _nongen_degree(mon, q), _nongen_degree(mon, t)
            return q^((a+b)/2) * t^((a-b)/2)
        return self._apply_to_func(to_qt, f)

    def _qt_to_q1q2(self, f):
        """
        Converts `f` from the `q=sqrt(q_1q_2)` and `t=sqrt(q_1/q_2)` basis
        to the coordinate basis `q_1` and `q_2`.
        """
        def to_q1q2(mon):
            q, t = self.q, self.t
            a, b = _nongen_degree(mon, q), _nongen_degree(mon, t)
            return q^(a+b) * t^(a-b)
        return self._apply_to_func(to_q1q2, f)
    
    def _initial_stab_matrix(self, n):
        """
        Initial change of basis matrix from self to localized fixed point
        basis, for instanton number `n`. It is given by plethystically
        modified Schur functions and is equal to the slope-zero stable basis.
        """
        fps = self._Hilb.fixed_points(n)
        init = [self._Ht(self._plethystic_schur(p)) for p in fps]
        laurent = lambda g: self._wR(g.numerator()) / g.denominator()
        return (matrix([[g.coefficient(p) for p in fps] for g in init]) /
                self._localization_matrix(n)).apply_map(laurent)

    @cached_method
    def _stab_matrix(self, n):
        """
        Change of basis matrix from self to localized fixed point basis,
        for instanton number `n`.
        """
        fps = self._Hilb.fixed_points(n)
        stab = self._q1q2_to_qt(self._initial_stab_matrix(n))

        # Gram-Schmidt to correct off-diagonal entries in each row,
        # using polynomial long division to satisfy degree constraints
        # in the anti-diagonal t variable.
        tgen = self.t^(1/2)
        slopes = [_nongen_degree(self._q1q2_to_qt(self._Hilb.O1_at(p)), tgen)
                  for p in fps]
        for i in range(len(fps)):
            for j in range(i-1, -1, -1):
                f, g = stab[i][j], stab[j][j]
                s = self.slope * (slopes[j] - slopes[i])
                r, _ = quo_rem_with_slope(f, g, tgen, s)
                stab.add_multiple_of_row(i, j, -r)

        return self._qt_to_q1q2(stab)

    @cached_method
    def _localization_matrix(self, n):
        r"""
        Change of basis matrix from localized fixed point basis `I` to
        the unlocalized fixed point basis `\tilde I`, which in the ring
        of symmetric functions is the modified Macdonald basis `\tilde H`.
        The precise relation is

        .. MATH::

            [I_\lambda] = \frac{[\tilde I_\lambda]}{T_\lambda \text{Hilb}}.
        """
        THilb = lambda mu: KTheory.measure_unsymmetrized(self._Hilb.tangent_space(mu))
        return diagonal_matrix(THilb(mu) for mu in self._Hilb.fixed_points(n))

    @cached_method
    def _self_to_Ht_matrix(self, n):
        """
        Change of basis matrix from self to fixed point basis,
        for instanton number `n`.
        """
        return (self._stab_matrix(n)*self._localization_matrix(n)).transpose()

    def _self_monomial_to_Ht(self, mu):
        r"""
        Returns the stable envelope of `\mu` in the fixed point basis.
        """
        n = mu.size()
        fps = self._Hilb.fixed_points(n)
        k = fps.index(mu)
        vec = self._self_to_Ht_matrix(n).column(k)
        return sum(c * self._Ht(p) for c, p in zip(vec, fps))

    def _self_to_Ht(self, f):
        """
        Convert a symmetric function `f` in the stable basis into the
        fixed point basis.
        """
        return sum((cmu * self._self_monomial_to_Ht(mu) for mu, cmu in f),
                   self._Ht.zero())

    @cached_method
    def _Ht_to_self_matrix(self, n):
        """
        Change of basis matrix from the fixed point basis to self,
        for instanton number `n`.
        """
        return self._self_to_Ht_matrix(n).inverse()

    def _Ht_monomial_to_self(self, mu):
        r"""
        Returns the (unlocalized) fixed point `\mu` in the stable basis.
        """
        n = mu.size()
        fps = self._Hilb.fixed_points(n)
        k = fps.index(mu)
        vec = self._Ht_to_self_matrix(n).column(k)
        return sum(c * self(p) for c, p in zip(vec, fps))

    def _Ht_to_self(self, f):
        """
        Convert a symmetric function `f` in the fixed point basis into
        the stable basis.
        """
        return sum((cmu * self._Ht_monomial_to_self(mu) for mu, cmu in f),
                   self.zero())

    class Element(SymmetricFunctionAlgebra_generic.Element):
        pass

############################################################
## Some useful functions for working with respect to
## powers of generators of polynomial rings.

def _nongen(x):
    """
    If `x = x_0^m` where `x_0` is a generator in its parent, return
    the pair `(m, x_0)`.
    """
    if len(x.variables()) != 1:
        raise ValueError("%s is not a power of a generator" % x)
    xgen = x.variables()[0]
    return x.degree(xgen), xgen

def _nongen_degree(f, x):
    """
    Returns the degree of `x` in `f`, where `x` is some power of a
    generator in the parent ring of `f`.
    """
    if x not in f.parent():
        return 0
    m, xgen = _nongen(x)
    return QQ(f.degree(xgen)) / m
