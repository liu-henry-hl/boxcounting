"""
DT and PT (bare) vertices.
"""
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation
from itertools import chain, combinations

load("partition_3d.sage")
load("pt_configuration.sage")

load("setup.sage") # contains Default and KTheory
load("edge.sage")

class BareVertex(UniqueRepresentation):
    """
    Equivariant DT (bare) vertex with three given legs.

    The leg `\lambda` has rows along the `y` axis and columns along
    the `z` axis. In other words, `\lambda_1` is its length in the
    `y` direction. The other two legs are oriented in the cyclically
    symmetric way.
    """
    @staticmethod
    def __classcall_private__(cls, lamb, mu, nu, ct=KTheory):
        # UniqueRepresentation objects cannot have mutable parameters.
        # So we need to make lamb, mu, nu into Partitions.
        lamb = Partition(lamb)
        mu = Partition(mu)
        nu = Partition(nu)
        return cls.__classcall__(cls, lamb, mu, nu, ct)

    def __init__(self, lamb, mu, nu, ct):
        self._partitions = Partitions3d(lamb, mu, nu)
        self._ct = ct

    def __repr__(self):
        return "Bare vertex with legs %s using %s" \
            % (self._partitions.legs(), self._ct.name)

    @staticmethod
    def weight(partition, x=Default.x, y=Default.y, z=Default.z):
        r"""
        Computes the (K-theoretic) vertex weight of ``partition`` using
        variables `x`, `y`, `z`. Always returns a Laurent polynomial in
        these variables.

        This is the function `V_{\alpha}` in MNOP I.

        EXAMPLES::

            sage: box = Partition3d([(0, 0, 0)])
            sage: BareVertex.weight(box)
            z^-1 + y^-1 + x^-1 - y^-1*z^-1 - x^-1*z^-1 - x^-1*y^-1
        """
        lamb, mu, nu = partition.legs()

        # Q = Qnum / (1-x)(1-y)(1-z) 
        Qnum = partition._unnormalized_character(x, y, z)

        # \bar{Q} = Qnum_inv / (1-x^-1)(1-y^-1)(1-z^-1)
        Qnum_inv = partition._unnormalized_character(x^-1, y^-1, z^-1)

        # F = Q - \bar{Q}/xyz + Q \bar{Q} (1-x)(1-y)(1-z) / xyz
        Fnum = Qnum + Qnum_inv - Qnum * Qnum_inv

        # Pole subtraction: V = F + F_ab(y, z)/(1 - x) + (cyclic perms.)
        Fnum += Edge.raw_weight(lamb, y, z) * (1-y)*(1-z)
        Fnum += Edge.raw_weight(mu, z, x) * (1-z)*(1-x)
        Fnum += Edge.raw_weight(nu, x, y) * (1-x)*(1-y)

        # Check we can divide out (1-x)(1-y)(1-z)
        quo, rem = Fnum.quo_rem( (1-x)*(1-y)*(1-z) )
        if rem != 0:
            raise ValueError("vertex weight computation went wrong")

        return quo

    @cached_method
    def term(self, k):
        r"""
        Returns the ``k``th non-zero term in the q-series
        corresponding to ``self``.
        """
        R = Default.boxcounting_ring.base_ring()
        return sum(R(self._ct.measure(self.__class__.weight(PP)))
                   for PP in self._partitions.with_num_boxes(k))

    @cached_method
    def series_unreduced(self, prec, q=Default.q):
        r"""
        Return the *unreduced* series corresponding to ``self``,
        indexed by `-q`. The series will have precision ``prec``,
        i.e. will contain exactly ``prec`` terms.
        """
        min_vol = self._partitions.minimal_volume()
        if prec <= 0:
            return Default.boxcounting_ring.zero().add_bigoh(min_vol)

        res = sum(self.term(k) * (-q)^(k+min_vol) for k in xrange(prec))
        return res.add_bigoh(prec+min_vol)

    @cached_method
    def series(self, prec, q=Default.q):
        r"""
        Return the series corresponding to ``self``, indexed by `-q`.
        The series will have precision ``prec``, i.e. will contain
        exactly ``prec`` terms.
        """
        deg0 = self.__class__([], [], [], ct=self._ct)
        return (self.series_unreduced(prec,q) / deg0.series_unreduced(prec,q))

def _adjoin_variables_to_LPR(LPR, m, name='u'):
    r"""
    Adjoins `m` new variables to the LaurentPolynomialRing `R` with
    ``name``. Return the ring and the new variables.
    """
    original_vars = list(LPR.variable_names())
    new_vars = [name+'%s' % i for i in xrange(m)]
    new_ring = LaurentPolynomialRing(LPR.base_ring(), new_vars + original_vars)
    return new_ring, new_ring.gens()[:m]

class BareVertexPT(UniqueRepresentation):
    """
    Equivariant PT (bare) vertex with three given legs.

    The leg `\lambda` has rows along the `y` axis and columns along
    the `z` axis. In other words, `\lambda_1` is its length in the
    `y` direction. The other two legs are oriented in the cyclically
    symmetric way.
    """
    @staticmethod
    def __classcall_private__(cls, lamb, mu, nu, ct=KTheory):
        # UniqueRepresentation objects cannot have mutable parameters.
        # So we need to make lamb, mu, nu into Partitions.
        lamb = Partition(lamb)
        mu = Partition(mu)
        nu = Partition(nu)
        return cls.__classcall__(cls, lamb, mu, nu, ct)

    def __init__(self, lamb, mu, nu, ct):
        self._configs = PTConfigurations(lamb, mu, nu)
        self._ct = ct
        self._min_vol = Partitions3d(lamb, mu, nu).minimal_volume()

    def __repr__(self):
        return "PT bare vertex with legs %s using %s" \
            % (self._configs.legs(), self._ct.name)

    @staticmethod
    def weight(config, x=Default.x, y=Default.y, z=Default.z, KRing=None):
        r"""
        Computes the PT vertex weight of ``configuration`` using variables
        `x`, `y`, `z`. Line bundles over products of `\mathbb{P}^1` are
        represented by generators of ``KRing`` (default variables: `u_i`).

        Always returns a Laurent polynomial in these variables.

        This is the function `V_{\alpha}` in Pandharipande-Thomas.

        EXAMPLES::

            TODO
        """
        lamb, mu, nu = config.legs()
        m = config.dimension() # number of P1 factors
        if KRing is None:
            KRing, u = _adjoin_variables_to_LPR(x.parent(), m)

        # Poincare polynomial: Q = (1+P) / (1-x)(1-y)(1-z)
        P = config._unnormalized_character(x, y, z, KRing=KRing) - 1
        Pinv = P.subs({t : 1/t for t in P.parent().gens()})

        # F = (1 - P \bar{P}) / (1-x)(1-y)(1-z)
        Fnum = 1 - P*Pinv

        # Pole subtraction: V = F + F_ab(y, z)/(1 - x) + (cyclic perms.)
        Fnum += Edge.raw_weight(lamb, y, z) * (1-y)*(1-z)
        Fnum += Edge.raw_weight(mu, z, x) * (1-z)*(1-x)
        Fnum += Edge.raw_weight(nu, x, y) * (1-x)*(1-y)

        # Check we can divide out (1-x)(1-y)(1-z)
        quo, rem = Fnum.quo_rem( (1-x)*(1-y)*(1-z) )
        if rem != 0:
            raise ValueError("vertex weight computation went wrong")

        return quo

    @staticmethod
    def contribution(config, x=Default.x, y=Default.y, z=Default.z):
        """
        Returns the contribution of a PT configuration, split into:

        - the untwisted normal weights

        - the twisted normal weights, with their degrees
        """
        m = config.dimension() # number of P1 factors
        R = x.parent()
        KRing, u = _adjoin_variables_to_LPR(R, m)

        V = BareVertexPT.weight(config, x, y, z, KRing)
        V -= sum(2*ui - 1 for ui in u) # tangent weights of the (P1)^m
        
        N, Ntwisted = R.zero(), []
        for exps, coeff in V.dict().items():
            P_exps, wt_exps = exps[:m], exps[m:]
            if all(e == 0 for e in P_exps):
                N += R({wt_exps: coeff})
            else:
                for _ in xrange(abs(coeff)): # multiplicity
                    Ntwisted.append( (P_exps, R({wt_exps: sign(coeff)})) )
        return N, Ntwisted

    def _integrate_over_fixed_loci(self, f):
        r"""
        Computes the integral oer `(\mathbb{P}^1)^m` of the K-theory
        class `f^\vee`.

        The element `f` must be a list of pairs ``(deg, wt)`` where:

        - ``deg`` is a tuple `(d_1, \ldots, d_m)` of exponents, representing
          a twist by the bundle `\mathcal{O}(d_1, \ldots, d_m)`;

        - ``wt`` is a character.
        """
        if len(f) == 0:
            return 1

        dims = set(len(deg) for deg, _ in f) # number of P1 factors
        if len(dims) > 1:
            raise ValueError("all twists must have the same length: %s" % f)
        m = dims.pop()

        # Localization weights q_i, for each P1 that appears.
        wt_ring = f[0][1].parent() # weight ring
        _, q = _adjoin_variables_to_LPR(wt_ring, m, name='q')

        def powerset(s):
            return chain.from_iterable(combinations(s, r) for \
                                       r in xrange(len(s)+1))
        res = 0
        for fixed_pt in powerset(range(m)):
            # Localization on (P1)^m
            L1, L2 = fixed_pt, set(xrange(m)) - set(fixed_pt)
            term = sum(1/q[i] for i in L1) + sum(q[i] for i in L2) + \
                   sum(wt * prod(q[i]^(deg[i]) for i in L2) for deg, wt in f)
            res += self._ct.measure(term)

        R = Default.boxcounting_ring.base_ring()
        return R(res.subs({qi : 1 for qi in q}))

    @cached_method
    def _term(self, k):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``.
        """
        R = Default.boxcounting_ring.base_ring()
        res = R.zero()
        for PP in self._configs.with_num_boxes(k):
            N, Ntwisted = self.__class__.contribution(PP)
            contrib = self._integrate_over_fixed_loci(Ntwisted)
            res += R(self._ct.measure(N)) * contrib
        return res

    def term(self, k, x=Default.x, y=Default.y, z=Default.z):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``, in variables `x, y, z`.
        """
        res = self._term(k)
        if (x, y, z) != (Default.x, Default.y, Default.z):
            R = Default.boxcounting_ring.base_ring()
            res = res.subs(x=R(x), y=R(y), z=R(z))
        return res

    def series(self, prec, x=Default.x, y=Default.y, z=Default.z, q=Default.q):
        r"""
        Return the series corresponding to ``self``, indexed by `-q`.
        The series will have precision ``prec``, i.e. will contain
        exactly ``prec`` terms.
        """
        min_vol = self._min_vol
        if prec <= 0:
            return Default.boxcounting_ring.zero().add_bigoh(min_vol)

        res = sum(self.term(k,x,y,z) * (-q)^(k+min_vol) for k in xrange(prec))
        return res.add_bigoh(prec+min_vol)
