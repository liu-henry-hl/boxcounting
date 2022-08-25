"""
DT and PT (bare) vertices.
"""
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation
from itertools import chain, combinations

load("setup.sage") # contains Default and KTheory
load("edge.sage")

load("partition_3d.sage")
load("pt_configuration.sage")

class BareVertex(UniqueRepresentation):
    r"""
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
    def _term(self, k, descendant=None):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``.
        """
        R = Default.boxcounting_ring.base_ring()
        x, y, z = Default.x, Default.y, Default.z
        if descendant is None:
            descendant = lambda f: R.one()

        return sum(R(self._ct.measure(self.__class__.weight(PP))) *
                   R(descendant(PP._unnormalized_character(x,y,z)))
                   for PP in self._partitions.with_num_boxes(k))

    def term(self, k, x=Default.x, y=Default.y, z=Default.z, descendant=None):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``, in variables `x, y, z`.
        """
        res = self._term(k, descendant)
        if (x, y, z) != (Default.x, Default.y, Default.z):
            res = res.subs(x=x, y=y, z=z)
        return res

    @cached_method
    def series_unreduced(self, prec, x=Default.x, y=Default.y, z=Default.z, q=Default.q, descendant=None):
        r"""
        Return the *unreduced* series corresponding to ``self``,
        indexed by `-q`. The series will have precision ``prec``,
        i.e. will contain exactly ``prec`` terms.
        """
        min_vol = self._partitions.minimal_volume()
        if prec <= 0:
            return q.parent().zero().add_bigoh(min_vol)

        res = sum(self.term(k, x,y,z, descendant) * (-q)^(k+min_vol)
                  for k in range(prec))
        return res.add_bigoh((prec + min_vol)*q.valuation())

    @cached_method
    def series(self, prec, x=Default.x, y=Default.y, z=Default.z, q=Default.q, descendant=None):
        r"""
        Return the series corresponding to ``self``, indexed by `-q`.
        The series will have precision ``prec``, i.e. will contain
        exactly ``prec`` terms.
        """
        res = self.series_unreduced(prec, x,y,z, q, descendant)
        if prec <= 0:
            return res # no need to normalize by "zero"
        else:
            deg0 = self.__class__([], [], [], ct=self._ct)
            return res / deg0.series_unreduced(prec, x,y,z, q)

def _adjoin_variables_to_LPR(LPR, m, name='u'):
    r"""
    Adjoins `m` new variables to the LaurentPolynomialRing `R` with
    ``name``. Return the ring and the new variables.
    """
    original_vars = list(LPR.variable_names())
    new_vars = [name+'%s' % i for i in range(m)]
    new_ring = LaurentPolynomialRing(LPR.base_ring(), new_vars + original_vars)
    return new_ring, new_ring.gens()[:m]

class BareVertexPT(UniqueRepresentation):
    r"""
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
                for _ in range(abs(coeff)): # multiplicity
                    Ntwisted.append( (P_exps, R({wt_exps: sign(coeff)})) )
        return N, Ntwisted

    def _integrate_over_fixed_loci(self, f, integrand=None, descendant=None, u=None):
        r"""
        Computes the integral over `(\mathbb{P}^1)^m` of the measure
        of `f^\vee`, with integrand ``integrand`` using twisting variables `u`.
        We assume that if `u` is unspecified, then it is the first `m`
        variables in the ring containing ``integrand``.

        Here `f` must be a list of pairs ``(deg, wt)`` where:

        - ``deg`` is a tuple `(d_1, \ldots, d_m)` of exponents, representing
          a twist by the bundle `\mathcal{O}(d_1, \ldots, d_m)`;

        - ``wt`` is a character.
        """
        R = Default.boxcounting_ring.base_ring()
        if integrand is None:
            integrand = R.one()
        if descendant is None:
            descendant = lambda f: 1

        if len(f) == 0:
            return R(descendant(integrand))

        dims = set(len(deg) for deg, _ in f) # number of P1 factors
        if len(dims) > 1:
            raise ValueError("all twists must have the same length: %s" % f)
        m = dims.pop()

        # Localization weights q_i, for each P1 that appears.
        wt_ring = f[0][1].parent() # weight ring
        qR, q = _adjoin_variables_to_LPR(wt_ring, m, name='q')

        uR = integrand.parent()
        if u is None:
            u = uR.gens()[:m]

        def powerset(s):
            return chain.from_iterable(combinations(s, r) for \
                                       r in range(len(s)+1))
        res = 0
        for fixed_pt in powerset(range(m)):
            # Localization on (P1)^m
            L1, L2 = fixed_pt, set(range(m)) - set(fixed_pt)
            qq = [(q[i] if i in L2 else 1) for i in range(m)]
            term = sum(1/q[i] for i in L1) + sum(q[i] for i in L2) + \
                   sum(wt * prod(qi^d for qi, d in zip(qq, deg))
                       for deg, wt in f)
            integrand_res = Hom(uR, qR)(qq + list(wt_ring.gens()))(integrand)
            res += self._ct.measure(term) * descendant(integrand_res)

        return R(res.subs({qi : self._ct.from_monomial(1) for qi in q}))

    @cached_method
    def _term(self, k, descendant=None):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``.
        """
        if descendant is None:
            descendant = lambda f: 1
        R = Default.boxcounting_ring.base_ring()
        x, y, z = Default.x, Default.y, Default.z
        res = R.zero()
        for PP in self._configs.with_num_boxes(k):
            N, Ntwisted = self.__class__.contribution(PP)
            integrand = PP._unnormalized_character(x,y,z)
            contrib = self._integrate_over_fixed_loci(Ntwisted, integrand, descendant)
            res += R(self._ct.measure(N)) * contrib
        return res

    def term(self, k, x=Default.x, y=Default.y, z=Default.z, descendant=None):
        r"""
        Returns the `k`-th non-zero term in the q-series
        corresponding to ``self``, in variables `x, y, z`.
        """
        res = self._term(k, descendant)
        if (x, y, z) != (Default.x, Default.y, Default.z):
            R = Default.boxcounting_ring.base_ring()
            res = res.subs(x=R(x), y=R(y), z=R(z))
        return res

    @cached_method
    def series(self, prec, x=Default.x, y=Default.y, z=Default.z, q=Default.q, descendant=None):
        r"""
        Return the series corresponding to ``self``, indexed by `-q`.
        The series will have precision ``prec``, i.e. will contain
        exactly ``prec`` terms.
        """
        min_vol = self._min_vol
        if prec <= 0:
            return Default.boxcounting_ring.zero().add_bigoh(min_vol)

        res = sum(self.term(k, x,y,z, descendant) * (-q)^(k+min_vol)
                  for k in range(prec))
        return res.add_bigoh((prec + min_vol)*q.valuation())
