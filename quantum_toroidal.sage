"""
Quantum toroidal algebra.
"""
from sage.categories.algebras import Algebras
from sage.categories.cartesian_product import cartesian_product
from sage.sets.family import Family
from sage.combinat.free_module import CombinatorialFreeModule
from sage.monoids.indexed_free_monoid import IndexedFreeAbelianMonoid
from sage.modules.with_basis.indexed_element import IndexedFreeModuleElement
from sage.rings.polynomial.laurent_polynomial_ring import is_LaurentPolynomialRing

class QuantumToroidalAlgebraElement(IndexedFreeModuleElement):
    """
    An element of the quantum toroidal algebra.
    """
    def rotate(self, M):
        r"""
        Act on ``self`` by a `2 \times 2` integer matrix `M`.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: M = matrix([[1,2], [3,-5]]); M
            [ 1  2]
            [ 3 -5]
            sage: QTA.e(1,0).rotate(M)
            e(1,3)
        """
        M = matrix(ZZ, 2,2, M) # ensure M is a 2x2 integer matrix
        return self.map_basis(lambda a: M * (ZZ^2)(a))
        
    def map_basis(self, f):
        """
        Act by `f` on indices. The functional `f` must take and produce
        a list/tuple in `\mathbb{Z}^2`.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: f = lambda (a1, a2): (a1*3, a2+1)
            sage: QTA.e(1,0).map_basis(f)
            e(3,1)
        """
        def map_monomial(x):
            mons = x.parent()
            return prod(mons.gen(tuple(f(k[:2])) + (k[2],))
                        for k in x.to_word_list())
        return self.map_support(map_monomial)

    def is_term(self):
        r"""
        Returns ``True`` if ``self`` is a single term.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: x = (1 - QTA.t1) * QTA.e(1,0); x
            (-t1+1)*e(1,0)
            sage: x.is_term()
            True
            sage: x = QTA.e(1,0) + QTA.e(0,1); x
            e(1,0) + e(0,1)
            sage: x.is_term()
            False
            sage: QTA.one().is_term()
            True
            sage: QTA.zero().is_term()
            False
        """
        return len(self) == 1

    def is_unit(self):
        r"""
        Return ``True`` if ``self`` is a unit.

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.e(1,0).is_unit()
            False
            sage: x = (1 - QTA.t1) * QTA.K(1,2); x
            (-t1+1)*K(1,2)
            sage: x.is_unit()
            True
        """
        if self.is_term():
            ks = self.support_of_term().to_word_list()
            return len(ks) == 0 or (len(ks) == 1 and ks[0][2] == 'K')
        else:
            return False

    def __invert__(self):
        r"""
        Return the inverse of ``self`` if it exists.

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: ~QTA.e(1,0)
            Traceback (most recent call last):
            ...
            ValueError: e(1,0) is not a unit in Quantum toroidal algebra
            sage: x = (1 - QTA.t1) * QTA.K(1,2); x
            (-t1+1)*K(1,2)
            sage: ~x
            (1/(-t1+1))*K(-1,-2)
        """
        R = self.parent()
        if self.is_unit():
            res = R.one()
            ks = self.support_of_term().to_word_list()
            if len(ks) == 1:
                res = R.K(-ks[0][0], -ks[0][1])
            return ~self.coefficients()[0] * res
        else:
            raise ValueError("%s is not a unit in %s" % (self, R))

    def _isolate_e_term(self, x):
        r"""
        Given a monomial `x` consisting of only `e`'s, return
        the coefficient of `x` in ``self`` and the sum of all
        other terms. The coefficient may involve `K`'s.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: x = (QTA.t1+QTA.K(1,2))*QTA.e(1,0) + QTA.e(1,0)*QTA.e(0,1); x
            t1*e(1,0) + K(1,2)*e(1,0) + e(1,0)*e(0,1)
            sage: x._isolate_e_term(QTA.e(1,0))
            (t1*u + K(1,2), e(1,0)*e(0,1))
        """
        if not x.is_term():
            raise ValueError("%s is not a single term" % x)

        kx = x.support_of_term().to_word_list()
        if len(kx) > 0 and kx[0][2] == 'K':
            raise ValueError("%s doesn't consist only of e terms" % x)

        R = self.parent()
        coeff, rest = R.zero(), R.zero()
        for term in self.terms():
            K, ky = R.one(), term.support_of_term().to_word_list()
            if len(ky) > 0 and ky[0][2] == 'K':
                K, ky = R.K(ky[0][:2]), ky[1:]
            if sorted(ky) == sorted(kx):
                coeff += term.coefficients()[0] * K
            else:
                rest += term

        return coeff, rest

    def _act_on_(self, x, is_left):
        r"""
        Defines the action of ``self`` on `x`. The argument ``is_left``
        specifies whether ``self`` acts on the left or right.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: Sym = SymmetricFunctions(R.fraction_field())
            sage: P = Sym.macdonald(q=R.0, t=R.1).Ht()
            sage: QTA.e(1,2) * P[1]
            McdHt[]
        """
        if x in SymmetricFunctions(x.base_ring()):
            # Act on symmetric functions using Fock representation
            # with evaluation parameter 1.
            return self.fock(x, is_left, eval_param=1)
        else:
            return IndexedFreeModuleElement._act_on_(self, x, is_left)

    def fock(self, x, is_left, eval_param):
        r"""
        Act by ``self`` on a symmetric polynomial `x` via the
        Fock representation with evaluation parameter ``eval_param``.

        EXAMPLES::

            sage: R = ZZ['t1','t2','u']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: Sym = SymmetricFunctions(R.fraction_field())
            sage: P = Sym.macdonald(q=R.0, t=R.1).Ht()
            sage: QTA.e(1,2).fock(P[1], True, R.2)
            1/u^2*McdHt[]
        """
        res = sum(coeff * self.parent().fock_rep(mon, x, is_left, eval_param)
                  for mon, coeff in self.monomial_coefficients().items())
        return x.parent()(res) # convert back to original basis

class QuantumToroidalAlgebra(CombinatorialFreeModule):
    """
    Quantum toroidal algebra `U_q(\hat{\hat{\mathfrak{gl}}}_1)`.
    """
    Element = QuantumToroidalAlgebraElement

    def __init__(self, t1, t2):
        """
        Creates the quantum toroidal algebra.
        """
        if t1.parent() != t2.parent():
            raise ValueError("%s and %s not in same ring" % (t1, t2))

        # Indexing set, consisting of all elements e(a,b) and K(a,b)
        S = cartesian_product([ZZ, ZZ, ['e','K']])
        monomials = IndexedFreeAbelianMonoid(S, prefix='', bracket=False,
                                             sorting_key=self._monoid_key)

        # Create the algebra as a free module over the indexing set
        R = t1.parent()
        if is_LaurentPolynomialRing(R):
            R = R.polynomial_ring()
            t1, t2 = R(t1), R(t2)
        RR = R.fraction_field()
        cat = Algebras(RR).WithBasis().Filtered()
        CombinatorialFreeModule.__init__(self, RR, monomials,
                                         prefix='', bracket=False,
                                         latex_bracket=False,
                                         sorting_key=self._monomial_key,
                                         category=cat)
        self.t1, self.t2 = t1, t2

    def _basis_key(self, k):
        """
        Key for ordering elements `e_a` and `K_a` within monomials.

        All elements `K_a` are put in front. The elements `e_a` are
        ordered by increasing slope, and normal ordered within each slope.
        Each monomial corresponds to a convex path in `\mathbb{Z}^2`.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA._basis_key((0, 2, 'K'))
            ('K', +Infinity, 0)
            sage: QTA._basis_key((0, -1, 'e'))
            ('e', -Infinity, 0)
            sage: QTA._basis_key((2, -3, 'e'))
            ('e', -3/2, -2)
        """
        a1, a2, elt = k
        if a1 == 0:
            return (elt, sign(a2)*oo, -a1)
        else:
            return (elt, a2/a1, -a1)

    def _monoid_key(self, x):
        r"""
        Key function for the underlying monoid of ``self``.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: I = QTA._indices.gens()
            sage: I[1,-1,'e'] * I[0,-1,'e'] * I[4,0,'K'] # indirect doctest
            (4, 0, 'K')*(0, -1, 'e')*(1, -1, 'e')
        """
        return self._basis_key(x[0])

    def _monomial_key(self, x):
        r"""
        Compute the key for the monomial ``x`` so that terms are ordered
        by increasing degree (and decreasing convexity within each degree).

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.e(0,1) * QTA.e(1,0) # indirect doctest
            -e(1,1) + e(1,0)*e(0,1)
        """
        return (len(x), [self._basis_key(l) for l in x.to_word_list()])

    def _repr_(self):
        r"""
        Return a string representation of ``self``.
        """
        return "Quantum toroidal algebra (t1=%s and t2=%s)" % (self.t1,self.t2)

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.
        """
        return "U_{q}(\widehat{\widehat{\mathfrak{gl}}}_1)"

    def _repr_term(self, m):
        r"""
        Return a string representation of the term indexed by ``m``.

        The unit of the algebra is denoted by ``u``.
        """
        if m == self.one_basis():
            return 'u'
            
        def to_str(x):
            (a1, a2, res), e = x
            res = res + "(%s,%s)" % (a1, a2)
            if e > 1:
                res = res + "^%s" % e
            return res
        return '*'.join(to_str(x) for x in m._sorted_items())

    def _latex_term(self, m):
        r"""
        Return a latex representation of the term indexed by ``m``.
        """
        if m == self.one_basis():
            return "\\mathbb{1}"

        def to_str(x):
            (a1, a2, res), e = x
            res = res + "_{(%s,%s)}" % (a1, a2)
            if e > 1:
                res = res + "^{%s}" % e
            return res
        return ' '.join(to_str(x) for x in m._sorted_items())

    def algebra_generators(self):
        r"""
        Return the algebra generators of ``self``.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.algebra_generators()
            Lazy family (generator map(i))_{i in The Cartesian product
             of (Integer Ring, Integer Ring, {'e', 'K'})}
        """
        G = self._indices.gens()
        return Family(self._indices._indices, lambda x: self.monomial(G[x]),
                      name="generator map")

    gens = algebra_generators

    def e(self, a1, a2=None):
        r"""
        The generator `e_{(a_1, a_2)}` of the algebra. By convention,
        `e_{(0,0)}` is the unit of the algebra.

        If ``a2`` is unspecified, ``a1`` should be a pair of integers.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.e(0,1)
            e(0,1)
            sage: QTA.e([0,1])
            e(0,1)
            sage: QTA.e(0,0)
            u
        """
        if a2 is None:
            a1, a2 = tuple((ZZ^2)(a1))
        if (a1, a2) == (0, 0):
            return self.one()
        else:
            return self.gens()[a1, a2, 'e']

    def K(self, a1, a2=None):
        r"""
        The generator `K_{(a_1, a_2)}` of the algebra. By convention,
        `K_{(0,0)}` is the unit of the algebra.

        If ``a2`` is unspecified, ``a1`` should be a pair of integers.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.K(0,1)
            K(0,1)
            sage: QTA.K([0,1])
            K(0,1)
            sage: QTA.K(0,0)
            u
        """
        if a2 is None:
            a1, a2 = tuple((ZZ^2)(a1))
        if (a1, a2) == (0, 0):
            return self.one()
        else:
            return self.gens()[a1, a2, 'K']

    def _an_element_(self):
        r"""
        Return an element of ``self``.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.an_element()
            e(-1,0) + t1*e(1,1) - 2*e(0,-1)*e(1,0)
        """
        return (self.e(-1,0) - 2*self.e(0,-1)*self.e(1,0) +
                self.base_ring().an_element()*self.e(1,1))

    def bracket(self, x, y):
        """
        Returns the commutator `[x, y]`.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.bracket(QTA.e(1,0), QTA.e(1,1))
            e(2,1)
            sage: QTA.bracket(QTA.e(-1,0), QTA.e(1,1))
            -K(1,0)*e(0,1)
        """
        return x*y - y*x

    commutator = bracket

    def one_basis(self):
        """
        Return the basis element indexing `1`.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: ob = QTA.one_basis(); ob
            1
            sage: ob.parent()
            Free abelian monoid indexed by The Cartesian product
             of (Integer Ring, Integer Ring, {'e', 'K'})
        """
        return self._indices.one()

    def n(self, d):
        """
        Return the coefficient `n_d`, defined as

        .. MATH::

            n_d = \frac{(1 - t_1^d)(1 - t_2^d)(1 - \hbar^-d)}{d}

        where `\hbar = t_1 t_2`.
        """
        return ((1 - self.t1^d) * (1 - self.t2^d) *
                (1 - self.t1^-d * self.t2^-d)) / d

    @cached_method
    def Psi(self, a1, a2=None):
        """
        Returns the element `\Psi_{(a_1, a_2)}`, where

        .. MATH::

            \sum_{k=0}^\infty \Psi_{k \vec a} z^k = \exp\left(\sum_{m=1}^\infty n_m e_{m \vec a} z^m\right)

        for lattice points `\vec a` with coprime coordinates.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.Psi(1,2) == QTA.n(1) * QTA.e(1,2)
            True
            sage: QTA.Psi(2,2) == QTA.n(2)*QTA.e(2,2) + QTA.n(1)^2/2*QTA.e(1,1)^2
            True
        """
        if a2 is None:
            a1, a2 = tuple((ZZ^2)(a1))
        if a1 == 0 and a2 == 0:
            return self.one()
        
        k = gcd(a1, a2)
        a1_red, a2_red = a1 // k, a2 // k

        return sum((prod(self.n(m)*self.e(m*a1_red, m*a2_red) for m in L) /
                    factorial(len(L))) for L in Compositions(k))
        
    @cached_method
    def product_on_basis(self, lhs, rhs):
        r"""
        Return the product of the two (module) basis elements
        ``lhs`` and ``rhs``.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.e(1,0) * QTA.e(0,1)
            e(1,0)*e(0,1)
            sage: QTA.e(0,1) * QTA.e(1,0)
            -e(1,1) + e(1,0)*e(0,1)
        """
        # Some trivial base cases
        if lhs == self.one_basis():
            return self.monomial(rhs)
        if rhs == self.one_basis():
            return self.monomial(lhs)

        B = self._indices.gens()
        kl = lhs.trailing_support()
        kr = rhs.leading_support()

        lhs_rest = self.monomial(lhs // B[kl])
        rhs_rest = self.monomial(rhs // B[kr])

        a, b = (ZZ^2)(kl[:2]), (ZZ^2)(kr[:2])

        if kr[2] == 'K' and kl[2] == 'K':
            # Always merge two adjacent K's.
            return lhs_rest * self.K(a + b) * rhs_rest

        if self._basis_key(kl) <= self._basis_key(kr):
            # Already ordered, so no commutation necessary.
            return self.monomial(lhs * rhs)

        term = self.monomial(B[kr] * B[kl]) # commuted term

        if kr[2] == 'K':
            pass # K's are central

        elif self.determinant(a, b) == 0:
            # a and b collinear; non-trivial commutator only when a + b = 0..
            if (a + b).is_zero():
                # Defining relation of the algebra.
                term += (self.K(-a) - self.K(a)) / self.n(self.deg(a))

        elif self.num_interior_lattice_points(a, a+b) == 0:
            # Either deg(a) = deg(b) = 2 or one of them is deg 1.
            if self.deg(a) == 2 and self.deg(b) == 2:
                # Recurse using e(b) term in [e(b/2+a/2), e(b/2-a/2)].
                ea, ep, en = self.e(a), self.e((b+a)/2), self.e((b-a)/2)
                coeff, rest = self.bracket(ep, en)._isolate_e_term(self.e(b))
                term += ~coeff * (self.bracket(en, self.bracket(ep, ea)) -
                                  self.bracket(ep, self.bracket(en, ea)) +
                                  self.bracket(rest, ea))
            else:
                # Use defining relation of the algebra.
                negate_commutator = False
                if self.deg(b) == 1:
                    a, b = b, a
                    negate_commutator = True
                eab = sign(self.determinant(a, b))
                alpha = (self.sign(a)*a + self.sign(b)*b -
                         self.sign(a+b)*(a+b)) / 2
                if eab == 1:
                    alpha *= self.sign(a)
                else:
                    alpha *= self.sign(b)
                commutator = -(eab * self.K(alpha) * self.Psi(a+b)) / self.n(1)
                if negate_commutator:
                    commutator = -commutator
                term += commutator
        else:
            # Recurse on a primitive interior lattice point c.
            c = next(self.primitive_interior_lattice_points(a, a+b))
            eb, ec, eac = self.e(b), self.e(c), self.e(a-c)
            coeff, rest = self.bracket(ec, eac)._isolate_e_term(self.e(a))
            term += ~coeff * (self.bracket(self.bracket(eb, eac), ec) -
                              self.bracket(self.bracket(eb, ec), eac) -
                              self.bracket(rest, eb))

        return lhs_rest * term * rhs_rest

    def sign(self, a1, a2=None):
        r"""
        Returns the sign `\pm 1` of a lattice point
        `(a_1, a_2) \in \mathbb{Z}^\pm`, where

        .. MATH::

            \mathbb{Z}^+ = \{(i,j) \in \mathbb{Z} : i>0 \text{ or } i=0,\, j>0\}

        and `\mathbb{Z}^- = -\mathbb{Z}^+`.

        If ``a2`` is unspecified, ``a1`` should be a pair of integers.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.sign(0, -1)
            -1
            sage: QTA.sign(1, -2)
            1
        """
        if a2 is None:
            a1, a2 = tuple((ZZ^2)(a1))
        if a1 > 0 or (a1 == 0 and a2 > 0):
            return 1
        elif a1 < 0 or (a1 == 0 and a2 < 0):
            return -1
        else:
            raise ValueError("sign undefined for (%s, %s)" % (a1, a2))

    def deg(self, a1, a2=None):
        r"""
        Computes the degree of a lattice point `(a_1, a_2)`, defined
        to be the gcd of its coordinates.

        If ``a2`` is unspecified, ``a1`` should be a pair of integers.
        """
        if a2 is None:
            a1, a2 = tuple((ZZ^2)(a1))
        return gcd(a1, a2)

    def determinant(self, a, b):
        """
        Computes the determinant of lattice points `\vec a` and `\vec b`.
        """
        return a[0]*b[1] - a[1]*b[0]

    def num_interior_lattice_points(self, a, b):
        """
        Returns the number of interior lattice points in the triangle
        formed by 0, `\vec a` and `\vec b`, computed using Pick's formula.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: QTA.num_interior_lattice_points((-1,-2), (3,1))
            2
            sage: QTA.num_interior_lattice_points((1,3), (3,1))
            3
        """
        a, b = (ZZ^2)(a), (ZZ^2)(b)
        A = abs(self.determinant(a, b)) # twice area of triangle

        def num_lattice_points_on_line(a, b):
            # number of interior lattice points on the line connecting
            # integer points (a1, a2) and (b1, b2)
            x = a - b
            return gcd(abs(x[0]), abs(x[1])) - 1

        b = 3 + (num_lattice_points_on_line(0, a) +
                 num_lattice_points_on_line(0, b) +
                 num_lattice_points_on_line(a, b))
        return (A + 2 - b) // 2

    def primitive_interior_lattice_points(self, a, b):
        """
        Iterates through primitive interior lattice points in the
        triangle formed by 0, `\vec a` and `\vec b`.

        A point `\vec c` is defined to be primitive if
        `\text{deg}(\vec c) = \text{deg}(\vec a - \vec c) = 1` and
        the triangle formed by 0, `\vec a` and `\vec c` has no
        interior lattice points.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: list(QTA.primitive_interior_lattice_points((2,3), (3,2)))
            [(1, 1)]
        """
        # Use the stupidest possible algorithm: form a rectangular
        # bounding box and test whether each lattice point in it is in
        # the given triangle manually.
        a, b = (ZZ^2)(a), (ZZ^2)(b)
        edges = (0,a), (a,b), (b,0) # edge vectors in cyclic orientation
        for y in xrange(min(0, a[1], b[1])+1, max(0, a[1], b[1])):
            for x in xrange(min(0, a[0], b[0])+1, max(0, a[0], b[0])):
                c = (ZZ^2)((x, y))
                if self.deg(c) != 1 or self.deg(a-c) != 1:
                    continue
                dets = [self.determinant(c-p, q-p) for (p,q) in edges]
                if all(t > 0 for t in dets) or all(t < 0 for t in dets):
                    if self.num_interior_lattice_points(a, c) == 0:
                        yield c

    @cached_method
    def _fock_rep_e_on_monomial(self, a, mu, R, eval_param):
        r"""
        Defines the Fock representation of the element `e(a)` of the
        quantum toroidal algebra, on the symmetric polynomial ``R[mu]``.

        If ``eval_param`` (default: 1) is specified, use it as the
        evaluation parameter for the Fock module.

        This function is separate from :meth:`fock_rep` for caching.
        """
        x = R[mu]
        sym = SymmetricFunctions(R.base_ring())

        if a[1] == 0:
            m = a[0] # defining action of e(m,0)
            if m < 0:
                return R(-(self.t1*self.t2)^(m/2) /
                         ((1 - self.t1^m) * (1 - self.t2^m)) *
                         sym.powersum()[-m] * x)
            else:
                return m * self._derivative_with_respect_to_pm(x, m, sym)

        elif a[0] == 0:
            m = a[1] # defining action of e(0,m)
            def sc(nu, coeff):
                return nu, coeff * self._tautological_weight(nu, m)
            McdHt = sym.macdonald(q=self.t1, t=self.t2).Ht()
            res = sign(m)/(eval_param^m*(1-self.t1^m)) * McdHt(x).map_item(sc)
            return R(res) # convert back to original basis

        else:
            # Recurse on a closer lattice point.
            b = (ZZ^2)((a[0], 0))
            if self.num_interior_lattice_points(a, b) == 0:
                c = b / self.deg(b) # need deg 1 element in commutator
            else:
                c = next(self.primitive_interior_lattice_points(a, b))

            ec, eac = self.e(c), self.e(a-c)
            fock = lambda f, g: f.fock(g, True, eval_param)
            commutator = fock(ec, fock(eac, x)) - fock(eac, fock(ec, x))
            coeff, rest = self.bracket(ec, eac)._isolate_e_term(self.e(a))
            return fock(~coeff, commutator - fock(rest, x))
        
    def fock_rep(self, mon, x, is_left=True, eval_param=1):
        r"""
        Defines the Fock representation of a monomial ``mon``, in the
        quantum toroidal algebra, on a symmetric polynomial ``x``.

        The polynomial ``x`` must live in the ring of symmetric functions
        over the same base ring. The resulting symmetric function is
        given in the same basis as ``x``. 

        If ``eval_param`` (default: 1) is specified, use it as the
        evaluation parameter for the Fock module.

        EXAMPLES::

            sage: R = ZZ['t1','t2']; QTA = QuantumToroidalAlgebra(R.0, R.1)
            sage: Sym = SymmetricFunctions(R.fraction_field())
            sage: Ht = Sym.macdonald(q=R.0, t=R.1).Ht()
            sage: QTA.e(1,2) * Ht[1] # indirect doctest
            McdHt[]
        """
        B = self._indices.gens()
        R = x.parent()

        if x.is_zero():
            return x

        res = x
        while mon != self.one_basis():
            if is_left:
                k = mon.trailing_support()
            else:
                k = mon.leading_support()
            a = (ZZ^2)(k[:2])
            mon = mon // B[k]

            if k[2] == 'K':
                # Defining action of K(i,j).
                res = (self.t1*self.t2)^(a[0]/2) * res
            else:
                # Defining action of e(i,j).
                res = sum((c*self._fock_rep_e_on_monomial(a, mu, R, eval_param)
                           for mu, c in res), R.zero())
        return res

    def _derivative_with_respect_to_pm(self, x, m, sym):
        """
        Differentiates the symmetric function `x` with respect to
        the power sum basis element `p_m`.
        """
        def differentiate(partition, coeff):
            L = list(partition)
            e = L.count(m)
            if e == 0:
                return partition, 0
            else:
                L.remove(m)
                return Partition(L), e*coeff

        px = sym.powersum()(x) # convert to power sum basis
        res = px.map_item(differentiate)
        return x.parent()(res) # convert back to original basis

    def _tautological_weight(self, partition, m):
        r"""
        Weight of `m`-th Adams operation of tautological bundle over
        the fixed point given by ``partition``.
        """
        return (sum(self.t1^(m*l)*self.t2^(m*i)
                   for i, l in enumerate(partition)) +
                self.t2^(m*len(partition)) / (1 - self.t2^m))
