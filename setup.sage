"""
Configuration for rings, variables, cohomology theory.
"""
from sage.rings.fraction_field_element import FractionFieldElement
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing
from sage.rings.polynomial.laurent_polynomial_ring import is_LaurentPolynomialRing
from sage.rings.power_series_ring import is_PowerSeriesRing
from sage.rings.multi_power_series_ring import is_MPowerSeriesRing
from sage.rings.laurent_series_ring import is_LaurentSeriesRing
from sage.rings.fraction_field import is_FractionField
from sage.structure.element import is_Matrix
from sage.combinat.sf.sfa import is_SymmetricFunction
import itertools

def pretty(f):
    """
    Pretty-prints `f`.
    """
    if is_Matrix(f):
        return f.apply_map(pretty)
    elif is_SymmetricFunction(f):
        return f.map_coefficients(pretty)
    elif isinstance(f, (tuple, list)):
        return [pretty(g) for g in f]
    elif is_PolynomialRing(f.parent()) or is_MPolynomialRing(f.parent()):
        return SR(f).factor()
    elif is_LaurentPolynomialRing(f.parent()):
        return pretty(f.parent().fraction_field()(f))
    elif is_PowerSeriesRing(f.parent()):
        if len(f.coefficients()) == 0:
            return f
        base = pretty(f.coefficients()[-1]).parent()
        return f.map_coefficients(pretty, base)
    elif is_MPowerSeriesRing(f.parent()):
        prec = f.prec()
        testx = pretty(f.base_ring().an_element())
        RSR = f.parent().change_ring(testx.parent())
        return sum(pretty(c) * RSR(mon)
                   for mon, c in f.coefficients().items()).add_bigoh(prec)
    elif is_LaurentSeriesRing(f.parent()):
        prec = f.prec()
        testx = pretty(f.base_ring().an_element())
        RSR = f.parent().change_ring(testx.parent())
        x = RSR.gen()
        return sum(pretty(coeff) * x^exp for exp, coeff
                   in zip(f.exponents(), f.coefficients())).add_bigoh(prec)
    elif hasattr(f, 'map_coefficients'):
        return f.map_coefficients(pretty)
    elif f:
        return SR(f).factor()
    else:
        return f

class EquivariantSetup:
    """
    Container for default rings and variables.
    """
    weight_ring = LaurentPolynomialRing(ZZ, 'x,y,z')
    boxcounting_ring = LaurentSeriesRing(weight_ring.fraction_field(), 'q')
    series_ring = PowerSeriesRing(boxcounting_ring, 'A')
    x, y, z = weight_ring.gens()
    q = boxcounting_ring.gen()
    A = series_ring.gen()

    weight_aut = weight_ring.Hom(weight_ring)
    boxcounting_aut = boxcounting_ring.Hom(boxcounting_ring)
    series_aut = series_ring.Hom(series_ring)

    @classmethod
    def inject_variables(cls):
        """
        Makes all default variables available for interactive use.
        """
        cls.weight_ring.inject_variables()
        cls.boxcounting_ring.inject_variables()
        cls.series_ring.inject_variables()

    @classmethod
    def _apply_to_weight_ring(cls, func, f, codomain=None):
        """
        Apply the function ``func`` to the parts of ``f`` that
        live in the weight ring.

        If ``func`` maps to a ring which is not the fraction field
        of the default weight ring, specify it as ``codomain``.
        """
        if codomain is None:
            codomain = cls.weight_ring.fraction_field()

        R = f.parent()

        if R is cls.weight_ring or R is cls.weight_ring.fraction_field():
            return codomain(func(f)) # apply
        
        elif R is cls.boxcounting_ring: # unroll
            qR = R.change_ring(codomain)
            q, val, prec = qR.gen(), f.valuation(), f.precision_absolute()
            res = sum(cls._apply_to_weight_ring(func, coeff, codomain) \
                      * q**(k+val) for k, coeff in enumerate(f))
            res = qR(res) # in case res = 0
            if prec < Infinity:
                res = res.add_bigoh(prec)
            return res
        
        elif R is cls.series_ring: # unroll
            new_func = lambda f: cls._apply_to_weight_ring(func, f, codomain)
            qR = cls.boxcounting_ring.change_ring(codomain)
            return cls._apply_to_boxcounting_ring(new_func, f, qR)

        else:
            raise NotImplementedError("%s" % R)
            return f

    @classmethod
    def _apply_to_boxcounting_ring(cls, func, f, codomain=None):
        """
        Apply the function ``func`` to the parts of ``f`` that
        live in the boxcounting ring.

        If ``func`` maps to a ring which is not the default
        boxcounting ring, specify it as ``codomain``.
        """
        if codomain is None:
            codomain = cls.boxcounting_ring

        R = f.parent()

        if R is cls.boxcounting_ring:
            return codomain(func(f)) # apply
        
        elif R is cls.series_ring: # unroll
            qAR = R.change_ring(codomain)
            A, prec = qAR.gen(), f.precision_absolute()
            res = sum(cls._apply_to_boxcounting_ring(func, coeff, codomain) \
                      * A**k for k, coeff in enumerate(f))
            res = qAR(res) # in case res = 0
            if prec < Infinity:
                res = res.add_bigoh(prec)
            return res

        else:
            raise NotImplementedError("%s" % R)
            return f

    @classmethod
    def substitute_xyz(cls, f, x, y, z):
        """
        Given a function `f` made from default variables, substitute
        the weights with `x`, `y`, `z`.
        """
        return cls._apply_to_weight_ring(lambda f: f(x, y, z), f)

    @classmethod
    def substitute_q(cls, f, q):
        """
        Given a function `f` made from default variables, substitute
        the boxcounting variable with `q`.
        """
        return cls._apply_to_boxcounting_ring(lambda f: f(q), f)

class EquivariantTestSetup:
    """
    Container for default rings and variables for testing purposes.
    """
    ff = GF(next_prime(10^8))
    a = ff.gen()
    xv, yv, zv = 59482422*a, 77119312*a, 22010603*a
    
    weight_ring = LaurentPolynomialRing(ZZ, 'x,y,z')
    x, y, z = weight_ring.gens()
    
    boxcounting_ring = LaurentSeriesRing(ff, 'q')
    series_ring = PowerSeriesRing(boxcounting_ring, 'A')
    q = boxcounting_ring.gen()
    A = series_ring.gen()

    weight_aut = weight_ring.Hom(weight_ring)
    boxcounting_aut = boxcounting_ring.Hom(boxcounting_ring)
    series_aut = series_ring.Hom(series_ring)

############################################################
# Change this to various setups to do various things!
# E.g. EquivariantTestSetup is for verifying equivariant
# identities without computing the actual function of x,y,z
############################################################
############################################################

Default = EquivariantSetup
# Default = EquivariantTestSetup

############################################################
############################################################

class KTheory:
    """
    Container for K-theoretic methods
    """
    name = "K-theory" # printed name
    
    @staticmethod
    def from_monomial(m):
        """
        Convert the K-theoretic monomial `m` into a K-theoretic monomial.
        """
        return m

    @staticmethod
    def measure(f):
        r"""
        Returns the K-theoretic vertex measure applied to `f`.

        This is the homomorphism `\hat{a}(w) = 1/(w^{1/2} - w^{-1/2})`.
        The result always lives in the fraction field of the weight ring.
        """
        R = f.parent()

        if is_LaurentPolynomialRing(R): # use a fast implementation
            numer, denom = R.one(), R.one()
            for exp, coeff in f.dict().items():
                # create the term w^(1/2) - w^(-1/2)
                if exp.is_constant():
                    term = R.zero()
                else:
                    term = R({exp: 1, exp.emul(-1): -1})
                if coeff < 0:
                    numer *= term ** (-coeff)
                elif coeff > 0:
                    denom *= term ** coeff
            return R.fraction_field()(numer) / denom

        else:
            raise NotImplementedError("%s (%s)" % (R, f))

    @staticmethod
    def measure_unsymmetrized(f, m=None, inv=True):
        """
        Returns the *unsymmetrized* K-theoretic vertex measure
        applied to `f`.

        This is the homomorphism `a(w) = 1/(1 - m/w)`. The result always
        lives in the fraction field of the weight ring unless `m` is
        specified.
        """
        R = f.parent()
        if m is None:
            m = R.one()
        else: # find common parent (heuristic)
            R = sage.categories.pushout.pushout(m.parent(), R.fraction_field())

        if f.parent() is ZZ:
            L = [(ZZ(f), 1)]
        else:
            L = list(f)
            
        numer, denom = R.one(), R.one()
        for coeff, monomial in L:
            if inv:
                term = 1 - m*monomial^-1
            else:
                term = 1 - m*monomial
            if coeff < 0:
                numer *= term ** (-coeff)
            elif coeff > 0:
                denom *= term ** coeff

        if is_LaurentPolynomialRing(R):
            return R.fraction_field()(numer) / denom # want Frac(poly ring)
        else:
            return numer / denom

    @staticmethod
    def determinant(f, m=None):
        """
        Returns the determinant of `f`.
        """
        if m is None:
            m = 1
        if f in ZZ:
            return m^ZZ(f)
        else:
            return prod((m*mon)^coeff for coeff, mon in f)

    @staticmethod
    def rank(f):
        """
        Returns the rank of `f` as a virtual bundle.
        """
        if f in ZZ:
            return ZZ(f)
        else:
            return sum(f.coefficients())

    @staticmethod
    def sym(k, f):
        """
        Compute the `k`-th symmetric power of the K-theory class `f`.
        """
        # Do it the stupid way: extract the u^k coefficient.
        R = f.parent()
        uR.<u> = PowerSeriesRing(R, default_prec=k+1)
        series = KTheory.measure_unsymmetrized(f, m=u, inv=False)
        coeffs = uR(series).coefficients()
        return coeffs[k] if k < len(coeffs) else R.zero()

    @staticmethod
    def adams(k, f):
        r"""
        Apply the `k`-th Adams operation to `f`, namely the substitution
        `(x_1, \ldots, x_N) \mapsto (x_1^k, \ldots, x_N^k)` for all
        variables `x_i` appearing in `f`.

        Supports only (Laurent) polynomial/series rings.
        """
        R = f.parent()
        if ( is_PolynomialRing(R) or is_MPolynomialRing(R) or
             is_LaurentPolynomialRing(R) or is_PowerSeriesRing(R) or
             is_MPowerSeriesRing(R) ):
            if R.ngens() > 1:
                res = R( {tuple(ZZ(e*k) for e in exps) : KTheory.adams(k, coeff)
                          for exps, coeff in f.dict().items()} )
            else:
                res = R( {ZZ(exp*k) : KTheory.adams(k, coeff)
                          for exp, coeff in f.dict().items()} )
        elif is_FractionField(R):
            res = ( R(KTheory.adams(k, f.numerator()))
                    / KTheory.adams(k, f.denominator()) )
        elif is_LaurentSeriesRing(R):
            x = R.gen()
            res = R(sum(x^(ZZ(exp)*k) * KTheory.adams(k, coeff)
                        for exp, coeff in zip(f.exponents(), f.coefficients())))
        else:
            res = f

        if hasattr(f, 'precision_absolute'):
            if f.precision_absolute() < Infinity:
                res = res.add_bigoh(f.precision_absolute()*k)

        return res

    @staticmethod
    def plethexp(f, prec):
        """
        Plethystic exponential of `f` to precision `prec`.
        """
        R = f.parent()
        g = sum( (KTheory.adams(k, f) / k for k in range(1, prec)), R.zero() )
        return sum( (g^k/factorial(k) for k in range(prec)), R.zero() )

    @staticmethod
    def plethlog(f):
        """
        Plethystic logarithm of `f`.
        """
        raise NotImplementedError
    
    @staticmethod
    def edge_transformation(x, y, z, a, b):
        """
        Returns the new coordinate system x, y, z on the other side
        of an edge with normal bundle O(a)+O(b).
        """
        return x**(-1), y * x**(-a), z * x**(-b)
        
    @staticmethod
    def index_limit(f, s, kappa):
        r"""
        For a balanced rational function `f(x, y, z)`, compute
        the index limit with preferred direction given by the
        slope `s = (a, b, c)`.

        The result is given using the formal variable ``kappa``.

        E.g. for `s = (N, -N-1, 1)` for `N \gg 0`, this agrees with
        section 8.2.5 of Nekrasov-Okounkov with preferred slope
        fixing the z-axis. Our ``kappa`` is their `\kappa^{1/2}`.

        ALGORITHM:

        - Set `x, y, z = u^a, u^b, \kappa u^c`.

        - Take the limit `u \to 0`.
        """
        def smallest_u_term(f):
            # Keep track of the coefficient of the u term with
            # smallest degree seen so far as we iterate through f.
            # Assume f lives in a (Laurent)PolynomialRing
            min_deg_u = Infinity
            coeff = 0
            for exps, c in f.dict().items():
                deg_u = sum(sk*ek for sk,ek in zip(s, exps))
                if deg_u > min_deg_u:
                    continue
                if deg_u < min_deg_u:
                    min_deg_u = deg_u
                    coeff = 0
                coeff += c * kappa^(exps[0])
            return min_deg_u, coeff

        deg_num, coeff_num = smallest_u_term(f.numerator())
        deg_denom, coeff_denom = smallest_u_term(f.denominator())
        if deg_num != deg_denom:
            raise ValueError("index limit of %s does not exist" % f)
        return coeff_num / coeff_denom

class KTheory_hashed:
    r"""
    Container for K-theory methods, but hashed.

    This can only be used with ``Default=EquivariantTestSetup`.
    """
    name = "K-theory hashed" # printed name

    @classmethod
    def measure(cls, f):
        """
        Returns a hashed K-theory measure applied to `f`.

        TODO: apply this to PT integrate_over_fixed_loci code...
              - deal with extra q[i] variables
        """
        if Default is not EquivariantTestSetup:
            raise ValueError("%s can only be used with EquivariantTestSetup" %
                             cls.name)

        R = f.parent().change_ring(Default.ff)
        res = R.one()
        for coeff, mon in f:
            # create the term w^(1/2) - w^(-1/2)
            term = mon(x=Default.xv, y=Default.yv, z=Default.zv)
            term = term - ~term
            if term == 0 and coeff < 0:
                return R.zero() # trivial weight
            res *= ~(term^coeff)
        return res

class Cohomology:
    """
    Container for cohomological methods
    """
    name = "cohomology" # printed name

    @staticmethod
    def from_monomial(m):
        """
        Convert the K-theoretic monomial `m` into a cohomological monomial.
        The cohomological monomial lives in the polynomial ring associated
        to the K-theoretic ring.
        """
        R = m.parent()
        if R is ZZ:
            return 0
        else:
            return R.polynomial_ring()(sum(m.degree(x) * x for x in R.gens()))

    @staticmethod
    def from_character(f):
        """
        Converts a character ``f`` (from K-theory) to a list of
        cohomological weights in the numerator and denominator.
        """
        R = f.parent()
        numer, denom = [], []

        if is_LaurentPolynomialRing(R): # K-theory weight ring
            for coeff, mon in list(f):
                wt = Cohomology.from_monomial(mon)
                if coeff < 0:
                    numer += (-coeff) * [wt]
                elif coeff > 0:
                    denom += coeff * [wt]
            return numer, denom

        else:
            raise NotImplementedError("%s" % R)
    
    @staticmethod
    def measure(f):
        r"""
        Returns the cohomological vertex measure applied to ``f``.

        This first converts ``f`` into a list of cohomological weights,
        and then takes the product of all such weights. The result
        always lives in the fraction field of the weight ring.
        """
        R = f.parent()
        numer, denom = Cohomology.from_character(f)
        return R.fraction_field()(prod(numer) / prod(denom))

    @staticmethod
    def edge_transformation(x, y, z, a, b):
        """
        Returns the new coordinate system x, y, z on the other side
        of an edge with normal bundle O(a)+O(b).
        """
        R = Default.weight_ring.polynomial_ring()
        return R(-x), R(y - a*x), R(z - b*x)

    @staticmethod
    def chern_character(k, f):
        r"""
        Computes the `k`-th Chern character of the K-theoretic `f`.
        The output is in cohomology, implicitly treating the K-theoretic
        variables as cohomological ones. (Namely, an output variable `u`
        implicitly means `\log u`.)
        """
        div = lambda a,b: a.parent().fraction_field()(a) / b
        return sum(c * div(Cohomology.from_monomial(w)^k, factorial(k))
                   for c, w in f)

    @staticmethod
    def chern_class(k, f):
        r"""
        Computes the `k`-th Chern class of the K-theoretic `f`.
        The output is in cohomology, implicitly treating the K-theoretic
        variables as cohomological ones. (Namely, an output variable `u`
        implicitly means `\log u`.)
        """
        roots = sum((c*[Cohomology.from_monomial(w)] for c, w in f), [])
        return sum(prod(S) for S in itertools.combinations(roots, k))

class Counting:
    """
    Container for counting methods.

    Note that this is actually slower than adjusting parts of the code
    to do the counting directly. Using this class with the current code
    means characters are computed for every configuration and then discarded.
    """
    name = "counting" # printed name

    @staticmethod
    def measure(f):
        """
        Returns the counting measure applied to `f`.
        """
        return 1

    @staticmethod
    def from_monomial(f):
        """
        Takes a K-theoretic monomial `m` and returns zero.

        This method is provided for consistency with other theories.
        """
        return 0

    @staticmethod
    def edge_transformation(x, y, z, a, b):
        """
        Returns the new coordinate system x, y, z on the other side
        of an edge with normal bundle O(a)+O(b).
        """
        return x, y, z # doesn't matter what we do
