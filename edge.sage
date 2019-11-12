"""
DT/PT edge
"""
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation

load("setup.sage") # contains Default and KTheory

class Edge(UniqueRepresentation):
    """
    An `(a, b)` edge with partition `\lambda`.

    The edge is assumed to run in the `x` direction. Rows of `\lambda`
    run in the `y` direction, and columns run in the `z` direction.

    EXAMPLES::

        TODO
    """
    @staticmethod
    def __classcall_private__(cls, a, b, ct=KTheory):
        return cls.__classcall__(cls, a, b, ct)

    def __init__(self, a, b, ct):
        self._a, self._b = a, b
        self._ct = ct

    def __repr__(self):
        return "(%s, %s) edge using %s" % (self._a, self._b, self._ct.name)

    @staticmethod
    @cached_method
    def raw_weight(lamb, y, z):
        r"""
        Computes the raw localization weight of the edge ``lamb``.
        Always returns a Laurent polynomial in these variables.

        This is the function `F_{\alpha\beta}` in MNOP I.

        EXAMPLES:

            TODO
        """
        Q = character_2d_partition(lamb, y, z)
        Qinv = character_2d_partition(lamb, y^-1, z^-1)

        return -Q - Qinv/(y*z) + Q*Qinv*(1-y)*(1-z)/(y*z)

    @staticmethod
    def weight(lamb, a, b, x=Default.x, y=Default.y, z=Default.z):
        r"""
        Computes the localization weight of the edge ``lamb`` with
        normal degrees `a` and `b`, using `x`, `y`, `z`.
        Always returns a Laurent polynomial in these variables.

        This is the function `E_{\alpha\beta}` in MNOP I.
        """
        F = Edge.raw_weight(lamb, y, z)
        Fsub = Edge.raw_weight(lamb, y * x^-a, z * x^-b)

        Enum = x*Fsub - F

        # Check that we can divide out (1-x)
        quo, rem = Enum.quo_rem(1-x)
        if rem != 0:
            raise ValueError("edge weight computation went wrong")

        return quo

    @staticmethod
    @cached_method
    def chi(lamb, a, b):
        r"""
        Computes the contribution to the Euler characteristic
        of an edge ``lamb`` with normal degrees `a` and `b`.
        """
        return sum(-a*i - b*j + 1 for (i, j) in lamb.cells())

    @cached_method
    def term_q(self, lamb, x=Default.x, y=Default.y, z=Default.z, q=Default.q):
        r"""
        Returns the q-series term corresponding to ``lamb``.
        """
        term = self._ct.measure(Edge.weight(lamb, self._a, self._b))
        if (x, y, z) != (Default.x, Default.y, Default.z):
            R = Default.boxcounting_ring.base_ring()
            term = term.subs(x=R(x), y=R(y), z=R(z))

        return term * (-q)^Edge.chi(lamb, self._a, self._b)
