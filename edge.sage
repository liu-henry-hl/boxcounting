"""
DT/PT edge
"""
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation

load("setup.sage") # contains Default and KTheory
load("partition_3d.sage")

class Edge(UniqueRepresentation):
    r"""
    An `(a, b)` edge with partition `\lambda`.

    The edge is assumed to run in the `x` direction. Rows of `\lambda`
    run in the `y` direction, and columns run in the `z` direction.

    For a higher-rank edge, specify *lists* of partitions.

    EXAMPLES::

        TODO
    """
    def __init__(self, a, b, x, y, z, u=(1,), ct=KTheory):
        self.a, self.b = a, b
        self.x, self.y, self.z = x, y, z
        self.u = u

        self._ct = ct

    def __repr__(self):
        return "(%s, %s) edge in x=%s, y=%s, z=%s, u=%s using %s" % \
            (self.a, self.b, self.x, self.y, self.z, self.u, self._ct.name)

    @staticmethod
    @cached_method
    def unnormalized_raw_weight(lamb, y, z, u=(1,)):
        """
        Computes the *unnormalized* raw localization weight of the edge
        ``lamb``. Always returns a Laurent polynomial in these variables.
        """
        if lamb in Partitions():
            lamb = (lamb,) # rank 1 case

        # "Poincare" polynomial Q = (1+P) / (1-y)(1-z)
        P = [character_2d_partition(p,y,z)*(1-y)*(1-z) - 1 for p in lamb]
        Pinv = [character_2d_partition(p,~y,~z)*(1-~y)*(1-~z) - 1 for p in lamb]

        # E = (1 - P \bar{P}) / (1-y)(1-z)
        # (The stupid hack is because 1/1 is in Q, not Z; we avoid this.)
        Enum = sum((1 - Pi * Pinvj) * (1 if ui == uj else ui/uj)
                   for ui, Pi in zip(u, P) for uj, Pinvj in zip(u, Pinv))

        return -Enum

    @staticmethod
    def raw_weight(lamb, y, z, u=(1,)):
        """
        Computes the raw localization weight of the edge ``lamb``.
        Always returns a Laurent polynomial in these variables.
        
        This is the function `F_{\alpha\beta}` in MNOP I when ``lamb``
        is a single partition.
        """
        Enum = Edge.unnormalized_raw_weight(lamb, y, z, u)

        # Check we can divide out (1-y)(1-z)
        quo, rem = Enum.quo_rem( (1-y)*(1-z) )
        if rem != 0:
            raise ValueError("raw edge weight computation went wrong")

        return quo

    @cached_method
    def weight(self, lamb):
        r"""
        Computes the localization weight of the edge ``lamb``.
        Always returns a Laurent polynomial in `x`, `y`, `z`, `u`.

        This is the function `E_{\alpha\beta}` in MNOP I if ``lamb``
        is a single partition.
        """
        x, y, z, u = self.x, self.y, self.z, self.u
        F = Edge.raw_weight(lamb, y, z, u)
        Fsub = Edge.raw_weight(lamb, y * x^-self.a, z * x^-self.b, u)

        Enum = x*Fsub - F # clearly divisible by (1-x)

        return Enum // (1 - x)

        # quo, rem = Enum.quo_rem( (1-x) )
        # if rem != 0: # somehow buggy...
        #     print Enum
        #     print 1-x
        #     print quo
        #     print rem
        #     raise ValueError("edge weight computation went wrong")

        # return quo

    def chi(self, lamb):
        r"""
        Computes the contribution to the Euler characteristic
        of an edge ``lamb``.
        """
        if lamb in Partitions():
            lamb = (lamb,) # rank 1 case
        return sum(sum(-self.b*i - self.a*j + 1 for (i, j) in p.cells())
                   for p in lamb)

    @cached_method
    def term_q(self, lamb, q):
        r"""
        Returns the q-series term corresponding to ``lamb``.
        """
        return (-q)^self.chi(lamb) * self._ct.measure(self.weight(lamb))
