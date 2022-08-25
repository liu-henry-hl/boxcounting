"""
3d partitions with legs.
"""
from six import add_metaclass

from sage.structure.list_clone import ClonableElement
from sage.misc.inherit_comparison import InheritComparisonClasscallMetaclass
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.combinat.partition import Partition
from sage.rings.infinity import PlusInfinity

def character_2d_partition(lamb, x, y):
    """
    Returns the character of ``lamb`` in variables ``x, y``.
    Rows of ``lamb`` run along ``x``, and columns run along ``y``.

    EXAMPLES::

        sage: R.<x,y> = PolynomialRing(ZZ)
        sage: character_2d_partition(Partition([3,1]), x, y)
        x^2 + x + y + 1
    """
    return sum(y**i * x**j for i, j in lamb.cells())

@add_metaclass(InheritComparisonClasscallMetaclass)
class Partition3d(ClonableElement):
    r"""
    A 3d partition with legs is a collection of boxes stacked on top
    of each other, with three infinite legs extending along the
    `x, y, z` axes.

    INPUT:

    - ``boxes`` -- list of coordinates `(i, j, k)` of additional boxes
      which are not part of the three pre-existing legs.
    
    - ``lamb``, ``mu``, ``nu`` -- 2d partitions specifying the profiles
      of the legs `\lambda`, `\mu`, `\nu`.
    
    The leg `\lambda` has rows along the `y` axis and columns along
    the `z` axis. In other words, `\lambda_1` is its length in the
    `y` direction. The other two legs are oriented in the cyclically
    symmetric way.

    EXAMPLES::

        sage: V = Partition3d([(0,0,1)], lamb=[3], mu=[1,1], nu=[])
        3d partition with legs [3], [1, 1], [] and extra boxes [(0, 0, 1)]
        sage: Partition3d([[0,1,1]], [3], [1,1], [])
        ValueError: first argument must be a list of (i, j, k)
        sage: W = Partition3d([(0,0,1)], [3], [1,1], []);
        sage: V == W
        True
        sage: V is W
        False
        sage: Partition3d([(0,1,1)], [3], [1,1], [])
        ValueError: invalid box at (0, 1, 1)
        sage: V.volume()
        -5
        sage: V in Partitions3d([3], [1,1], [])
        True
    """
    @staticmethod
    def __classcall_private__(cls, boxes, lamb=None, mu=None, nu=None, check=True):
        """
        Constructs a 3d partition with legs with the appropriate parent.
        """
        if isinstance(boxes, cls):
            return boxes
        
        if isinstance(boxes, (list, tuple)):
            if all(isinstance(box, tuple) and len(box) == 3 for box in boxes):
                return Partitions3d(lamb, mu, nu)(boxes, check)

        raise ValueError("first argument must be a list of (i, j, k)")
    
    def __init__(self, parent, boxes, check=True):
        """
        Initializes ``self``.

        Set ``check`` (default: True) to False to omit checking
        that the input ``boxes`` forms a valid 3d partition.
        """
        self._lamb = parent._lamb
        self._mu = parent._mu
        self._nu = parent._nu

        ClonableElement.__init__(self, parent)

        self._Nx = parent._min_Nx
        self._Ny = parent._min_Ny
        self._Nz = parent._min_Nz
        
        self._boxes = set()
        for box in boxes:
            self._add_box_in_place(*box)

        self.set_immutable()
        if check:
            self.check()

    def check(self):
        """
        Check that ``self`` is a valid 3d partition with given legs.
        
        The boxes in the legs automatically satisfy this condition.
        """
        for (i, j, k) in self._boxes:
            if not self._is_box_valid(i, j, k) or \
               self._in_num_legs(i, j, k) > 0:
                raise ValueError("invalid box (%s, %s, %s)" % (i, j, k))
        
    def _is_box_valid(self, i, j, k):
        r"""
        Check that it is valid to have a box in ``self`` at `(i, j, k)`.

        This means that a box at `(i, j, k)` must have neighboring boxes
        at `(i, j, k-1)` and `(i, j-1, k)` and `(i-1, j, k)`.
        """
        return ((k == 0 or (i, j, k-1) in self) and
                (j == 0 or (i, j-1, k) in self) and
                (i == 0 or (i-1, j, k) in self))
        
    def __contains__(self, x):
        """
        Checks whether there is a box at ``x``.

        EXAMPLES::

            sage: V = Partition3d([(0,0,1)], [3], [1,1], [])
            3d partition with legs [3], [1, 1], [] and extra boxes [(0, 0, 1)]
            sage: (30, 2, 0) in V
            True
            sage: (2, 3, 0) in V
            False
        """
        if not isinstance(x, (tuple, list)):
            return False
        if len(x) != 3:
            return False
        
        return (self._in_num_legs(*x) > 0 or x in self._boxes)

    def _in_num_legs(self, i, j, k):
        """
        Returns the number of legs that `(i, j, k)` belongs to.
        """
        return self._exists_in_legs(i, j, k).count(True)

    def _exists_in_legs(self, i, j, k):
        """
        Returns the legs that `(i, j, k)` belongs to.
        """
        return [self._exists_in_lamb(i, j, k),
                self._exists_in_mu(i, j, k),
                self._exists_in_nu(i, j, k)]

    def _exists_in_lamb(self, i, j, k):
        r"""
        Checks whether `(i, j, k)` is a box in the infinite leg `\lambda`.
        """
        return 0 <= k < len(self._lamb) and 0 <= j < self._lamb[k]
        
    def _exists_in_mu(self, i, j, k):
        r"""
        Checks whether `(i, j, k)` is a box in the infinite leg `\mu`.
        """
        return 0 <= i < len(self._mu) and 0 <= k < self._mu[i]

    def _exists_in_nu(self, i, j, k):
        r"""
        Checks whether `(i, j, k)` is a box in the infinite leg `\nu`.
        """
        return 0 <= j < len(self._nu) and 0 <= i < self._nu[j]

    def __repr__(self):
        """
        Return a string representation of ``self``.
        """
        if not self._lamb and not self._mu and not self._nu:
            return "3d partition with boxes %s" % list(self._boxes)
        else:
            return "3d partition with legs %s, %s, %s and extra boxes %s" % \
                (self._lamb, self._mu, self._nu, list(self._boxes))

    def __hash__(self):
        """
        Return the hash of ``self``.
        """
        return hash(self.parent()) ^^ hash(frozenset(self._boxes))

    def __copy__(self):
        """
        Return a copy of ``self``.
        """
        # Manually copy boxes, otherwise res._boxes is self._boxes
        res = ClonableElement.__copy__(self)
        res._boxes = self._boxes.copy()

        return res
        
    def __eq__(self, other):
        """
        Return true if ``self`` is the same 3d partition as ``other``.
        """
        if isinstance(other, self.__class__):
            return (self.parent() == other.parent() and
                    self._boxes == other._boxes)
        return False

    def __ne__(self, other):
        """
        Return true if ``self`` is not the same 3d partition as ``other``.
        """
        return not self.__eq__(other)
    
    def plot(self, colors=('red','green','blue')):
        """
        Plot ``self`` as a Graphics3d object.
        """
        Nx, Ny, Nz = self.bounding_box()
        Bx, By, Bz = max(10, Nx+5), max(10, Ny+5), max(10, Nz+5)
        
        from sage.plot.plot3d.shapes import ColorCube
        cube = ColorCube([.5,.5,.5], colors, opacity=0.85)
        plot = sum(cube.translate(*b) for b in self.boxes(Nx=Bx, Ny=By, Nz=Bz))

        from sage.plot.plot3d.plot3d import axes
        plot += axes(max(max(Bx, By), Bz)+1, 3, color='black')

        plot.show(frame=False, axes=True, aspect_ratio=1)

    def boxes(self, Nx=PlusInfinity, Ny=PlusInfinity, Nz=PlusInfinity):
        r"""
        Iterate through all boxes in ``self`` which are contained in
        the bounding box `[0, Nx) x [0, Ny) x [0, Nz)`.

        ALGORITHM: iterate through all `(i, j)` in `[0, Nx) x [0, Ny)`
        that have a box at `(i, j, 0)`, and then iterate through all k
        where there is a box at `(i, j, k)`.
        """
        if (0, 0, 0) not in self or Nx <= 0 or Ny <= 0 or Nz <= 0:
            return # if (0, 0, 0) is not even present, nothing else is
        stack = [(0, 0)]
        seen = {}
        while stack:
            (i, j) = stack.pop()
            for k in range(Nz):
                if (i, j, k) not in self:
                    break
                yield (i, j, k)

            if (i+1 < Nx) and ((i+1, j) not in seen) and ((i+1, j, 0) in self):
                seen[(i+1, j)] = True
                stack.append((i+1,j))
            if (j+1 < Ny) and ((i, j+1) not in seen) and ((i, j+1, 0) in self):
                seen[(i, j+1)] = True
                stack.append((i,j+1))

    def volume(self):
        r"""
        Returns the *normalized* volume of ``self``.

        The normalized volume of a 3d partition `\pi` with legs
        `\lambda`, `\mu`, `\nu` is the quantity

        .. MATH::

            #\{\pi \cap [0, N]^3\} - (N+1) (|\lambda| + |\mu| + |\nu|)

        which is independent of `N` for sufficiently large `N`.

        EXAMPLES::

            sage: Partition3d([], [1], [], []).volume()
            0
            sage: Partition3d([], [1], [1], []).volume()
            -1
            sage: Partition3d([(0,0,1)], [3], [1,1], []).volume()
            -5
        """
        return self.parent().minimal_volume() + len(self._boxes)

    def bounding_box(self):
        r"""
        Returns the box `[0, Nx) x [0, Ny) x [0, Nz)` beyond which there
        are only boxes belonging to the asymptotic legs, with no overlap.

        EXAMPLES::

            sage: Partition3d([(0,0,0)], [], [], []).bounding_box()
            (1, 1, 1)
            sage: Partition3d([], [3], [1,1], []).bounding_box()
            (2, 3, 1)
        """
        return (self._Nx, self._Ny, self._Nz)

    def _unnormalized_character(self, x, y, z):
        r"""
        Returns the character associated to ``self`` (see :meth:`character`),
        multipled by the additional factor `(1-x)(1-y)(1-z)`.

        This guarantees the result is a Laurent polynomial in `x, y, z`.
        """
        Nx, Ny, Nz = self._Nx, self._Ny, self._Nz

        char = sum(x**i * y**j * z**k
                   for (i,j,k) in self.boxes(Nx=Nx, Ny=Ny, Nz=Nz))
        char *= (1-x)*(1-y)*(1-z)
        
        char += self.leg_character_lamb(x,y,z) * x**Nx * (1-y)*(1-z)
        char += self.leg_character_mu(x,y,z) * y**Ny * (1-z)*(1-x)
        char += self.leg_character_nu(x,y,z) * z**Nz * (1-x)*(1-y)

        return char

    def character(self, x, y, z):
        r"""
        Return the character associated to ``self``, in variables `x, y, z`.

        The character of a 3d partition `\pi` is

        .. MATH::

            \sum_{(i,j,k) \in \pi} x^i y^j z^k.

        In general, it lives in the fraction field of polynomials
        in `x, y, z`.

        EXAMPLES::

            sage: V = Partition3d([], lamb=[1], mu=[1], nu=[1])
            sage: R.<x,y,z> = PolynomialRing(ZZ)
            sage: char = V.character(x, y, z)
            sage: char == 1/(1 - x) + 1/(1 - y) + 1/(1 - z) - 2
            True
        """
        return self._unnormalized_character(x, y, z) / ( (1-x)*(1-y)*(1-z) )
    
    def legs(self):
        r"""
        Returns the three legs `\lambda`, `\mu`, and `\nu` of ``self``.
        """
        return self.parent().legs()

    def leg_character_lamb(self, x, y, z):
        r"""
        Returns the character associated to the leg `\lambda`.

        EXAMPLES::

            sage: R.<x,y,z> = PolynomialRing(ZZ)
            sage: Partition3d([], [3,1], [], []).leg_character_lamb(x, y, z)
            y^2 + y + z + 1
        """
        return character_2d_partition(Partition(self._lamb), y, z)

    def leg_character_mu(self, x, y, z):
        r"""
        Returns the character associated to the leg `\mu`.

        EXAMPLES::

            sage: R.<x,y,z> = PolynomialRing(ZZ)
            sage: Partition3d([], [], [3,1], []).leg_character_mu(x, y, z)
            z^2 + x + z + 1
        """
        return character_2d_partition(Partition(self._mu), z, x)

    def leg_character_nu(self, x, y, z):
        r"""
        Returns the character associated to the leg `\nu`.

        EXAMPLES::

            sage: R.<x,y,z> = PolynomialRing(ZZ)
            sage: Partition3d([], [], [], [3,1]).leg_character_nu(x, y, z)
            x^2 + x + y + 1
        """
        return character_2d_partition(Partition(self._nu), x, y)

    def _add_box_in_place(self, i, j, k):
        r"""
        Add a box at `(i, j, k)` to ``self`` in place.

        This is an internal method. Users should use :meth:`add_box` instead.
        """
        self._require_mutable()

        self._boxes.add( (i,j,k) )

        self._Nx = max(i+1, self._Nx)
        self._Ny = max(j+1, self._Ny)
        self._Nz = max(k+1, self._Nz)

    def add_box(self, i, j, k, check=True):
        r"""
        Return a new 3d partition which is ``self`` with an
        extra box at `(i, j, k)`.

        Set ``check=False`` to skip checking that adding such a box is valid.

        EXAMPLES::

            sage: V = Partition3d([], lamb=[3], mu=[1,1], nu=[]); V
            3d partition with legs [3], [1, 1], [] and extra boxes []
            sage: W = V.add_box(0, 0, 1); W
            3d partition with legs [3], [1, 1], [] and extra boxes [(0, 0, 1)]
            sage: W.character() - V.character()
            z
        """
        with self.clone(check=check) as new_PP:
            new_PP._add_box_in_place(i, j, k)

        return new_PP

    def addable_boxes(self):
        r"""
        Iterates through all `(i, j, k)` where it is valid to
        add an extra box to ``self``.

        EXAMPLES::

            sage: V = Partition3d([], lamb=[3], mu=[1,1], nu=[]); V
            3d partition with legs [3], [1, 1], [] and extra boxes []
            sage: list(V.addable_boxes())
            [(0, 0, 1), (2, 3, 0)]
        """
        # TODO: could use a slightly smarter algorithm...
        for i in range(self._Nx + 1):
            for j in range(self._Ny + 1):
                for k in range(self._Nz + 1):
                    if (i, j, k) not in self and self._is_box_valid(i, j, k):
                        yield (i, j, k)
                        break # can't add higher boxes

    def partitions_with_one_more_box(self):
        """
        Iterates through all partitions with one more box than ``self``
        """
        for (i, j, k) in self.addable_boxes():
            yield self.add_box(i, j, k, check=False)

class Partitions3d(UniqueRepresentation, Parent):
    """
    The set of 3d partitions with specified legs.

    EXAMPLES::

        sage: PPs = Partitions3d([3], [1,1], []); PPs
        3d partitions with legs [3], [1, 1], []
        sage: PP = PPs([]); PP
        3d partition with legs [3], [1, 1], [] and extra boxes []
        sage: PP in PPs
        True
        sage: PPs_finite = Partitions3d([], [], []); PPs_finite
        Finite 3d partitions
        sage: PPs == PPs_finite
        False
    """
    Element = Partition3d

    @staticmethod
    def __classcall_private__(cls, lamb=None, mu=None, nu=None):
        # UniqueRepresentation objects cannot have mutable parameters.
        # So we need to make lamb, mu, nu into Partitions.
        # This has the nice side effect of standardizing the representation.
        lamb = Partition(lamb if lamb else [])
        mu = Partition(mu if mu else [])
        nu = Partition(nu if nu else [])
        return cls.__classcall__(cls, lamb, mu, nu)
    
    def __init__(self, lamb, mu, nu):
        r"""
        Initializes ``self``.
        """
        Parent.__init__(self, category=InfiniteEnumeratedSets())

        # Lists are good enough for us
        self._lamb = lamb.to_list()
        self._mu = mu.to_list()
        self._nu = nu.to_list()

        # Minimum size of bounding box with given legs
        self._min_Nx = max(len(self._mu), self._nu[0] if self._nu else 0)
        self._min_Ny = max(len(self._nu), self._lamb[0] if self._lamb else 0)
        self._min_Nz = max(len(self._lamb), self._mu[0] if self._mu else 0)

        # Data of minimal configuration with given legs
        self._min_vol = None
        self._compute_minimal_volume()

        # Cache all partitions with k additional boxes once we've computed
        # them all for a given k. This saves work.
        self._generated_up_to = 0
        self._cache = [set([self.minimal_element()])]

    def _an_element_(self):
        """
        Returns a 3d partition in ``self``.
        """
        return self.minimal_element()
        
    def minimal_element(self):
        """
        Returns the element with the smallest volume in ``self``.
        """
        return self.element_class(self, boxes=[])

    def minimal_volume(self):
        """
        Returns the minimal possible volume of an element in ``self``.
        """
        return self._min_vol

    def _compute_minimal_volume(self):
        """
        Computes the *normalized* volume of the minimal configuration
        of boxes with given legs. Called on initialization. 
        """
        PP = self.minimal_element()
        vol = 0
        for (i, j, k) in PP.boxes(Nx=self._min_Nx, Ny=self._min_Ny, Nz=self._min_Nz):
            vol += 1 - PP._in_num_legs(i, j, k)
        self._min_vol = vol

    def __contains__(self, x):
        """
        Check if ``x`` is contained in ``self``.
        """
        if isinstance(x, self.element_class):
            return x.parent() == self
        else:
            return False

    def __repr__(self):
        """
        Return a string representation of ``self``.
        """
        if not self._lamb and not self._mu and not self._nu:
            return "Finite 3d partitions"
        else:
            return "3d partitions with legs %s, %s, %s" % \
                (self._lamb, self._mu, self._nu)

    def _hash_(self):
        """
        Return the hash of ``self``.
        """
        return hash(self._lamb) ^^ hash(self._mu) ^^ hash(self._nu)

    def legs(self):
        r"""
        Returns the three legs `\lambda`, `\mu`, and `\nu` of ``self``.
        """
        return Partition(self._lamb), Partition(self._mu), Partition(self._nu)

    def _compute_next_partitions(self):
        r"""
        Compute all 3d partitions in ``self`` with volume one more
        than what has already been computed and cached.
        """
        new_PPs = set()
        for PP in self._cache[-1]:
            for new_PP in PP.partitions_with_one_more_box():
                if new_PP not in new_PPs:
                    new_PPs.add(new_PP)
        self._cache.append(new_PPs)
        self._generated_up_to += 1

    def with_num_boxes(self, n):
        r"""
        Iterates through all elements of ``self`` with specified legs
        and volume exactly `n`.

        EXAMPLES::

            sage: PPs_finite = Partitions3d([], [], [])
            sage: list(PPs_finite.with_num_boxes(2))
            [3d partition with boxes [(1, 0, 0), (0, 0, 0)],
             3d partition with boxes [(0, 1, 0), (0, 0, 0)],
             3d partition with boxes [(0, 0, 0), (0, 0, 1)]]
            sage: [len(list(PPs_finite.with_num_boxes(k))) for k in (0..6)]
            [1, 1, 3, 6, 13, 24, 48]
        """
        while self._generated_up_to < n:
            self._compute_next_partitions()

        for PP in self._cache[n]:
            yield PP

    def up_to_num_boxes(self, n):
        r"""
        Iterates through all elements of ``self`` with specified legs
        and volume up to (and including) `n`.

        EXAMPLES::

            sage: PPs_finite = Partitions3d([], [], [])
            sage: list(PPs_finite.up_to_num_boxes(1))
            [3d partition with boxes [], 3d partition with boxes [(0, 0, 0)]]
            sage: [len(list(PPs_finite.up_to_num_boxes(k))) for k in (0..6)]
            [1, 2, 5, 11, 24, 48, 96]
        """
        k = 0
        while k <= n:
            for PP in self.with_num_boxes(k):
                yield PP
            k += 1

    def __iter__(self):
        r"""
        Iterates through all eleemnts of ``self``, in order of increasing
        volume.
        """
        for PP in self.up_to_num_boxes(PlusInfinity):
            yield PP

    def random_element_with_num_boxes(self, n):
        r"""
        Picks a random element with volume `n` in ``self``.

        NOTE: distribution is *not* uniform!

        ALGORITHM: pick a box to add uniformly at random (among all
        possible boxes to add), and do this `n` times.
        """
        PP = self.minimal_element()
        for _ in range(n):
            addable_boxes = list(PP.addable_boxes())

            import random
            box = random.choice(addable_boxes)

            PP = PP.add_box(*box)

        return PP
