"""
PT box configurations.

All notation follows the paper arxiv:0709.3823 by Pandharipande-Thomas,
"The 3-fold vertex via stable pairs".

The full 3-leg vertex in Calabi-Yau specialization has been tested for
all legs of size up to 4, with series precision up to 9.
"""
from sage.misc.inherit_comparison import InheritComparisonClasscallMetaclass
from sage.misc.cachefunc import cached_method, cached_function

load("partition_3d.sage")

@add_metaclass(InheritComparisonClasscallMetaclass)
class PTConfiguration(Partition3d):
    """
    A PT configuration.
    """
    @staticmethod
    def __classcall_private__(cls, boxes, labels=None, lamb=None, mu=None, nu=None, check=True):
        """
        Constructs a PT configuration with legs with the appropriate parent.
        """
        if isinstance(boxes, cls):
            return boxes

        if not isinstance(boxes, (list, tuple)) or \
           not all(isinstance(box, tuple) and len(box) == 3 for box in boxes):
            raise ValueError("first argument must be a list of (i, j, k)")
        if labels and not isinstance(labels, dict):
            raise ValueError("second argument must be dict of labels")
            
        return PTConfigurations(lamb, mu, nu)(boxes, labels, check)

    def __init__(self, parent, boxes, labels=None, check=True):
        r"""
        Initializes ``self``.
        """
        self._Mx = 0
        self._My = 0
        self._Mz = 0

        self._length = 0
        self._unrestricted_paths = None

        if labels is None:
            self._labels = dict()
        else:
            self._labels = labels

        Partition3d.__init__(self, parent, boxes, check=False)
        if check is True:
            self.check()

    def check(self):
        r"""
        Check that ``self`` is a valid PT configuration.
        """
        for (i, j, k) in self._boxes:
            label = self._labels.get((i, j, k), None)
            if self._is_box_valid(i, j, k, label)[0] is False:
                raise ValueError("invalid box (%s, %s, %s, %s)" % (i, j, k, label))

    @cached_method
    def type_and_leg(self, i, j, k):
        r"""
        Returns a pair ``(box_type, leg)`` for the box at `(i, j, k)`.

        - ``box_type`` is either 1, 2, 3, or ``None``, corresponding
          to a type `I^-`, `II`, or `III` box, or an invalid box.

        - ``leg`` is either 1, 2, 3, or ``None``.

            - For type `I^-` boxes, this corresponds to the leg that
              the box belongs to.

            - For type `II` boxes, this corresponds to the only leg
              that the box *does not* belong to.

            - For type `III` boxes, this is always ``None``.
        """
        in_leg = [self._exists_in_lamb(i, j, k),
                  self._exists_in_mu(i, j, k),
                  self._exists_in_nu(i, j, k)]
        nlegs = in_leg.count(True)

        if nlegs == 1:
            if i < 0:
                return (nlegs, 1)
            elif j < 0:
                return (nlegs, 2)
            elif k < 0:
                return (nlegs, 3)
        elif nlegs == 2:
            return (nlegs, in_leg.index(False)+1)
        elif nlegs == 3:
            return (nlegs, None)

        return (None, None)

    def _is_box_valid(self, i, j, k, label=None):
        r"""
        Check that it is valid to have a box in ``self`` at `(i, j, k)`.

        Returns ``(valid, label)`` where:

        - ``valid`` is True if such a box is valid;

        - ``label`` is the most general possible label such a box can have.
          It is always ``None`` unless applicable (i.e. type III box)
        """
        box_type, box_leg = self.type_and_leg(i, j, k)
        if box_type is None:
            return (False, None) # box isn't even in support

        # Keep track of the most general possible label for this box
        box_label = None
        if box_type == 3:
            box_label = -1 # unlabeled is the most general

        def specialize_label(old, new):
            if old == -1 or (old == 0 and new >= 0) or old == new:
                return new
            elif old > 0 and new == 0:
                return old # valid labeled box: restrict an unrestricted path
            else:
                return None # invalid
        
        # Check all neighbors exist and record constraints on our label.
        for ii, jj, kk in self._neighbors(i, j, k):
            adj_type, adj_leg = self.type_and_leg(ii, jj, kk)
            if adj_type is None:
                continue # neighbor not in support; automatically OK

            elif (ii, jj, kk) in self:
                # Check for constraints on our label due to neighbor
                if adj_type != 3:
                    continue # no constraints
                adj_label = self._labels[ii, jj, kk]
                if adj_label == -1:
                    continue # unlabeled; no constraints

                if box_type == 3:
                    # Most general label is that of the neighbor.
                    box_label = specialize_label(box_label, adj_label)
                    if box_label is None:
                        return (False, None) # existing label is incompatible
                elif box_type == 1:
                    if adj_label != 0 and box_leg != adj_label:
                        # Neighbor has specified label and we don't match it
                        return (False, None)

            elif box_type == 3 and adj_type == 2:
                # Missing type II neighbor is OK, but constraints our label.
                box_label = specialize_label(box_label, adj_leg)
                if box_label is None:
                    return (False, None) # existing label is incompatible

            else:
                return (False, None) # missing neighbor, can't add box

        if box_type == 3:
            if label is None:
                return (True, box_label) # return most general possible label
            if box_label > 0 and label > 0:
                return (box_label == label, label)
            elif label >= box_label:
                return (True, label)
            else:
                return (False, None)
        else:
            return (True, label)

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
        return x in self._boxes

    def __repr__(self):
        """
        Return a string representation of ``self``.
        """
        return "PT configuration: boxes=%s, labels=%s" % \
            (list(self._boxes), self._labels)

    def _hash_(self):
        """
        Return the hash of ``self``.
        """
        return (super(PTConfiguration, self)._hash_() ^^
                hash(frozenset(self._labels)))

    def __copy__(self):
        """
        Return a copy of ``self``.
        """
        # Manually copy boxes, otherwise res._labels is self._labels
        res = super(PTConfiguration, self).__copy__()
        res._labels = self._labels.copy()
        return res

    def __eq__(self, other):
        """
        Return true if ``self`` is the same PT configuration as ``other``.
        """
        if isinstance(other, self.__class__):
            return (super(PTConfiguration, self).__eq__(other) and
                    self._labels == other._labels)
        return False

    def __ne__(self, other):
        """
        Return true if ``self`` is not the same PT configuration as ``other``.
        """
        return not self.__eq__(other)

    def plot(self):
        """
        Plot ``self`` as a Graphics3d object.

        TODO: fix this
        """
        from sage.plot.plot3d.shapes import ColorCube
        cube = ColorCube([.5,.5,.5], ['red', 'blue', 'green'], opacity=0.85)
        plot = sum(cube.translate(*b) for b in self.boxes(labels=False))
        
        plot.show(aspect_ratio=1)

    def boxes(self, **kwargs):
        r"""
        Iterate through all boxes ``(i, j, k)`` in ``self``.

        If ``labels=True``, then return each box in the form
        ``(i, j, k, label)``. If not a type III box, ``label`` is ``None``.
        """
        do_labels = False
        if 'labels' in kwargs:
            do_labels = kwargs.get('labels')
        for (i, j, k) in self._boxes:
            if do_labels is True:
                yield (i, j, k, self._labels.get((i, j, k), None))
            else:
                yield (i, j, k)

    def boxes_with_arbitrary_label(self):
        r"""
        Iterates through all type III boxes `(i, j, k)` in ``self``
        which have an arbitrary label.

        These are factors of `\mathbb{P}^1` in the fixed locus.
        """
        for (i, j, k) in self.boxes():
            if self._labels.get((i, j, k), None) == 0:
                yield (i, j, k)

    def _subsumes(self, other):
        r"""
        Returns ``True`` if the fixed locus corresponding to ``self``
        contains the fixed locus of ``other``.

        This happens when ``self`` has at least one unrestricted path
        component such that *all* boxes in that component are specialized
        to the same label in ``other``, and everything else is identical.
        """
        if self._boxes != other._boxes:
            return False

        # Check if any unrestricted path components have been restricted.
        restricted = set()
        for component in self.unrestricted_paths():
            S = set(other._labels[i, j, k] for (i, j, k) in component)
            if len(S) != 1:
                continue
            label = S.pop()
            if label > 0:
                restricted.update(component)
        if len(restricted) == 0:
            return False # nothing restricted, so doesn't subsume

        # Check that everything else is identical.
        return all(self._labels.get(box) == other._labels.get(box)
                   for box in self._boxes if box not in restricted)

    def length(self):
        r"""
        Returns the *length* of ``self``, defined as the number of boxes
        where unlabeled type `III` boxes count twice.
        """
        return self._length

    def volume(self):
        r"""
        Returns the *normalized* volume of ``self``.

        The normalized volume of a PT configuration is defined as
        its length plus the normalized volume of the legs.
        """
        return self.length() + self.parent().minimal_volume()

    def bounding_box(self):
        r"""
        Returns the smallest box `[Mx, Nx) x [My, Ny) x [Mz, Nz)` that
        contains all boxes in ``self``.

        EXAMPLES::

            sage: Partition3d([(0,0,0)], [], [], []).bounding_box()
            (1, 1, 1)
            sage: Partition3d([], [3], [1,1], []).bounding_box()
            (2, 3, 1)
        """
        return (self._Mx, self._Nx), (self._My, self._Ny), (self._Mz, self._Nz)

    def _neighbors(self, i, j, k, increasing_only=True):
        r"""
        Iterates through neighbors of `(i, j, k)`. If ``increasing_only=True``,
        then include only neighboring boxes generated by `(i, j, k)`. This
        means that coordinates are only allowed to *increase* by 1.
        """
        yield (i+1, j, k)
        yield (i, j+1, k)
        yield (i, j, k+1)
        if not increasing_only:
            yield (i-1, j, k)
            yield (i, j-1, k)
            yield (i, j, k-1)

    def unrestricted_paths(self):
        r"""
        Returns a list of all unrestricted paths in ``self``. Each path
        is a set of its constituent boxes.
        """
        if self._unrestricted_paths is not None:
            return self._unrestricted_paths
            
        boxes = set(self.boxes_with_arbitrary_label())
        res = list()
        seen = set()
        for initial_box in boxes:
            if initial_box in seen:
                continue
            component = set()
            stack = [initial_box]
            while stack:
                box = stack.pop()
                component.add(box)
                for adj_box in self._neighbors(*box, increasing_only=False):
                    if adj_box in seen:
                        continue
                    if adj_box in boxes:
                        stack.append(adj_box)
                        seen.add(adj_box)
            res.append(component)

        self._unrestricted_paths = res
        return res

    def dimension(self):
        r"""
        Return the dimension of the fixed locus represented by ``self``.
        """
        return len(self.unrestricted_paths())

    def _unnormalized_character(self, x, y, z, KRing=None):
        r"""
        Returns the character associated to ``self`` (see :meth:`character`),
        multipled by the additional factor `(1-x)(1-y)(1-z)`.

        This guarantees the result is a Laurent polynomial in `x, y, z`
        and the K-theory variables in ``KRing`` (default variables: `u_i`.)
        """
        R = x.parent()
        if KRing is None:
            wtvars = list(R.variable_names())
            Kvars = ['u%s' % i for i in xrange(self.dimension())]
            KRing = LaurentPolynomialRing(R.base_ring(), Kvars + wtvars)
        
        char = R.zero()
        u = KRing.gens()[:self.dimension()] # K-theory variables

        # Add boxes in unrestricted path components, with O(-1) twist each.
        counted_boxes = set()
        for i, component in enumerate(self.unrestricted_paths()):
            counted_boxes.update(component)
            nboxes = len(component)
            contrib = sum(x**i * y**j * z**k for (i, j, k) in component)
            char += ~u[i] * contrib

        # Add all other boxes not in the legs.
        for (i, j, k) in self.boxes():
            if (i, j, k) not in counted_boxes:
                contrib = x**i * y**j * z**k
                if self._labels.get((i, j, k), None) == -1:
                    contrib *= 2 # unlabeled type III box
                char += contrib

        char *= (1-x) * (1-y) * (1-z)

        # Add boxes in legs
        char += self.parent()._unnormalized_legs_character(x, y, z)

        return char

    def character(self, x, y, z, KRing=None):
        r"""
        Return the character associated to ``self``, in variables `x, y, z`.

        Note that the character of a PT configuration may include
        non-trivial elements of the K-theory of `(\mathbb{P}^1)^m`.
        Generators `\mathcal{O}(1)` of each `\mathbb{P}^1` should be
        generators of ``KRing``.
        """
        return self._unnormalized_character(x,y,z,KRing) / ( (1-x)*(1-y)*(1-z) )

    def _add_box_in_place(self, i, j, k, label=None):
        r"""
        Add a box at `(i, j, k)` with ``label`` to ``self`` in place.

        This is an internal method. Users should use :meth:`add_box` instead.

        Ensure that if ``label`` is not ``None`` then `(i, j, k)` is
        actually a type III box! This is not checked.
        """
        self._require_mutable()

        super(PTConfiguration, self)._add_box_in_place(i, j, k)

        self._Mx = min(i, self._Mx)
        self._My = min(j, self._My)
        self._Mz = min(k, self._Mz)

        if label is not None:
            self._labels[i, j, k] = label

        box_type, box_leg = self.type_and_leg(i, j, k)
        if box_type == 3 and self._labels[i, j, k] == -1:
            self._length += 2 # unlabeled type III boxes count as 2
        else:
            self._length += 1
        
        if box_type == 1 or (box_type == 3 and self._labels[i, j, k] > 0):
            # May have to restrict some unrestricted paths.
            if box_type == 1:
                label = box_leg
            paths = self.unrestricted_paths()
            for adj_box in self._neighbors(i, j, k):
                for component in paths:
                    if adj_box not in component:
                        continue
                    for (ii, jj, kk) in component:
                        self._labels[ii, jj, kk] = label

        self._unrestricted_paths = None

    def add_box(self, i, j, k, label=None, check=True):
        r"""
        Return a new 3d partition which is ``self`` with an
        extra box at `(i, j, k)` with ``label``.

        Set ``check=False`` to skip checking that adding such a box is valid.

        EXAMPLES::

            sage: V = Partition3d([], lamb=[3], mu=[1,1], nu=[]); V
            3d partition with legs [3], [1, 1], [] and extra boxes []
            sage: W = V.add_box(0, 0, 1); W
            3d partition with legs [3], [1, 1], [] and extra boxes [(0, 0, 1)]
            sage: W.character() - V.character()
            z
        """
        with self.clone(check=check) as new_config:
            new_config._add_box_in_place(i, j, k, label)

        return new_config

    def addable_boxes(self):
        r"""
        Iterates through all ``(i, j, k, label)`` where it is valid to
        add an extra box to ``self``.

        EXAMPLES::

            sage: V = Partition3d([], lamb=[3], mu=[1,1], nu=[]); V
            3d partition with legs [3], [1, 1], [] and extra boxes []
            sage: list(V.addable_boxes())
            [(0, 0, 1), (2, 3, 0)]
        """
        # TODO: could use a slightly smarter algorithm...
        for i in xrange(self._Mx-2, self._Nx):
            for j in xrange(self._My-2, self._Ny):
                for k in xrange(self._Mz-2, self._Nz):
                    if (i, j, k) in self:
                        break # can't add higher boxes
                    valid, label = self._is_box_valid(i, j, k, label=None)
                    if not valid:
                        continue
                    yield (i, j, k, label)

                    box_type, _ = self.type_and_leg(i, j, k)
                    if box_type == 3 and label == -1:
                        # Can add a labeled type III box with arbitrary label
                        # instead of an unlabeled type III box.
                        yield (i, j, k, 0)
        
    def partitions_with_one_more_box(self):
        """
        Iterates through all configurations with one more box than ``self``
        """
        for (i, j, k, label) in self.addable_boxes():
            yield self.add_box(i, j, k, label, check=False)
            
class PTConfigurations(Partitions3d):
    """
    The set of PT box configurations with given legs.
    """
    Element = PTConfiguration

    @staticmethod
    def __classcall_private__(cls, lamb=None, mu=None, nu=None):
        # UniqueRepresentation objects cannot have mutable parameters.
        # So we need to make lamb, mu, nu into Partitions.
        # This has the nice side effect of standardizing the representation.
        lamb = Partition(lamb if lamb else [])
        mu = Partition(mu if mu else [])
        nu = Partition(nu if nu else [])
        return PTConfigurations.__classcall__(cls, lamb, mu, nu)

    def __init__(self, lamb, mu, nu):
        r"""
        Initializes ``self``.
        """
        Partitions3d.__init__(self, lamb, mu, nu)

        self._legs = Partitions3d(lamb, mu, nu).minimal_element()

        self._cache = [set([self.minimal_element()])]

    def __repr__(self):
        r"""
        Return a string representation of ``self``.
        """
        return "PT configurations with legs %s, %s, %s" % \
            (self._lamb, self._mu, self._nu)

    @cached_method
    def _unnormalized_legs_character(self, x, y, z):
        r"""
        Return the character of all boxes in the legs, in `x`, `y`, `z`.
        This is the character of the underlying Cohen-Macaulay curve.
        """
        return self._legs._unnormalized_character(x, y, z)

    def _compute_next_partitions(self):
        r"""
        Compute all configurations in ``self`` obtained by adding one
        box to what has already been computed and cached.

        Note that adding one box may add two to length, via an unlabeled
        type III box.
        """
        if self._generated_up_to+1 == len(self._cache):
            self._cache.append(set()) # in case we increase length by 2
        self._cache.append(set())

        for config in self._cache[self._generated_up_to]:
            for new_config in config.partitions_with_one_more_box():
                length = new_config.length()
                if new_config not in self._cache[length]:
                    self._cache[length].add(new_config)

        self._generated_up_to += 1

        # Check if any configurations subsume other ones, and remove them.
        exclude = set()
        L = self._cache[self._generated_up_to]
        for config in L:
            if config in exclude:
                continue
            if any(config.boxes_with_arbitrary_label()):
                for other in L:
                    if other in exclude or other is config:
                        continue
                    if config._subsumes(other):
                        exclude.add(other)
        self._cache[self._generated_up_to] = L - exclude
