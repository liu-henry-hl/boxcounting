"""
Examples for using Partition3d/Partitions3d objects.

Run test_bare_vertex() and test_DT_PT() to make sure everything works.
"""
load("bare_vertex.sage")

tR.<t> = LaurentPolynomialRing(QQ)
qtR = Default.boxcounting_ring.change_ring(tR)
q = qtR.gen()

def compute_refined_vertex_by_index_limit(lamb, mu, nu, n=4):
    """
    Takes the index limit of the bare vertex to get the
    refined vertex in `qt^-1` and `qt`, with at least `n`
    terms of precision in `q`.

    This is by Nekrasov-Okounkov, section 8.
    """
    bare = BareVertex(lamb, mu, nu).series_unreduced(n)

    return KTheory.index_limit(bare, t)

def compute_refined_vertex_by_formula(lamb, mu, nu, n=4):
    """
    Uses formula 23 or 24 in Iqbal-Kozcaz-Vafa to compute the
    refined vertex in `qt^-1` and `qt`, with at least `n`
    terms of precision in `q`.
    """
    if not lamb and not mu and not nu:
        # Degree 0 case: use formula 23 (MacMahon generalization)
        M = qtR.one().add_bigoh(n)
        M *= prod((1 - q^(i+j-1)*t^(i-j+1))^-1 \
                  for i in xrange(1, n) for j in xrange(1, n-i+1))
        return M
    else:
        # General case: use formula 24.
        raise NotImplementedError # TODO!!

"""
Code for testing that all examples in this file work.
"""
def random_partition(size_up_to=8):
    """
    Returns a random partition.
    """
    from random import randint
    return Partitions(randint(0, size_up_to)).random_element()

def test_equal(func1, func2, *args, **kwds):
    """
    Test equality and print an error if unequal.
    """
    res1 = func1(*args, **kwds)
    res2 = func2(*args, **kwds)
    if res1 != res2:
        print "TEST FAILED"
        print "  %s = %s" % (func1.__name__, res1)
        print "  %s = %s" % (func2.__name__, res2)
        print "  args: %s, kwds: %s" % (args, kwds)

def test_bare_vertex():
    """
    Run some tests involving all examples in this file.
    """
    # Test index limit of bare vertex in deg 0 case
    test_equal(compute_refined_vertex_by_index_limit,
               compute_refined_vertex_by_formula, [], [], [], n=4)

"""
Test DT/PT correspondence.
"""
def test_DT_PT():
    """
    Test that the full equivariant reduced DT vertex is equal to
    the PT vertex.
    """
    DT = lambda lamb, mu, nu, n: BareVertex(lamb, mu, nu).series(n)
    PT = lambda lamb, mu, nu, n: BareVertexPT(lamb, mu, nu).series(n)

    # Big partition, small series test
    lamb, mu, nu = random_partition(5), random_partition(5), random_partition(6)
    print "Testing n=2, %s, %s, %s" % (lamb, mu, nu)
    test_equal(DT, PT, lamb, mu, nu, 2)

    # Small partition, big series test (might take a while: ~60secs)
    lamb, mu, nu = random_partition(3), random_partition(3), random_partition(2)
    print "Testing n=3, %s, %s, %s" % (lamb, mu, nu)
    test_equal(DT, PT, lamb, mu, nu, 3)

def test_DT_PT_hashed():
    """
    Test that the full equivariant reduced DT vertex is equal to
    the PT vertex after plugging in some values for `x`, `y`, and `z` in
    a large finite field.
    """
    ct = KTheory_hashed
    DT = lambda lamb, mu, nu, n: BareVertex(lamb, mu, nu, ct).series(n)
    PT = lambda lamb, mu, nu, n: BareVertexPT(lamb, mu, nu, ct).series(n)

    # Big partition, small series test
    lamb, mu, nu = random_partition(5), random_partition(5), random_partition(6)
    print "Testing n=5, %s, %s, %s" % (lamb, mu, nu)
    test_equal(DT, PT, lamb, mu, nu, 5)

    # Small partition, big series test (might take a while: ~60secs)
    lamb, mu, nu = random_partition(3), random_partition(3), random_partition(2)
    print "Testing n=8, %s, %s, %s" % (lamb, mu, nu)
    test_equal(DT, PT, lamb, mu, nu, 8)

def test_DT_PT_hashed_thorough():
    ct = KTheory_hashed
    DT = lambda lamb, mu, nu, n: BareVertex(lamb, mu, nu, ct).series(n)
    PT = lambda lamb, mu, nu, n: BareVertexPT(lamb, mu, nu, ct).series(n)

    for lamb in chain(*[Partitions(n) for n in xrange(4,0,-1)]):
        for mu in chain(*[Partitions(n) for n in xrange(4,0,-1)]):
            print "Reached %s, %s" % (lamb, mu)
            for nu in chain(*[Partitions(n) for n in xrange(4,0,-1)]):
                test_equal(DT, PT, lamb, mu, nu, 6)

def test_DT_PT_counts():
    """
    Test that DT = PT only on non-equivariant counts.
    """
    DT_wt = lambda PP: 1
    PT_wt = lambda PP: 2^PP.dimension() # \chi_top((P1)^dim) = 2^dim
    
    DT = lambda lamb, mu, nu, n: BareVertex(lamb, mu, nu).series(n, DT_wt)
    PT = lambda lamb, mu, nu, n: BareVertexPT(lamb, mu, nu).series(n, PT_wt)

    # Big partition, small series test
    lamb, mu, nu = random_partition(8), random_partition(8), random_partition(9)
    print "Testing n=5, %s, %s, %s" % (lamb, mu, nu)
    test_equal(DT, PT, lamb, mu, nu, 5)

    # Small partition, big series test (might take a while: ~60secs)
    lamb, mu, nu = random_partition(4), random_partition(4), random_partition(4)
    print "Testing n=9, %s, %s, %s" % (lamb, mu, nu)
    test_equal(DT, PT, lamb, mu, nu, 9)

def test_DT_PT_counts_thorough():
    DT_wt = lambda PP: 1
    PT_wt = lambda PP: 2^PP.dimension() # \chi_top((P1)^dim) = 2^dim
    
    DT = lambda lamb, mu, nu, n: BareVertex(lamb, mu, nu).series(n, DT_wt)
    PT = lambda lamb, mu, nu, n: BareVertexPT(lamb, mu, nu).series(n, PT_wt)

    for lamb in chain(*[Partitions(n) for n in xrange(4,0,-1)]):
        for mu in chain(*[Partitions(n) for n in xrange(4,0,-1)]):
            for nu in chain(*[Partitions(n) for n in xrange(4,0,-1)]):
                test_equal(DT, PT, lamb, mu, nu, 9)
