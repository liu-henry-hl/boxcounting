"""
Examples for using Partition3d/Partitions3d objects.

Run test_partition_3d() to make sure everything in here works.
"""
load("partition_3d.sage")

qR.<q> = LaurentSeriesRing(ZZ)

def compute_macmahon_by_counting(n=10):
    """
    By enumeration, return the generating series for finite 3d partitions
    with at least ``n`` terms of precision.
    """
    PPs = Partitions3d([], [], [])
    M = sum(q^(PP.volume()) for PP in PPs.up_to_num_boxes(n-1))

    return qR(M).add_bigoh(n)

def compute_macmahon_by_formula(n=10):
    """
    By MacMahon's formula, return the generating series for finite
    3d partitions with at least ``n`` terms of precision.
    """
    M = qR.one().add_bigoh(n)
    M *= prod((1 - q^k)^-k for k in range(1, n))

    return M

def compute_topological_vertex_by_counting(lamb, mu, nu, n=8):
    r"""
    By enumeration, return the topological vertex in `1/q` for
    3d partitions with given legs, with at least `n` terms of precision.

    Implements formula 3.23 in Okounkov-Reshetikhin-Vafa to relate
    the generating series with the topological vertex. Since it may
    involve `q^{1/2}`, all variables are squared.
    """
    lamb, mu, nu = Partition(lamb), Partition(mu), Partition(nu) # in case

    PPs = Partitions3d(lamb, mu, nu)
    P = sum(q^(2*PP.volume()) for PP in PPs.up_to_num_boxes(n-1))
    P = P.truncate_laurentseries(P.valuation() + 2*n)

    C = P * prod((1 - q^(2*i))^i for i in range(1, n))

    def partition_norm(lamb):
        return sum(l^2 for l in lamb)

    C *= q^(partition_norm(lamb.conjugate()) + \
            partition_norm(mu.conjugate()) + \
            partition_norm(nu.conjugate()))

    return C

def skew_schur_q(lamb, mu, nu, q, n=8):
    r"""
    Returns the skew Schur function `s_{lamb/mu}(q^{-nu-rho})`,
    with at least `n` terms of precision.

    Here `rho = (-1/2, -3/2, -5/2, ...)`.
    """
    if not lamb.contains(mu):
        return qR.zero()
    
    s = SymmetricFunctions(ZZ).s()
    sp = SkewPartition([lamb, mu])
    get = lambda mu, i: mu[i] if i < len(mu) else 0

    # Compute the skew Schur function with as many variables as necessary
    nvars = max(get(nu, 0), 1) * sum(nu) + n+2
    f = s.skew_schur(sp).expand(nvars, 'x')
    args = (q^(-get(nu, i) + i + 1/2) for i in range(nvars))
    fq = qR(f(*args))

    return fq.truncate_laurentseries(fq.valuation() + 2*n)

def compute_topological_vertex_by_formula(lamb, mu, nu, n=8):
    r"""
    By the Okounkov-Reshetikhin-Vafa formula, return the topological
    vertex in `1/q` for 3d partitions with given legs, with at least
    `n` terms of precision.

    Implements formula 3.15 in Okounkov-Reshetikhin-Vafa.
    """
    lamb, mu, nu = Partition(lamb), Partition(mu), Partition(nu) # in case

    def partition_kappa(lamb):
        return 2 * sum(j - i for i, j in lamb.cells())

    prefactor = q^(-partition_kappa(lamb) - partition_kappa(nu))

    prefactor *= skew_schur_q(nu.conjugate(), [], [], q^2, n)

    res = qR.zero()
    for k in range(lamb.size()+1):
        for eta in Partitions(k, outer=lamb.conjugate()):
            res += skew_schur_q(lamb.conjugate(), eta, nu, q^2, n) * \
                   skew_schur_q(mu, eta, nu.conjugate(), q^2, n)

    return prefactor * res.truncate_laurentseries(res.valuation() + 2*n)

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
        print("TEST FAILED")
        print("  %s = %s" % (func1.__name__, res1))
        print("  %s = %s" % (func2.__name__, res2))
        print("  args: %s, kwds: %s" % (args, kwds))

def test_partition_3d():
    """
    Run some tests involving all examples in this file.
    """
    # Test enumeration of finite 3d partitions
    test_equal(compute_macmahon_by_counting,
               compute_macmahon_by_formula, n=10)

    # Test enumeration of 3d partitions with legs
    for _ in range(3):
        lamb = random_partition(size_up_to=3)
        mu = random_partition(size_up_to=3)
        nu = random_partition(size_up_to=3)
        test_equal(compute_topological_vertex_by_counting,
                   compute_topological_vertex_by_formula,
                   lamb, mu, nu, n=6)
