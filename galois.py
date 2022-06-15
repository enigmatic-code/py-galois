#! python3
# -*- mode: Python; py-indent-offset: 2; -*-

from __future__ import print_function

# an implementation of finite Galois fields

from enigma import (prime_factor, invmod, irange, peek, identity, printf)

# return a finite field of order N (N must be a power of a prime)
# where N is a non-trivial power of a prime the irreducible polynomial can be provided
# (as a list of coefficients (ala Polynomial()) or an integer in base p)
# if it is not provided one will be generated
def GF(N, poly=None, cached=1):

  # do we want to cache polynomial generated fields?
  # (a field can be cached by calling the .cached() method on it)
  cache = ((lambda f: f.cached()) if cached else identity)

  if N > 1:
    # the order is always p^n for prime n
    fs = list(prime_factor(N))
    if len(fs) > 1: raise ValueError("impossible (cannot construct GF({N}))".format(N=N))
    (p, n) = fs[0]

    # if n > 1 we can use a polynomial field
    if n > 1:
      if poly is None: poly = _gf_irreducible.get(N, None) or peek(poly_irreducible(p, n))
      #printf("[GF(N={N}): poly={poly[0]} [{poly[1]}]]", poly=(poly_print(poly), poly_value(poly, p)) if isinstance(poly, list) else (poly_print(reversed(nsplit(poly, base=p))), poly))
      if p == 2:
        return cache(_GF_2(n, poly))
      else:
        return cache(_GF_poly(p, n, poly))

  # integers mod N provides a model for N=0, 1, prime
  return _GF_mod(N)

# some monic irreducible polynomials to save generating for small values
_gf_irreducible = {
  # 2^n
  4: 7, 8: 11, 16: 19, 32: 37, 64: 67, 128: 131, 256: 283, 512: 515, 1024: 1033, 2048: 2053,
  # 3^n
  9: 10, 27: 34, 81: 86, 243: 250, 729: 748, 2187: 2206, 6561: 6572,
  # 5^n
  25: 27, 125: 131, 625: 627, 3125: 3176,
  # 7^n
  49: 50, 343: 345, 2401: 2409,
  # 11^n
  121: 122, 1331: 1376,
  # other powers (so we're good up to 2000)
  169: 171, 289: 292, 361: 362, 529: 530, 841: 843, 961: 962, 1369: 1371, 1681: 1684, 1849: 1850,
}


# parent class for GF objects
class _GF(object):

  def __init__(self, N):
    self.N = N

  def __repr__(self):
    return self.__class__.__name__ + "(N=" + str(self.N) + ")"

  def elements(self):
    return irange(0, self.N - 1)

  # choose a random element
  def choose(self):
    import random
    return random.randint(0, self.N - 1)

  # inverse of an operator
  def _inv(self, op, i, a):
    for b in self.elements():
      if op(a, b) == i:
        return b

  def add_inv(self, a):
    return self._inv(self.add, 0, a)

  def sub(self, a, b):
    return self.add(a, self.add_inv(b))

  def mul_inv(self, a):
    return self._inv(self.mul, 1, a)

  def div(self, a, b):
    return self.mul(a, self.mul_inv(b))

  def pow(self, a, k):
    if k == 0: return 1
    if k == 1: return a
    r = 1
    while k > 0:
      (k, m) = divmod(k, 2)
      if m: r = self.mul(r, a)
      if k: a = self.mul(a, a)
    return r

  # table of an operator
  def _table(self, op):
    for a in self.elements():
      yield list(op(a, b) for b in self.elements())

  # addition table
  def table_add(self):
    for row in self._table(self.add): yield row

  # multipication table
  def table_mul(self):
    for row in self._table(self.mul): yield row

  # return a cached version of this field
  def cached(self):
    return _GF_table(self.N, list(self.table_add()), list(self.table_mul()))

  # verify a field
  def verify(self, verbose=0):
    from enigma import (Accumulator, product)

    r = Accumulator(fn=(lambda a, b: a & b), value=True)

    def check(text, value, verbose=0):
      if verbose: printf("  [{text} -> {value}]")
      r.accumulate(value)

    if verbose: printf("[VERIFYING ...]")
    S = self.elements()
    add = self.add
    mul = self.mul
    closed = lambda fn: all(fn(a, b) in S for (a, b) in product(S, repeat=2))
    associative = lambda fn: all(fn(a, fn(b, c)) == fn(fn(a, b), c) for (a, b, c) in product(S, repeat=3))
    commutative = lambda fn: all(fn(a, b) == fn(b, a) for (a, b) in product(S, repeat=2))
    # add is closed
    check("add: closed", closed(add), verbose)
    # add is associative
    check("add: associative", associative(add), verbose)
    # add is commutatative
    check("add: commutative", commutative(add), verbose)
    # every element had an additive inverse
    check("add: inverse", all(sum(add(a, b) == 0 for b in S) == 1 for a in S), verbose)
    # mul is closed
    check("mul: closed", closed(mul), verbose)
    # mul is associative
    check("mul: associative", associative(mul), verbose)
    # mul is commutative
    check("mul: commutative", commutative(mul), verbose)
    # every non-zero element has a multiplicative inverse
    if 1 in S: check("mul: inverse", all(sum(mul(a, b) == 1 for b in S) == 1 for a in S if a != 0), verbose)
    # mul distributes over add
    check("mul: distributive", all(mul(a, add(b, c)) == add(mul(a, b), mul(a, c)) for (a, b, c) in product(S, repeat=3)), verbose)
    # 0 and 1 behave themselves
    check("add: zero", all(add(0, a) == a for a in S), verbose)
    check("mul: zero", all(mul(0, a) == 0 for a in S), verbose)
    if 1 in S: check("mul: one", all(mul(1, a) == a for a in S), verbose)
    if verbose: printf("[VERIFIED]" if r.value else "[FAILED]")
    return r.value


# integers mod N
class _GF_mod(_GF):
  def __init__(self, N):
    super(_GF_mod, self).__init__(N)
    self.add = lambda a, b: (a + b) % N
    self.mul = lambda a, b: (a * b) % N
    self.add_inv = lambda a: (-a) % N
    self.mul_inv = lambda a: (None if a == 0  else invmod(a, N))


# addition/multiplication tables provided
class _GF_table(_GF):
  def __init__(self, N, t_add, t_mul):
    super(_GF_table, self).__init__(N)
    self.add = lambda a, b: t_add[a][b]
    self.mul = lambda a, b: t_mul[a][b]
    self.add_inv = lambda a: t_add[a].index(0)
    self.mul_inv = lambda a: (None if a == 0 else t_mul[a].index(1))
    self.cached = lambda: self


# GF(2^n) polys are encoded as bit vectors
class _GF_2(_GF):

  def __init__(self, n, poly):
    N = (1 << n)
    super(_GF_2, self).__init__(N)
    self.mask = N
    self.poly = (poly_value(poly, 2) if isinstance(poly, list) else poly)

  def add(self, a, b):
    return a ^ b

  sub = add

  def mul(self, a, b):
    mask = self.mask
    poly = self.poly
    r = 0
    while a and b:
      if b & 1: r ^= a
      a <<= 1
      if a & mask: a ^= poly
      b >>= 1
    return r


# GF(p^n) general polynomial implementation

from enigma import (nsplitter, poly_value, poly_add, poly_mul, poly_print, cache)

int2poly = lambda p, b: list(nsplitter(p, base=b))

class _GF_poly(_GF):

  def __init__(self, p, n, poly):
    N = p ** n
    super(_GF_poly, self).__init__(N)
    self.p = p
    self.n = n
    self.poly = (poly if isinstance(poly, list) else int2poly(poly, p))
    self._e2p_cache = dict()

  # element -> poly
  def e2p(self, e):
    r = self._e2p_cache.get(e)
    if r is None:
      r = int2poly(e, self.p)
      self._e2p_cache[e] = r
    return r

  # poly -> element
  def p2e(self, p):
    return poly_value(poly_mod(p, self.p), self.p)

  # addition
  def add(self, a, b):
    # add the corresponding polys
    return self.p2e(poly_add(self.e2p(a), self.e2p(b)))

  def sub(self, a, b):
    # subtract the corresponding polys
    return self.p2e(poly_sub(self.e2p(a), self.e2p(b)))

  # multiplication
  def mul(self, a, b):
    # multiply the corresponding polys, and get the remainder modulo the irreducible poly
    (d, r) = poly_divmod(poly_mul(self.e2p(a), self.e2p(b)), self.poly)
    return self.p2e(r)

  def pow(self, a, k):
    if k == 0: return 1
    if k == 1: return a
    p = self.e2p(a)
    r = self.e2p(1)
    while k > 0:
      (k, m) = divmod(k, 2)
      if m: r = poly_mul(r, p)
      if k: p = poly_mul(p, p)
      if m or k: p = poly_mod(p, self.p)
      (d, r) = poly_divmod(r, self.poly)
    return self.p2e(r)

  # generate irreducible monic polys
  def irreducible_poly(self):
    for p in poly_irreducible(self.p, self.n):
      yield p


# some extra polynomial stuff

from enigma import (poly_map, poly_zero, poly_unit, poly_from_pairs, poly_sub)

# reduce poly coefficients mod m
def poly_mod(p, m):
  return poly_map(p, (lambda x: x % m))

# in the following functions
# div is used to divide coefficients if divisor is not monic
# normalise is used to keep polynomials in a certain domain

# divide two polynomials p / q
def poly_divmod(p, q, div=None, normalise=identity):
  fn = (identity if q[-1] == 1 else (lambda x: div(x, q[-1])))
  (d, r) = (poly_zero, p)
  while r != poly_zero:
    k = len(r) - len(q)
    if k < 0: break
    x = poly_from_pairs([(k, fn(r[-1]))])
    d = normalise(poly_add(d, x))
    r = normalise(poly_sub(r, normalise(poly_mul(x, q))))
  return (d, r)

# if irreducible polynomials are not provided we can find them as follows...

# generate irreducible monic polys for GF(m^n)
def poly_irreducible(m, n):
  from itertools import (product, combinations)

  # everything happens mod m (which is the prime (p) in N = p^n)
  normalise = (lambda p: poly_mod(p, m))
  field = GF(m)
  div = (lambda a, b: field.div(a, b))

  # p^n mod q
  def poly_powmod(p, n, q, div=None, normalise=identity):
    r = poly_unit
    while n > 0:
      (n, m) = divmod(n, 2)
      if m: r = normalise(poly_mul(r, p))
      if n: p = normalise(poly_mul(p, p))
    (d, r) = poly_divmod(r, q, div=div, normalise=normalise)
    return r

  # gcd
  def poly_gcd(p, q, div=None, normalise=identity):
    while q != poly_zero:
      (d, r) = poly_divmod(p, q, div=div, normalise=normalise)
      (p, q) = (q, r)
    return p

  # rabin test for irreducible polys
  # https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields#Rabin's_test_of_irreducibility
  def is_irreducible(p):
    x = [0, 1]
    q = x
    for i in irange(1, len(p) // 2):
      q = poly_powmod(q, m, p, div=div, normalise=normalise)
      g = poly_gcd(p, normalise(poly_sub(q, x)), div=div, normalise=normalise)
      if len(g) > 1: return False
    return True

  # consider polynomials with increasing numbers of non-zero coefficients
  for k in irange(1, n):
    for s in product(irange(1, m - 1), repeat=k):
      for js in combinations(irange(1, n - 1), k - 1):
        p = poly_from_pairs([(0, s[0]), (n, 1)] + list(zip(js, s[1:])))
        if is_irreducible(p):
          yield p


if __name__ == "__main__" or __name__ == "<run_path>":

  from enigma import arg

  N = arg(7, 0, int)

  try:
    printf("[generating GF({N}) ...]")
    field = GF(N)
  except ValueError as e:
    printf("ERROR: {e}")
    exit()
  field.verify(verbose=1)

  printf("GF[{N}].add = [")
  for row in field.table_add(): printf("  {row},")
  printf("]")

  printf("GF[{N}].mul = [")
  for row in field.table_mul(): printf("  {row},")
  printf("]")

