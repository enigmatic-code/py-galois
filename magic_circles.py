#!/usr/bin/env python -t
# -*- mode: Python; py-indent-offset: 2; -*-

from __future__ import print_function

# generate "Magic Circles"

from galois import GF
from enigma import irange, gcd, printf

# calculate powers of element x in field, return x^k for k = a .. b
def powers(f, x, b, a=1):
  n = 1
  r = x
  while not(n > b):
    if not(n < a): yield r
    n += 1
    r = f.mul(r, x)

# find a generator for GF*(N), where f = GF(N)
def generator(f):
  for g in f.elements():
    if g == 0: continue
    if not any(x == 1 for x in powers(f, g, f.N // 2)):
      yield g

# make a perfect difference set of size n
def perfect_difference_set(n):

  # make the galois field GF(N) where N = n^3
  f = GF(n ** 3, cached=0)
  #printf("[perfect_difference_set: using field {f} ...]")

  # find an element of GF(N) that generates GF*(N)
  g = next(generator(f))

  # find the elements of subgroup GF*(n) in GF*(N)
  m = n * (n + 1) + 1
  x = next(powers(f, g, m, m))
  fstar = [x]
  fstar.extend(powers(f, x, n - 1, 2))

  # make the pds
  pds = [0, 1]
  for (i, x) in enumerate(powers(f, g, n ** 3, 2), start=2):
    if f.sub(x, g) in fstar:
      pds.append(i % m)

  pds.sort()
  return pds
        

# generate magic circles of size n
def magic(n):

  # make a perfect difference set of the required size
  pds = perfect_difference_set(n - 1)

  # generate all magic circles
  seen = dict()
  m = n * (n - 1) + 1
  for j in irange(1, m - 1):
    if gcd(j, m) != 1: continue
    ds = sorted((x * j) % m for x in pds)
    s = list(ds[i + 1] - ds[i] for i in irange(0, n - 2))
    s.append(m + ds[0] - ds[n - 1])
    # bring 1 to the start
    i = s.index(1)
    s = tuple(s[i:] + s[:i])
    if s[1] < s[-1] and not s in seen:
      yield s
      seen[s] = 1


if __name__ == "__main__":

  from enigma import arg

  n = arg(8, 0, int)
  printf("[n={n}]")

  for s in magic(n):
    printf("{s}")
