__all__ = ['gcd', 'lcm', 'prod', 'comb', 'perm', 'pow']

import sys
from math import factorial

def _gcd2(a, b):
	'''Greatest Common Divisor between a and b.'''
	while b:
		a, b = b, a % b
	return a

def _gcd(*integers):
	'''Greatest Common Divisor.'''
	it = iter(integers)
	res = next(it)

	for x in it:
		res = _gcd2(x, res)
	return res

def _lcm(*integers):
	'''Least Common Multiple.'''
	it = iter(integers)
	res = next(it)

	for x in it:
		res = res * x // _gcd2(res, x)
	return res

def _prod(iterable, start=1):
	'''
	Calculate the product of all the elements in the input iterable.

	The default start value for the product is 1.

	When the iterable is empty, return the start value.  This function is
	intended specifically for use with numeric values and may reject
	non-numeric types.
	'''
	res = start
	for x in iterable:
		res *= x
	return res

def _comb(n, k):
	'''
	Number of ways to choose k items from n items without repetition and without order.

	Evaluates to n! / (k! * (n - k)!) when k <= n and evaluates
	to zero when k > n.

	Also called the binomial coefficient because it is equivalent
	to the coefficient of k-th term in polynomial expansion of the
	expression (1 + x)**n.

	Raises TypeError if either of the arguments are not integers.
	Raises ValueError if either of the arguments are negative.
	'''
	if type(n) is not int or type(k) is not int:
		raise TypeError('arguments must be positive integers')
	if n < 0 or k < 0:
		raise ValueError('arguments must be positive integers')

	if k > n:
		return 0
	return factorial(n) // (factorial(k) * factorial(n - k))

def _perm(n, k=None):
	'''
	Number of ways to choose k items from n items without repetition and with order.

	Evaluates to n! / (n - k)! when k <= n and evaluates
	to zero when k > n.

	If k is not specified or is None, then k defaults to n
	and the function returns n!.

	Raises TypeError if either of the arguments are not integers.
	Raises ValueError if either of the arguments are negative.
	'''
	if type(n) is not int:
		raise TypeError('arguments must be positive integers')
	if n < 0:
		raise ValueError('arguments must be positive integers')

	if k is None:
		return factorial(n)

	if type(k) is not int:
		raise TypeError('arguments must be positive integers')
	if k < 0:
		raise ValueError('arguments must be positive integers')

	if k > n:
		return 0
	return factorial(n) // factorial(n - k)

def egcd(a, b):
	if a == 0:
		return (b, 0, 1)
	g, y, x = egcd(b % a, a)
	return (g, x - (b // a) * y, y)

def _modinv(base, mod):
	g, inv, _ = egcd(base, mod)
	if g != 1:
		raise ValueError('base is not invertible for the given modulus')
	return inv % mod

def _pow(base, exp, mod=None):
	'''
	Equivalent to base**exp with 2 arguments or base**exp % mod with 3 arguments

	Some types, such as ints, are able to use a more efficient algorithm when
	invoked using the three argument form.
	'''
	if exp >= 0:
		# Ok for any Python 3.x
		return real_pow(base, exp, mod)

	# Polyfill for Python < 3.8
	return real_pow(_modinv(base, mod), -exp, mod)

real_pow = pow
pow = real_pow

if sys.version_info >= (3, 9):
	from math import (
		gcd,  # accepts > 2 arguments since 3.9
		lcm,  # since 3.9
		prod, # since 3.8
		comb, # since 3.8
		perm, # since 3.8
	)

	pow = real_pow
elif sys.version_info >= (3, 8):
	from math import prod, comb, perm
	gcd = _gcd
	lcm = _lcm
	pow = _pow
else:
	gcd = _gcd
	lcm = _lcm
	prod = _prod
	comb = _comb
	perm = _perm
	pow = _pow
