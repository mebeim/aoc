__all__ = ['gcd', 'lcm', 'prod', 'comb', 'perm']

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


if sys.version_info >= (3, 9):
	from math import (
		gcd,  # 3.9
		lcm,  # 3.9
		prod, # 3.8
		comb, # 3.8
		perm, # 3.8
	)
elif sys.version_info >= (3, 8):
	from math import prod, comb, perm
	gcd = _gcd # gcd is present from 3.5, but we want the 3.9 version
	lcm = _lcm
else:
	gcd = _gcd
	lcm = _lcm
	prod = _prod
	comb = _comb
	perm = _perm
