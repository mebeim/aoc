__all__ = ['rangesum', 'arithmetic_series', 'geometric_series']

from operator import floordiv, truediv
from typing import Optional, Union

# PEP 484 says that when float is used int is acceptable too, but we want to
# be explicit for clarity
IntOrFloat = Union[int,float]

def rangesum(a: int, b: Optional[int]=None) -> int:
	'''With 1 arg: calculate the sum of all the integers in the range [1, a].
	With 2 args: calculate the sum of all the integers in the range [a, b].
	'''
	if b is None:
		if a < 0:
			raise ValueError(f'a must be non-negative, got a={a}')
		return a * (a + 1) // 2
	if b < a:
		raise ValueError(f'invalid range, need a <= b, got a={a} b={b}')
	return (b - a + 1) * (a + b) // 2

def arithmetic_series(first_term: IntOrFloat, delta: IntOrFloat, n: int) -> IntOrFloat:
	'''Calculate the sum of the first n elements of the arithmetic progression
	starting with the given first_term and having the given delta between
	consecutive terms, also known as arithmetic series.
	'''
	if n < 0:
		raise ValueError(f'n must be non-negative, got n={n}')

	# Try to return an int result if possible
	div = floordiv if isinstance(first_term, int) and isinstance(delta, int) else truediv
	return div(n * (2 * first_term + (n - 1) * delta), 2)

def geometric_series(first_term: IntOrFloat, factor: IntOrFloat, n: int) -> IntOrFloat:
	'''Calculate the sum of the first n elements of the geometric progression
	starting with the given first_term and having the given growing factor
	between consecutive terms, also known as geometric series.
	'''
	if n < 0:
		raise ValueError(f'n must be non-negative, got n={n}')
	if factor == 0:
		raise ValueError(f'a zero factor does not make much sense, does it?')

	if factor == 1:
		return first_term * (n > 0)

	# Try to return an int result if possible
	div = floordiv if isinstance(first_term, int) and isinstance(factor, int) else truediv
	return div(first_term * (1 - factor**n), (1 - factor))
