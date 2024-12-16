__all__ = ['Vector', 'Vec', 'MutableVector', 'MutVec']

from math import sqrt
from collections.abc import MutableSequence, Sequence
from itertools import starmap
from operator import sub
from typing import Union

from ..polyfill import prod, isqrt

IntOrFloat = Union[int,float]

class Vector(Sequence):
	'''An immutable N-dimensional vector of scalar numbers.
	Uses a tuple as backing for its components.
	'''

	__slots__ = ('components')

	def __init__(self, *components: IntOrFloat):
		self.components = components

	def __hash__(self):
		return hash(self.components)

	def __len__(self):
		return len(self.components)

	def __getitem__(self, i):
		return self.components[i]

	def __iter__(self):
		# Override default Sequence mixin (which uses __len__ and __getitem__)
		# for performance
		return iter(self.components)

	def __reversed__(self):
		# Override default Sequence mixin (which uses __len__ and __getitem__)
		# for performance
		return reversed(self.components)

	def __pos__(self):
		return self.__class__(*self)

	def __neg__(self):
		return self.__class__(*map(int.__neg__, self))

	def __abs__(self):
		s = sum(x**2 for x in self)

		# Try computing the integer square root to keep everything an `int`.
		if isinstance(s, int):
			res = isqrt(s)
			if res * res == s:
				return res

		# Fall back to normal square root returning a `float`.
		return sqrt(s)

	def __add__(self, other):
		self._check_dim(len(other))
		return self.__class__(*map(sum, zip(self, other)))

	def __sub__(self, other):
		self._check_dim(len(other))
		return self.__class__(*starmap(sub, zip(self, other)))

	def __mul__(self, v):
		if not isinstance(v, IntOrFloat):
			raise ValueError('ambiguous product by non-scalar: use A.dot(B) or A.cross(B)')
		return self.__class__(*(x * v for x in self))

	def __mod__(self, v):
		if not isinstance(v, IntOrFloat):
			raise ValueError('mod with non-scalar')
		return self.__class__(*(x % v for x in self))

	def __divmod__(self, v):
		if not isinstance(v, IntOrFloat):
			raise ValueError('divmod with non-scalar')
		if isinstance(v, float):
			return self / v, self % v
		return self // v, self % v

	def __truediv__(self, v: IntOrFloat):
		if not isinstance(v, IntOrFloat):
			raise ValueError('division by non-scalar')
		return self.__class__(*(x / v for x in self))

	def __floordiv__(self, v: IntOrFloat):
		if not isinstance(v, IntOrFloat):
			raise ValueError('division by non-scalar')
		return self.__class__(*(x // v for x in self))

	def __eq__(self, other):
		return self.components == other.components

	def __lt__(self, other):
		return self.components < other.components

	def __repr__(self):
		return f'Vec{self.components}'

	def _check_dim(self, dim: int, msg: Union[str,None]=None):
		if len(self) != dim:
			if msg is None:
				msg = f'vector dimension mismatch: have {len(self)}, expected {dim}'
			raise ValueError(msg)

	def dot(self, other: Sequence) -> IntOrFloat:
		'''Component-wise product yielding a scalar.

			Vector(1, 2, 3).dot((4, 5, 6)) == 1*4 + 2*5 + 3*6 == 32
		'''
		self._check_dim(len(other))
		return sum(map(prod, zip(self, other)))

	def dot_product(self, other: Sequence) -> IntOrFloat:
		'''Convenience alias for .dot().'''
		return self.dot(other)

	def cross(self, other: Sequence) -> 'Vector':
		'''Cross product (aka vector product) yielding a vector. The result is
		a vector orthogonal to both this vector and the operand, with a
		direction given by the right-hand rule.

			Vector(1, 0, 0).cross((0, 1, 0)) == Vector(0, 0, 1)
			In math terms: A x B = |a||b|sin(theta)n
		'''
		self._check_dim(3, 'this vector is not 3-dimensional')
		if len(other) != 3:
			raise ValueError('operand not 3-dimensional')

		return self.__class__(
			self[1] * other[2] - self[2] * other[1],
			self[2] * other[0] - self[0] * other[2],
			self[0] * other[1] - self[1] * other[0]
		)

	def cross_product(self, other: Sequence) -> 'Vector':
		'''Convenience alias for .cross().'''
		return self.cross(other)

	def magnitude(self) -> IntOrFloat:
		'''Convenience alias for abs(vector).'''
		return abs(self)

	def rotate2d(self, n: int) -> 'Vector':
		'''Rotate 2D vector 90 degrees n times, clockwise if n is positive,
		counter-clockwise if n is negative.
		'''
		self._check_dim(2, 'this vector is not 2-dimensional')

		n %= 4
		if n == 0: return self.__class__(*self)
		if n == 1: return self.__class__(self.y, -self.x)
		if n == 2: return self.__class__(-self.x, -self.y)
		return self.__class__(-self.y, self.x)

	# Convenience properties for 1D, 2D, 3D, 4D space
	@property
	def x(self) -> IntOrFloat: return self[0]
	@property
	def y(self) -> IntOrFloat: return self[1]
	@property
	def z(self) -> IntOrFloat: return self[2]
	@property
	def w(self) -> IntOrFloat: return self[3]

	# Convenience properties for 2D grids
	@property
	def r(self) -> IntOrFloat: return self[0]
	@property
	def c(self) -> IntOrFloat: return self[1]


class MutableVector(Vector, MutableSequence):
	'''A mutable N-dimensional vector of scalar numbers.
	Uses a list as backing for its components.
	'''

	__slots__ = ('components')

	def __init__(self, *components: IntOrFloat):
		self.components = list(components)

	def __repr__(self):
		return f'MutVec{self.components}'

	def __hash__(self):
		# Ideally we would like a Vector to be hashable to easily insert it into
		# sets or dicts, but we cannot safely do this since it's mutable. We
		# prefer mutability over hashability for common operations like
		# `v.x = 123` or `v.y += 1` or `v[10] = 456`. Add an hint in the error
		# message.
		raise TypeError(f"unhashable type: '{self.__class__.__name__}', use tuple(vector) if needed")

	def __setitem__(self, i, v):
		self.components[i] = v

	def __delitem__(self, i):
		# Do not support shrinking a Vector (also called for `pop` and `remove`)
		raise NotImplementedError('what the hell are you doing?')

	def insert(self, i, v):
		# Do not support expanding a Vector (also called for `append` and `extend`)
		raise NotImplementedError('what the hell are you doing?')

	def __iadd__(self, other):
		self._check_dim(len(other))

		for i, x in enumerate(other):
			self[i] += x
		return self

	def __isub__(self, other):
		self._check_dim(len(other))

		for i, x in enumerate(other):
			self[i] -= x
		return self

	def __imul__(self, v):
		if not isinstance(v, IntOrFloat):
			raise ValueError('ambiguous product by non-scalar: use A.dot(B) or A.cross(B)')

		for i in range(len(self)):
			self[i] *= v
		return self

	def __itruediv__(self, v):
		if not isinstance(v, IntOrFloat):
			raise ValueError('division by non-scalar')

		for i in range(len(self)):
			self[i] /= v
		return self

	def __ifloordiv__(self, v):
		if not isinstance(v, IntOrFloat):
			raise ValueError('division by non-scalar')

		for i in range(len(self)):
			self[i] //= v
		return self

	# Convenience properties for 1D, 2D, 3D, 4D space
	@Vector.x.setter
	def x(self, x): self[0] = x
	@Vector.y.setter
	def y(self, y): self[1] = y
	@Vector.z.setter
	def z(self, z): self[2] = z
	@Vector.w.setter
	def w(self, w): self[3] = w

	# Convenience properties for 2D grids
	@Vector.r.setter
	def r(self, r): self[0] = r
	@Vector.c.setter
	def c(self, c): self[1] = c

# Convenience aliases
Vec    = Vector
MutVec = MutableVector
