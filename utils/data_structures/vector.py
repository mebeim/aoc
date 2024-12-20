__all__ = ['Vector', 'Vec', 'MutableVector', 'MutVec']

from collections.abc import Iterable, Iterator, MutableSequence, Sequence
from functools import total_ordering, wraps
from itertools import starmap
from math import prod, sqrt, isqrt
from operator import sub
from typing import Union


IntOrFloat = Union[int,float]


def ensure2d(method):
	'''Decorator to ensure that a method operates on a 2-dimensional Vector.'''

	@wraps(method)
	def wrapper(self, *args, **kwargs):
		self._check_dim(2, 'this vector is not 2-dimensional')
		return method(self, *args, **kwargs)

	return wrapper


def ensure3d(method):
	'''Decorator to ensure that a method operates on a 3-dimensional Vector.'''

	@wraps(method)
	def wrapper(self, *args, **kwargs):
		self._check_dim(3, 'this vector is not 3-dimensional')
		return method(self, *args, **kwargs)

	return wrapper


def ensure3d_binop(operator):
	'''Decorator to ensure that an operator method operates on two 3-dimensional
	Vectors (self and other). In particular, other can also be a Sequence.'''

	@wraps(operator)
	def wrapper(self, other: Sequence[IntOrFloat]) -> 'Vector':
		self._check_dim(3, 'this vector is not 3-dimensional')
		if len(other) != 3:
			raise TypeError('operand is not 3-dimensional')
		return operator(self, other)

	return wrapper


@total_ordering
class Vector(Sequence):
	'''An immutable N-dimensional vector of scalar numbers.
	Uses a tuple as backing store for its components.
	Supports total ordering and hashing (behaving like a tuple).
	'''
	components: tuple[IntOrFloat]
	__slots__ = ('components')

	def __init__(self, *components: IntOrFloat):
		self.components = components

	def __hash__(self) -> int:
		# hash(vec)
		return hash(self.components)

	def __len__(self) -> int:
		# len(vec)
		return len(self.components)

	def __getitem__(self, i: int) -> IntOrFloat:
		# vec[i]
		return self.components[i]

	def __iter__(self) -> Iterator[IntOrFloat]:
		# Override default Sequence mixin (which uses __len__ and __getitem__)
		# for performance
		return iter(self.components)

	def __reversed__(self) -> Iterator[IntOrFloat]:
		# Override default Sequence mixin (which uses __len__ and __getitem__)
		# for performance
		return reversed(self.components)

	def __pos__(self) -> 'Vector':
		# +vec: component-wise (no-op)
		return type(self)(*self)

	def __neg__(self) -> 'Vector':
		# -vec: component-wise negation
		return type(self)(*(-x for x in self))

	def __abs__(self) -> 'Vector':
		# abs(vec): component-wise absolute value
		return type(self)(*(abs(x) for x in self))

	def __invert__(self) -> 'Vector':
		# ~vec: component-wise bitwise NOT
		return type(self)(*(~x for x in self))

	def __add__(self, other: Iterable[IntOrFloat]) -> 'Vector':
		# vec + other: component-wise sum
		self._check_dim(len(other))
		return type(self)(*map(sum, zip(self, other)))

	def __sub__(self, other: Iterable[IntOrFloat]) -> 'Vector':
		# vec - other: component-wise difference
		self._check_dim(len(other))
		return type(self)(*starmap(sub, zip(self, other)))

	def __mul__(self, v: IntOrFloat) -> 'Vector':
		# vec * v: component-wise product by scalar
		if not isinstance(v, IntOrFloat):
			raise TypeError('ambiguous product by non-scalar: use '
				'vec.dot(other) or vec.cross(other)')
		return type(self)(*(x * v for x in self))

	def __mod__(self, v: IntOrFloat) -> 'Vector':
		# vec % v: component-wise modulo by scalar
		if not isinstance(v, IntOrFloat):
			return NotImplemented
		return type(self)(*(x % v for x in self))

	def __divmod__(self, v: IntOrFloat) -> 'Vector':
		# divmod(vec, v): component-wise divmod by scalar
		if not isinstance(v, IntOrFloat):
			return NotImplemented
		if isinstance(v, float):
			return self / v, self % v
		return self // v, self % v

	def __truediv__(self, v: IntOrFloat) -> 'Vector':
		# vec / v: component-wise float division by scalar
		if not isinstance(v, IntOrFloat):
			return NotImplemented
		return type(self)(*(x / v for x in self))

	def __floordiv__(self, v: IntOrFloat) -> 'Vector':
		# vec // v: component-wise integer division by scalar
		if not isinstance(v, IntOrFloat):
			return NotImplemented
		return type(self)(*(x // v for x in self))

	def __eq__(self, other: Sequence[IntOrFloat]) -> bool:
		# vec == other
		if isinstance(other, self.__class__):
			return self.components == other.components
		if not isinstance(other, Sequence):
			return NotImplemented

		# Support comparison with other sequences
		return len(self) == len(other) and all(a == b for a, b in zip(self, other))

	def __lt__(self, other: Sequence[IntOrFloat]) -> bool:
		# vec < other
		if isinstance(other, self.__class__):
			return self.components < other.components
		if not isinstance(other, Sequence):
			return NotImplemented

		# Support comparison with other sequences
		if any(a > b for a, b in zip(self, other)):
			return False
		return len(self) < len(other)

	def __repr__(self) -> str:
		return f'Vec{self.components}'

	def _check_dim(self, dim: int, msg: Union[str,None]=None):
		if len(self) != dim:
			if msg is None:
				msg = f'vector dimension mismatch: have {len(self)}, expected {dim}'
			raise TypeError(msg)

	@property
	def sign(self) -> 'Vector':
		'''Component-wise sign of the vector yielding another vector.
		NOTE: 0 and -0.0 will have a sign of 0.
		'''
		return type(self)(*((x > 0) - (x < 0) for x in self))

	@property
	def norm(self) -> IntOrFloat:
		'''Euclidean norm (magnitude) of the vector, i.e. the square root of the
		sum of the squares of its components.
		'''
		s = sum(x**2 for x in self)

		# Try computing the integer square root to keep everything an `int`.
		if isinstance(s, int):
			res = isqrt(s)
			if res * res == s:
				return res

		# Fall back to normal square root returning a `float`.
		return sqrt(s)

	@property
	def magnitude(self) -> IntOrFloat:
		'''Convenience alias for vec.norm'''
		return self.norm()

	@property
	def modulus(self) -> IntOrFloat:
		'''Convenience alias for vec.magnitude'''
		return self.magnitude()

	def dot(self, other: Sequence[IntOrFloat]) -> IntOrFloat:
		'''Component-wise product yielding a scalar.

			Vector(1, 2, 3).dot((4, 5, 6)) == 1*4 + 2*5 + 3*6 == 32
		'''
		self._check_dim(len(other))
		return sum(map(prod, zip(self, other)))

	def dot_product(self, other: Sequence[IntOrFloat]) -> IntOrFloat:
		'''Convenience alias for vec.dot()'''
		return self.dot(other)

	def distance(self, other: Sequence[IntOrFloat]) -> float:
		'''Euclidean distance between two vectors, i.e. the square root of the
		sum of the squared differences of their components.
		'''
		self._check_dim(len(other))
		return (self - other).norm

	def manhattan(self, other: Sequence[IntOrFloat]) -> IntOrFloat:
		'''Manhattan distance between two vectors, i.e. the sum of the absolute
		differences of their components.
		'''
		self._check_dim(len(other))
		return sum(abs(self - other))

	def taxicab(self, other: Sequence[IntOrFloat]) -> IntOrFloat:
		'''Convenience alias for vec.manhattan()'''
		return self.manhattan(other)

	@ensure2d
	def rot2d(self, n: int) -> 'Vector':
		'''2D vector rotation in *Cartesian plane* (NOT grid) of 90 degrees n
		times: clockwise if n is positive, counter-clockwise if n is negative.

		NOTE: rotation assumes 2D Cartesian coords, not 2D grid coords! Use
		vec.grid_rot2d() for grids coords.
		'''
		n %= 4
		if n == 0: return type(self)(*self)
		if n == 1: return type(self)(-self.y, self.x)
		if n == 2: return type(self)(-self.x, -self.y)
		return type(self)(self.y, -self.x)

	@ensure2d
	def grid_rot2d(self, n: int) -> 'Vector':
		'''2D vector rotation in *grid* (NOT Cartesian plane) of 90 degrees n
		times: clockwise if n is positive, counter-clockwise if n is negative.

		NOTE: rotation assumes 2D grid coords, not 2D Cartesian coords! Use
		vec.rot2d() for Cartesian coords.
		'''
		n %= 4
		if n == 0: return type(self)(*self)
		if n == 1: return type(self)(self.c, -self.r)
		if n == 2: return type(self)(-self.r, -self.c)
		return type(self)(-self.c, self.r)

	@ensure2d
	def reflect2d(self, vertical=False) -> 'Vector':
		'''2D vector reflection using *Cartesian* coordinates.

		vertical=False: horizontal reflection  x|x
		vertical=True : vertical reflection
		                 o
		                ---
		                 o

		NOTE: reflection assumes 2D Cartesian coords, not grid coords!
		'''
		if vertical:
			return type(self)(self.x, -self.y)
		return type(self)(-self.x, self.y)

	@ensure2d
	def grid_reflect2d(self, vertical=False) -> 'Vector':
		'''2D vector reflection using *grid* coordinates.

		vertical=False: horizontal reflection  o|o
		vertical=True : vertical reflection
		                 o
		                ---
		                 o

		NOTE: reflection assumes 2D grid coords, not Cartesian coords!
		'''
		if vertical:
			return type(self)(-self.r, self.c)
		return type(self)(self.r, -self.c)

	@ensure2d
	def adj4(self) -> Iterator['Vector']:
		'''Yield the 4 cardinal neighbor coordinates (N, S, W, E) of a 2D vector
		representing Cartesian or grid coordinates.

		NOTE: components should be *integers*!
		'''
		yield self + (0, 1)
		yield self + (0, -1)
		yield self + (1, 0)
		yield self + (-1, 0)

	@ensure2d
	def adj8(self) -> Iterator['Vector']:
		'''Yield the 8 neighbor coordinates (N, S, W, E, NW, NE, SW, SE) of a 2D
		vector representing Cartesian or grid coordinates.

		NOTE: components should be *integers*!
		'''
		yield self + (0, 1)
		yield self + (0, -1)
		yield self + (-1, 0)
		yield self + (1, 0)
		yield self + (1, -1)
		yield self + (1, 1)
		yield self + (-1, -1)
		yield self + (-1, 1)

	@ensure3d
	def adj4_3d(self) -> Iterator['Vector']:
		'''Yield the 4 cardinal neighbor coordinates (N, S, W, E) on the same Z
		plane of a 3D vector representing 3D-space coordinates.

		NOTE: components should be *integers*!
		'''
		yield self + (0, 1, 0)
		yield self + (0, -1, 0)
		yield self + (1, 0, 0)
		yield self + (-1, 0, 0)

	@ensure3d
	def adj8_3d(self) -> Iterator['Vector']:
		'''Yield the 8 neighbor coordinates (N, S, W, E, NW, NE, SW, SE) on the
		same Z plane of a 3D vector representing 3D-space coordinates.

		NOTE: components should be *integers*!
		'''
		yield self + (0, 1, 0)
		yield self + (0, -1, 0)
		yield self + (-1, 0, 0)
		yield self + (1, 0, 0)
		yield self + (1, -1, 0)
		yield self + (1, 1, 0)
		yield self + (-1, -1, 0)
		yield self + (-1, 1, 0)

	@ensure3d
	def adj6(self) -> Iterator['Vector']:
		'''Yield the 6 neighbor coordinates (N, S, W, E, UP, DOWN) of a 3D
		vector representing 3D-space coordinates. These correspond to the center
		of the 6 faces of a 3x3x3 cube where this vector represents the coords
		of the center.

		NOTE: components should be *integers*!
		'''
		yield self + (0, 1, 0)
		yield self + (0, -1, 0)
		yield self + (-1, 0, 0)
		yield self + (1, 0, 0)
		yield self + (0, 0, 1)
		yield self + (0, 0, -1)

	@ensure3d
	def adj26(self) -> Iterator['Vector']:
		'''Yield the 26 neighbor coordinates of a 3D vector representing
		3D-space coordinates. These correspond to the 26 "cells" of a 3x3x3 cube
		where this vector represents the coords of the center.

		NOTE: components should be *integers*!
		'''
		for dz in (-1, 0, 1):
			for dy in (-1, 0, 1):
				for dx in (-1, 0, 1):
					if dx == dy == dz == 0:
						continue
					yield self + (dx, dy, dz)

	@ensure3d_binop
	def cross(self, other: Sequence[IntOrFloat]) -> 'Vector':
		'''3D cross product (aka vector product) yielding a vector. The result
		is a vector orthogonal to both this vector and the operand, with a
		direction given by the right-hand rule.

			Vector(1, 0, 0).cross((0, 1, 0)) == Vector(0, 0, 1)
			In math terms: A x B = |a||b|sin(theta)n
		'''
		return type(self)(
			self[1] * other[2] - self[2] * other[1],
			self[2] * other[0] - self[0] * other[2],
			self[0] * other[1] - self[1] * other[0]
		)

	def cross_product(self, other: Sequence[IntOrFloat]) -> 'Vector':
		'''Convenience alias for vec.cross()'''
		return self.cross(other)

	### Convenience properties for 1D, 2D, 3D, 4D space ###

	@property
	def x(self) -> IntOrFloat:
		return self[0]

	@property
	def y(self) -> IntOrFloat:
		return self[1]

	@property
	def z(self) -> IntOrFloat:
		return self[2]

	@property
	def w(self) -> IntOrFloat:
		return self[3]

	### Convenience properties for 2D space ###
	# ^ Y
	# |   X
	# o--->

	@property
	@ensure2d
	def north(self) -> 'Vector':
		return self + (0, 1)

	@property
	@ensure2d
	def south(self) -> 'Vector':
		return self + (0, -1)

	@property
	@ensure2d
	def west(self) -> 'Vector':
		return self + (-1, 0)

	@property
	@ensure2d
	def east(self) -> 'Vector':
		return self + (1, 0)

	@property
	@ensure2d
	def nw(self) -> 'Vector':
		return self + (-1, 1)

	@property
	@ensure2d
	def ne(self) -> 'Vector':
		return self + (1, 1)

	@property
	@ensure2d
	def sw(self) -> 'Vector':
		return self + (-1, -1)

	@property
	@ensure2d
	def se(self) -> 'Vector':
		return self + (1, -1)

	### Convenience properties for 2D grids ###
	# o--->
	# |   C
	# v R

	@property
	def r(self) -> IntOrFloat:
		return self[0]

	@property
	def c(self) -> IntOrFloat:
		return self[1]

	@property
	@ensure2d
	def grid_north(self) -> 'Vector':
		return self + (-1, 0)

	@property
	@ensure2d
	def grid_south(self) -> 'Vector':
		return self + (1, 0)

	@property
	@ensure2d
	def grid_west(self) -> 'Vector':
		return self + (0, -1)

	@property
	@ensure2d
	def grid_east(self) -> 'Vector':
		return self + (0, 1)

	@property
	@ensure2d
	def grid_nw(self) -> 'Vector':
		return self + (-1, -1)

	@property
	@ensure2d
	def grid_ne(self) -> 'Vector':
		return self + (-1, 1)

	@property
	@ensure2d
	def grid_sw(self) -> 'Vector':
		return self + (1, -1)

	@property
	@ensure2d
	def grid_se(self) -> 'Vector':
		return self + (1, 1)


class MutableVector(Vector, MutableSequence):
	'''A mutable N-dimensional vector of scalar numbers.
	Uses a list as backing store for its components.
	Supports total ordering.
	'''

	components: list[IntOrFloat]
	__slots__ = ('components')

	def __init__(self, *components: IntOrFloat):
		self.components = list(components)

	def __repr__(self) -> str:
		return f'MutVec{self.components}'

	def __hash__(self):
		# Ideally we would like a Vector to be hashable to easily insert it into
		# sets or dicts, but we cannot safely do this since it's mutable. We
		# prefer mutability over hashability for common operations like
		# `v.x = 123` or `v.y += 1` or `v[10] = 456`. Add an hint in the error
		# message.
		raise TypeError(f"unhashable type: '{self.__class__.__name__}', use tuple(vec) if needed")

	def __setitem__(self, i: int, v: IntOrFloat):
		# vec[i] = v
		self.components[i] = v

	def __delitem__(self, i):
		# del vec[i]
		# Do not support shrinking a Vector (also called for `pop` and `remove`)
		raise NotImplementedError('what the hell are you doing?')

	def insert(self, i, v):
		'''NOT IMPLEMENTED! Will raise NotImplementedError.'''
		# Do not support expanding a Vector (also called for `append` and `extend`)
		raise NotImplementedError('what the hell are you doing?')

	def __iadd__(self, other: Iterable[IntOrFloat]) -> 'MutableVector':
		# vec += other: in-place component-wise sum
		self._check_dim(len(other))

		for i, x in enumerate(other):
			self[i] += x
		return self

	def __isub__(self, other: Iterable[IntOrFloat]) -> 'MutableVector':
		# vec -= other: in-place component-wise difference
		self._check_dim(len(other))

		for i, x in enumerate(other):
			self[i] -= x
		return self

	def __imul__(self, v: IntOrFloat) -> 'MutableVector':
		# vec *= v: in-place component-wise product by scalar
		if not isinstance(v, IntOrFloat):
			raise TypeError('ambiguous product by non-scalar: use '
				'vec.dot(other) or vec.cross(other)')

		for i in range(len(self)):
			self[i] *= v
		return self

	def __itruediv__(self, v: IntOrFloat) -> 'MutableVector':
		# vec /= v: in-place component-wise float division by scalar
		if not isinstance(v, IntOrFloat):
			return NotImplemented

		for i in range(len(self)):
			self[i] /= v
		return self

	def __ifloordiv__(self, v: IntOrFloat) -> 'MutableVector':
		# vec //= v: in-place component-wise integer division by scalar
		if not isinstance(v, IntOrFloat):
			return NotImplemented

		for i in range(len(self)):
			self[i] //= v
		return self

	### Convenience properties for 1D, 2D, 3D, 4D space ###

	@Vector.x.setter
	def x(self, x):
		self[0] = x

	@Vector.y.setter
	def y(self, y):
		self[1] = y

	@Vector.z.setter
	def z(self, z):
		self[2] = z

	@Vector.w.setter
	def w(self, w):
		self[3] = w

	### Convenience properties for 2D grids ###
	# o--->
	# |   C
	# v R

	@Vector.r.setter
	def r(self, r):
		self[0] = r

	@Vector.c.setter
	def c(self, c):
		self[1] = c


# Convenience aliases
Vec    = Vector
MutVec = MutableVector
