__all__ = ['autorange', 'transpose', 'sliding_window']


from collections import deque
from collections.abc import Iterable, Iterator, Sequence
from typing import Any


def autorange(start: int, end: int, step: int=1) -> range:
	'''Range from start to end (end is INCLUDED) in steps of +/- step regardless
	if start > end or end > start.

	autorange(1, 3) -> 1, 2, 3
	autorange(3, 1) -> 3, 2, 1
	autorange(10, 1, 2) -> 10, 8, 6, 4, 2
	'''
	if start > end:
		return range(start, end - 1, -step)
	return range(start, end + 1, step)

def transpose(matrix: Sequence[Sequence[Any]]) -> Sequence[Sequence[Any]]:
	'''Transpose a matrix keeping the same container types. Assumes that the
	elements (rows) of the matrix are all the same continer type.

	transpose([(1, 2, 3), (4, 5, 6)]) -> [(1, 4), (2, 5), (3, 6)]
	transpose([b'aaa', b'bbb']) -> [b'ab', b'ab', b'ab']
	transpose(('ab', 'cd', 'ef')) -> ('ace', 'bdf')
	'''
	outer = type(matrix)
	inner = type(matrix[0])

	if inner is str:
		# Need to special case this and use str.join() if we want to keep strings
		return outer(map(''.join, zip(*matrix)))
	if inner is bytes:
		# Funny bytes behaving as ints when iterated over :')
		return outer(map(bytes, map(bytearray, zip(*matrix))))
	return outer(map(inner, zip(*matrix)))

def sliding_window(iterable: Iterable[Any], length: int) -> Iterator[tuple[Any,...]]:
	'''Return an iterator over a sliding window of the specified length from the
	given iterable. NOTE that if length is larger than the total number of
	elements in iterable, the returned iterator will stop immediately.
	'''
	if length <= 0:
		raise ValueError('length must be greater than 0')

	window = deque(maxlen=length)

	for item in iterable:
		window.append(item)

		if len(window) == length:
			yield tuple(window)
			window.popleft()
