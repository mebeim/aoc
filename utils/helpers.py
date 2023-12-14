__all__ = ['autorange', 'transpose']

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
