__all__ = ['log_calls', 'selective_cache']

from functools import wraps, lru_cache
from inspect import signature, Parameter
from .helpers import log

def log_calls(log_return=True):
	'''Decorate a function logging arguments and return value
	(if log_return=True) of every call to standard error.
	'''
	def decorator(fn):
		@wraps(fn)
		def wrapper(*args):
			log('{}{}\n', fn.__name__, args)
			retval = fn(*args)

			if log_return:
				log('-> {}\n', retval)

			return retval
		return wrapper
	return decorator

def selective_cache(*arg_names):
	'''Memoize results using only arguments with the specified names as key.
	Note: does NOT support functions using *args, **kwargs or default values.

	Example:

		# Cache results using (a, b) as key.
		@selective_cache('a', 'b')
		def func(a, b, c):
			return a + b + c

		>>> func(1, 2, 3)
		6
		>>> func.cache
		{(1, 2): 6}
		>>> func(1, 2, 99)
		6

	func.cache: internal cache.
	func.cache_clear(): clears internal cache.

	Cache size is unbounded! Beware.
	'''
	def decorator(fn):
		key_args_indexes = []
		cache = {}

		for i, (name, p) in enumerate(signature(fn).parameters.items()):
			# We are lazy, supporting every kind of strange Python parameter
			# type is very complex. Detect bad usages here and bail out.
			if p.kind not in (Parameter.POSITIONAL_OR_KEYWORD, Parameter.POSITIONAL_ONLY):
				raise TypeError('can only wrap functions with positional '
					"parameters, and '{}' is not positional".format(name))
			elif p.default != Parameter.empty:
				raise TypeError('can only wrap functions without default '
					"parameter values, and '{}' has a default".format(name))

			if name in arg_names:
				key_args_indexes.append(i)

		@wraps(fn)
		def wrapper(*args):
			nonlocal cache, key_args_indexes

			key = tuple(args[i] for i in key_args_indexes)
			if key in cache:
				return cache[key]

			res = fn(*args)
			cache[key] = res
			return res

		wrapper.cache = cache
		wrapper.cache_clear = cache.clear
		return wrapper

	return decorator
