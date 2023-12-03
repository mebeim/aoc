__all__ = ['log_calls', 'log_calls_recursive', 'selective_cache']

from sys import _getframe
from functools import wraps
from itertools import count, starmap, chain
from inspect import signature, Parameter

from .helpers import log, rlog, reprint

# Adapted from: https://stackoverflow.com/a/47956089/3889449
def _stack_size(size_hint: int=8) -> int:
	'''Get number of call frames for the caller.'''
	frame = 0

	try:
		while True:
			frame = _getframe(size_hint)
			size_hint *= 2
	except ValueError:
		if frame:
			size_hint //= 2
		else:
			while not frame:
				size_hint = max(2, size_hint // 2)
				try:
					frame = _getframe(size_hint)
				except ValueError:
					continue

	for size in count(size_hint):
		frame = frame.f_back
		if not frame:
			return size

def log_calls(log_return: bool=True):
	'''Decorate a function logging arguments and return value
	(if log_return=True) of every call to standard error.
	'''
	def decorator(fn):
		@wraps(fn)
		def wrapper(*args, **kwargs):
			repr_args = map(repr, args)
			repr_kwargs = starmap('{}={!r}'.format, kwargs.items())
			signature = ', '.join(chain(repr_args, repr_kwargs))
			log('{}({})\n', fn.__name__, signature)

			retval = fn(*args, **kwargs)

			if log_return:
				log('-> {!r}\n', retval)

			return retval
		return wrapper
	return decorator

def log_calls_recursive(log_call: bool=True, log_return: bool=True):
	'''Decorate a function logging arguments (if log_call=True) and return value
	(if log_return=True) of every call to standard error, indenting the logs for
	recursive calls according to the recursion level.

	Additionally, add .log() and .eprint() methods to the decorated function
	that will act as log() or eprint(), but add indentation according to the
	current recursion level.

	Usage example:

		@log_calls_recursive()
		def fib(n):
			if n == 0 or n == 1:
				return n

			fib.eprint('hello!')

			return n + fib(n - 1) + fib(n - 2)

		>>> fib(3)
		 ┌ fib(3)
		 │ hello!
		 │ ┌ fib(2)
		 │ │ hello!
		 │ │ ┌ fib(1)
		 │ │ └> 1
		 │ │ ┌ fib(0)
		 │ │ └> 0
		 │ └> 3
		 │ ┌ fib(1)
		 │ └> 1
		 └> 7
	'''
	# Explanation for the depth calculation:
	#
	# Since we are wrapping the function, every time the function is called we
	# actually add 2 call frames instead of 1, because wrapper() is called,
	# which then calls the real function:
	#
	#     depth = _stack_size() // 2
	#
	# Additionally, since the logging is done eithr through logfunc() or
	# through eprintfunc(), there is always one more frame to discard:
	#
	#     depth = (_stack_size() - 1) // 2
	#
	# If logfunc() or eprintfunc() are called by the user with func.log() or
	# func.eprint() inside the decorated function, then we have yet another
	# frame to discard:
	#
	#     depth = (_stack_size() - 1 - 1) // 2
	#
	# We use _user_call to distinguish between an internal call (_user_call=0)
	# or one made by the user (_user_call=1):
	#
	#     depth = (_stack_size() - 1 - _user_call) // 2

	def decorator(fn):
		initial_depth = None

		def logfunc(*a, _user_call=1, **kwa):
			nonlocal initial_depth

			depth = (_stack_size() - 1 - _user_call) // 2
			if initial_depth is None:
				initial_depth = depth

			rlog(depth - initial_depth)(*a, **kwa)

		def eprintfunc(*a, _user_call=1, **kwa):
			nonlocal initial_depth

			depth = (_stack_size() - 1 - _user_call) // 2
			if initial_depth is None:
				initial_depth = depth

			reprint(depth - initial_depth)(*a, **kwa)

		fn.log = logfunc
		fn.eprint = eprintfunc

		@wraps(fn)
		def wrapper(*args, **kwargs):
			repr_args = map(repr, args)
			repr_kwargs = starmap('{}={!r}'.format, kwargs.items())
			signature = ', '.join(chain(repr_args, repr_kwargs))

			if log_call:
				fn.log('{}({})\n', fn.__name__, signature, _user_call=0, is_header=True)

			retval = fn(*args, **kwargs)

			if log_return:
				fn.eprint(retval, _user_call=0, is_retval=True)

			return retval
		return wrapper
	return decorator

def selective_cache(*arg_names: str):
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
