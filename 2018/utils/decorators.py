from functools import wraps

from .helpers import log

def log_calls(fn, log_return=True):
	@wraps(fn)
	def wrapper(*args):
		log('{}{}\n', fn.__name__, args)
		retval = fn(*args)

		if log_return:
			log('-> {}\n', retval)

		return retval

	return wrapper

__all__ = [
	'log_calls'
]
