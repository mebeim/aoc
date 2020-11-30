from functools import wraps

from .helpers import log

def log_calls(log_return=True):
	def decorating_func(fn):
		@wraps(fn)
		def wrapper(*args):
			log('{}{}\n', fn.__name__, args)
			retval = fn(*args)

			if log_return:
				log('-> {}\n', retval)

			return retval

		return wrapper

	return decorating_func

__all__ = ['log_calls']
