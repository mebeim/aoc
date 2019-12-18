import re
import sys
import copy
import heapq
import string

from importlib import find_loader
from functools import lru_cache, reduce, partial
from collections import defaultdict, deque, namedtuple, Counter
from operator import itemgetter, attrgetter, methodcaller

if find_loader('z3') is not None:
	import z3

if find_loader('blist') is not None:
	import blist

if find_loader('sortedcontainers') is not None:
	import sortedcontainers

if find_loader('numpy') is not None:
	try:
		import numpy as np
	except ImportError:
		pass

if find_loader('networkx') is not None:
	import networkx as nx
