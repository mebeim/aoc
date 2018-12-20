#!/usr/bin/env python3

import re
import sys
import copy
import heapq
from string import *
from collections import defaultdict, deque, namedtuple, Counter

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()
