__all__ = ['UnionFind']

class UnionFind:
	'''Generic disjoint-set data structure a.k.a. union-find.'''
	# Supports any hashable object.
	# Supports retrieval of all elements of a set in linear time.
	# Implements find with path halving.
	# Implements union by rank.
	__slots__ = ('elements', 'size')

	class Element:
		# Internal rich representation of user elements.
		# Each Element is in a circular linked list of els of the same set.
		__slots__ = ('el', 'rank', 'size', 'parent', 'next')

		def __init__(self, el):
			self.el     = el
			self.rank   = 0
			self.size   = 1
			self.parent = self
			self.next   = self

		def __repr__(self):
			parent = repr(self.parent.el) if self.parent is not self else '.'
			_next = repr(self.next.el) if self.next is not self else '.'
			return '<Element {!r} parent={} rank={} next={}>'.format(
				self.el, parent, self.rank, _next)

	def __init__(self, initial_elements=None):
		self.elements = {} # map user elements to their corresponding rich internal representation
		self.size     = 0  # number of distinct disjoint sets in the UnionFind

		if initial_elements:
			for el in initial_elements:
				self.make_set(el)

	def __in__(self, el):
		'''Check if an element is in any of the sets of the UnionFind.'''
		return el in self.elements

	def __len__(self):
		# Avoid ambiguity since it's not obvious whether len() should return
		# the number of sets in the UF or the total number of elements in all
		# sets of the UF.
		raise NotImplementedError('len() not supported, use .size to get the '
			'number of disjoint sets present in this UnionFind') from None

	def make_set(self, el):
		'''Create a new set with el as the only member. Does nothing if el is
		already present in the UnionFind.
		'''
		if el not in self.elements:
			self.elements[el] = UnionFind.Element(el)
			self.size += 1

	def add(self, el):
		'''Convenience alias for make_set().'''
		self.make_set(el)

	def add_all(self, iterable):
		'''Create a new set for each element in iterable.'''
		for el in iterable:
			self.make_set(el)

	def _find(self, uel):
		while uel.parent is not uel:
			uel.parent = uel.parent.parent
			uel = uel.parent
		return uel

	def find(self, el):
		'''Find set representative for el.'''
		uel = self.elements.get(el)
		if uel is None:
			return None
		return self._find(uel).el

	def union(self, a, b):
		'''Merge the set containing a with the set containing b. Returns the new
		size of the merged set.'''
		try:
			ua = self.elements[a]
			ub = self.elements[b]
		except KeyError as e:
			raise LookupError('element {!r} is not in the UnionFind'.format(e.args[0])) from None

		ua = self._find(ua)
		ub = self._find(ub)
		if ua is ub:
			return

		if ua.rank < ub.rank:
			ua, ub = ub, ua

		ub.parent = ua
		ua.size += ub.size
		if ua.rank == ub.rank:
			ua.rank += 1

		ua.next, ub.next = ub.next, ua.next
		self.size -= 1
		return ua.size

	def merge(self, a, b):
		'''Convenience alias for union().'''
		return self.union(a, b)

	def get_size(self, el):
		'''Get the size of the set of elements of which el is a member.'''
		try:
			uel = self.elements[el]
		except KeyError as e:
			raise LookupError('element {!r} is not in the UnionFind'.format(e.args[0])) from None

		return self._find(uel).size

	def iter_set(self, el):
		'''Iterator over each element in the same set of el (el included).'''

		try:
			head = self.elements[el]
		except KeyError as e:
			raise LookupError('element {!r} is not in the UnionFind'.format(e.args[0])) from None

		yield head.el
		cur = head.next

		while cur is not head:
			yield cur.el
			cur = cur.next

	def get_set(self, el):
		'''Get the set of elements of which el is a member (el included).'''
		return set(self.iter_set(el))

	def all_sets(self):
		'''Get a list of all distinct sets in the UnionFind.'''
		uels = self.elements
		els  = set(self.elements.keys())
		sets = []

		while els:
			head    = uels[els.pop()]
			cur     = head.next
			cur_set = {head.el}

			while cur is not head:
				cur_set.add(cur.el)
				els.remove(cur.el)
				cur = cur.next

			sets.append(cur_set)

		return sets
