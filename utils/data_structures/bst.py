import json
from operator import attrgetter
from collections import deque
from collections.abc import Mapping, MutableMapping, MappingView, KeysView, ValuesView, ItemsView

__all__ = ['BST', 'AVLTree', 'RBTree']

class BSTNode:
	__slots__ = ('left', 'right', 'parent', 'key', 'value')

	def __init__(self, key, value, parent=None):
		self.left   = None
		self.right  = None
		self.parent = parent
		self.key    = key
		self.value  = value

	def child(self, right):
		return self.right if right else self.left

	def sibling(self, child):
		return self.child(child is self.left)

	def set_child(self, right, node):
		if node:
			node.parent = self
		if right:
			self.right = node
		else:
			self.left = node

	def replace_child(self, child, node):
		self.set_child(child is self.right, node)

	def _repr_info(self):
		return

	def __repr__(self):
		n = self.__class__.__name__
		l = self.left and self.left.key
		r = self.right and self.right.key
		p = self.parent and self.parent.key
		i = self._repr_info()
		isroot = '' if self.parent else ' (root)'
		info = f' {i}' if i else ''
		return f'<{n}{isroot} k={self.key!r} v={self.value!r} l={l!r} r={r!r} p={p!r}{info}>'

	def _dot_attributes(self):
		label = json.dumps(f'{self.key}\n{self.value}')
		return f'[label={label}]'

	def dot(self):
		l, r = self.left, self.right
		h, hl, hr = hash(self), hash(l), hash(r)
		res = f'"n{h}" {self._dot_attributes()}\n'

		if l:
			res += f'"n{h}" -> "n{hl}" [label=L]\n'
			res += l.dot()

		if r:
			res += f'"n{h}" -> "n{hr}" [label=R]\n'
			res += r.dot()

		return res

class BST(MutableMapping):
	# NOTE: .setdefault(), .update(), .__eq__(), .__ne__() are provided by
	#       MutableMapping's default implementation, which might not be optimal.
	# NOTE: In particular, __eq__/__ne__ only care about whether two instances
	#       contain the same .items(), and DO NOT check the tree shape! This
	#       means that e.g. BST(((1, 2), (3, 4))) == {1: 2, 3: 4}.

	__slots__ = ('root', '_len')

	INORDER, PREORDER, POSTORDER = range(3)

	def __init__(self, iterable_or_mapping=None):
		self.root = None
		self._len = 0

		if isinstance(iterable_or_mapping, Mapping):
			self.update(iterable_or_mapping)
		elif iterable_or_mapping is not None:
			for k, v in iterable_or_mapping:
				self[k] = v

	def __getitem__(self, key):
		node = self._find_node(key)
		if node is None:
			raise KeyError(key)
		return node.value

	def __setitem__(self, key, value):
		if self._set(BSTNode(key, value)):
			self._len += 1

	def __delitem__(self, key):
		node = self._find_node(key)
		if node is None:
			raise KeyError(key)
		self._delete(node)
		self._len -= 1

	def __contains__(self, key):
		return self._find_node(key) is not None

	def __iter__(self):
		return iter(self.keys())

	def __len__(self):
		return self._len

	def __bool__(self):
		return self.root is not None

	def _leftmost(self, node):
		while node.left:
			node = node.left
		return node

	def _rightmost(self, node):
		while node.left:
			node = node.left
		return node

	def _predecessor(self, node):
		if node.left is not None:
			return self._rightmost(node.left)

		parent = node.parent
		while parent and node != parent.left:
			node = parent
			parent = parent.parent

		return parent

	def _successor(self, node):
		if node.right is not None:
			return self._leftmost(node.right)

		parent = node.parent
		while parent and node != parent.right:
			node = parent
			parent = parent.parent

		return parent

	def _shift(self, node, child):
		parent = node.parent

		if parent is None:
			self.root = child
			child.parent = None
		else:
			parent.replace_child(node, child)

	def _rotate(self, node, right):
		parent  = node.parent
		sibling = node.child(not right)
		nephew  = sibling.child(right)

		node.set_child(not right, nephew)
		sibling.set_child(right, node)

		if parent:
			parent.replace_child(node, sibling)
		else:
			self.root = sibling
			sibling.parent = None

		return sibling

	def _find_node(self, key):
		cur = self.root

		while cur:
			curk = cur.key

			if key > curk:
				nxt = cur.right
			elif key < curk:
				nxt = cur.left
			else:
				break

			cur = nxt

		return cur

	def _must_find_node(self, key):
		n = self._find_node(key)
		if n is None:
			raise KeyError(key)
		return n

	def _set(self, node):
		if self.root is None:
			self.root = node
			return True

		k = node.key
		nxt = self.root

		while nxt:
			cur = nxt
			curk = cur.key

			if k > curk:
				nxt = cur.right
			elif k < curk:
				nxt = cur.left
			else:
				cur.value = node.value
				return False

		node.parent = cur

		if k > curk:
			cur.right = node
		else:
			cur.left = node

		return True

	def _delete(self, node):
		if not node.left:
			self._shift(node, node.right)
			return

		if not node.right:
			self._shift(node, node.left)
			return

		succ = self._successor(node)

		if succ.parent is not node:
			self._shift(succ, succ.right)
			succ.right = node.right
			succ.right.parent = succ

		self._shift(node, succ)
		succ.left = node.left
		succ.left.parent = succ

	def _visit_inorder(self, node=None, reverse=False, start=None):
		if node is None:
			node = self.root

		stack = deque()

		if start is not None:
			while node:
				key = node.key

				if start > key:
					if reverse:
						stack.append(node)
					node = node.right
				elif start < key:
					if not reverse:
						stack.append(node)
					node = node.left
				else:
					stack.append(node)
					break

			node = None

		while stack or node:
			if node:
				stack.append(node)
				node = node.child(reverse)
			else:
				node = stack.pop()
				yield node
				node = node.child(not reverse)

	def _visit_preorder(self, node=None, reverse=False):
		if node is None:
			node = self.root

		stack = deque([node])

		while stack:
			node = stack.pop()
			if node is None:
				continue

			yield node
			stack.append(node.child(not reverse))
			stack.append(node.child(reverse))

	def _visit_postorder(self, node=None, reverse=False):
		if node is None:
			node = self.root

		stack = deque()
		last = None

		while stack or node:
			if node:
				stack.append(node)
				node = node.child(reverse)
			else:
				top = stack[-1]
				child = top.child(not reverse)

				if child and (last is not child):
					node = child
				else:
					yield top
					last = stack.pop()

	def _height(self, node):
		stack = deque([(0, node)])
		maxh  = 0

		while stack:
			h, node = stack.pop()
			if node is None:
				continue

			if h > maxh:
				maxh = h

			stack.append((h + 1, node.left))
			stack.append((h + 1, node.right))

		return maxh

	def get(self, key, default=None):
		node = self._find_node(key)
		return default if node is None else node.value

	def pop(self, key):
		node = self._must_find_node(key)
		self._delete(node)
		self._len -= 1
		return node.value

	def popitem(self):
		if self.root is None:
			raise KeyError('popitem() on an empty binary search tree')

		res = self.root.key, self.root.value
		self._delete(self.root)
		return res

	def popmin(self):
		if self.root is None:
			raise KeyError('popmin() on an empty binary search tree')

		node = self._leftmost(self.root)
		self._delete(node)
		self._len -= 1
		return node.value

	def popmax(self):
		if self.root is None:
			raise KeyError('popmax() on an empty binary search tree')

		node = self._rightmost(self.root)
		self._delete(node)
		self._len -= 1
		return node.value

	def clear(self):
		self.root = None
		self._len = 0

	def keys(self, order=INORDER):
		return bst_keys(self, order)

	def values(self, order=INORDER):
		return bst_values(self, order)

	def items(self, order=INORDER):
		return bst_items(self, order)

	def minkey(self):
		if self.root is None:
			raise KeyError('minkey() on an empty binary search tree')
		return self._leftmost(self.root).key

	def maxkey(self):
		if self.root is None:
			raise KeyError('maxkey() on an empty binary search tree')
		return self._rightmost(self.root).key

	def min(self):
		if self.root is None:
			raise KeyError('min() on an empty binary search tree')
		return self._leftmost(self.root).value

	def max(self):
		if self.root is None:
			raise KeyError('max() on an empty binary search tree')
		return self._rightmost(self.root).value

	def prevkey(self, key):
		p = self._predecessor(self._must_find_node(key))
		return p and p.key

	def nextkey(self, key):
		s = self._successor(self._must_find_node(key))
		return s and s.key

	def prev(self, key):
		p = self._predecessor(self._must_find_node(key))
		return p and p.value

	def next(self, key):
		s = self._successor(self._must_find_node(key))
		return s and s.value

	def height(self):
		return self._height(self.root)

	def depth(self, key):
		cur = self.root
		depth = 0

		while cur:
			if key > cur.key:
				cur = cur.right
			elif key < cur.key:
				cur = cur.left
			else:
				return depth

			depth += 1

		raise KeyError(key)

	def balance_factor(self):
		lh = self._height(self.root and self.root.left)
		rh = self._height(self.root and self.root.right)
		return rh - lh

	def head(self, maxkey):
		return bst_head(self, maxkey)

	def tail(self, minkey):
		return bst_tail(self, minkey)

	def range(self, minkey, maxkey):
		return bst_range(self, minkey, maxkey)

	def dot(self):
		res = 'digraph {\ngraph [ordering="out"]\n'

		if self.root:
			res += self.root.dot()

		return res + '}\n'

class bst_view(MappingView):
	__slots__ = ('bst', '_getter', '_visit')

	def __init__(self, bst, attrs, order=None, iter_nodes=None):
		if iter_nodes is None:
			if order == BST.INORDER:
				iter_nodes = bst._visit_inorder
			elif order == BST.PREORDER:
				iter_nodes = bst._visit_preorder
			elif order == BST.POSTORDER:
				iter_nodes = bst._visit_postorder
			else:
				raise ValueError('order must be one of BST.INORDER, BST.PREORDER or BST.POSTORDER')

		self.bst     = bst
		self._getter = attrgetter(*attrs)
		self._visit  = iter_nodes

	def __contains__(self, x):
		x in iter(self)

	def __iter__(self):
		return iter(map(self._getter, self._visit()))

	def __len__(self):
		return len(self.bst)

	def __bool__(self):
		return bool(self.bst)

	def __repr__(self):
		return f'{self.__class__.__name__}({list(self)})'

class bst_keys(bst_view, KeysView):
	def __init__(self, bst, order=None, iter_nodes=None):
		super().__init__(bst, ('key',), order, iter_nodes)

	def __contains__(self, k):
		k in self.bst

class bst_values(bst_view, ValuesView):
	def __init__(self, bst, order=None, iter_nodes=None):
		super().__init__(bst, ('value',), order, iter_nodes)

class bst_items(bst_view, ItemsView):
	def __init__(self, bst, order=None, iter_nodes=None):
		super().__init__(bst, ('key', 'value'), order, iter_nodes)

	def __contains__(self, item):
		k, v = item
		node = self.bst._find_node(k)
		return node is not None and node.value == v

class bst_subview(MappingView):
	__slots__ = ('bst',)

	def __init__(self, bst):
		self.bst = bst

	def __iter__(self):
		return iter(self.keys())

	def __len__(self):
		# NOTE: this is O(n) as we can't really easily know the number of nodes.
		return sum(1 for _ in self)

	def __bool__(self):
		for _ in self:
			return True
		return False

	def _iter_nodes(self):
		raise NotImplementedError('subclass must override this method')

	def keys(self):
		return bst_keys(self.bst, iter_nodes=self._iter_nodes)

	def values(self):
		return bst_values(self.bst, iter_nodes=self._iter_nodes)

	def items(self):
		return bst_items(self.bst, iter_nodes=self._iter_nodes)

class bst_head(bst_subview):
	__slots__ = ('maxkey',)

	def __init__(self, bst, maxkey):
		super().__init__(bst)
		self.maxkey = maxkey

	def __contains__(self, k):
		return k < self.maxkey and k in self.bst

	def __repr__(self):
		return f'bst_head({self.bst}, maxkey={self.maxkey})'

	def _iter_nodes(self):
		for node in self.bst._visit_inorder():
			if node.key >= self.maxkey:
				break
			yield node

	def head(self, maxkey):
		if maxkey >= self.maxkey:
			return self
		return bst_head(self.bst, maxkey)

	def tail(self, minkey):
		return bst_range(minkey, self.maxkey)

	def range(self, minkey, maxkey):
		return bst_range(self.bst, minkey, min(maxkey, self.maxkey))

class bst_tail(bst_subview):
	__slots__ = ('minkey',)

	def __init__(self, bst, minkey):
		super().__init__(bst)
		self.minkey = minkey

	def __contains__(self, k):
		return k >= self.minkey and k in self.bst

	def __repr__(self):
		return f'bst_tail({self.bst}, minkey={self.minkey})'

	def _iter_nodes(self):
		return self.bst._visit_inorder(start=self.minkey)

	def head(self, maxkey):
		return bst_range(self.bst, self.minkey, maxkey)

	def tail(self, minkey):
		if minkey <= self.minkey:
			return self
		return bst_tail(self.bst, minkey)

	def range(self, minkey, maxkey):
		return bst_range(self.bst, max(minkey, self.minkey), maxkey)

class bst_range(bst_subview):
	__slots__ = ('minkey', 'maxkey')

	def __init__(self, bst, minkey, maxkey):
		super().__init__(bst)
		self.minkey = minkey
		self.maxkey = maxkey

	def __contains__(self, k):
		return self.minkey <= k < self.maxkey and k in self.bst

	def __repr__(self):
		return f'bst_range({self.bst}, minkey={self.minkey}, maxkey={self.maxkey})'

	def _iter_nodes(self):
		for node in self.bst._visit_inorder(start=self.minkey):
			if node.key >= self.maxkey:
				break
			yield node

	def head(self, maxkey):
		if maxkey >= self.maxkey:
			return self
		return bst_range(self.bst, self.minkey, maxkey)

	def tail(self, minkey):
		if minkey <= self.minkey:
			return self
		return bst_range(self.bst, minkey, self.maxkey)

	def range(self, minkey, maxkey):
		if minkey <= self.minkey and maxkey >= self.maxkey:
			return self
		return bst_range(self.bst, max(minkey, self.minkey), min(maxkey, self.maxkey))

class RBNode(BSTNode):
	__slots__ = ('red',)

	def __init__(self, key, value, parent=None, red=True):
		super().__init__(key, value, parent)
		self.red = red

	def _repr_info(self):
		return 'red' if self.red else 'blk'

	def _dot_attributes(self):
		bg = 'red' if self.red else 'black'
		fg = 'black' if self.red else 'white'
		label = json.dumps(f'{self.key}\n{self.value}')
		return f'[label={label}, style=filled, fillcolor={bg}, fontcolor={fg}]'

class RBTree(BST):
	def __setitem__(self, key, value):
		node = RBNode(key, value)
		if self._set(node):
			self._rebalance(node)
			self._len += 1

	def _rebalance(self, node):
		p = node.parent

		while p:
			if not p.red:
				break

			pp = p.parent
			if not pp:
				p.red = False
				break

			uncle = pp.sibling(p)

			if not uncle or not uncle.red:
				right = node is p.right
				pright = p is pp.right

				if pright != right:
					self._rotate(p, pright)
					node = p
					p = pp.child(pright)

				self._rotate(pp, not pright)
				p.red  = False
				pp.red = True
				break

			pp.red = True
			p.red = uncle.red = False
			node = pp
			p = node.parent

	def _delete(self, node):
		l, r, p, red = node.left, node.right, node.parent, node.red

		if node is self.root and not l and not r:
			self.root = None
			return

		if l and r:
			succ = self._successor(node)
			node.key, node.value = succ.key, succ.value
			node = succ
			l, r, p, red = node.left, node.right, node.parent, node.red

		if red:
			p.replace_child(node, None)
			return

		child = l or r

		if child:
			child.red = False
			p.replace_child(node, child)
			return

		right = node is p.right
		p.replace_child(node, None)

		while p:
			s = p.child(not right)
			d = s.child(not right)
			c = s.child(right)

			if s.red:
				self._rotate(p, right)
				p.red = True
				s.red = False
				d = s.child(not right)

				if d and d.red:
					self._rotate(p, right)
					s.red = p.red
					p.red = d.red = False
					break

				c = s.child(right)
				if c and c.red:
					self._rotate(s, not right)
					s.red = True
					c.red = False
					d, s = s, c
					self._rotate(p, right)
					s.red = p.red
					p.red = d.red = False
					break

				s.red = True
				p.red = False
				break

			if d and d.red:
				self._rotate(p, right)
				s.red = p.red
				p.red = d.red = False
				break

			if c and c.red:
				self._rotate(s, not right)
				s.red = True
				c.red = False
				d, s = s, c
				self._rotate(p, right)
				s.red = p.red
				p.red = d.red = False
				break

			if p.red:
				s.red = True
				p.red = False
				break

			s.red = True
			node = p
			p = node.parent
			right = node is p.right

class AVLNode(BSTNode):
	__slots__ = ('bf',)

	def __init__(self, key, value, parent=None, bf=0):
		super().__init__(key, value, parent)
		self.bf = 0

	def _repr_info(self):
		return f'bf={self.bf}'

	def _dot_attributes(self):
		label = json.dumps(f'{self.key}\n{self.value}')
		return  f'[label={label}]'

class AVLTree(BST):
	def __setitem__(self, key, value):
		node = AVLNode(key, value)

		if self._set(node):
			self._rebalance(node)
			self._len += 1

	def _rotate_left(self, node):
		new = self._rotate(node, False)

		if new.bf == 0:
			node.bf = +1
			new.bf = -1
		else:
			node.bf = new.bf = 0

	def _rotate_right(self, node):
		new = self._rotate(node, True)

		if new.bf == 0:
			node.bf = -1
			new.bf = +1
		else:
			node.bf = new.bf = 0

	def _rotate_left_right(self, node):
		self._rotate(node.left, False)
		new = self._rotate(node, True)

		bf, l, r = new.bf, new.left, new.right

		if bf == 0:
			l.bf = r.bf = 0
		elif bf > 0:
			l.bf = -1
			r.bf = 0
		else:
			l.bf = 0
			r.bf = +1

		new.bf = 0

	def _rotate_right_left(self, node):
		self._rotate(node.right, True)
		new = self._rotate(node, False)

		bf, l, r = new.bf, new.left, new.right

		if bf == 0:
			l.bf = r.bf = 0
		elif bf > 0:
			l.bf = -1
			r.bf = 0
		else:
			l.bf = 0
			r.bf = +1

		new.bf = 0

	def _rebalance(self, node):
		p = node.parent

		while p:
			bf, pbf = node.bf, p.bf

			if node is p.right:
				if pbf > 0:
					if bf < 0:
						self._rotate_right_left(p)
					else:
						self._rotate_left(p)
				else:
					if pbf < 0:
						p.bf = 0
						break

					p.bf = +1
					node, p = p, p.parent
					continue
			else:
				if pbf < 0:
					if bf > 0:
						self._rotate_left_right(p)
					else:
						self._rotate_right(p)
				else:
					if pbf > 0:
						p.bf = 0
						break

					p.bf = -1
					node, p = p, p.parent
					continue

			break

	def balance_factor(self):
		return self.root.bf if self.root else 0
