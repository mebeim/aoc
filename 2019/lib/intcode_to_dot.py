#!/usr/bin/env python3
#
# Convert an Intcode program from Advent of Code 2019 into a .dot file
# representing the Control Flow Graph of the program.
#
# Once the .dot file is generated, one can transform it in an image simply by
# using the dot utility:
#
#     dot -Tpng cfg.dot > cfg.png
#
# (C) 2019 Marco Bonelli -- https://github.com/mebeim/aoc
#

import sys
import argparse
from operator import attrgetter
import pygraphviz as pgv
from intcode import *

def breaks_basic_block(op):
	return op.mnemonic in ('jnz', 'jz') and op.argmodes[1] == ARGMODE_IMMEDIATE

def disassemble(block):
	lines = []

	fmtargs = {
		'cmain': 'blue4',
		'cpc': 'gray50',
		'cmnemonic': 'blue4',
		'carg1': 'blue4',
		'carg2': 'blue4',
		'carg3': 'blue4',
	}

	fmts = (
		'<font color="{cmain}"><font color="{cpc}">{pc:>4d}:</font>  <font color="{cmnemonic}">{mnemonic:<4s}</font></font>{raw}<br align="left"/>',
		'<font color="{cmain}"><font color="{cpc}">{pc:>4d}:</font>  <font color="{cmnemonic}">{mnemonic:<4s}</font> <font color="{carg1}">{arg1:>8s}</font></font><br align="left"/>',
		'<font color="{cmain}"><font color="{cpc}">{pc:>4d}:</font>  <font color="{cmnemonic}">{mnemonic:<4s}</font> <font color="{carg1}">{arg1:>8s}</font> <font color="{carg2}">{arg2:>8s}</font></font><br align="left"/>',
		'<font color="{cmain}"><font color="{cpc}">{pc:>4d}:</font>  <font color="{cmnemonic}">{mnemonic:<4s}</font> <font color="{carg1}">{arg1:>8s}</font> <font color="{carg2}">{arg2:>8s}</font> <font color="{carg3}">{arg3:>8s}</font></font><br align="left"/>',
	)

	for op in block:
		l = len(op.args)
		t = type(op)

		fmtargs['pc'] = op.pc
		fmtargs['mnemonic'] = op.mnemonic
		fmtargs['raw'] = ''

		if t == OpInvalid:
			fmtargs['cmnemonic'] = 'crimson'
			fmtargs['raw'] = ' <font color="gray">{}</font>'.format(op.vm.code[op.pc])
		else:
			fmtargs['cmnemonic'] = 'blue3'

		for i, (a, m) in enumerate(zip(op.args, op.argmodes), 1):
			if m == ARGMODE_IMMEDIATE:
				fmtargs['arg%d' % i] = '{} '.format(a)
				fmtargs['carg%d' % i] = 'blue3'
			elif m == ARGMODE_POSITIONAL:
				fmtargs['arg%d' % i] = '[{}]'.format(a)
				fmtargs['carg%d' % i] = 'indigo'
			elif m == ARGMODE_RELATIVE:
				fmtargs['arg%d' % i] = '[r{}{}]'.format('+' if a >= 0 else '', a)
				fmtargs['carg%d' % i] = 'purple'

		line = fmts[l].format(**fmtargs)
		lines.append(line)

	return '<' + ''.join(lines) + '>'

def cfg(program, out_fname, simplify_jumps=False):
	vm         = IntcodeVM(program)
	vm.code    = vm.orig_code[:]
	addr_to_op = {}
	ops        = []

	while vm.pc < len(vm.code):
		op = Op.fromcode(vm, vm.pc)
		op.head = False
		op.tail = breaks_basic_block(op)
		ops.append(op)
		addr_to_op[op.pc] = op
		vm.pc += op.length

	ops[0].head = True

	for prev, cur in zip(ops, ops[1:]):
		if prev.tail:
			cur.head = True

	for op in filter(attrgetter('tail'), ops):
		op.jump_addr = op.decode_arg(1)

		if op.jump_addr in addr_to_op:
			dst = addr_to_op[op.jump_addr]
			dst.head = True

	blocks       = []
	cur_block    = None
	cur_block_id = 0
	edges        = []

	for op in ops:
		op.block_id = cur_block_id

		if op.head:
			if cur_block:
				blocks.append(cur_block)

			cur_block = [op]
			cur_block_id += 1
		else:
			cur_block.append(op)

	if cur_block:
		blocks.append(cur_block)

	for i, (prev, cur) in enumerate(zip(blocks, blocks[1:])):
		prev_op = prev[-1]

		if type(prev_op) == OpHlt:
			continue

		if prev_op.tail:
			mode = prev_op.argmodes[0]
			dst = None

			if prev_op.jump_addr in addr_to_op:
				dst = addr_to_op[prev_op.jump_addr].block_id

			if simplify_jumps and type(prev_op) == OpJz and mode == ARGMODE_IMMEDIATE:
				if prev_op.args[0] == 0 and dst is not None:
					edges.append((i, dst, J_UNCONDITIONAL))
				else:
					kind = J_UNCONDITIONAL
			elif simplify_jumps and type(prev_op) == OpJnz and mode == ARGMODE_IMMEDIATE:
				if prev_op.args[0] != 0 and dst is not None:
					edges.append((i, dst, J_UNCONDITIONAL))
				else:
					kind = J_UNCONDITIONAL
			else:
				if dst is not None:
					edges.append((i, dst, J_TRUE))

				edges.append((i, i + 1, J_FALSE if cur[0].head else J_UNCONDITIONAL))
		else:
			edges.append((i, i + 1, J_UNCONDITIONAL))

	G = pgv.AGraph(directed=True, **GRAPH_ATTRS)
	G.node_attr.update(NODE_ATTRS)
	G.edge_attr.update(EDGE_ATTRS)

	for i, b in enumerate(blocks):
		G.add_node(i, label=disassemble(b))

	for src, dst, kind in edges:
		G.add_edge(src, dst, color=COLORS[kind]) #**J_ATTRS[kind])

	G.write(out_fname)


J_UNCONDITIONAL, J_TRUE, J_FALSE = range(3)
COLORS = ('grey30', 'green3', 'red')

# Meh, not that cool...
# J_ATTRS = (
# 	{'tailport': 's', 'headport': 'n'},
# 	{'tailport': 'se', 'headport': 'ne'},
# 	{'tailport': 'sw', 'headport': 'nw'}
# )

GRAPH_ATTRS = {}
NODE_ATTRS = {'shape': 'box', 'fontname': 'monospace'}
EDGE_ATTRS = {}

if __name__ == '__main__':
	parser = argparse.ArgumentParser(
		description='Parse an intcode program and generate a .dot file representing its Control Flow Graph.'
	)

	parser.add_argument('in_fname', metavar='program', help='Intcode program filename')
	parser.add_argument('out_fname', metavar='output.dot', nargs='?', default=None, help='optional output filaneme')
	parser.add_argument('-j', dest='simplify_jumps', action='store_true', help='simplify unconditional jumps')
	args = parser.parse_args()

	if not args.out_fname:
		ext = args.in_fname.rfind('.')
		args.out_fname = (args.in_fname if ext == -1 else args.in_fname[:ext]) + '.dot'

	with open(args.in_fname) as fin:
		try:
			program = list(map(int, fin.read().split(',')))
		except:
			sys.stderr.write(
				'Error parsing intcode program. '
				'Make sure the file only contains a list of integers separated '
				'by commas.\n'
			)
			sys.exit(1)

	cfg(program, args.out_fname, args.simplify_jumps)
