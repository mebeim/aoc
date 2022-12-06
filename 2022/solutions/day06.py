#!/usr/bin/env python3

from utils import advent

def find_start(data, header_len, start=0):
	for i in range(start, len(data) - header_len):
		if len(set(data[i:i + header_len])) == header_len:
			return i + header_len


advent.setup(2022, 6)

with advent.get_input() as fin:
	data = fin.read()

sop = find_start(data, 4)
som = find_start(data, 14, sop)

advent.print_answer(1, sop)
advent.print_answer(2, som)
