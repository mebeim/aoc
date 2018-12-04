#!/usr/bin/env python3

import utils

utils.setup(2018, 1, dry_run=True)
fin = utils.get_input()

deltas = list(map(int, fin.readlines()))
done = False
freq = 0
seen = set()
seen.add(0)


for d in deltas:
	freq += d

	if not done and freq in seen:
		done = True

	seen.add(freq)

# assert freq == 435

utils.submit_answer(1, freq)

while not done:
	for d in deltas:
		freq += d

		if freq in seen:
			done = True
			break

		seen.add(freq)

# assert freq == 245

utils.submit_answer(2, freq)
