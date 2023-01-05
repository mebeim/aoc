#!/usr/bin/env python3

from utils.timer import timer_start
from math import inf as INFINITY
from functools import partial
from operator import itemgetter
from itertools import combinations, product
from collections import defaultdict

from utils import advent


def floyd_warshall(g):
    distance = defaultdict(lambda: defaultdict(lambda: INFINITY))

    for a, bs in g.items():
        distance[a][a] = 0

        for b in bs:
            distance[a][b] = 1
            distance[b][b] = 0

    for a, b, c in product(g, g, g):
        bc, ba, ac = distance[b][c], distance[b][a], distance[a][c]

        if ba + ac < bc:
            distance[b][c] = ba + ac

    return distance


def score(rates, valves):
    return sum(rates[v] * t for v, t in valves.items())


def solutions(distance, rates, valves, time=30, cur='AA', chosen=None):
    if chosen is None:
        chosen = {}
    for nxt in valves:
        new_time = time - distance[cur][nxt] - 1
        if new_time < 2:
            continue

        new_chosen = chosen | {nxt: new_time}
        yield from solutions(distance, rates, valves - {nxt}, new_time, nxt, new_chosen)

    yield chosen


advent.setup(2022, 16)

timer_start()

graph = defaultdict(list)
rates = {}

with advent.get_input() as fin:
    for fields in map(str.split, fin):
        src = fields[1]
        dsts = list(map(lambda x: x.rstrip(','), fields[9:]))
        rate = int(fields[4][5:-1])

        rates[src] = rate

        for dst in dsts:
            graph[src].append(dst)

good = frozenset(filter(rates.get, graph))
distance = floyd_warshall(graph)
score = partial(score, rates)
best = max(map(score, solutions(distance, rates, good)))

advent.print_answer(1, best)


maxscore = defaultdict(int)

for solution in solutions(distance, rates, good, 26):
    k = frozenset(solution)
    s = score(solution)

    if s > maxscore[k]:
        maxscore[k] = s

best = max(sa + sb for (a, sa), (b, sb)
           in combinations(maxscore.items(), 2) if not a & b)
advent.print_answer(2, best)
