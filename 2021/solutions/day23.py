#!/usr/bin/env python3

from utils import advent
from math import inf as INFINITY
from functools import lru_cache

ROOM_DISTANCE = (
	(2, 1, 1, 3, 5, 7, 8), # from/to room 0
	(4, 3, 1, 1, 3, 5, 6), # from/to room 1
	(6, 5, 3, 1, 1, 3, 4), # from/to room 2
	(8, 7, 5, 3, 1, 1, 2), # from/to room 3
)

def move_cost(room, hallway, r, h, room_size, to_room=False):
	if r + 1 < h:
		start = r + 2
		end   = h + (not to_room)
	else:
		start = h + to_room
		end   = r + 2

	if any(x is not None for x in hallway[start:end]):
		return INFINITY

	obj = hallway[h] if to_room else room[0]

	return 10**obj * (ROOM_DISTANCE[r][h] + (to_room + room_size - len(room)))

def moves_to_room(rooms, hallway, room_size):
	for h, obj in enumerate(hallway):
		if obj is None:
			continue

		room = rooms[obj]
		if any(o != obj for o in room):
			continue

		cost = move_cost(room, hallway, obj, h, room_size, to_room=True)
		if cost == INFINITY:
			continue

		new_rooms   = rooms[:obj] + ((obj,) + room,) + rooms[obj + 1:]
		new_hallway = hallway[:h] + (None,) + hallway[h + 1:]
		yield cost, (new_rooms, new_hallway)

def moves_to_hallway(rooms, hallway, room_size):
	for r, room in enumerate(rooms):
		if all(o == r for o in room):
			continue

		for h in range(len(hallway)):
			cost = move_cost(room, hallway, r, h, room_size)
			if cost == INFINITY:
				continue

			new_rooms   = rooms[:r] + (room[1:],) + rooms[r + 1:]
			new_hallway = hallway[:h] + (room[0],) + hallway[h + 1:]
			yield cost, (new_rooms, new_hallway)

def possible_moves(rooms, hallway, room_size):
	try:
		yield next(moves_to_room(rooms, hallway, room_size))
	except StopIteration:
		yield from moves_to_hallway(rooms, hallway, room_size)

def done(rooms, room_size):
	for r, room in enumerate(rooms):
		if len(room) != room_size or any(obj != r for obj in room):
			return False
	return True

@lru_cache(maxsize=None)
def solve(rooms, hallway, room_size=2):
	if done(rooms, room_size):
		return 0

	best = INFINITY

	for cost, next_state in possible_moves(rooms, hallway, room_size):
		cost += solve(*next_state, room_size)

		if cost < best:
			best = cost

	return best

def parse_rooms(fin):
	next(fin)
	next(fin)
	rooms = []

	for _ in range(2):
		l = next(fin)
		rooms.append(map('ABCD'.index, (l[3], l[5], l[7], l[9])))

	return tuple(zip(*rooms))


advent.setup(2021, 23)
fin = advent.get_input()

hallway  = (None,) * 7
rooms    = parse_rooms(fin)
min_cost = solve(rooms, hallway)

advent.print_answer(1, min_cost)


newobjs  = [(3, 3), (2, 1), (1, 0), (0, 2)]
newrooms = []

for room, new in zip(rooms, newobjs):
	newrooms.append((room[0], *new, room[-1]))

rooms    = tuple(newrooms)
min_cost = solve(rooms, hallway, len(rooms[0]))

advent.print_answer(2, min_cost)
