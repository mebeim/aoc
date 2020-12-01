Advent of Code 2020 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Report Repair](#day-1---report-repair)


Day 1 - Report Repair
---------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution]

### Part 1

We are given a list of numbers as input, and we are asked to find a pair of
numbers that sums up to `2020`, and provide their product as an answer.

This is such a standard coding interview question! Though anybody usually would
immediately think of writing two nested `for` loops to find the answer in
[quadratic time][wiki-polynomial-time], this is solvable in [linear
time][wiki-linear-time] (that is, scanning the list of numbers only once).

We'll scan the numbers building up a [`set`][py-set] of 2020's complements
(`2020 - x` for each `x`). Then, for each number, check if we already have it in
the set: if so, this means that we already saw its complement, and we know it's
`2020 - x`; otherwise add its complement to the set.

```python
numbers = tuple(map(int, fin.readlines()))
compls  = set()

for x in numbers:
    y = 2020 - x

    if y in compls:
        ans = x * y
        break

    compls.add(y)

print('Part 1:', ans)
```

### Part 2

Same thing as part 1, but we need to search for *three* numbers that sum up to
`2020` now.

This complicates things a little bit. We can no longer find an answer in linear
time, but we surely can avoid cubic time and find it in quadratic time. We can
use the exact same aproach used for part 1, wrapping everything in one more
`for` loop.

It's like solving the same problem for each number: for every `x` we want to
find `y` and `z` such that `y + z == 2020 - x`. So for each number `x` we can
just calculate `2020 - x` and then do the exact same search that we did before.
In order to iterate over `numbers` while getting both the values and their
indexes at once, we can use the useful [`enumerate()`][py-builtin-enumerate]
buil-in function.

```python
for i, x in enumerate(numbers):
    compls = set()
    yz = 2020 - x

    for y in numbers[i + 1:]:
        z = yz - y

        if y in compls:
            ans = x * y * z
            break

        compls.add(z)

print('Part 2:', ans)
```

First two stars of the year. Off to a good start!


[d01-problem]: https://adventofcode.com/2020/day/1
[d01-solution]: solutions/day01.py

[py-builtin-enumerate]: https://docs.python.org/3/library/functions.html#enumerate
[py-set]:               https://docs.python.org/3/library/stdtypes.html?#set

[algo-manhattan]:     https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:      https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-bfs]:           https://en.wikipedia.org/wiki/Breadth-first_search
[algo-kahn]:          https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
[algo-binsrc]:        https://en.wikipedia.org/wiki/Binary_search_algorithm
[algo-wall-follower]: https://en.wikipedia.org/wiki/Maze_solving_algorithm#Wall_follower

[wiki-linear-time]:     https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-polynomial-time]: https://en.wikipedia.org/wiki/Time_complexity#Polynomial_time