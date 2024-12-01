Advent of Code 2024 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Historian Hysteria][d01]
<!--
- [Day 2 - xxx][d02]
- [Day 3 - xxx][d03]
- [Day 4 - xxx][d04]
- [Day 5 - xxx][d05]
- [Day 6 - xxx][d06]
- [Day 7 - xxx][d07]
- [Day 8 - xxx][d08]
- [Day 9 - xxx][d09]
- [Day 10 - xxx][d10]
- [Day 11 - xxx][d11]
- [Day 12 - xxx][d12]
- [Day 13 - xxx][d13]
- [Day 14 - xxx][d14]
- [Day 15 - xxx][d15]
- [Day 16 - xxx][d16]
- [Day 17 - xxx][d17]
- [Day 18 - xxx][d18]
- [Day 19 - xxx][d19]
- [Day 20 - xxx][d20]
- [Day 21 - xxx][d20]
- [Day 22 - xxx][d20]
- [Day 23 - xxx][d20]
- [Day 24 - xxx][d20]
- [Day 25 - xxx][d20]
-->



Day 1 - Historian Hysteria
--------------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution] — [Back to top][top]

### Part 1

All right, let's get this year started! We have two lists of integers and need
to find differences between their elements, pairing them up in increasing order.
First, read each input line, split it and convert to `int` using
[`map()`][py-builtin-map].

```python
fin = open(...)

total = 0
left = []
right = []

for line in fin:
    l, r = map(int, line.split())
    left.append(l)
    right.append(r)
```

Now all we need to do is [`.sort()`][py-list-sort] them, then then iterate over
the sorted pairs obtained via [`zip()`][py-builtin-zip] summing up their
differences. For that, [`sum()`][py-builtin-sum] plus a [generator
expression][py-gen-expr] will do the trick.


```python
left.sort()
right.sort()

total = sum(abs(l - r) for l, r in zip(left, right))
print('Part 1:', total)
```

### Part 2

Now instead of summing differences we need to sum products. Each number on the
left list needs to be multiplied by the number of times it appears on the right
list. We can again use a generator expression or convert everything into a `for`
loop to do both parts at once. The number of occurrences can be obtained via
[`.count()`][py-list-count].

```python
for l, r in zip(left, right):
    total1 += abs(l - r)
    total2 += l * right.count(l)

print('Part 1:', total1)
print('Part 2:', total2)
```

---

*Copyright &copy; 2024 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)


[top]: #advent-of-code-2023-walkthrough
[d01]: #day-1---trebuchet
[d02]: #day-2---cube-conundrum
[d03]: #day-3---gear-ratios
[d04]: #day-4---scratchcards
[d05]: #day-5---if-you-give-a-seed-a-fertilizer
[d06]: #day-6---wait-for-it
[d07]: #day-7---camel-cards
[d08]: #day-8---haunted-wasteland
[d09]: #day-9---mirage-maintenance
[d10]: #day-10---
[d11]: #day-11---cosmic-expansion
[d12]: #day-12---hot-springs
[d13]: #day-13---point-of-incidence
[d14]: #day-14---parabolic-reflector-dish
[d15]: #day-15---lens-library
[d16]: #day-16---the-floor-will-be-lava
[d17]: #day-17---clumsy-crucible
[d18]: #day-18---lavaduct-lagoon
[d19]: #day-19---aplenty
[d20]: #day-20---pulse-propagation
[d21]: #day-21---
[d22]: #day-22---
[d24]: #day-24---
[d25]: #day-25---

[d01-problem]: https://adventofcode.com/2023/day/1
[d02-problem]: https://adventofcode.com/2023/day/2
[d03-problem]: https://adventofcode.com/2023/day/3
[d04-problem]: https://adventofcode.com/2023/day/4
[d05-problem]: https://adventofcode.com/2023/day/5
[d06-problem]: https://adventofcode.com/2023/day/6
[d07-problem]: https://adventofcode.com/2023/day/7
[d08-problem]: https://adventofcode.com/2023/day/8
[d09-problem]: https://adventofcode.com/2023/day/9
[d10-problem]: https://adventofcode.com/2023/day/10
[d11-problem]: https://adventofcode.com/2023/day/11
[d12-problem]: https://adventofcode.com/2023/day/12
[d13-problem]: https://adventofcode.com/2023/day/13
[d14-problem]: https://adventofcode.com/2023/day/14
[d15-problem]: https://adventofcode.com/2023/day/15
[d16-problem]: https://adventofcode.com/2023/day/16
[d17-problem]: https://adventofcode.com/2023/day/17
[d18-problem]: https://adventofcode.com/2023/day/18
[d19-problem]: https://adventofcode.com/2023/day/19
[d20-problem]: https://adventofcode.com/2023/day/20
[d21-problem]: https://adventofcode.com/2023/day/21
[d22-problem]: https://adventofcode.com/2023/day/22
[d24-problem]: https://adventofcode.com/2023/day/24
[d25-problem]: https://adventofcode.com/2023/day/25

[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py
[d04-solution]: solutions/day04.py
[d05-solution]: solutions/day05.py
[d06-solution]: solutions/day06.py
[d07-solution]: solutions/day07.py
[d08-solution]: solutions/day08.py
[d09-solution]: solutions/day09.py
[d10-solution]: solutions/day10.py
[d11-solution]: solutions/day11.py
[d12-solution]: solutions/day12.py
[d13-solution]: solutions/day13.py
[d14-solution]: solutions/day14.py
[d15-solution]: solutions/day15.py
[d16-solution]: solutions/day16.py
[d17-solution]: solutions/day17.py
[d18-solution]: solutions/day18.py
[d19-solution]: solutions/day19.py
[d20-solution]: solutions/day20.py
[d21-solution]: solutions/day21.py
[d22-solution]: solutions/day22.py
[d24-solution]: solutions/day24.py
[d25-solution]: solutions/day25.py


[py-gen-expr]: https://docs.python.org/3/reference/expressions.html#generator-expressions

[py-builtin-map]: https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]: https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]: https://docs.python.org/3/library/functions.html#zip
[py-list-count]:  https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:   https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
