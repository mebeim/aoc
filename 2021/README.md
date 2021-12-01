Advent of Code 2021 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Sonar Sweep][d01]

Day 1 - Sonar Sweep
-------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution] — [Back to top][top]

### Part 1

We are given a list of numbers as input, and we are asked to count the number of
consecutive pairs (overlapping) where the second number is higher than the
first.

After getting the numbers from the input file into a list. We can use the
[`map()`][py-builtin-map] built-in over the opened file object to convert every
line into `int`. To iterate over pairs of consecutive numbers we can use the
[`zip()`][py-builtin-zip] built-in. Then, for each pair check whether the
condition applies: we can use `map()` again for this: map each pair `(a, b)` to
the expression `b > a`, and then [`sum()`][py-builtin-sum] up all the values
(this works because `True` and `False` evaluate to `1` and `0` respectively when
summing). All in all, it's a single line of code:

```python
nums = tuple(map(int, fin))
tot  = sum(b > a for a, b in zip(nums, nums[1:]))
print('Part 1:', tot)
```

### Part 2

Now we need to group numbers by 3, using a sliding-window method to determine
how many couples of (overlapping) triplets are there where the second triplet
has an higher sum than the first one. For example, in `1 2 3 4` the triplet
`2 3 4` has higher sum than the previous triplet `1 2 3`.

We could write a one liner again, but that'd be annoyingly ugly. Let's actually
use a loop this time. We can use `zip` again to group the numbers in triplets
and then `map()` with `sum` to convert the triplets into their sum:

```python
tot  = 0
prev = float('inf')

for cur in map(sum, zip(nums, nums[1:], nums[2:])):
    if cur > prev:
        tot += 1
    prev = cur

print('Part 2:', tot)
```

The trick `prev = float('inf')` makes `prev` the highest possible Python number
so that we don't have to write a special case for the first element in the
`for`.

Well, well, well. Welcome to Advent of Code 2021!

---

*Copyright &copy; 2021 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2021-walkthrough
[d01]: #day-1---sonar-sweep

[d01-problem]: https://adventofcode.com/2021/day/1

[d01-solution]: solutions/day01.py

[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
