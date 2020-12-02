Advent of Code 2020 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Report Repair](#day-1---report-repair)
- [Day 2 - Password Philosophy](#day-2---password-philosophy)


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


Day 2 - Password Philosophy
---------------------------

[Problem statement][d02-problem] — [Complete solution][d02-solution]

### Part 1

This is a password validation puzzle. We get a list of "password policies" as
input, one per line, in the following form:

```
<min>-<max> <letter>: <password>
Example: 4-10 e: ilovedolphins
```

A password is deemed "valid" if it contains the specified `<letter>` at least
`<min>` times, but no more than `<max>` times. We are asked to determine the
number of valid passwords.

Let's use the [`re`][py-re] module to make our life easier and parse the
policies using a [regular expression][wiki-regexp]. In order to match a single
policy, we can use the following regexp:

```
\d+-\d+ \w: \w+
```

Which means: *match one or more digits, followed by an hyphen, followed by or
more digits, followed by a space, followed by a character, followed by a colon
and a space, followed by one or more characters.*

Since we want to *extract* and separate those fields though, we can use capture
groups (`(...)`). When using capture groups, the result of a match is split into
a tuple, one element per capture group. This makes it very easy to parse complex
text formats.

We can add parentheses around every field we are interested in to turn it into a
capture group, and then use [`re.findall()`][py-re-findall] to parse the entire
input content and return a list of tuples, one tuple per policy:

```python
data     = fin.read()
policies = rexp.findall(r'(\d+)-(\d+) (\w): (\w+)', data)
```

Now just check each tuple, transforming the first two elements into integers,
and count valid passwords. We can just use [`str.count()`][py-str-count] for
this. I will call the two numbers `mmin` and `mmax`, because `min` and `max` in
Python are global names of built-in functions, and it's good practice to not
override any of those.

```python
valid = 0

for mmin, mmax, letter, password in policies:
	mmin, mmax = int(mmin), int(mmax)

	if mmin <= password.count(letter) <= mmax:
		valid += 1

print('Part 1:', valid)
```

Note: the comparison `a <= x <= b` checks if `x` is between `a` and `b`. This is
a Python specific feature. In most other programming languages (e.g. C and C++),
this does *not* behave in the same way, and `a <= x && x <= b` should be used
instead.

### Part 2

For the second part, we still have to count the number of valid passwords, but
the validation policy changes: our two numbers (min and max) now become indexes:
a password is valid if *only one* of the two letters at the specified indexes is
equal to the given letter. Note: these indexes start at `1`.

Since we are already transforming `mmin` and `mmax` into integers in the
previous loop, let's just modify it to calculate both answers instead of doing
the whole thing again.

```python
valid1, valid2 = 0, 0

for mmin, mmax, letter, password in policies:
	mmin, mmax = int(mmin), int(mmax)

	if mmin <= password.count(letter) <= mmax:
		valid1 += 1

	if password[mmin - 1] == letter and password[mmax - 1] != letter:
		valid2 += 1
	elif password[mmin - 1] != letter and password[mmax - 1] == letter:
		valid2 += 1

print('Part 1:', valid1)
print('Part 2:', valid2)
```


[d01-problem]: https://adventofcode.com/2020/day/1
[d02-problem]: https://adventofcode.com/2020/day/2
[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py

[py-builtin-enumerate]: https://docs.python.org/3/library/functions.html#enumerate
[py-set]:               https://docs.python.org/3/library/stdtypes.html?#set
[py-str-count]:         https://docs.python.org/3/library/stdtypes.html#str.count
[py-re]:                https://docs.python.org/3/library/re.html
[py-re-findall]:        https://docs.python.org/3/library/re.html#re.findall

[algo-manhattan]:     https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:      https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-bfs]:           https://en.wikipedia.org/wiki/Breadth-first_search
[algo-kahn]:          https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
[algo-binsrc]:        https://en.wikipedia.org/wiki/Binary_search_algorithm
[algo-wall-follower]: https://en.wikipedia.org/wiki/Maze_solving_algorithm#Wall_follower

[wiki-linear-time]:     https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-polynomial-time]: https://en.wikipedia.org/wiki/Time_complexity#Polynomial_time
[wiki-regexp]:          https://www.regular-expressions.info/
