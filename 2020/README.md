Advent of Code 2020 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Report Repair](#day-1---report-repair)
- [Day 2 - Password Philosophy](#day-2---password-philosophy)
- [Day 3 - Toboggan Trajectory](#day-3---toboggan-trajectory)


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
policy, we can use the regexp `\d+-\d+ \w: \w+`, which means: *match one or more
digits, followed by an hyphen, followed by one or more digits, followed by a
space, followed by a character, followed by a colon and a space, followed by one
or more characters.*

Since we want to *extract* and separate those fields though, we can use capture
groups (`(...)`). When using capture groups, the result of a match is split into
a tuple, one element per capture group. This makes it very easy to parse complex
text formats. We can therefore add parentheses around every field we are
interested in to turn it into a capture group, then use
[`re.findall()`][py-re-findall] to parse the entire input content and get a list
of tuples, one tuple per policy:

```python
data     = fin.read()
policies = rexp.findall(r'(\d+)-(\d+) (\w): (\w+)', data)
```

The syntax `r'string'` denotes a [raw string][py-raw-string]: it means to
interpret the content of the string *literally*, without processing escape
sequences, like for example `\n`, which in a normal string would be turned into
a single character (a line feed).

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
the whole thing again. In order to check if *only one* of the two indexes in the
password contains the letter we want, we can use the XOR operator (`^`), which
in Python it can also be used on boolean values, and returns `True` if only one
of the two operands is `True`.

```python
valid1, valid2 = 0, 0

for mmin, mmax, letter, password in policies:
    mmin, mmax = int(mmin), int(mmax)

    if mmin <= password.count(letter) <= mmax:
        valid1 += 1

    if (password[mmin - 1] == letter) ^ (password[mmax - 1] != letter):
        valid2 += 1

print('Part 1:', valid1)
print('Part 2:', valid2)
```

Note: another way to compute the logical XOR between two boolean values is `!=`.
In fact, if two boolean values are different from each other then one of them
must be `True` and the other one must be `False`.


Day 3 - Toboggan Trajectory
---------------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution]

### Part 1

First grid of ASCII characters of the year! I was just waiting for that. Today's
puzzle input consists of a rectangular grid of characters. Each character can be
either be a dot (`.`) meaning "open square" or a hash (`#`) representing a tree.
The grid we are given is quite tall but very thin (i.e. `height >> width`).
However, we are told that the rows of the real grid are actually periodic and
they extend indefinitely to the right.

We need to traverse the grid following a certain "slope", starting from the
top-left corner and moving 1 square down and 3 squares to the right each step,
counting all the trees that we encounter on our way.

First of all, let's parse the input. We use a
[generator expression][py-generator-expr] iterating over the file line by line
(in case you did not know, iterating over a file obtained from `open()` yields
the lines one by one) using [`str.strip()`][py-str-strip] to remove newline
characters (`\n`) at the end of each line. We end up with a list of strings, one
string per row of the grid.

```python
grid = [l.rstrip() for l in fin]
height, width = len(grid), len(grid[0])
```

Now we can just start at `(0, 0)` and check each square we want incrementing by
`(1, 3)` each time. To take into account the fact that the grid is actually
periodically repeating to the right, we can use the modulo (`%`) operator for
the column, doing `col % width`, which will effectively "wrap" around and
re-start from `0` each time we go above `width`, as if the row is repeating.

```python
trees = 0
col = 0

for row in range(height):
    if grid[row][col % width] == '#':
        trees += 1
    col += 3
```

Okay, that seems reasonable. It doesn't smell *Pythonic* enough though! A
simpler, more concise way to do this is to use the [`zip()`][py-builtin-zip]
built-in function to iterate over two ranges (one for `row` and one for `col`)
at the same time. One problem though: we don't know when to stop `col`. We could
calculate the number mathematically, but a really simpler way is to take
advantage of [`itertools.count()`][py-itertools-count]: this generator function
takes a `start` and a `step`, and returns numbers from `start` to infinity, in
increments of `step`. Since `zip()` stops at the end of the shortest iterable
supplied, it will automagically stop for us when we reach `height`.

```python
from itertools import count

trees = 0
for row, col in zip(range(height), count(0, 3)):
    if grid[row][col % width] == '#':
        trees += 1

print('Part 1:', trees)
```

Now that looks nice and compact.

### Part 2

Now we need to do the same thing as part 1 multiple times, for different slopes.
Our original slope was `(1, 3)` (1 down and 3 right each step). We now have four
additional slopes to follow and count trees on: `(1, 1)`, `(1, 5)`, `(1, 7)`,
and `(2, 1)`. The answer we must give is the product of the number of
encountered trees on each different slope.

Simple enough, we can just wrap everything in a `for` loop, iterating over the
slopes. The only difference from part 1 is that now we'll need to advance our
`range()` and `count()` with the two steps given by each slope. We already
calculated the number of trees for slope `(1, 3)`, so we start with that number.

```python
total = trees
slopes = ((1, 1), (1, 5), (1, 7), (2, 1))

for dr, dc in slopes:
    trees = 0

    # Only difference from part 1 is that we now use 'dr' and 'dc' as steps
    for row, col in zip(range(0, height, dr), count(0, dc)):
        if grid[row][col % width] == '#':
            trees += 1

    total *= trees

print('Part 2:', total)
```

And that's six out of fifty stars!


[d01-problem]: https://adventofcode.com/2020/day/1
[d02-problem]: https://adventofcode.com/2020/day/2
[d03-problem]: https://adventofcode.com/2020/day/3
[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py

[py-raw-string]:        https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
[py-generator-expr]:    https://www.python.org/dev/peps/pep-0289/
[py-set]:               https://docs.python.org/3/library/stdtypes.html?#set
[py-str-count]:         https://docs.python.org/3/library/stdtypes.html#str.count
[py-str-strip]:         https://docs.python.org/3/library/stdtypes.html#str.strip
[py-builtin-enumerate]: https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-zip]:       https://docs.python.org/3/library/functions.html#zip
[py-itertools-count]:   https://docs.python.org/3/library/itertools.html#itertools.count
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
