Advent of Code 2020 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Report Repair](#day-1---report-repair)
- [Day 2 - Password Philosophy](#day-2---password-philosophy)
- [Day 3 - Toboggan Trajectory](#day-3---toboggan-trajectory)
- [Day 4 - Passport Processing](#day-4---passport-processing)


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


Day 4 - Passport Processing
---------------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution]

### Part 1

Another input validation puzzle. This time we are going to process passports: we
are given a list of passports as input, which are separated by empty lines (that
is, two consecutive newline characters). Each passport is a list `key:value`
pairs delimited by either a space or a newline.

A passport is deemed valid if and only if it has all the required fields, which
are identified by these keys: `byr`, `iyr`, `eyr`, `hgt`, `hcl`, `ecl`, `pid`.
There is also a `cid` field described, but it does not matter if it's present or
not. We need to count the number of valid passports.

First of all, let's get all passports:

```python
passports = fin.read().split('\n\n')
```

Easy enough, after splitting the input data on empty lines, we can just check if
all the required fields above are present in each passport. Since we don't know
what the `value` of a field could contain, we cannot simply just check if each
field key is present in the string representation of a passport: we also need to
make sure it's present *as a key*. We could parse each passport, but I'm going
to cheat and solve this check by just adding a colon (`:`) after each field key,
since keys must be followed by colons.

```python
KEYS = ('byr:', 'iyr:', 'eyr:', 'hgt:', 'hcl:', 'ecl:', 'pid:')
n_valid = 0

for passport in passports:
    valid = False
    for k in KEYS:
        if k not in passport:
            valid = False

    if valid:
        n_valid += 1
```

Okay, that's a bit too long for my taste. Not Pythonic at all! We can simplify
here taking advantage of the [`all()`][py-builtin-all] and
[`sum()`][py-builtin-sum] built-in functions. The `all()` function checks if all
the values of an iterable are `True` (or evaluate to `True`, e.g. a non-empty
list, and so on). We can therefore rewrite the internal loop (`for k in keys`)
as a single line using a generator expression:

```python
all(k in passport for k in keys)
# -> True only if the passport has all the required keys
```

The `sum()` function computes the sum of all the values of an iterable (duh!),
and treats boolean values as integers (`int(True) == 1`, `int(False) == 0`).
This means that we can use `sum(all(...))` to count how many values are true in
an iterable. Therefore, one more generator expression gives us the solution in
just one line.

```python
n_valid = sum(all(k in p for k in KEYS) for p in passports)
print('Part 1:', n_valid)
```

### Part 2

We now also have to validate the `value` of each field. We still need to ignore
the `cid` field, but other fields have specific validity requirements:

- `byr` (Birth Year): a 4-digit number in the range `[1920, 2002]`.
- `iyr` (Issue Year): a 4-digit number in the range `[2010, 2020]`.
- `eyr` (Expiration Year): a 4-digit number in the range `[2020, 2030]`.
- `hgt` (Height): a number followed by `cm` or `in`. If `cm`, it must be in the
  range `[150, 193]`; if `in`, it must be in the range `[59, 76]`.
- `hcl` (Hair Color): `#` followed by exactly six characters `0-9` or `a-f`.
- `ecl` (Eye Color): exactly one of: `amb`, `blu`, `brn`, `gry`, `grn`, `hzl`, `oth`.
- `pid` (Passport ID): a 9-digit number, including leading zeroes.

Whelp, now we really need to parse those passports. We don't care about having a
`{key: value}` dictionary of fields since we will need to validate all fields
anyway, so a simple `list` of `(key, value)` pairs will suffice. To obtain the
fields, we'll split the entire "raw" passport string using the
[`str.split()`][py-str-split] method, which by default conveniently splits on
any sequence of whitespace, so we don't even need to care about passports
contining newlines. Then, we'll split each field on `:` to saparate keys and
values.

```python
for raw in passports:
    passport = (field.split(':') for field in raw.split())
```

To validate each field, since the validations to perform are rather simple, we
can use a dictionary of [`lambda`][py-lambda] expressions. It's simpler to show
the code than describe it:

```python
def check_height(v):
    if v.endswith('cm'):
        return 150 <= int(v[:-2]) <= 193
    if v.endswith('in'):
        return 59 <= int(v[:-2]) <= 76
    return False

checks = {
    'byr': lambda v: 1920 <= int(v) <= 2002,
    'iyr': lambda v: 2010 <= int(v) <= 2020,
    'eyr': lambda v: 2020 <= int(v) <= 2030,
    'pid': lambda v: len(v) == 9 and all(c.isdigit() for c in v),
    'hcl': lambda v: len(v) == 7 and all(c.isdigit() or c in 'abcdef' for c in v[1:]),
    'ecl': lambda v: v in ('amb', 'blu', 'brn', 'gry', 'grn', 'hzl', 'oth'),
    'cid': lambda v: True,
    'hgt': check_height
}
```

The check for `pid` uses the built-in [`str.isdigit()`][py-str-isdigit], which
is faster than checking `c in '0123456789'` or even
`ok = set('123456789'); c in ok`. The check for `hcl` could also be written
using a regular expression or an `in` on a `set`, but for such a short
string and simple set of characters that would just slow things down.

The only non `lambda` function in the above dictionary is `check_weight`, since
it needs to do a couple of checks more than the others and writing it as a
`lambda` would make it pretty hard to read and understand. Finally, the `lambda`
function for `cid` just returns `True` since we do not care about that field.

We can now parse all passports and run the right check for any given `key:value`
field. We can again use the `all()` function to make all checks for a single
passport in one line, iterating over the `(key, value)` pairs that we have.

```python
n_valid = 0

for raw in passports:
    passport = (field.split(':') for field in raw.split())

    if all(checks[k](v) for k, v in passport):
        n_valid += 1
```

Note that in the above code we are *not* enclosing the generator expression to
parse the passport in square brackets (`[]`), but merely in parentheses (`()`):
that's because we only need to iterate over it once, so we don't care about
transforming it into a `list`, that would just slow things down. Using
parentheses yields the underlying `generator` object ready to be iterated over.

Going one last little step further we can also do both vaildity checks (part 1
and part 2) in a single loop:

```python
n_valid1 = 0
n_valid2 = 0

for raw in passports:
    if all(k in raw for k in KEYS):
        n_valid1 += 1
        passport = (field.split(':') for field in raw.split())

        if all(checks[k](v) for k, v in passport):
            n_valid2 += 1

print('Part 1:', n_valid1)
print('Part 2:', n_valid2)
```

Not really that interesting or complicated of a puzzle if you ask me, but the
code looks nice nonetheless!


[d01-problem]: https://adventofcode.com/2020/day/1
[d02-problem]: https://adventofcode.com/2020/day/2
[d03-problem]: https://adventofcode.com/2020/day/3
[d04-problem]: https://adventofcode.com/2020/day/4
[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py
[d04-solution]: solutions/day04.py

[py-raw-string]:        https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
[py-generator-expr]:    https://www.python.org/dev/peps/pep-0289/
[py-lambda]:            https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-set]:               https://docs.python.org/3/library/stdtypes.html?#set
[py-str-count]:         https://docs.python.org/3/library/stdtypes.html#str.count
[py-str-isdigit]:       https://docs.python.org/3/library/stdtypes.html#str.isdigit
[py-str-split]:         https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-strip]:         https://docs.python.org/3/library/stdtypes.html#str.strip
[py-builtin-enumerate]: https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-all]:       https://docs.python.org/3/library/functions.html#all
[py-builtin-sum]:       https://docs.python.org/3/library/functions.html#sum
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
