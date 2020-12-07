Advent of Code 2020 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Report Repair][d01]
- [Day 2 - Password Philosophy][d02]
- [Day 3 - Toboggan Trajectory][d03]
- [Day 4 - Passport Processing][d04]
- [Day 5 - Binary Boarding][d05]
- [Day 6 - Custom Customs][d06]
- [Day 7 - Handy Haversacks][d07]

Day 1 - Report Repair
---------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution] — [Back to top][top]

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
policies using a [regular expression][misc-regexp]. In order to match a single
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

[Problem statement][d03-problem] — [Complete solution][d03-solution] — [Back to top][top]

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

[Problem statement][d04-problem] — [Complete solution][d04-solution] — [Back to top][top]

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


Day 5 - Binary Boarding
-----------------------

[Problem statement][d05-problem] — [Complete solution][d05-solution] — [Back to top][top]

### Part 1

Cool and simple problem today. We have a list of "special" seat numbers as
input: each one consists of exactly 10 characters, where the first 7 are either
`F` or `B` and represent the seat row, while the last 3 are either `L` or `R`
and represent the seat column. The airplane we are boarding has 128 rows
(numbered `0` through `127` from the front) and 8 columns (numbered `0` through
`7` from the left).

The first character of the seat's row identifies a half of the plane where the
seat will be: either the front half `F` (rows `0` through `63`) or the back half
`B` (rows `64` to `127`). Moving on, each subsequent character identifies which
half of *the previous half* the row will be. Each character restricts the space
to a half of the previous one until we finally identify a single row.

We need to identify the seat with the highest ID, calculated as `row * 8 + col`.

To make it clearer, let's look at an example. Assume the first 7 characters of
the seat are `FBFBBFF`, this means:

1. `F` front half: from `0` to `63`.
2. `B` back half of previous half: from `32` to `63`.
3. `F` front half of previous half: from `32` to `47`.
4. `B` back half: from `40` to `47`.
5. `B` back half: from `44` to `47`.
6. `F` front half: row `44` or `45`.
7. `F` the row is `44`.

It's easy to notice that all those `F`s and `B`s are doing is just encode the
row in binary. `F` makes the number lower, so it can be seen as a binary `0`,
and `B` makes the number higher, so it can be seen as `1`. If we rewrite the
above example substituting `F` with `0` and `B` with `1` we get `0101100`, which
is exactly `44` in binary. The exact same thing applies to the columns, each `L`
can be seen as a `0` and each `R` as a `1`.

All we have to do to find the row and column of a seat is to just separate row
and column first, and then interpret those as two binary numbers. Python already
knows how to transform a string representing a binary number into an integer,
but it obviouslt expects the characters to be either `0` or `1`. We can just
replace all instances of `F` and `L` with `0`, and all instances of `B` and `R`
with `1`. Then, separate the first 7 and the last 3, and use
[`int(x, 2)`][py-builtin-int] to convert them to integers.

Normally, to replace a characters in a string you would use
[`str.replace()`][py-str-replace], so something like this:

```python
>>> 'FBFBBFFRLR'.replace('F', '0').replace('B', '1').replace('L', '0').replace('R', '1')
'0101100101'
```

However, that is (1) pretty ugly and (2) pretty slow as it scans everything
*four* times. Thankfully, we can do this in a much cleaner way using
[`str.maketrans()`][py-str-maketrans] and [`str.translate()`][py-str-translate].
These two built-in methods exist exactly for this purpose: `.maketrans()` takes
two strings of equal length and builds a *translation table* that turns each
i-th character of the first to the i-th character of the second. This
translation table can then be passed to `.translate()` to do the translation. If
you are familiar with Linux command line tools, you might know about
[`tr`][misc-man1-tr]: what we are going to write will produce exactly the same
result as the command `cat input | tr BFRL 1010`.

It's almost ridicolous that all of the long explanations above just translate to
two lines of Python:

```python
table = str.maketrans('BFRL', '1010')
seats = fin.read().translate(table).splitlines()
# 'BBFFBFBRRR\nBBFBFFBLLR\n...' -> ['1100101111', '1101001001', ...]
```

We now have a list of binary strings. Remember what we want to find? We want to
get the ID obtained as `row * 8 + col`. Do we really need to split the string in
two and convert each `row` and `col` from binary to integer to do this? Not
really! What that multiplication by `8` actually does, thinking about it in
binary, is just shifting `row` left by 3 bits. In fact, `row * 8` and `row << 3`
are equivalent operations. The column, which is the lower 3 bits, is then added
to it. In short, we are doing:

```
1100101|111 -> 1100101000 + 111 == 1100101000 + 111 == 110010111
    row|col ->    row * 8 + col == (row << 3) + col == initial number!
```

So all of this is just useless gibberish. We already have the binary
representation of all the seat IDs! We just need to turn them into integers.
Let's use our beloved `map()` and `lambda` combination again to do just that.
Then, use [`max()`][py-builtin-max] to find the maximum of those.

```python
ids    = tuple(map(lambda s: int(s, 2), seats))
max_id = max(ids)

print('Part 1:', max_id)
```

Today's part 1 was 4 lines of Python. Actually, you could make it 1 line if
you really wanted, but that's probably not going to help anybody when it comes
to readability. On we go!

Note: we are making that seemingly useless `tuple()` of `ids` only because it's
needed for part 2.

### Part 2

We are now told that our seat is missing from the input list, and we need to
find its ID. We know that the plane does not have seats at the very front and at
the very back, so those are also missing from our list. Our seat was not at the
very front or very back though, and the seats with ID at distance `+1` and `-1`
from our ID are present in the list.

Interesting. We know we have a list of *consecutive* IDs, starting from some
`min_id`, going up to our already calculated `max_id`. Somewhere in the middle
of those, there is a missing ID, which is the one we are looking for.

We should know the formula to get the sum of a range of consecutive numbers
without actually having to calculate it, right? Well, let's look at Wikipedia to
[refresh our memory][wiki-sum-range]. We know the sum of consecutive integers
from `1` to `N` is `N * (N - 1) // 2`: if our consecutive integers don't start
from `1` but from some `m`, we can just subtract the sum of the integers from
`1` to `m` from that, and we have the sum of all the consective integers from
`m` to `N`. That is: `N * (N - 1) // 2 - m * (m - 1) // 2`.

Which means, we can compute the sum of all our IDs from the minimum to the
maximum like this:

```python
min_id   = min(ids)
expected = max_id * (max_id + 1) // 2 - min_id * (min_id - 1) // 2
```

That would be the *expected* sum, if our ID wasn't missing. That's right. We can
now just calculate the *real* sum and get the missing ID with a subtraction:

```python
my_id = expected - sum(ids)
print('Part 2:', my_id)
```

### Reflections

Calculating the missing ID with a simple mathematical formula is pretty neat,
but you might be wondering: can't the above code be optimized? It seems like we
are wasting more time than needed by iterating over the entire list of IDs
multiple times: one with `tuple()` to build the tuple of IDs, one with `max()`
for part 1, and another two times with `min()` and `sum()` for part 2. Couldn't
we just iterate over it once and get all the three values?

Well, there is no built-in function for that, which means we would need to write
our own. Something like this (assuming our numbers are all positive and lower
than 1024, which is the case for this problem):

```python
def min_max_sum(iterable):
    mmin, mmax, ssum = 0, 1024, 0

    for x in iterable:
        ssum += x

        if x < mmin:
            mmin = x
        elif x > mmax:
            mmax = x

    return mmin, mmax, ssum
```

We could then just solve part 1 and part 2 without iterating over the ids ever
again, which also means that we wouldn't need to build a `tuple()` in the first
place and we could just pass the generator returned by the very first `map()` to
our `min_max_sum()`.

```python
table = str.maketrans('BFRL', '1010')
seats = fin.read().translate(table).splitlines()
ids   = map(lambda s: int(s, 2), seats)

m, M, s = min_max_sum(ids)
```

This looks pretty good on paper. We are saving unneeded iterations, so it should
take less time, right? Well... not really. As it turns out, Python bytecode is
*pretty slow*, while the `min()`, `max()` and `sum()` built-in functions use
internal Python code, which means native, compiled and optimized C code. As a
consequence, any of those functions traverses an iterable faster than any Python
`for` loop by an order of magnitude. This means that the above "optimized"
solution that iterates *only once* over the `ids` is actually *slower* than my
original solution which iterates over the `ids` *four times*!

Of course, this is only true because our list of IDs is pretty small, and it
also does not apply to *all* Python implementations, but it is true for the
"official" and most widely used one, which is [CPython][wiki-cpython]. Running
this on my machine with CPython 3.9, timing with my [timer
utilities](/utils/timer.py) yields the following:

```
Timer A: 241.736µs wall, 240.477µs CPU
Timer B: 328.511µs wall, 328.626µs CPU
```

Where `A` uses `tuple()` + `min()` + `max()` + `sum()` while `B` uses
`min_max_sum()` defined above. The "optimized" solution is ~36% slower. Pretty
sad, huh? The slowness of interpreted languages!


Day 6 - Custom Customs
----------------------

[Problem statement][d06-problem] — [Complete solution][d06-solution] — [Back to top][top]

### Part 1

Remember all those times I said "todays puzzle could really be solved in one/two
lines of Python"? Well guess what, I'ma stop talking and do it for real this
time. It's a simple puzzle, and the solution looks clean enough for my taste.

**Disclaimer:** this is going to be rather lengthy, in order to explain
everything properly.

We have an unknown set of questions identified by lowercase letters (`a` to
`z`). We are given a list of groups of answers. Each group of answers is
separated by an empty line (just like passports in [day 4][d04]); each line of a
group of answers corresponds to a person, and contains multiple lowercase
letters identifying which questions they answered "yes" to.

To better understand the problem, here's an example input:

```
abc
def

ac
ab
acd
```

And here are some facts about the above input:

- There are 2 groups of people: one with 2 people and one with 3 people.
- In the first group, the first person answered "yes" to questions `a`, `b`
  and `c`.
- In the second group, the third person answered "yes" to questions `a`, `c`,
  `d`.
- The number of *unique* questions answered by the first group is 6 (they all
  answered different questions).
- The number of *unique* questions answered by the second group is 4. Every
  person answered to `a`, and person 1 and 3 both answered to `c`.

For the first part of this puzzle, we need to find the sum of the number of
unique questions answered by each group. In the above example, it would be 6 + 4
= 10.

First, let's notice one thing: we do not really care about the fact that each
group is split into different people. We can treat groups just as strings of
letters (ignoring the newlines). Now, how would you count the number of unique
letters in a string? Simple: build a [`set()`][py-set] from its characters and
get the length of the set.

The solution should now be simple. Start by separating the groups in the input,
and removing newline characters from each group. Another straightforward usage
of [`map()`][py-builtin-map] and [`lambda`][py-lambda] combination.

```python
raw_groups = fin.read().split('\n\n')
groups = map(lambda g: g.replace('\n', ''), raw_groups)
```

Now we just need to build a set out of each group, and sum the lengths of all
the sets. You guessed it: `map()` it again, this time computing `len(set(g))`
for every group `g`, and [`sum()`][py-builtin-sum] everything up. We could
either use a single `map()` with a `lambda g: len(set(g))`, or a double `map()`
first for `set`, then for `len`. The latter is fastest, because it's less Python
code.

```python
n_any_yes = sum(map(len, map(set, groups)))
print('Part 1:', n_any_yes)
```

Yes, the above could be compressed even more by avoiding the usage of those
temporary variables:

```python
n_any_yes = sum(map(len, map(set, map(lambda g: g.replace('\n', ''), fin.read().split('\n\n')))))
```

But no thanks, that's where I draw the line between "cool solution" and
"unreadable mess".

### Part 2

Now the fact that each group contains answers given by different people comes
into play. For each group, we need to count the number of questions to which all
people in the group answered. The solution to give for this second part is the
sum of that count for all groups.

We need to re-build our groups, this time separating different lines. We'll
transform each group into a `list` of strings (one string per person), using
[`str.splitlines()`][py-str-splitlines].

```python
groups = map(lambda g: str.splitlines(g), raw_groups)
```

To give an idea of what the above produces, applying it to our example:

```
abc
def

ac
ab
acd
```

Will produce the following:

```python
>>> next(groups)
['abc', 'def']
>>> next(groups)
['ac', 'ab', 'acd']
```

As we can already see, the solution for this example would be 1 (in the second
group there is `a` which was answered by all three).

Given two strings of letters (answers from two people), how would you compute
the number of letters that are in *both* strings? Well, we know how to get all
the unique letters of a string `s`: `set(s)`. If we do this for two strings and
then calculate the [intersection][wiki-set-intersection] of the two, the result
will be the set of letters that appear in both strings. In Python, the
intersection between two sets can be calculated using the `&` operator, or the
equivalent [`.intersection()`][py-set-intersection] method.

Our `groups` now are just lists of strings. We want to turn those strings into
sets to compute their intersection. To do this, we'll need an additional
`map()`, so the above becomes:

```python
groups = map(lambda g: map(set, g.splitlines()), raw)
```

Which produces:

```python
>>> g = next(groups)
>>> g
<map at 0x7f7a0e40fdf0>
>>> tuple(g)
({'a', 'b', 'c'}, {'d', 'e', 'f'})
>>> tuple(next(groups))
({'a', 'c'}, {'a', 'b'}, {'a', 'c', 'd'})
```

Note that we now have a `map` of `map`s. These are only iterable *onece*. We
don't need to, but if we wanted to iterate on those multiple times, we would
need to turn them into `tuple`s or `list`s first.

Now iterate over the groups, compute the intersection of all the sets of answers
in each group, and sum everything up:

```python
n_all_yes = 0

for group in groups:
    # Start with the first set of answers
    all_yes = group[0]

    # Intersect with all other sets
    for answers in group[1:]:
        all_yes &= answers

    n_all_yes += len(all_yes)
```

**Note that** there is a huge difference between `a &= b` and `a = a & b` when
working with sets. These operations would usually be analogous for integers, but
Python sets behave differently. Doing `a &= b` computes the intersection and
modifies the original `a` without creating a new `set`, while `a = a & b`
creates a new `set`, which is the result of the intersection, and then assigns
that to `a`. The actual analogous method for the `&=` operator is
[`.intersection_update()`][py-set-intersection-u].

The above code already gives us the answer, and we could stop there, but today I
want to go a little bit further.

Notice that we are applying the same operation to all the elements of a
sequence, accumulating the result into a single variable? This technique is
called [reduction][wiki-reduction], and it's one of the most useful operations
in functional programming. Granted, Python isn't really a functional language,
but to some extent it can be treated as such.

The body of the above loop can be shortened into a single line taking advantage
of the very cool [`reduce()`][py-functools-reduce] function from the
[`functools`][py-functools] module. This function takes a function, an iterable
and an optional initializer (if not supplied, the first element of the iterable
is used). It starts with `res = initializer`, and then for each element of the
iterable does `res = function(res, element)`, finally returning `res`. This
means that if we supply [`set.intersection`][py-set-intersection] as function,
and our `groups` as iterable, the body of the above loop can be rewritten in one
line.

```python
from functools import reduce

n_all_yes = 0
for group in groups:
    n_all_yes += len(reduce(set.intersection, group))
```

Huh, now we are using a loop just to sum values. Wonder if there is a function
that does that for us. Yep, `sum()`. The `map()` feng shui never ends! The above
can just be simplified into:

```python
n_all_yes = sum(map(lambda g: len(reduce(set.intersection, g)), groups))
```

We can make this a little bit readable using
[`functools.partial()`][py-functools-partial] to fix the first argument of
`reduce` to `set.intersection`, trasforming it into a function that only takes
one argument (an iterable) and returns the intersection of all the items in the
iterable.

```python
from functools import reduce, partial

intersect = partial(reduce, set.intersection)
n_all_yes = sum(map(len, map(intersect, groups)))

print('Part 2:', n_all_yes)
```

### One last stretch

We can re-use the same technique of part 2 for part 1 too. The only difference
is that for part 1 we need to calcualte the [union][wiki-set-union] of the sets
of answers (using [`set.union`][py-set-union]). To iterate over the `groups` two
times, we'll now need to turn them into `tuple`s of `tuple`s. After that, we can
apply the same dance of `sum()` + `map()` + `reduce()` for both parts.

```python
from functools import reduce, partial

raw_groups = fin.read().split('\n\n')

groups = tuple(map(lambda g: tuple(map(set, g.splitlines())), raw_groups))

# Or equivalent, "abusing" partial():
map_to_sets = partial(map, set)
groups = tuple(map(tuple, map(map_to_sets, map(str.splitlines, raw_groups))))
```

Finally:

```python
unionize  = partial(reduce, set.union)
intersect = partial(reduce, set.intersection)
n_any_yes = sum(map(len, map(unionize, groups)))
n_all_yes = sum(map(len, map(intersect, groups)))
```

We now have a quite elegant functional Python solution!


Day 7 - Handy Haversacks
------------------------

[Problem statement][d07-problem] — [Complete solution][d07-solution] — [Back to top][top]

### Part 1

Today's puzzle is the first puzzle of the year to involve graphs! Last year's
PTSD starts to creep in. Thankfully it's only day 7, so nothing wild.

We have a bunch of color-coded bags. Each bag of a certain color can hold a
specific number of bags of other colors. This information is given as input in a
quite verbose manner, like so:

```
dark orange bags contain 3 bright white bags.
bright white bags contain 1 shiny gold bag.
muted yellow bags contain 2 shiny gold bags, 9 faded blue bags.
faded blue bags contain no other bags.
```

We are asked to find how many differently colored bags can contain (either
directly or indirectly) at least one `shiny gold` bag.

Looking at the above example, the answer would be 3, because:

- `dark orange` can contain `bright white`, which can contain `shiny gold`
- `bright white` can directly contain `shiny gold`
- `muted yellow` can directly contain `shiny gold`

Let's get started. First of all, we need an appropriate data structure to keep
track of the relationship "is directly contained by": we can use a dictionary
for this, of the form `{inner_color: [outer_color1, outer_color2, ...]}`.

In order to parse each line, we will first split it in two right at
`"bags contain"`. The first part will just be the color of the outer bag. Then
we'll use a [regular expression][misc-regexp] to extract all colors of the
second part. Since bag colors are always followed by the word `bag` or `bags`
and then by a comma (`,`) or a dot (`.`), we can search for letters and spaces
followed by `bags?[.,]` to match each inner color.

To make our life easier, we'll use a
[`defaultdict`][py-collections-defaultdict], which is an awesome dictionary
that, given a function returning a "default" entry, automatically creates
missing entries if we try to access a missing key. Since we want a dict of
lists, we'll pass the `list` function as parameter so that by default missing
entries will be created as empty lists. This makes us able to do
`d[k].append(x)` even if `k` is not a dictionary key.

```python
fin = open(...)

inner_exp    = re.compile(r'(\d+) ([\w ]+) bags?[.,]')
contained_by = defaultdict(list)

for line in fin:
    outer, inners = line.split(' bags contain ')
    inners = inner_exp.findall(inners)

    for _, inner in inners:
        contained_by[inner].append(outer)
```

The above regular expression does not match lines saying
`X bags contain no other bags`, it returns an empty list of matches for those.
This is good since we don't care about that information and can avoid doing more
filtering.

Note: the above regular expression is a little bit more complex than what we
need, since it also extracts the numbers (which we'll only need in part 2).

Now `contained_by[x]` is the list of bag colors capable of directly containing
bags of color `x`. If we think about it for a second, the `contained_by`
dictionary we just built represents a [directed acyclic graph][wiki-dag]
(assuming the input does not say both "A contains B" and "B contains A", which
wouldn't make much sense). Nodes represent bag colors, and edges signify "is
directly contained by". In graph terms, `contained_by[x]` yields the list of
nodes that are reachable from `x`.

Drawing it out, it looks something like this (using the example input above):

```
     shiny gold   faded blue
      |        \     |
      v         v    v
bright white    muted yellow
      |
      v
dark orange
```

All we have to do now to find how many differently colored bags can contain a
`shiny gold` bag is explore the graph starting from `shiny gold` and counting
how many different colors we can reach. This can be done through eigther a
[breadth-first][algo-bfs] or [depth-first][algo-dfs] search. We'll use the
latter for its simplicity, writing a recursive implementation:

```python
def count_can_contain(G, src, visited=set()):
    for color in G[src]:
        if color not in visited:
            visited.add(color)
            count_can_contain(G, color, visited)

    return len(visited)
```

At the end of the search we return the length of the `visited` set instead of
the set itself, because that's all we really care about. We could have also
created the `visited` set in the function body, but that would have just been
slower since each recursive call would have created a new set, and would have
also needed to return it. Taking `visited` as parameter makes us modify that set
only without creating new ones.

Notice how above we just access `G[src]` without checking `if src in G` first:
this would normally raise a `KeyError` on a normal `dict`, but not on a
`defaultdict`: we just get an empty list back.

We can now just call the above function to get the solution:

```python
can_contain_gold = count_can_contain(contained_by, 'shiny gold')
print('Part 1:', can_contain_gold)
```

### Part 2

Things get a little bit more complicated. We are now asked the "opposite"
question: count how many bags are contained in one `shiny gold` bag.

To make it clear, here's an example:

```
shiny gold bags contain 1 dark red bag, 2 dark green bags.
dark red bags conain 5 bright yellow bags, 2 bright blue bags.
dark green bags contain 3 bright blue bags.
```

How many bags does a `shiny gold` bag contain?

- `dark red` bags contain 7 bags total: 5 `bright yellow`, 2 `bright blue`.
- `dark green` bags contain 3 `bright blue` bags.

Therefore a `shiny gold` bag, which contains 1 `dark red` and 2 `dark green`
bags, will contain `1 + 1*7 + 2 + 2*3 = 16` bags total.

It's easy to see that this one is also a problem that involves exploring a
directed acyclic graph. This time though, we want to traverse it in the opposite
direction, that is, the relationship we care about ("contains") is the opposite
of the one we used in part 1 ("is contained by").

The graph we build earlier is of no use now. We need a new one that has edges in
the opposite direction, and we also need to remember the number of bags
associated with each edge. Let's modify the initial input parsing loop to build
this second graph too:

```python
inner_exp    = re.compile(r'(\d+) ([\w ]+) bags?[.,]')
contained_by = defaultdict(list)
contains     = defaultdict(list) # line added

for line in fin:
    outer, inners = line.split(' bags contain ')
    inners = inner_exp.findall(inners)

    for qty, inner in inners: # line modified
        contained_by[inner].append(outer)
        contains[outer].append((int(qty), inner)) # line added
```

Now we have a dictionary of the form:
`{outer: [(n1, inner1), (n2, inner2), ...]}` where nodes represent bag colors,
and edges signify "contains". Now `contains[x]` is the list of bag colors and
quantities that are contained in a bag of color `x`.

Drawing it for the above example, it looks something like this:

```
           shiny gold
         1 /       \ 2
          v         v
       dark red    dark green
      5 |    2 \      | 3
        v       v     v
bright yellow   bright blue
```

Bear with my questionable ASCII art graphing abilities, hope it's clear enough.

Given a graph like this one, we now essentially have to do the same thing as
before and explore it using depth-first search. The only difference is that (as
can be seen from th example above) we can very well visit a node multiple times,
and we also want to take into account the numbers on each edge which indicate
how many inner bags of such color our outer bag contains.

Opting for a recursive solution again for its consiseness, each time we visit a
node (bag color) we will first add the number of needed bags of that color to
the total, then recursively calculate the subtotal number of bags which that
specific color can hold, and multiply it by the `qty` of that color, adding the
result to the total. It's simpler to show the code really.

```python
def count_contained(G, src):
    tot = 0
    for qty, color in G[src]:
        tot += qty
        tot += qty * count_contained(G, color)

    return tot
```

That's it, we are one function call away from the answer...

However, we can optimize this a bit more: we can "remember" the number of bags
contained by each color so that if we get to the same color multiple times we
don't have to re-calculate everything again. This technique is known as
[*memoization*][wiki-memoization], and is the holy grail of speeding up
redundant recursive algorithms that need to calculate the same values many
times. To do memoization, we can use a simple dictionary as cache:

```python
def count_contained(G, src, cache={}):
    if src in cache:
        return cache[src]

    tot = 0
    for qty, color in G[src]:
        tot += qty * (1 + count_contained(G, color))

    cache[src] = tot
    return tot
```

Although the time this takes is still infinitesimal, this second function is
about 70% faster on my machine. I've also simplified the two additions into one.

As it turns out, Python already has a decorator for memoizing function results
based on the passed arguments: [`functools.cache`][py-functools-cache]. We can
refactor the above code using the global `contains` dictionary like this and let
Python do the caching for us:

```python
@cache
def count_contained(src):
    tot = 0
    for qty, color in contains[src]:
        tot += qty * (1 + count_contained(color))

    return tot
```

About the same speed as the previous manual method. Maaaaaybe around one
microsecond faster, but really who knows. Let's finally calculate the solution:

```python
total_bags = count_contained(contains, 'shiny gold')
print('Part 2:', total_bags)
```

*P.S.:* we could have also abused this decorator just for fun to avoid keeping
track of the visited nodes for part 1. Up to you to figure out how, if you want.

---

*Copyright &copy; 2020 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)


[top]: #advent-of-code-2020-walkthrough
[d01]: #day-1---report-repair
[d02]: #day-2---password-philosophy
[d03]: #day-3---toboggan-trajectory
[d04]: #day-4---passport-processing
[d05]: #day-5---binary-boarding
[d06]: #day-6---custom-customs
[d07]: #day-7---handy-haversacks

[d01-problem]: https://adventofcode.com/2020/day/1
[d02-problem]: https://adventofcode.com/2020/day/2
[d03-problem]: https://adventofcode.com/2020/day/3
[d04-problem]: https://adventofcode.com/2020/day/4
[d05-problem]: https://adventofcode.com/2020/day/5
[d06-problem]: https://adventofcode.com/2020/day/6
[d07-problem]: https://adventofcode.com/2020/day/7
[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py
[d04-solution]: solutions/day04.py
[d05-solution]: solutions/day05.py
[d06-solution]: solutions/day06.py
[d07-solution]: solutions/day07.py

[py-raw-string]:              https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
[py-generator-expr]:          https://www.python.org/dev/peps/pep-0289/
[py-lambda]:                  https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-set]:                     https://docs.python.org/3/library/stdtypes.html#set
[py-set-intersection]:        https://docs.python.org/3/library/stdtypes.html#frozenset.intersection
[py-set-intersection-u]:      https://docs.python.org/3/library/stdtypes.html#frozenset.intersection_update
[py-set-union]:               https://docs.python.org/3/library/stdtypes.html#frozenset.union
[py-set-union-u]:             https://docs.python.org/3/library/stdtypes.html#frozenset.union_update
[py-str-count]:               https://docs.python.org/3/library/stdtypes.html#str.count
[py-str-isdigit]:             https://docs.python.org/3/library/stdtypes.html#str.isdigit
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-replace]:             https://docs.python.org/3/library/stdtypes.html#str.replace
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-strip]:               https://docs.python.org/3/library/stdtypes.html#str.strip
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-cache]:         https://docs.python.org/3/library/functools.html#functools.cache
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-re]:                      https://docs.python.org/3/library/re.html
[py-re-findall]:              https://docs.python.org/3/library/re.html#re.findall

[algo-manhattan]:     https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:      https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-bfs]:           https://en.wikipedia.org/wiki/Breadth-first_search
[algo-dfs]:           https://en.wikipedia.org/wiki/Depth-first_search
[algo-kahn]:          https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
[algo-binsrc]:        https://en.wikipedia.org/wiki/Binary_search_algorithm
[algo-wall-follower]: https://en.wikipedia.org/wiki/Maze_solving_algorithm#Wall_follower

[wiki-cpython]:          https://en.wikipedia.org/wiki/CPython
[wiki-dag]:              https://en.wikipedia.org/wiki/Directed_acyclic_graph
[wiki-linear-time]:      https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-memoization]:      https://en.wikipedia.org/wiki/Memoization
[wiki-polynomial-time]:  https://en.wikipedia.org/wiki/Time_complexity#Polynomial_time
[wiki-reduction]:        https://en.wikipedia.org/wiki/Reduction_Operator
[wiki-set-intersection]: https://en.wikipedia.org/wiki/Intersection_(set_theory)
[wiki-set-union]:        https://en.wikipedia.org/wiki/Union_(set_theory)
[wiki-sum-range]:        https://en.wikipedia.org/wiki/1_%2B_2_%2B_3_%2B_4_%2B_%E2%8B%AF

[misc-man1-tr]: https://man7.org/linux/man-pages/man1/tr.1.html
[misc-regexp]:  https://www.regular-expressions.info/
