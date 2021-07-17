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
- [Day 8 - Handheld Halting][d08]
- [Day 9 - Encoding Error][d09]
- [Day 10 - Adapter Array][d10]
- [Day 11 - Seating System][d11]
- [Day 12 - Rain Risk][d12]
- [Day 13 - Shuttle Search][d13]
- [Day 14 - Docking Data][d14]
- [Day 15 - Rambunctious Recitation][d15]
- [Day 16 - Ticket Translation][d16]
- [Day 17 - Conway Cubes][d17]
- [Day 18 - Operation Order][d18]
- [Day 19 - Monster Messages][d19]
- [Day 20 - Jurassic Jigsaw][d20]
- [Day 21 - Allergen Assessment][d21]
- [Day 22 - Crab Combat][d22]
- [Day 23 - Crab Cups][d23]
- [Day 24 - Lobby Layout][d24]
- [Day 25 - Combo Breaker][d25]

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

    if x in compls:
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
use the exact same approach used for part 1, wrapping everything in one more
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
policies = re.findall(r'(\d+)-(\d+) (\w): (\w+)', data)
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
in Python can also be used on boolean values, and acts like a logical XOR,
returning `True` if only one of the two operands is `True`.

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
but it obviously expects the characters to be either `0` or `1`. We can just
replace all instances of `F` and `L` with `0`, and all instances of `B` and `R`
with `1`. Then, separate the first 7 and the last 3, and use
[`int(x, 2)`][py-builtin-int] to convert them to integers.

Normally, to replace a character in a string you would use
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
`1` to `m` from that, and we have the sum of all the consecutive integers from
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
code and more optimized built-in magic.

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

Note that we now have a `map` of `map`s. These are only iterable *once*. We
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

We are applying the same operation (that is, intersection) to all the elements
of each group. The final result is the intersection of multiple sets. As it
turns out, [`set.intersection()`][py-set-intersection] can take an arbitrary
amount of sets as parameters, and calculate the intersection of all of them. The
body of the above loop can be shortened into a single line taking advantage of
this, passing all sets in a `group` to `set.intersection()` through
[unpacking][py-unpacking]:

```python
from functools import reduce

n_all_yes = 0
for g in groups:
    n_all_yes += len(set.intersection(*g))
```

Huh, now we are using a loop just to sum values. Wonder if there is a function
that does that for us. Yep, [`sum()`][py-builtin-sum]. The above can just be
simplified into a single line using `sum()` and a
[generator expression][py-generator-expr], giving us the following final form:

```python
n_all_yes = sum(len(set.intersection(*g)) for g in groups)
print('Part 2:', n_all_yes)
```

### One last stretch

We can apply the same technique of part 2 to part 1 too. The only difference is
that for part 1 we need to calcualte the [union][wiki-set-union] of the sets of
answers (using [`set.union()`][py-set-union]). To iterate over the `groups` two
times, we'll now need to turn them into `tuple`s of `tuple`s. After that, we can
apply the same dance of `sum()` + generator for both parts.

```python
raw_groups = fin.read().split('\n\n')
groups = tuple(map(lambda g: tuple(map(set, g.splitlines())), raw_groups))
```

Finally:

```python
n_any_yes = sum(len(set.union(*g)) for g in groups)
n_all_yes = sum(len(set.intersection(*g)) for g in groups)
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
dark red bags contain 5 bright yellow bags, 2 bright blue bags.
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

Opting for a recursive solution again for its conciseness, each time we visit a
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

Note: `@cache` is new in Python 3.9, but it's only a shorthand for
`@lru_cache()`. You can use the latter on older Python versions.

About the same speed as the previous manual method. Maaaaaybe around one
microsecond faster, but really who knows. Let's finally calculate the solution:

```python
total_bags = count_contained(contains, 'shiny gold')
print('Part 2:', total_bags)
```

*P.S.:* we could have also abused this decorator just for fun to avoid keeping
track of the visited nodes for part 1. Up to you to figure out how, if you want.


Day 8 - Handheld Halting
------------------------

[Problem statement][d08-problem] — [Complete solution][d08-solution] — [Back to top][top]

### Part 1

First puzzle of the year to involve writing a custom [virtual machine][wiki-vm]!
I was waiting for this to happen. Hopefully this year we'll have a saner
specification than [last year's][2019-d05] self-modifying "Intcode".

We have only 3 opcodes:

- `nop N`: does nothing, advances to the next instruciton, the argument is
  ignored.
- `acc N`: increments the value of a global "accumulator" by `N`, which is a
  signed integer. The accumulator starts at `0`.
- `jmp N`: jumps `N` instructions forward (or backwards if `N` is negative) the
  current instruction. I.E. `jmp +1` goes to the next instruction.

The source code we are given as input, if executed, will result in an endless
loop. We need to detect when that happens, stopping the first time we try to
execute an already seen instruction (before *executing* it). The solution is
the accumulator value after stopping.

Since the VM implementation will likely change and I will keep updating the same
file, I'll just link to the exact version of the code at the time of writing,
containing the current VM implementation, which we'll be writing ritht now. You
can find the link above.
*A posteriori note: this turned out to be the only VM puzzle this year.*

Let's start! We need our VM to have at least three fundamental properties:

1. Ability to easily pause and resume execution.
2. Ability to reset in order to restart execution without having to
   re-initialize everything manually.
3. Ability to inspect and alter the execution state from outside (program
   counter, accumulator, the program itself, etc...).

Let's declare a `VM` class for this. The [`__init__()`][py-object-init] method
will take the source code as argument and parse it extracting opcodes and
arguments, then it will initialize the initial state doing a reset right away.

```python
class VM:
    def __init__(self, source):
        self.parse_program(source)
        self.reset()
```

We now want to have a program counter, an accumulator, and a boolean value
indicating whether the VM is running or not, useful for external inspection.
We'll just create and initialize these values as attributes of our class in the
`reset()` method:

```python
    def reset(self):
        self.pc  = 0
        self.acc = 0
        self.running = True
```

Onto the parsing: for now, we will just assume an instruction to be of the form
`op A1 A2 A3 ...`, with space separated integer arguments. In the
`parse_program()` method, we'll parse the `source` into a list of tuples in the
form `(op, (a1, a2, ...))`, simply splitting each line and turning arguments
into `int`.

```python
    def parse_program(self, source):
        self.prog = []

        for line in source.splitlines():
            # Assume ops and args will be separated by spaces only
            op, *args = line.split()

            # Treat every argument as an immediate integer for now
            args = tuple(map(int, args))
            self.prog.append((op, args))

        # For faster and simpler bound checking later
        self.prog_len = len(self.prog)
```

Perfect. Now the core of the VM, the `run()` method. We'll use this to actually
run the parsed code that was stored in `self.code` during initialization. Since
we want to be able to pause and resume execution, we'll take a `steps` argument,
and then simply run everything in a `while steps` loop decrementing it each
time. To allow running without stopping, we'll use a simple trick: the
[`inf`][py-math-inf] special value from the [`math`][py-math] module, which is
the floating point representation of positive infinity and will never change no
matter how many times we try to decrement it.

The implementation for now is really simple, since we only have 3 instructions,
one of which (`nop`) we'll outright ignore.

```python
    def run(self, steps=inf):
        while steps:
            op, args = self.prog[self.pc]

            if op == 'acc':
                self.acc += args[0]
            elif op == 'jmp':
                self.pc += args[0] - 1

            self.pc += 1

            # Assume that running the last instruction (or jumping right after it)
            # means that the program terminated correctly
            if self.pc == self.prog_len:
                self.running = False
                break

            steps -= 1
```

Now let's actually solve the problem! We can finally put our `VM` to good use.
To detect when an instruction is executed again, we can save the values of the
program counter (`vm.pc`) in a [`set`][py-set], since the program counter
uniquely identifies an instruction in the whole program, and stop if we ever get
a value that was already seen.

```python
fin    = open(...)
source = fin.read()
vm     = VM(source)
seen   = set()

while vm.pc not in seen:
    seen.add(vm.pc)
    vm.run(1)

print('Part 1:', vm.acc)
```

Clean and simple as that!

### Part 2

Now we are told that we can "fix" our broken program that runs in an endless
loop simply by swapping a `nop` with a `jmp` (or vice-versa) somewhere in the
code. We need to find which instruction to change which will let the program
correctly run until its end. The solution is still the accumulator value after
the program terminates.

Well, there isn't much we can do except trying to change every single
instruction and restart the VM to see what happens. Okay, not true: there *is* a
better solution than bruteforcing, see [this Reddit thread][d08-better-solution]
if you are curious. However, the complexity of the code needed to implement such
a solution would most likely just outweigh its benefits. A dead-simple
bruteforce approach on such a small program is nearly instantaneous in any case
(on my machine one execution of the program takes less than 300 microseconds).

Anyway, where were we? Ah yes, testing all instructions: each time we try
executing the code we'll either end up in an infinite loop again (which can be
detected as we just did), or correctly finish execution (which can be detected
by checking if `vm.running == False` after `vm.run(1)`).

We'll iterate over and check each instruction in `vm.prog`, ignoring any `acc`,
but trying to swap any `nop` with `jmp` (and vice versa) before running the
program. If the run is not successful, we'll restore the original instruction
and go on with the next one.

```python
for i in range(1, vm.prog_len):
    original = vm.prog[i]

    if original[0] == 'acc':
        continue
    elif original[0] == 'jmp':
        vm.prog[i] = ('nop',) + original[1:]
    elif original[0] == 'nop':
        vm.prog[i] = ('jmp',) + original[1:]

    vm.reset()

    seen = set()
    while vm.running and vm.pc not in seen:
        seen.add(vm.pc)
        vm.run(1)

    if not vm.running:
        break

    vm.prog[i] = original

print('Part 2:', vm.acc)
```

Sweet! Hopefully the code we wrote is robust and simple enough to allow for easy
modifications in the next days. Assuming things will not get very weird... I
hope not.
*A posteriori note: this turned out to be the only VM puzzle this year.*


Day 9 - Encoding Error
----------------------

[Problem statement][d09-problem] — [Complete solution][d09-solution] — [Back to top][top]

### Part 1

We are given a list of numbers, and we are told that all the numbers in the list
should adhere to a specific rule: each number after the 25th is the sum of one
pair of numbers amongst the 25 that precede it. We need to find the first number
in the list that does not satisfy this rule.

We already know how to find a pair of numbers that sum up to some target number,
we did this in part 1 of [day 1][d01]. We can just loop over the numbers,
starting from the 25th, and keep going until we find the first one for which we
cannot find a pair summing up to amongst its 25 predecessors. Let's just write
this check like we did for day 1, but this time as a function:

```python
def two_sum(nums, target):
    compls = set()

    for x in nums:
        if x in compls:
            return True

        compls.add(target - x)

    return False
```

Now let's get the numbers from the input file into a `tuple` of integers using
[`map()`][py-builtin-map] as usual:

```python
nums = tuple(map(int, fin.readlines()))
```

And then just loop over the input numbers starting from the 26th and checking
each chunk of 25 numbers. The [`enumerate()`][py-builtin-enumerate] function
comes in handy.

```python
for i, target in enumerate(nums[25:]):
    if not two_sum(nums[i:i + 25], target):
        break

print('Part 1:', target)
```

Although it seems [quadratic in time][wiki-polynomial-time] (O(n<sup>2</sup>)),
this solution actually runs in [linear time][wiki-linear-time] (O(n)), as we
always need to check a fixed and relatively small amount of previous numbers
which does not depend on the length of the input sequence. We make at most
`25 * len(nums)` iterations (well, excluding the fact that `lst[x:y]` creates a
copy and therefore also iterates `y-x` times... dammit Python).

### Part 2

The goal changes: we need to find a contiguous subsequence of numbers (of any
length) that sums up to the number we just found in part 1 (`target`). Found the
sequence, the answer we must give is the sum of its minimum and its maximum
element.

We can do this the dumb way: loop over each possible subsequence and compute the
sum every time. This approach is cubic in time (O(n<sup>3</sup>), *iff* I am not
mistaken, well it's *at least* quadratic for sure). We are smart though, and
after thinking about it for a couple minutes we figure out that this can be done
in linear time with a single scan of the input sequence.

We can take advantage of the *cumulative sum*, also known as
[running total][wiki-running-total]. Given a sequence `S` of numbers, the sum of
the numbers in a given subsequence `s = S[a:b]` is equal to
`sum(S[0:b]) - sum(S[0:a])`, that is: the difference between the cumulative sum
of the first `b` elements and the cumulative sum of the first `a` elements. If
we pre-calculate the all the cumulative sums from the first number up to all
numbers, we can then calculate the sum of any subsequence (given its start and
end) with a single subtraction: `cusum[end] - cusum[start]`.

Our numbers are all positive, so the cumulative sum can only increase each time.
We can begin with an initial "guess" for the correct start and end of the
subsequence: `S[a:b] = S[0:1]`. Then, adjust the extremes iteratively until we
converge to the solution:

1. Start with `a, b = 0, 1`.
2. Compute `partsum = sum(S[a:b]) == cusum[b] - cusum[a]`.
3. Compare `partsum` and `target`:
   - If `partsum < target` then we need to sum more elements: `b += 1`.
   - If `partsum > target` then we overestimated `target`, drop the element at
     the start of the subsequence: `a += 1`.
   - If `partsum == target` then we found the correct subsequence.

Note: this only works if a subsequence with partial sum equal to the target
exists in the input list (which is our case). If it does not, we'd just keep
advancing `b` and go beyond its end running into an `IndexError`.

In terms of code:

```python
cusums = [0]
for n in nums:
    cusums.append(cusums[-1] + n)

a, b = 0, 1

while 1:
    partsum = cusums[b] - cusums[a]

    if partsum < target:
        b += 1
    elif partsum > target:
        a += 1
    else:
        break
```

Note: we set `cusums[0] = 0` since we also want to account for the first number
of the sequence (if we set `cusums[0] = nums[0]` instead, then
`cusums[1] - cusums[0]` would just be `nums[1]` and we'd exclude `nums[0]` from
all our calculations).

We do not actually need to precalculate *all* the cumulative sums, we are never
going to use all of them unless our subsequence ends up being the entire initial
sequence of numbers. We can re-write the above loop to only calculate the needed
cumulative sums lazily, when advancing `b`. This time we need to start at
`a, b = 0, 0` though.

```python
cusums = [0]
a, b = 0, 0

while 1:
    partsum = cusums[b] - cusums[a]

    if partsum < target:
        cusums.append(cusums[-1] + nums[b])
        b += 1
    elif partsum > target:
        a += 1
    else:
        break

subsequence = nums[a:b + 1]
answer = min(subsequence) + max(subsequence)

print('Part 2:', answer)
```

As a last note: we could even implement our "sliding window" using a
[`deque`][py-collections-deque], popping elements from the left as we increment
`a` to minimize the used space. This "optimization" is kind of insignificant
though, and the space used would still be linear in terms of `len(nums)`.


Day 10 - Adapter Array
----------------------

[Problem statement][d10-problem] — [Complete solution][d10-solution] — [Back to top][top]

### Part 1

First part of today's puzzle feels more like a reading comprehension test than
an actual programming puzzle.

Long story short: we are given a list of numbers and we are told (with a
reeeeally long explanation) that these numbers respect a certain rule: when
sorted, the difference between any pair of consecutive numbers is always between
at least 1 and at most 3. We are also told that we need to start our sequence
with a `0` (which is not in our input) and end it with the maximum value we have
plus 3.

After doing this, we want to count how many pairs of any two numbers have a
difference of (A) exactly 1 and (B) exactly 3. The answer we must give is the
product of these two counts.

Looks pretty simple: in order to do this we can sort the input sequence and then
scan it starting from the second number. Let's do the sorting right away using
the built-in [`sorted()`][py-builtin-sorted] function, and also add the two
initial and final numbers:

```python
nums = sorted(map(int, fin))
nums = [0] + nums + [max(nums) + 3]
```

Then, we can cycle through the numbers and check each of them against its
successor to see if their difference is `1` or `3`. To iterate over pairs of
consecutive numbers we can take advantage of the [`zip()`][py-builtin-zip]
function passing `nums, nums[1:]` as arguments. The checks are straightforward.

```python
dist1 = dist3 = 0

for cur, nxt in zip(nums, nums[1:]):
    delta = nxt - cur

    if delta == 1:
        dist1 += 1
    elif delta == 3:
        dist3 += 1
```

Now just multiply the two counts together and get the answer:

```python
ans = dist1 * dist3
print('Part 1:', ans)
```

### Part 2

The problem turns into a real puzzle: we need to count
*how many different subsets* of our numbers satisfy the rule defined in part 1.

As an example, if our numbers were `1 2 3 6`, we could build 4 different
sequences that respect the above rule using a subset of the numbers (always
adding `0` at the start and `9` at the end):

```
(0) 1 2 3 6 (9)
(0) 1 3 6 (9)
(0) 2 3 6 (9)
(0) 3 6 (9)
```

Something like `(0) 1 6 (9)` or `(0) 6 (9)` wouldn't be valid since the rule
does not hold for all numbers in the sequence.

Our list is kind of long, and we are told that the solution is in the order of
trillions, so we can't really use bruteforce testing all possible subsets of
numbers. This problem can be solved using
[dynamic programming][wiki-dynamic-programming].

Remember that our numbers are still sorted. For each number, we have the
possibility to choose betwee 1 and 3 successors. For example if we have
`(0) 1 2 3 ...`, after choosing `0` (forced choice), we could take any of
`1 2 3`, and those would constitute three different solutions. On the other hand
if we have `(0) 2 3` we only have two choices, and in the extreme case of
`(0) 3` we are forced to take `3` (one choice only).

We don't really know how to count the number of possible solutions if the list
is too large, but we can now think of this recursively:

- If we only have the last number left to choose, we can only take that number,
  so `1` possible solution.
- For any other number before the last, the number of possible solutions is the
  sum of the possible solutions choosing any of the valid successors we have.

Turning the above into a recursive function:

```python
# Returns the number of possible solutions having chosen nums[i]
def possible_solutions(nums, i):
    # If this is the last number, we only have one possible solution
    if i == len(nums) - 1:
        return 1

    # Otherwise, sum the number of possible solutions for any valid next number
    tot = 0
    for j in range(i + 1, min(i + 4, len(nums))): # min() to avoid going past the end of the list
        if nums[j] - nums[i] <= 3:                # difference <= 3 to enforce the rule
            tot += possible_solutions(nums, j)

    return tot
```

Pretty cool. We have a little bit of a problem though: for each number we have
we are calling this function between 1 and three times recursively. This means
that (in the worst case of 3 calls for each call) we'll end up making
3<sup>N</sup> calls (where N is the number of numbers we have). Needless to say,
such a solution, which runs in [exponential time][wiki-exponential-time] and
also uses an exponential amount of space, will never work. For my input I have
`len(nums) == 97`, so 3<sup>97</sup> = ~10<sup>46</sup> iterations. Nope!

The thing to notice to make this work is that we do not actually *need* to make
all those calls: that would be akin to bruteforcing the solution. Most of the
times, our recursive function will end up being called with the same `i`,
therefore calculating the same value multiple times. If we
[memoize][wiki-memoization] the results (just like we did to optimize
[day 7][d07] part 2) we can save an *enormous* amount of work.

In order to do this using the [`functools.lru_cache`][py-functools-lru-cache]
decorator, since we want to only memoize based on the index `i`, we can remove
the first argument and use the global `nums`.

```python
from functools import lru_cache

@lru_cache()
def possible_solutions(i):
    if i == len(nums) - 1:
        return 1

    tot = 0
    for j in range(i + 1, min(i + 4, len(nums))):
        if nums[j] - nums[i] <= 3:
            tot += possible_solutions(j)

    return tot
```

Now just call the above function with an argument of `0` to know the total
amount of possible solutions:

```python
total = possible_solutions(0)
print('Part 2:', total)
```

Cool puzzle!

### Reflections

This dance of having to move out arguments from functions just to make them
cacheable by `lru_cache()` is kind of annoying, isn't it? Also, as we
[learned last year][2019-d16-reflections], using global variables instead of
local variables is always slower. If we can, we should try avoiding it.

Indeed, we could solve this annoying problem in multiple ways:

1. If we only need to do a single external call, we can write a custom wrapper
   that remembers the first argument for us:

    ```python
    def func(A, x):
        # Decorate using lru_cache() without the first parameter
        @lru_cache()
        def real_func(x):
            nonlocal A
            # ... do work
            # ... recursively call real_func(y)
            return something

        # Do the actual initial call passing only the second parameter
        return real_func(x)

    # Example usage
    res = func(nums, 0)
    ```

    This is what I actually did in [my solution][d10-solution] for today's
    problem, and probably what I'll keep doing when possible.

    However, note that as mentioned above this is not a general solution at all,
    since calling `func()` multiple times from the outside just creates new
    copies of `real_func()`, which *don't* share the same cache.

2. If we need to do multiple external calls, we can do *almost the same* thing
   as above, returning the entire function instead, and then use *that*
   function.

    ```python
    def apply_caching(A):
        # Decorate using lru_cache() without the A parameter
        @lru_cache()
        def real_func(x):
            nonlocal A
            # ...
            return something

        # Return real_func, which will always use the same A and only take one
        # parameter
        return real_func

    # Example usage
    func = apply_caching(nums)
    res1 = func(0)
    res2 = func(1)
    ```

    This technique is known as [*closure*][wiki-closure]. Here, the internal
    `real_func()` will use the value of `A` that was originally passed to
    `apply_caching()`. This makes it possible to call the function externally
    multiple times always using the same cache and the same `A`.

3. For a general, reusable solution: create a custom more generic
   `selective_cache()` decorator which takes the names of specific arguments to
   use as keys for memoization. This solution is a lot cooler, but it obviously
   requires some fairly higher level of engineering.

   Nonetheless, I've [implemented this decorator][utils-selective-cache] in my
   utilities just for fun. I only plan on using it for my initial solves thogh,
   not in cleaned up solutions. Just know that it can be done and you have the
   code for it if you are curious.

Approach #3 could probably be made to work using `lru_cache()`, but I did not
figure out a good way of doing it, so I ended up implementing "manual" caching
using an internal dictionary.


Day 11 - Seating System
-----------------------

[Problem statement][d11-problem] — [Complete solution][d11-solution] — [Back to top][top]

### Part 1

Any cellular automaton fans around here? Before starting, let me just mark
another square in my [Advent of Code 2020 bingo card][misc-aoc-bingo]... done.
Let's go!

We are given a quite large character grid as input. The grid represents seats in
a public waiting area. Each cell in the grid can be in 3 different states
represented by different characters: occupied seat (`#`), empty seat (`L`) and
floor (`.`).

Cells change state according to a very simple set of rules, turning the whole
thing into a [cellular automaton][wiki-cellular-automaton]. Each iteration,
the new state of a cell depends on its current state and the current state of
its 8 neighbor cells. The rules are as follows:

1. Floor (`.`) never changes state.
2. If a seat is empty (`L`) and no neighbor seat is occupied (`#`), it becomes
   occupied.
3. If a seat is occupied (`#`) and at least 4 neighbor seats are also occupied,
   it becomes empty (`L`).

We want to simulate the evolution of the grid until all the cells "stabilize"
and stop changing states. That is, until the content of the grid stops changing.
Once stabilized, we must count the total number of occupied seats.

Before starting, let's define the seat states as some global constants so that
we don't get confused with different characters:

```python
OCCUPIED, EMPTY, FLOOR = '#L.'
```

Now let's get the grid from our input file, and turn it into a list of lists of
characters in order to be able to edit each cell individually. We need to remove
newline characters (`\n`) from each line, then turn it into a `list`. Our black
belt in Python iterable [mapping][py-builtin-map] makes us able to do this in
one line. We also calculate a couple more useful global constants to make
bound-checking easier for the rest of the program:

```python
original = list(map(list, map(str.rstrip, fin.readlines())))
MAXROW, MAXCOL = len(original) - 1, len(original[0]) - 1
```

If you're wondering why the name `original`, that's because we're going to need
the initial grid again for part 2. We'll make a copy of the original using
[`deepcopy()`][py-copy-deepcopy] from the [`copy`][py-copy] module in order to
preserve it for later.

```python
from copy import deepcopy
grid = deepcopy(original)
```

In order to evolve a cell we need to follow the rules, and in order to follow
the rules we need to be able to count the number of occupied neighbor seats.
We'll define a function that does just that.

```python
def occupied_neighbors(grid, r, c):
    deltas = ((-1, 0), ( 1,  0), (0, 1), ( 0, -1), # North, South, East, West
              (-1, 1), (-1, -1), (1, 1), ( 1, -1)) # NE, NW, SE, SW

    total = 0
    for dr, dc in deltas:
        rr, cc = r + dr, c + dc
        if 0 <= rr <= MAXROW and 0 <= cc <= MAXCOL:
            total += grid[rr][cc] == OCCUPIED # += True/False behaves as += 1/0

    return total
```

It's time to simulate! Every generation we'll create a new copy of the current
`grid`, then check the cells of the copy in order to not mix cells at different
generations together. Applying the rules is pretty straight forward. We'll keep
doing so until the grid stops changing: that is, after evolving the grid is
still equal the copy that was made before evolving.

We'll wrap everything in a function since we'll make good use of this code for
part 2 too with only a couple of modifications. When two consecutive generations
are equal (we can just check the two grids with `==`), we'll count the total
number of occupied seats ([`list.count()`][py-list-count] +
[`sum()`][py-builtin-sum]) and return it. As usual, we'll also make good use of
[`enumerate()`][py-builtin-enumerate] to make our life easier.

```python
def evolve(grid):
    while 1:
        previous = deepcopy(grid)

        for r, row in enumerate(previous):
            for c, cell in enumerate(row):
                if cell == FLOOR:
                    continue

                occ = occupied_neighbors(previous, r, c)

                # Evolve a single cell based on rules
                if cell == EMPTY and occ == 0:
                    grid[r][c] = OCCUPIED
                elif cell == OCCUPIED and occ >= 4:
                    grid[r][c] = EMPTY

        # If nothing changes, we reached a "stable" point and we're done
        if grid == previous:
            return sum(row.count(OCCUPIED) for row in grid)

        previous = grid
```

All that's left to do is call the function we just wrote:

```python
total_occupied = evolve(grid)
print('Part 1:', total_occupied)
```

### Part 2

The state of a seat now changes according to state of the first seats that can
be seen in each of the 8 directions (north, south, east, west, NE, NW, SE, SW).

The rules however stay almost the same: now an occupied seat (`#`) becomes empty
(`L`) if at least *5* in-sight seats are also occupied, and an empty seat still
stays empty unless there's no occupied seat in sight in any of the directions.

To make it clearer, in the following example:

```
  0123456789
0 .L.L.#.#.L
1 ..........
2 .......#.#
```

The empty seat at row column `1` only sees *1* other seat in total, which
is the empty seat at row `0` column `3`; it does not see any other seat beyond
that on the same row. The empty seat at column `9` sees *3* seats in total: the
occupied seats at `(0, 7)`, `(2, 7)` and `(2, 9)`.

Our task is still the same as before: count the total number of occupied seats
after the situation becomes stable.

There isn't really much to change in our evolution loop. All we need to do is
define a new function to count occupied "neighbors". We still look in the same 8
directions as before, but now we don't want to stop at the first cell in each
direction: we want to continue advancing in each direction until we find a seat.
Then, if that seat was occupied, count it.

In order to do this, we can start from the code of `occupied_neighbors()` above,
and add a loop for each direction, where we continue to increment the row and
column (`rr`, `cc`) of the same deltas (`dr`, `dc`) each step, stopping as soon
as we go out of bounds or we encounter a seat.

```python
def occupied_in_sight(grid, r, c):
    deltas = ((-1, 0), ( 1,  0), (0, 1), ( 0, -1), # North, South, East, West
              (-1, 1), (-1, -1), (1, 1), ( 1, -1)) # NE, NW, SE, SW

    total = 0
    for dr, dc in deltas:
        rr, cc = r + dr, c + dc

        while 0 <= rr <= MAXROW and 0 <= cc <= MAXCOL:
            if grid[rr][cc] != FLOOR:
                if grid[rr][cc] == OCCUPIED:
                    total += 1
                break

            rr += dr
            cc += dc

    return total
```

Our `evolve()` function can be made slightly more generic by passing a function
to use for counting occupied seats, and a threshold above which a seat will
change from occupied to empty. Everything else stays the same, including the
final calculation (number of occupied seats).

```python
def evolve(grid, occ_counter, occ_threshold): # new signature
    # ... unchanced ...
                occ = occ_counter(previous, r, c) # use function passed as parameter to count occupied seats

                # Evolve a single cell based on rules
                if cell == EMPTY and occ == 0:
                    grid[r][c] = OCCUPIED
                elif cell == OCCUPIED and occ >= occ_threshold: # use threshold parameter
                    grid[r][c] = EMPTY
    # ... unchanced ...
```

Part 1 solution can now be calculated passing the right parameters:

```python
total_occupied = evolve(grid, occupied_neighbors, 4)
print('Part 1:', total_occupied)
```

And so can part 2, after copying the original grid again:

```python
grid = deepcopy(original)
total_occupied = evolve(grid, occupied_in_sight, 5)
print('Part 2:', total_occupied)
```

That's some pretty slick code, [Conway][wiki-john-horton-conway] would be proud
:')

### Reflections

Today marks the first day of Advent of Code 2020 in which [PyPy][misc-pypy]
completely obliterates [CPython][wiki-cpython] in performance, being faster by
an order of magnitude (woah). I knew this would happen sooner or later.

When it comes to iterating over and modifying lists millions of times there
isn't much to do: CPython sucks hard and is greatly outperformed by PyPy. This
hasn't been the case for previous problems because (1) we did not make as much
list manipulation as we did today, and (2) the programs we wrote solved each
puzzle so fast that PyPy's [JIT compiler][wiki-jit] didn't even have the time to
*rev up* to be taken advantage of. Today's puzzle however the chosen Python
implementation makes a big difference:

```none
$ python day11.py
Timer part 1: 2.011s wall, 2.010s CPU
Timer part 2: 3.319s wall, 3.318s CPU

$ pypy day11.py
Timer part 1: 178.545ms wall, 178.426ms CPU
Timer part 2: 292.076ms wall, 291.934ms CPU
```

Tested on: `CPython 3.9.0+`, `PyPy 7.3.3 Python 3.7.9`.


Day 12 - Rain Risk
-------------------

[Problem statement][d12-problem] — [Complete solution][d12-solution] — [Back to top][top]

### Part 1

Moving in 2D space is easy right? Well, part 1 of today's puzzle is all about
that. We are driving a ship, initially facing east, and we are given a list of
commands in the form `<command><n>` where `<n>` is a positive integer.

Here are the different possible commands:

- `F`: move forward `n` steps in the currently facing direction.
- `L` / `R`: turn `n` degrees left/right without moving; `n` can only be one of
  `90`, `180`, `270`.
- `N` / `S` / `E` / `W`: directly move `n` steps north/south/east/west,
  independent of the currently facing direction.

After applying all commands, we need to calculate the
[Manhattan distance][wiki-manhattan-dist] between our final position and the
starting point.

Let's start with defining a handful of helpful constants:

```python
LEFT, RIGHT, FORWARD = 'LRF'
NORTH, SOUTH, EAST, WEST = 'NSEW'
```

Now let's parse the list of commands from the input file. We'll turn each line
into a tuple of tuples `(command, n)` using [`map()`][py-builtin-map] over a
simple [`lambda`][py-lambda]. We graduated top of the class in the Map-Lambda
Academy so this is too easy for us:

```python
commands = tuple(map(lambda l: (l[0], int(l[1:])), fin))
```

The coordinate system I'll be using for the rest of today's walkthrough is the
standard [cartesian coordinate system][wiki-cartesian-coords], with positive `x`
meaning "east" and positive `y` meaning "north". We'll define our position as a
point `(x, y)` in the cartesian plane. Then, we'll also define a
*delta [vector][wiki-vector]* `(dx, dy)` to indicate the change in position that
we apply for each step forward.

Starting at `0, 0`, we are initially facing east, therefore:

```python
x, y = 0, 0
dx, dy = 1, 0 # delta to apply when moving 1 step forward
```

A single step forward will then just be a `x += dx; y += dy`. For an arbitrary
amount `n` of steps, it will be:

```python
x += dx * n
y += dy * n
```

When turning, we'll update the delta vector to point in the new direction. In
order to do this, we'll need to update the coordinates `(dx, dy)` based on their
current value, the direction we are turning in and the amount of degrees of the
turn. We basically want to rotate the head of the vector around the origin.

A simple [rotation around the origin][wiki-2d-rotation] in 2D space can be
expressed as two reflections, effectively only swapping and/or changing sign of
the two components `(dx, dy)`:

- Rotating left or right 180 degrees around the origin means one reflection
  along the X axis and one along the Y axis: in other words, just invert the
  sign of both coordinates.
- Rotating right 90 degrees means inverting *y* and then swapping the two
  coordinates.
- Rotating right 270 degrees means inverting *x* and then swapping the two
  coordinates.
- Rotating left 270 degrees or right 90 degrees is the exact same operation;
  same goes for left 90 and right 270.

Instead of writing an inconsiderate amount of `if`/`elif` statements (which is
probably the first thing that comes to mind), we can approach the problem in a
[functional][wiki-functional-prog] (and perhaps more intuitive) way, with the
help of a couple of dictionaries and some `lambda` expressions.

We need to define a map of functions for handling rotations of our delta vector.
With the help of pen and paper it's simple to figure out the different functions
we need:

```python
# Functions to apply to rotate a point around the origin.
ROTMAP = {
    ( LEFT,  90): lambda x, y: (-y,  x), # same as RIGHT 270
    ( LEFT, 180): lambda x, y: (-x, -y), # same as RIGHT 180
    ( LEFT, 270): lambda x, y: ( y, -x), # same as RIGHT 90
    (RIGHT,  90): lambda x, y: ( y, -x), # same as LEFT 270
    (RIGHT, 180): lambda x, y: (-x, -y), # same as LEFT 180
    (RIGHT, 270): lambda x, y: (-y,  x), # same as LEFT 90
}
```

A rotation command can now be handled as a change of delta:

```python
# Here cmd = 'L' or 'R', and n = amount of degrees.
dx, dy = ROTMAP[cmd, n](dx, dy)
```

The final thing we need to consider are the commands that move us directly in a
direction regardless of which way we are facing. We'll create another dictionary
of `lambda` expresisons just for that. These will take our current coordinates
and the number of steps to move as parameters, and return the new coordinates.

```python
# Function to apply to move forward in a specific direction.
MOVEMAP = {
    NORTH: lambda x, y, n: (    x, y + n),
    SOUTH: lambda x, y, n: (    x, y - n),
    EAST : lambda x, y, n: (x + n,     y),
    WEST : lambda x, y, n: (x - n,     y)
}
```

A direct movement command (`NSEW`) can now be written as:

```python
x, y = MOVEMAP[cmd](x, y, n)
```

Putting all of this together and applying each command in a loop:

```python
x, y = 0, 0   # our current position
dx, dy = 1, 0 # delta to apply moving forward (start facing EAST)

for cmd, n in commands:
    if cmd == FORWARD:
        # move forward in the current direction
        x += dx * n
        y += dy * n
    elif cmd in (LEFT, RIGHT):
        # rotate delta to face the new direction
        dx, dy = ROTMAP[cmd, n](dx, dy)
    else:
        # directly move N/S/E/W
        x, y = MOVEMAP[cmd](x, y, n)
```

Nice. Now let's just calculate the Manhattan distance between the final position
and the starting point and we have our answer:

```python
dist = abs(x) + abs(y)
print('Part 1:', dist)
```

### Part 2

For this second part, our task is still to find the final Manhattan distance
from the starting point, but we are told that we were interpreting the commands
wrong. In reality, there is a "waypoint" which starts at position `(10, 1)`
relative to our position and moves with us. All the commands affect the
waypoint, except for `F` which affects our position too.

The new commands' meaning is the following:

- `F`: move to the current waypoint position `n` times in a row.
- `L` / `R`: rotate *the waypoint* `n` degrees left/right around us without
  moving; `n` can only be one of `90`, `180`, `270`.
- `N` / `S` / `E` / `W`: move *the waypoint* `n` steps north/south/east/west.

The two things to notice here are:

1. The waypoint moves with us, so its position relative to us does not change
   when we apply the `F` command. Exactly as the point of our previous delta
   vector `(dx, dy)`.
2. When applying `L`/`R` to rotate the waypoint, we are rotating it around us.
   This is the exact same thing we are already doing to update our delta vector.

All of this is effectively the same as working with a "longer" delta vector (our
original one was always one unit in modulus). "Waypoint" is only another name
for the vector.

In other words, the only thing that changes from our previous part 1 solution is
that now a direct movement command (`NSEW`) updates the head of the delta vector
instead of our position. The only two things that we need to change are the
initial value of `(dx, dy)` and the code in last `else` statement:

```python
x, y = 0, 0
dx, dy = 10, 0 # changed

for cmd, n in commands:
    # ... unchanged ...
    else:
        # directly adjust delta N/S/E/W
        dx, dy = MOVEMAP[cmd](dx, dy, n) # changed
```

Well, that was smooth. The final distance calculation is also unchanged, so
let's get our second star of the day:

```python
dist = abs(x) + abs(y)
print('Part 2:', dist)
```

Man, I kind of miss high school geometry classes... :')

### Reflections

As noted and tried by many (myself included), a more mathematical approach to
this problem would be to interpret coordinates as
[complex numbers][wiki-complex-numbers], and then implement all movement
commands as simple arithmetic operations on complex numbers.

This is pretty straightforward for this problem, because:

- Movements become simple additions between complex numbers.
- Rotations of 90 degrees [become a multiplication][wiki-complex-rotation] by
  *i* (imaginary unit) if counter-clockwise, or by *-i* if clockwise.
- Rotations where `n` is amultiple of 90 degrees are just multiple rotations of
  90 degrees, equivalent to multiplication by *`i**(n/90)`* (counter-clockwise)
  or *`i**(-n/90)`* (clockwise).

Python [supports complex numbers][py-complex] out of the box, and a complex
number can be created using the syntax `1 + 1j` where `j` has the special
meaning of imaginary unit.

Our solution for today could be written with (arguably) simpler and shorter code
in terms of complex numbers, eliminating the need for dictionary lookups and
`lambda` expressions. This also makes everything faster, about 50% faster on my
machine (not bad, though both solutions still run in under 1 millisecond).

If you are curious, you can find my solution using complex numbers
**[here][d12-alternative]**.


Day 13 - Shuttle Search
-----------------------

[Problem statement][d13-problem] — [Complete solution][d13-solution] — [Back to top][top]

### Part 1

Oh no, modular arithmetic shenanigans again!

As input, we are first given a timestamp in minutes, and then a bunch of
comma-separated fields, which can be either `x` or a number. For this first part
of the problem, we are told to just ignore those `x` and focus on the numbers:
they represent the IDs of different buses.

Each bus starts from the sea port, and has a pre-determined circular route to
follow. The number of minutes that it takes for a bus to travel its entire route
(ending up back at the sea port) is equal to its ID.

We want to catch a bus (any bus), and the timestamp we are given represents the
time at which we'll arrive at the sea port. We need to determine at which
timestamp we'll be able to catch the first bus that passes, and the time we need
to wait for it. The answer we must give is the product of these two values.

For simplicity and ease of understanding, let's refer to bus IDs as "periods",
since that's actually their meaning. It's clear that if our arrival time is a
multiple of one of the bus periods, we will catch that bus exactly at the same
time we arrive at the sea port, waiting `0` minutes. However, if that's not the
case, we'll need to wait some time for the bus to arrive. For example, if our
arrival time is `5` and there only is one bus with period `4`, then we'll have
to wait `3` minutes for it to arrive at timestamp `8`. The answer would then be
`3 * 8 = 24`.

Let's get and parse our input. We'll split the second line on commas (`,`), then
[`filter()`][py-builtin-filter] out any field that is `x`, and transform the
valid fields to integers using [`map()`][py-builtin-map].

```python
arrival = int(fin.readline())
raw     = fin.readline().strip().split(',') # will be reused in part 2
periods = map(int, filter(lambda x: x != 'x', raw))
```

For each bus, we want to calculate the amount of time that we would need to wait
at the sea port before catching it. If one bus has period `p`, and we arrive at
`arrival`, this means the bus will have already done `arrival // p` complete
rounds of its route before our arrival. If `arrival` is exactly a multiple of
`p`, then we arrive exactly at the same time of the bus, and there is no
additional wait time. Otherwise, we will have to wait for the bus to finish one
more cycle of its route.

In the end, we need to find the first multiple of `p` higher or equal to
`arrival`. This can be done with [`math.ceil()`][py-math-ceil] doing
`ceil(p/arrival)`. If we want to do this using integers only, we can use a
little trick to calculate this without `ceil()`.

```python
n = ceil(arrival / p)
wait = n * p - arrival

# Or equivalent using integers only
n = arrival // p + (arrival % p != 0)
wait = n * p - arrival
```

The second version works taking advantage of the fact that we can add an `int`
and a `bool` together (`+False == 0`, `+True == 1`).

Now to solve the problem we'll calculate the waiting time for each bus and then
take the minimum.

```python
best = float('inf')
best_p = None

for p in periods:
    n = arrival // p + (arrival % p != 0)
    wait = n * p - arrival

    if wait < best:
        best = wait
        best_p = p

ans = best_p * p
print('Part 1:', ans)
```

### Part 2

Things get *a lot* more complicated and also quite mathematical. You should read
the original problem statement linked above in order to understand this. The
explanation of the problem statement I will give here is shorter.

Now we need to ignore the first line of input (our arrival time) and just focus
on the second. The list of comma-separated values is still a list of bus IDs.
The *index* of each ID in the list is a *time delta*. We want to find some time
`t` for which all buses of our list depart from the sea station exactly *delta*
minutes after `t` (i.e. bus at index `i` in the list departs at `t + i`). The
`x` values just represent IDs that we do not care about (i.e. they are only
there to shift the index of the next bus in the list).

Let's take for example the list `2,3,5`. Bus `2` has index `0`, bus `3` has
index `1` and bus `5` has index `2`. This means that we want to find some `t`
such that bus `2` departs at `t`, bus `3` departs at `t + 1`, and bus `5`
departs at `t + 2`.

If we draw the bus departure times in a time table:

```
 time | bus 2 | bus 3 | bus 5 |
    0 |   .   |   .   |   .   | (all buses start at the sea port at 0)
    1 |       |       |       |
    2 |   .   |       |       |
    3 |       |   .   |       |
    4 |   .   |       |       |
    5 |       |       |   .   |
    6 |   .   |   .   |       |
    7 |       |       |       |
    8 |   X   |       |       | <-- bus 2 departs at t = 8
    9 |       |   X   |       | <-- bus 3 departs at t + 1 = 8 + 1 = 9
   10 |   .   |       |   X   | <-- bus 5 departs at t + 2 = 8 + 2 = 10
```

We can see that `t=8` is the solution, because we satisfy the input constraints
listed above. In the above table, `X` marks the time at which each bus will
match our constraints.

There are two approaches to solving this problem:
[the first one](#part-2---simple-approach) is simpler, with a combination of
math and bruteforce,
[the second one](#part-2---purely-mathematical-approach) is purely mathematical
and involves modular arithmetic. While the first is simpler to explain in
practice, I'll explain both step by step, since I cannot pick a favorite and
really enjoy both approaches.

### Part 2 - Simple approach

It's clear that simply trying *all possible timestamps* isn't going to get us
any solution anytime soon. The puzzle statement itself hints at the fact that
the solution is larger than 100,000,000,000,000.

In order to solve the problem, we need to notice a couple of things, for which
the above example can help. In the solution of the above example, we can see
that:

- Bus `2` departs at `8`: indeed, `8` is a multiple of `2` (the period of the
  bus).
- Bus `3` departs at `9`, which is a multiple of `3`.
- Bus `5` departs at `10`, which is a multiple of `5`.

Okay, this is all obvious. Now assume that we don't know the solution `t`, and
let's express those times in terms of `t`:

- Bus `2` needs to depart at `t`: since bus `2` departs at intervals of period
  `2`, then `t` must be a multiple of `2`.
- Bus `3` needs to depart at `t + 1`: since bus `3` departs at intervals of
  period `3`, then `t + 1` must be a multiple of `3`.
- Bus `5` needs to depart at `t + 2`: since bus `5` departs at intervals of
  period `5`, then `t + 2` must be a multiple of `5`.

Now let's only think about the buses `2` and `3` in the example in the section
above and see what would happen if we only had those two:

- We know bus `2` departure times "advance" `2` minutes at a time.
- We know bus `3` needs to be at distance `1` from any of the departure times
  of bus `2`.

We can start with `t=0` and advance 2 steps at a time until we find that `t + 1`
is a multiple of `3`. Since we don't know how much we'll need to advance, let's
use [`itertools.count()`][py-itertools-count] for simplicity.

```python
t = 0
step = 2

for t in count(t, step):
    if (t + 1) % 3 == 0:
        break
```

Indeed, the above works and spits out `2`, as we would expect:

```
 time | bus 2 | bus 3 |
    0 |   .   |   .   |
    1 |       |       |
    2 |   X   |       | <-- bus 2 departs at t = 2
    3 |       |   X   | <-- bus 3 departs at t + 1 = 2 + 1 = 3
```

Now what happens if we add another bus, for example `5`? We can use the exact
same approach to find out, and keep advancing of `2` steps each time. However,
we want to go faster than that, otherwise we'll never reach the insanely high
solution.

In order to do this, we need to notice one last thing: we still need to satisfy
the constraints of buses `2` and `3`. The next time that the departure times of
bus `2` and `3` will differ of the same time delta again is exactly after `6`
steps. Indeed, from now on, those times will only align every `6` steps: at
`t=8`, `t=14`... and so on.

In order for the two departure times to "align" again, since one is advancing
`2` minutes each time and the other `3` minutes each time, we need to advance
exactly a number of minutes equal to the [least common multiple][wiki-lcm]
of the two, whch is `6`.

I'll use an horizontal representation to show this for a longer period of time:

```
time  | 0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18 19 20 21 22 ...
------+-------------------------------------------------------------------------
bus 2 | .     x     .     .     x     .     .     x     .     .     x     .
bus 3 | .        x        .        x        .        x        .        x
------+-------^-----------------^-----------------^-----------------^-----------
              |                 |                 |                 |
              1st alignment     2nd alignment     3rd alignment     4th alignment
              t = 2             t = 2+6 = 8       t = 8+6 = 14      t = 14+6 = 20
```

Now it should be somehow clear: we can apply the same approach iteratively,
updating the step that we use to advance each time we "match" a bus. After each
match, we already know that the departure times of already matched buses will
only align again after *LCM(periods of all matched buses so far)* minutes, so
each time we match a bus, we can just update `step` to be the LCM of all the
matched buses' periods. Okay, onto the solution!

First, let's parse the buses into a list of tuples `(delta, period)`. The
`delta` of time is just the index in the input list, so let's use
[`enumerate()`][py-builtin-enumerate] for this and
[`filter()`][py-builtin-filter] out all the `x` values with a `lambda` like we
did in part 1.

```python
buses = []
for i, v in filter(lambda iv: iv[1] != 'x', enumerate(raw)):
    buses.append((i, int(v))) # delta, period for each bus
```

To compute the least common multiple of two numbers we can either use
[`math.lcm()`][py-math-lcm] (only available on Python >= 3.9) or create our own
using [`math.gcd()`][py-math-gcd] if we are not running a bleeding edge Python
version (*stares at his Debian Stretch installation shipping Python 3.5 trying
not to cry*).

Now in terms of code, we just need to wrap our solution above (which only
matches one bus) in a loop:

```python
from math import gcd
from itertools import count

# Don't have math.lcm() in Python < 3.9, but it's easy to implement.
def lcm(a, b):
    return a * b // gcd(a, b)

t, step = buses[0]
for delta, period in buses[1:]:
    for t in count(t, step):
        if (t + delta) % period == 0:
            break

    step = lcm(step, period)

print('Part 2:', t)
```

That was quick! I barely hit ENTER on my keyboard and the solution popped on the
terminal (a 15 digits solution, by the way).

Although I originally solved this problem using the solution illustrated in the
next section, I've decided to use this as my "clean" solution to link above for
today. This is because I find it much simpler to implement, and is also more
about programming than math. Continue reading for the alternative solution.

### Part 2 - Purely mathematical approach

This is a more complex mathematical solution, the one I used to solve the
problem the first time. I find this solution quite satisfying, but I must say it
may not be obvious to many. You can find the full solution
**[here][d13-alternative]**.

First, let's refresh our mind with the example I provided [earlier](#part-2-12).
As I said above, we know that:

- Bus `2` needs to depart at `t`: since bus `2` departs at intervals of period
  `2`, then `t` must be a multiple of `2`.
- Bus `3` needs to depart at `t + 1`: since bus `3` departs at intervals of
  period `3`, then `t + 1` must be a multiple of `3`.
- Bus `5` needs to depart at `t + 2`: since bus `5` departs at intervals of
  period `5`, then `t + 2` must be a multiple of `5`.

To generalize the above: for any given bus in our list at index (aka delta) `i`
and with period `p`, we know that it will need to depart at some time `t + i`
such that `t + i` is a multiple of `p`. Therefore, for each bus we want to
satisfy the formula `(t + i) % p == 0`.

*NOTE: going ahead, some basic knowledge of
[modular arithmetic][wiki-modular-arithmetic] is required, so feel free to stop
and read the Wikipedia articles I'll be linking if you are not familiar with
some of these concepts.*

Putting these constraints in terms of modular arithmetic, using the
[modular congruence][wiki-modular-congruence] notation:

(*t + i*) mod *p* = 0  ⇒  *t + i* ≡ 0 (mod *p*)  ⇒  *t* ≡ *-i* (mod *p*)

We now have a system of modular equations of the above form, one for each bus in
our list at index `i` and with ID (period) `p`. Let's rename *-i = a* for ease
of understanding. We have:

- *t* ≡ *a<sub>1</sub>* (mod *p<sub>1</sub>*)
- *t* ≡ *a<sub>2</sub>* (mod *p<sub>2</sub>*)
- ...
- *t* ≡ *a<sub>K</sub>* (mod *p<sub>K</sub>*)

To solve this system of modular equations, we can use the
[Chinese remainder theorem][wiki-chinese-remainder]. Let's call *P* the product
of all the *p* above. This theorem states that if all the integers
*p<sub>i</sub>*...*p<sub>K</sub>* form a [coprime set][wiki-coprime-set] (i.e.
all possible pairs of those numbers are [coprime][wiki-coprime] with each
other), then there is one and only one solution *t* such that *0 ≤ t < P*, and
the remainder of the [Euclidean division][wiki-euclidean-division] of *t* with
each *p<sub>i</sub>* is *a<sub>i</sub>*. The bus IDs in our input indeed form a
coprime set, so we can apply the theorem.

Putting aside all the math and theory behind this (which is quite a good
amount), this means that we are able to calculate our solution `t` using the
Chinese remainder theorem. This involves the calculation of the
[modular multiplicative inverse][wiki-modular-inverse] of a number. Overall,
this might not be an obvious and straightforward task, specially if we are not
familiar with modular arithmetic. Explaining the whole concept would probably
make today's walkthrough longer than this entire document, so I will only limit
myself to explaining the algorithm used to solve the Chinese remainder theorem.

Chinese remainder theorem for dummies:

1. Start with a list of remainders *a<sub>i</sub>* and a list of moduli
*p<sub>i</sub>*.
2. Compute *P* = product of all moduli *p<sub>i</sub>*.
3. For each *a<sub>i</sub>* calculate:
   - *n<sub>i</sub> = N/p<sub>i</sub>*
   - *y<sub>i</sub>* = modular inverse of *n<sub>i</sub>* modulo *p<sub>i</sub>*
   - *x<sub>i</sub> = a<sub>i</sub>n<sub>i</sub>y<sub>i</sub>*
4. Finally calculate the solution: *t* = (*sum of all x<sub>i</sub>*) mod *P*.

Translated into a Python function which takes a list of tuples `(ai, pi)`, we'll
have:

```python
def chinese_remainder_theorem(equations):
    # equations = [(a1, p1), (a2, p2), ...]
    t = 0
    P = 1
    for _, pi in equations:
        P *= pi

    for ai, pi in equations:
        ni = P // pi
        inv = pow(ni, -1, pi)
        t = (t + ai * ni * inv) % P

    return t
```

Here `pow(ni, -1, pi)` calculates the inverse of `ni` modulo `pi` using Python's
built-in [`pow()`][py-builtin-pow]. Support for calculation of the modular
inverse has only been added in Python 3.8, so if you have an earlier version you
will have to do this by hand, using (a simplification of) the
[extended Euclidean algorithm][algo-extended-euclidean]. Again, this is not the
simplest algorithm to explain, but nonetheless I've implemented this in a
comment of [my solution][d13-alternative], so you can check that out if you
want... or maybe just let Google be your friend.

We could simplify the calculation of `P` above using
[`math.prod()`][py-math-prod] (Python >= 3.8) with the handy
[`operator.itemgetter()`][py-operator-itemgetter] to extract the moduli from the
equations:

```python
from math import prod
from operator import itemgetter

P = prod(itemgetter(1), equations)
```

... or with [`functools.reduce()`][py-functools-reduce] plus
[`operator.mul()`][py-operator-mul]:

```python
from functools import reduce
from operator import mul

P = reduce(mul, map(itemgetter(1), equations))
```

Now that we have a function to solve the system using the Chinese remainder
theorem, we can just provide it with the correct input and let it spit out the
solution for us:

```python
buses = []
for i, v in filter(lambda iv: iv[1] != 'x', enumerate(raw)):
    buses.append((-i, int(v)))

time = chinese_remainder_theorem(buses)
print('Part 2:', time)
```

Overall, maybe the hardest puzzle so far, with a real steep increase in
difficulty from part 1 to part 2. Once again, you can find this "alternative"
solution [here][d13-alternative].


Day 14 - Docking Data
---------------------

[Problem statement][d14-problem] — [Complete solution][d14-solution] — [Back to top][top]

### Part 1

A good programmer should always be able to do some good ol' bit twiddling. Today
we need to emulate some kind of machine, which writes values to memory using a
really strange binary masking method. The machine works only with 36-bit
unsigned values.

Each line of our input is a command:

- `mask = MASKVAL`: sets the internal mask to `MASKVAL`, which is a binary
  number of exactly 36 digits: each digit can either be a binary digit (`01`) or
  the special digit `X`.
- `mem[ADDR] = VAL`: writes the value `VAL` to memory at address `ADDR`, both
  values are decimal.

The peculiar thing about this machine is that *before* writing a value to
memory, the value is modified according to the current mask:

- Each `0` or `1` bit in the mask overwrites the corresponding value bit.
- Each `X` in the mask leaves the corresponding value bit unchanged.

Our input always starts with a `mask` command to set the initial value of the
mask. After starting with a memory fully initialized to zero and applying all
commands, we need to calculate the sum of all values in memory.

Let's get to work. First, let's get the input file lines and create a
[regular expression][misc-regexp] to extract the values from `mem` commands:

```python
import re
lines = fin.readlines()
rexp = re.compile(r'mem\[(\d+)\] = (\d+)')
```

The next thing ***NOT*** to do is trying to create an array `mem = [0] * 2**36`,
like I immediately did like an idiot, exhausting all the RAM of my computer.
Instead, we'll use a dictionary for the memory, which is perfect for what we
need: values we add will be counted, values that are not present will still
count as zero when summing all up.

Let's parse each input line in a loop to extract the relevant values. For `mask`
commands it's just a simple skip of 7 and strip the trailing newline; for `mem`
commands we'll use the regexp and [`map()`][py-builtin-map] the values into
integers.

```python
mem = {}
for line in lines:
    if line.startswith('mask'):
        mask = line[7:].rstrip()
        # ...
    else:
        addr, value = map(int, rexp.findall(line)[0])
        # ...
```

The kind of mask we are working with isn't really a [bitmask][wiki-bitmask] at
all: it cannot simply be applied to values with bitwise operations, and does not
actually "extract" or "mask" anything, it just replaces bits. However, we can
turn it into a real mask.

We know that all bits set to `0` or `1` in the mask are going to overwrite the
bits at the same position in the value. Therefore, we can create a *clear mask*
which has a `1` for each `X` in the mask, and a `0` anywhere else.

Here's an example with only 8 bits to make it simple, the operation can be
performed with any number of bits:

```
      mask  X11XXX0X
clear mask  10011101
```

We can then use this real mask to actually mask the input value with a
[*bitwise AND*][wiki-bitwise-and] (`&` in Python), zeroing out every bit of
`value` that needs to be overwritten by the corresponding `0` or `1` bit in the
mask. Then, we can extract the actual bits of mask that need to be written to
the value (let's call this *set mask*) from the original mask (ignoring all `X`)
and set them with a [*bitwise OR*][wiki-bitwise-or]. This will have the effect
of setting the needed value bits after clearing them with the *clear mask*.

To make it clear, here's an example:

```
      mask  X11XXX0X
clear mask  10011101
  set mask  01100000

Suppose value = 42

       value  00101010 &
  clear mask  10011101 =
masked value  00001000

masked value  00001000 +
    set mask  01100000 =
 final value  01101000   ---> write this to memory
```

Now to extract two values from the mask:

- For the *clear mask* we need to perform 2 replacements: `1` with `0` and `X`
  with `1`, then turn the string into an `int`. We can use
  [`str.maketrans()`][py-str-maketrans] plus
  [`str.translate()`][py-str-translate] for this, just like we did in
  [day 5][d05].
- For the *set mask* we just need to replace every `X` with `0` and then turn
  the string into an `int`.

Finally, when writing to memory, we'll calculate the value as we did in the
above example. The code is quite simple really:

```python
table = str.maketrans('1X', '01')
mem = {}

for line in lines:
    if line.startswith('mask'):
        mask       = line[7:].rstrip()
        mask_clear = int(mask.translate(table), 2)
        mask_set   = int(mask.replace('X', '0'), 2)
    else:
        addr, value = map(int, rexp.findall(line)[0])
        mem[addr] = (value & mask_clear) | mask_set
```

Now we can just sum all values in memory and get our answer:

```python
total = sum(mem.values())
print('Part 1:', total)
```

### Part 2

Now the meaning of our strange mask changes. We need to use it to alter the
address we want to write to. In particular:

- Every `0` in the mask leaves the corresponding address bit unchanged.
- Every `1` in the mask overwrites the corresponding address bit with a `1`.
- Every `X` in the mask overwrites the corresponding address bit with a
  *floating bit*.

A floating bit is a bit that assumes both values at once. For example, `XXX` is
composed of 3 floating bits, and corresponds to any value from `000` to `111`.
When the machine tries to write a value at an address which contains floating
bits, the machine will actually write the same value at *all* addresses that the
address represents.

Here's an example:

```
       mask  00010X0X
    address  11001000
new address  11011X0X  (where X = floating bit)

Real addresses:

             11011000
             11011001
             11011100
             11011101
```

Our task is still finding the sum of all values in memory after running all
commands.

Okay, this complicates things: 1 floating bit in the address will translate to 2
different real addresses, 2 floating bits will translate to 4, and so on. In
general, if the address after applying the mask contains `n` floating bits, then
it will translate to `2**n` different addresses, representing all the possible
combinations of `0` and `1` in place of each `X`.

In order to properly emulate all memory operations, we need a function to
generate all real addresses given an address containing floating bits, so that
we can write the same value to each of those.

This task is kind of similar to the one accomplished by the
[`product()`][py-itertools-product] generator function from the
[`itertools`][py-itertools] module. In fact, this function does exactly what we
need if se supply the adequate values.

For example, if we want to generate all addresses for `10X0X`:

```python
>>> from itertools import product
>>> addrs = product('1', '0', '01', '0', '01')
>>> for a in addrs:
        print(''.join(a))

10000
10001
10100
10101
```

We can just transform each "floating bit" `X` into `'01'`, keep all the other
bits unchanged, and pass everything to `itertools.product()`. We'll start with
an empty list `[]`, then for each corresponding bit of address and mask:

- If the mask bit is `X`, add `'01'` to the list.
- If the mask bit is `0`, add the address bit to the list.
- If the mask bit is `1`, add `'1'` to the list.

After this, we can pass the list to `itertools.product()` using the
[unpack operator][py-unpacking] (`*lst`) to turn it into 36 different arguments.
The function we write will be a generator: it will convert each value yielded by
`product()` into an integer and then `yield` it.

```python
from itertools import product

def all_addrs(addr, mask): # addr and mask are two strings of 36 characters
    args = []

    for addr_bit, mask_bit in zip(addr, mask):
        if mask_bit == '0':
            args.append(addr_bit)
        elif mask_bit == '1':
            args.append('1')
        else:
            args.append('01')

    for a in product(*args):
        yield int(''.join(a), 2)
```

All that's left to do is parse each line and use the above function. We can
simply add a couple of lines in the original loop we wrote for part 1, using a
second memory dictionaty. To transform the decimal addresses that we read from
the input into a binary string we can use a [format string][py-format-string]
specifying `036b` as format.

```python
mem1  = {}
mem2  = {}

for line in lines:
    if line.startswith('mask'):
        mask       = line[7:].rstrip()
        mask_clear = int(mask.translate(table), 2)
        mask_set   = int(mask.replace('X', '0'), 2)
    else:
        addr, value = map(int, rexp.findall(line)[0])
        mem1[addr]  = (value & mask_clear) | mask_set

        # Part 2 code added
        addr = '{:036b}'.format(addr)
        for a in all_addrs(addr, mask):
            mem2[a] = value

total1 = sum(mem1.values())
total2 = sum(mem2.values())
print('Part 1:', total1)
print('Part 2:', total2)
```

An alternative manual implementation of the `itertools.product()` function for
our specific use case would be a recursive generator function whiwh yields an
integer if the address does not contain any `X`, otherwise does a recursive call
to get all possible values replacing that `X` with a `0` and a `1`. The [`yield
from`][py-yield-from] "generator delegation" syntax comes in handy.

```python
def all_addrs(addr, mask=None):
    if mask is not None:
        addr = ''.join(a if m == '0' else m for a, m in zip(addr, mask))

    if 'X' in addr:
        yield from all_addrs(addr.replace('X', '0', 1))
        yield from all_addrs(addr.replace('X', '1', 1))
    else:
        yield int(addr, 2)

# list(all_addrs('100', '1XX')) -> [0b100, 0b101, 0b110, 0b111] == [4, 5, 6, 7]
```

I really appreciate the elegance of the above code, however I chose to go with
the `itertools` approach in my solution just because it's faster.


Day 15 - Rambunctious Recitation
--------------------------------

[Problem statement][d15-problem] — [Complete solution][d15-solution] — [Back to top][top]

### Part 1

Quite a simple problem today, although the text takes some time to comprehend.
We have a short list of integers as input, and we need to implement an algorithm
to play a game:

- Start at turn 1, and "say" one number per turn from the input list.
- Then, continue indefinitely, based on the previous number:
  - If that number was already said before (other than the last turn), then the
    next number to say is the difference between the last two turns in which
    that number was said.
  - Otherwise, say 0.

Here's a simple example with the numbers `1,3,2`:

1. Say `1`.
2. Say `3`.
3. Say `2`.
4. The numbers in the list are over. The previous number was `2`: it was *not*
   seen before the previous turn, so say `0`.
5. `0` was *not* seen before the previous turn, say `0`.
6. `0` was seen before the previous turn at turn 4. Say `1` (`== 5 - 4`).
7. `1` was seen before the previous turn at turn 1. Say `5` (`== 6 - 1`).
8. `5` was *not* seen before the previous turn, say `0`.
9. ... and so on ...

We need to find the number that is going to be said at turn 2020.

Before we begin, little fun fact: this game seems to have been inspired by the
[Van Eck's sequence][misc-van-eck]. The rules for constructing this sequence are
the same, the only difference is that Van Eck's sequence starts with a single
number: 0.

Now let's start. Of course, first get the numbers from the input file. We can
just split the content on commas (`,`) and [`map()`][py-builtin-map] everything
to `int`, storing them in a `tuple`:

```python
fin = open(...)
nums = tuple(map(int, fin.read().split(',')))
```

To solve this puzzle, there isn't really much else to think about other than
following the directions. We'll write a really simple implementation using a
dictionary to keep track of the last time a number was said. It looks like we
need to remember the two most recent turns in which a number was said, but in
reality since one of the turns is always the previous turn, we can just remember
the one before that.

First, let's consume all the numbers from the list, and keep track of the turn
in which we last saw them. It does not really matter if we start the turns at
`0` or `1`, we can choose `1` since we can, just for consistency with the
problem statement and in case we want to debug the code. We can use a
[dict comprehension][py-dict-comprehension] plus
[`enumerate()`][py-builtin-enumerate] to process all numbers in one line.

```python
last_seen = {n: turn for turn, n in enumerate(nums[:-1], 1)}
prev = nums[-1]
```

We keep the last number as `prev` (without adding it to `last_seen`) because we
need if for the next turn, and we want to remember if we saw it before another
time.

Each turn we want to first look at `last_seen`. If the `prev` number is in
`last_seen`, then it was seen two times: the previous turn, and some turn before
that, which can just be retrieved from `last_seen`. The current number will
either be `0` if we did not see `prev` before the previous turn, or the
difference between the previous turn and `last_seen[prev]`. We can then update
`last_seen[prev]` with the previous turn and keep going.

Turning the above into a function:

```python
def play(nums, n_turns):
    last_seen = {n: turn for turn, n in enumerate(nums[:-1], 1)}
    prev = nums[-1]

    # We said len(nums) numbers now, so the next turn is len(nums) + 1
    # We want to keep going until n_turns (included), so n_turns + 1 since range() does one less iteration

    for turn in range(len(nums) + 1, n_turns + 1):
        if prev in last_seen:
            # Before the previous turn, prev was seen at turn last_seen[prev]
            cur = turn - 1 - last_seen[prev]
        else:
            cur = 0

        # Remember that prev was said one turn ago and keep going
        last_seen[prev] = turn - 1
        prev = cur

    return cur
```

Now to compute the solution we just need to call the function:

```python
ans = play(nums, 2020)
print('Part 1:', ans)
```

### Part 2

For part 2, we need to do the exact same thing as before, but this time we want
to know what number will be said on the 30000000th turn (30 millionth).

Well... we could really just run the above code again and be done with it:

```python
ans = play(nums, 30000000)
```

This works fine, but it is pretty damn slow to be honest, and this kind of bugs
me. A lot. On my machine, this takes around 9 seconds with
[CPython][wiki-cpython] 3.9, and around 6 second using [PyPy][misc-pypy] 7.3.3.

The first thing to notice to speed things up, is that we can use a `list`
instead of a dictionary for `last_seen`. How big? Well, I would say at least the
number of turns (i.e. 30 million items), since that is the worst case, in which
we see a number at the start and then we only see it again at the end, causing
the last number to be exactly the total number of turns (minus one I guess). In
theory this should significantly increase memory usage, but apparently Python
dictionaries take up a lot of space, and the memory consumption only goes up
from 360MB to 404MB on my machine using CPython.

So let's do it. We can just create a list of 30M zeroes since we start counting
turns from `1`. We can then check if `last_seen[last]` is zero or not. Now we
need to process the numbers and initialize `last_seen` "by hand" with a `for`
though.

```python
def play(nums, n_turns):
    last_seen = [0] * n_turns
    prev = nums[-1]
    for turn, n in enumerate(nums[:-1], 1):
        last_seen[n] = turn

    for turn in range(len(nums) + 1, n_turns + 1):
        if last_seen[prev]:
            cur = turn - 1 - last_seen[prev]
        else:
            cur = 0

        last_seen[prev] = turn - 1
        prev = cur

    return cur
```

The above code runs in 1.04 seconds with PyPy (nice!), but still in little less
than 9 seconds with CPython. Really CPython? `list` access takes the same time
as `dict` access? Wow. Let's continue!

We can very well avoid those `- 1` since we apply them to `turn` both when
storing it into `last_seen` and when calculating the `cur` number, so:

```python
cur = turn - 1 - last_seen[prev]
    == turn - 1 - (some_previous_turn - 1)
    == turn - some_previous_turn
```

Therefore we can just iterate over `prev_turn`, starting and stopping the range
at one less than before, and removing those `- 1` from calculations:

```python
def play(nums, n_turns):
    last_seen = [0] * n_turns
    prev = nums[-1]
    for turn, n in enumerate(nums[:-1], 1):
        last_seen[n] = turn

    for prev_turn in range(len(nums), n_turns):
        if last_seen[prev]:
            cur = prev_turn - last_seen[prev]
        else:
            cur = 0

        last_seen[prev] = prev_turn
        prev = cur

    return cur
```

Aaaand... that takes ~970ms with PyPy (sub-second, wohoo!) and ~6.8 seconds with
CPython. That's better. The last smart trick we can apply is avoiding indexing
`last_seen` two times. Each loop we first check `if last_seen[prev]` and then do
`last_seen[prev]` again in the calculation. We can avoid this exploiting the
fact that `last_seen` is initialized to `0`. If we just calculate
`cur = prev_turn - last_seen[prev]` right away, then if the number wasn't
already seen we'll have `last_seen[prev] == 0` and therefore `cur == prev_turn`.

```python
def play(nums, n_turns):
    last_seen = [0] * n_turns
    prev = nums[-1]
    for turn, n in enumerate(nums[:-1], 1):
        last_seen[n] = turn

    for prev_turn in range(len(nums), n_turns):
        cur = prev_turn - last_seen[prev]
        if cur == prev_turn:
            cur = 0

        last_seen[prev] = prev_turn
        prev = cur

    return cur
```

Well, after rewriting this for the n-th time: still ~970ms with PyPy, ~6.4s with
CPython. I think I'll take it. It's not the best, but not the worst either. The
next optimization step would just be to switch to a compiled language :P.

```python
ans = play(nums, 30000000)
print('Part 2:', ans)
```

30 stars and counting...


Day 16 - Ticket Translation
---------------------------

[Problem statement][d16-problem] — [Complete solution][d16-solution] — [Back to top][top]

### Part 1

Yet another input validation puzzle. This time we're going to validate some
very detailed train tickets.

Each ticket is composed of 20 fields, and each kind of field has some validity
requirements. The input we get is split in 3 parts, separated by empty lines:
first all the field names along with validity requirements, then our ticket, and
then a list of other tickets.

All the tickets we have are lists of comma separated integers, but we don't know
which field any of those represent (i.e. in which order the fields of a ticket
are listed). We need to find invalid tickets: a ticket is invalid if *any* of
its fields does not respect any validity requirement. We need to find all such
fields for every ticket *excluding ours*, and sum all of them.

Well, nothing exceptional to do except follow the directions. Since the input
data format is not that simple to parse all in one go, we'll create a function
to do it. First parse all requirements, which are field names and two couple of
integers for each field representing valid ranges. Then, skip a few lines and
get our ticket, skip some more lines and get all other tickets.

Each requirement is in the following form:

```
field name: A-B or C-D
```

Here `A`, `B`, `C` and `D` are integers representing two ranges of valid values
for the field. Since we'll need to check for validity of ticket fields a lot, we
want this to be as simple as possible. Creating a simple class which is capable
of handling the `in` operator seems like a pretty straightforward idea. We'll
create a `DoubleRange` class which takes the four values for initialization and
implements a custom [`__contains__()`][py-object-contains] method for easily
checking if a value is in any of the two ranges.

```python
class DoubleRange:
    def __init__(self, a, b, c, d):
        self.a, self.b, self.c, self.d = a, b, c, d

    def __contains__(self, value):
        return self.a <= value <= self.b or self.c <= value <= self.d
```

We don't really care about field names, so we'll just use `\d+` as regular
expression to extract all four numbers at once with
[`re.findall()`][py-re-findall], then [`map()`][py-builtin-map] the numbers to
`int`, and use them to create a `DoubleRange` object. We'll put all the ranges
in a `list` and return it. To extract tickets, we can instead just
[`.split()`][py-str-split] on commas (`,`) and `map()` to `int` directly,
creating a `tuple` per ticket. We'll return everything along with the ranges.

```python
import re

def parse_input(fin):
    ranges = []
    num_exp = re.compile(r'\d+')

    for line in map(str.rstrip, fin):
        if not line:
            break

        numbers = map(int, num_exp.findall(line))
        ranges.append(DoubleRange(*numbers))

    fin.readline()
    my_ticket = tuple(map(int, fin.readline().split(',')))
    fin.readline()
    fin.readline()

    tickets = []
    for line in fin:
        tickets.append(tuple(map(int, line.split(','))))

    return ranges, my_ticket, tickets

fin = open(...)
ranges, my_ticket, tickets = parse_input(fin)
```

Now that we have everything ready, we can create a function to check a ticket.
In particular, we want to extract all invalid fields (i.e. fields that are not
inside any of our `ranges`) from each ticket. For simplicity, we'll just pass
the ticket as parameter and use the global `ranges` list.

We'll create a nice generator function which given a ticket spits out all the
values of invalid fields. To check for validity of a single field of a ticket,
we can take advantage of the [`all()`][py-builtin-all] function to check the
value against all `ranges`. If the value isn't in any of the ranges, we'll
`yield` it and keep going. Easier to write than to explain.

```python
def invalid_fields(ticket):
    for value in ticket:
        if all(value not in rng for rng in ranges):
            yield value
```

Now all that's left to do is sum all the invalid fields for every ticket:

```python
total = 0
for ticket in tickets:
    for f in invalid_fields(ticket):
        total += f
```

The above can be simplified down to one line with the help of
[`sum()`][py-builtin-sum], mapping all tickets using `invalid_fields()`:

```python
total = sum(map(sum, map(invalid_fields, tickets)))
print('Part 1:', total)
```

We really spent more time writing the input parsing function than actually
solving the puzzle!

### Part 2

For the second part of the puzzle, we now need to deduce which field corresponds
to which number for each ticket. All tickets have their fields ordered in the
same way, but we don't know the order. In other words, we don't know the index
of a certain field in the list of values of a ticket.

We are however told that, considering *valid tickets only*, we can deduce this
from the ticket field values. This means that we can check for validity of the
values of every single field of each ticket and deduce the correct ordering of
the fields for tickets.

For example, we know that if the field `x` has ranges `5-10 15-20` and we have a
ticket `1,3,34,6`, then the field `x` can only be the last one (index `4`),
because none of the previous ones matches the validity requirements for `x`.

After determining the correct order of fields in tickets, we must calculate the
product of the six fields of our ticket whose name starts with `departure`.

First of all, we already know that these six fields are the first six of our
`ranges` array, so no need to parse field names or change existing code. We just
need to determine their correct index in our ticket.

We are told to also use our ticket for determining the correct field ordering so
we'll just include it in the list of tickets right away. Then, we'll keep a set
of "possible" valid positions for each field. We'll start creating one `set` for
each field including all the numbers from `0` to the number fo fields of a
ticket:

```python
tickets.append(my_ticket)
n_fields = len(my_ticket)
possible = [set(range(n_fields)) for _ in range(len(ranges))]
```

Now since we only want to work with valid tickets, let's create a function to
check the validity of a ticket. It's actually pretty simple, we just need to
make sure that each field in the ticket has a value that is correct according to
at least one of the field validity constraints.


```python
def is_valid(ticket):
    for value in ticket:
        ok = False
        for rng in ranges:
            if value in rng:
                ok = True
                break

        if not ok:
            return False

    return True
```

It may not be so simple to notice at first, but the above can be simplified a
lot with the help of [`all()`][py-builtin-all] and [`any()`][py-builtin-any].
In the inner loop we are checking if the current `value` is inside any of the
`ranges`. Therefore the inner loop can just be rewritten as:

```python
ok = any(value in rng for rng in ranges)
```

While in the outer loop we are making sure that the above is true for *all*
values of the ticket. Therefore the entire thing can be rewritten as:

```python
def is_valid(ticket):
    return all(any(v in r for r in ranges) for v in ticket)
```

Sweet. Now we just need to filter out invalid tickets and only work with valid
ones. Perfect use case for the [`filter()`][py-builtin-filter] buil-in. Then,
for each valid ticket, for each field we want to check if any of the ticket
values violate that particular field's validity requirements. If so, we'll
remove the index of that value as a possible index for the field.

We can iterate over `ranges` and `possible` pairwise using
[`zip()`][py-builtin-zip], and use [`enumerate()`][py-builtin-enumerate] to scan
the values of each ticket while also keeping track of their index.

```python
# For each valid ticket
for ticket in filter(is_valid, tickets):
    # For every field and its set of possible indexes
    for rng, poss in zip(ranges, possible):
        # For each value in the ticket
        for i, value in enumerate(ticket):
            # If that value cannot be valid for this field, then remove its
            # index from the possible indexes for the field
            if value not in rng and i in poss:
                poss.remove(i)
```

Perfect, now taking a look at those `possible` indexes:

```python
>>> for i, p in enumerate(possible):
        print(i, p)

0 {0, 1, 3, 4, 8, 11, 12}
1 {0, 1, 3, 4, 7, 8, 9, 11, 12}
2 {0, 1, 3, 4, 8, 9, 11, 12}
...
15 {8}
16 {0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19}
17 {0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 16, 17, 19}
18 {1, 3, 4, 8, 12}
19 {8, 12}
```

Hmm... It doesn't look like we are certain about which field should have which
position in a ticket. The only one we are sure about seems to be field `15`,
which we see only has `8` as a possible index. If you look carefully though, you
can see that field `19` only has `8` and `12` as possible indexes, but we know
that `8` *must* be the index of field `15`, since no other option is available
for it. We could therefore remove the `8` from the possible indexes of any other
field, because we know it must be used for `15`.

More generally, we can do the following in a loop until we find a solution:

1. Find a set of possible indexes which only has one index, remove that index
   from the set (making the set empty) and assign it to the corresponding field.
2. Cycle through all the other sets and remove the index we just assigned from
   each of them.
3. Check if all the sets are empty: if so, we assigned all field indexes and we
   are done.

Let's code it in a function:

```python
def simplify(possible):
    # Start with None for all fields so that we can catch errors later if some None is not replaced.
    assigned = [None] * len(possible)

    # Continue until all sets of possible indexes are empty (i.e. we assigned each field an index)
    while any(possible):
        # For each set of possible indexes
        for i, poss in enumerate(possible):
            # If only one possible index is left, then it must be assigned to this field
            if len(poss) == 1:
                assigned[i] = poss.pop()
                break

        # Remove the assigned value from every other set
        for other in possible:
            if assigned[i] in other:
                other.remove(match)

    # Optionally check for correctness
    assert all(a is not None for a in assigned)

    return assigned
```

Now we can just call the above function to finalize the index assignments and
know the correct position of each field.

```python
indexes = simplify(possible)
```

Now, simply look at the correct index in our ticket for the first 6 fields and
calculate their product. In order to multiply the values together we can use the
helpful [`math.prod()`][py-math-prod].

```python
from math import prod

total = prod(my_ticket[i] for i in indexes)
print('Part 2:', total)
```

I feel like after all the travel documents validations in this Advent of Code,
we're easily going to find a job as an airport passenger check-in officer.


Day 17 - Conway Cubes
---------------------

[Problem statement][d17-problem] — [Complete solution][d17-solution] — [Back to top][top]

### Part 1

Oh boy, I hope you like [cellular automata][wiki-cellular-automaton]. If you had
fun on [day 11][d11] you will have a lot more fun today!

I'll cut the gibberish to the minimum and come right to the point: we are
dealing with a 3-dimensional cellular automaton. In the initial generation all
cells are dead, except for a few in the [plane][wiki-plane] `z=0`.

Our input consists of the initial state of the cells at `z=0`: we are given a
grid of characters (`#` for alive, `.` for dead) which is 8 columns wide and 8
rows tall, representing a portion of 3D space from `(0, 0, 0)` to `(7, 7, 0)`.

We need to simulate life according to two simple rules of evolution from one
generation to the next:

- If a cell is dead (`.`) and exactly 3 of its neighbors are alive (`#`), the
  cell becomes alive (`#`).
- If a cell is alive (`#`) and exactly 2 or 3 of its neighbors are alive (`#`),
  the cell *stays alive*, otherwise it dies (`.`).

In 3D space, "neighbors" of a cell means any of the 26 other cells for which any
of the coordinates differs by at most 1. That is, the entire 3x3 cube of cells
centered at the coordinates of the cell, except the cell itself. You can also
see this as the 26 pieces surrounding the core of a
[Rubik's cube][wiki-rubiks-cube].

After evolving for 6 generations, we need to count the number of cells that are
alive.

Let's get input parsing out of the way. We have a grid of characters as input,
so we can just [`rstrip`][py-str-rstrip] each line of input to remove trailing
newlines using [`map()`][py-builtin-map] and turn the whole thing into a
`tuple`.

```python
grid = tuple(map(str.rstrip, fin))
```

Before we begin writing any more code, we need to think about which data
structure to use to hold information about cells. It's important to notice that
we can expand in *any* of the three dimensions, so using matrices (i.e. nested
`list`s) to represent each level of our 3-dimensional space is not as simple as
it looks.

After all, we do not really care how cells are arranged. The only thing we care
about is being able to tell if a given point `(x, y, z)` in space represents a
cell that is alive or not. In other words, we only want to keep track of the
coordinates which represent alive cells, and we can consider anything else dead.

To do this, we can only need a `set` of coordinates. Our initial `grid`
represents a small portion of the plane at `z=0`, so for each `(x, y)` we'll add
the coordinates `(x, y, 0)` to our set if `grid[x][y]` is alive (`#`). I'll use
[`enumerate()`][py-builtin-enumerate] to iterate over the grid.

```python
cube = set()

for x, row in enumerate(grid):
    for y, cell in enumerate(row):
        if cell == '#':
            cube.add((x, y, 0))
```

Now our `cube` represents the set of coordinates of alive cells in our 3D space.

The next thing to do is define a function which can count how many cells are
alive around a given cell (given its coordinates). Well, simple enough: it's
almost the same thing we did in [day 11][d11] part 1. We'll vary each coordinate
`c` in the range `[c+1, c-1]` and count how many of the coordinates we generate
are in our `cube`. We don't need to do any bound checking since we don't
actually have bounds. Doing `coords in cube` is enough to check if a cell at
`coords` is alive.

We'll actually split this in two functions, creating a small generator function
to get the neighbor coordinates, which we'll also use later. For performance
purposes, along with neighbor coordinates we'll also return the given
coordinates theirselves; we will check later with a single `if` whether we also
need them or not, rather than checking every single coordinate in the nested
loops, which would be a lot slower.

```python
def neighbors(x, y, z):
    for xx in range(x - 1, x + 2):
        for yy in range(y - 1, y + 2):
            for zz in range(z - 1, z + 2):
                yield xx, yy, zz

def alive_neighbors(cube, coords):
    alive = 0
    for n in neighbors(*coords):
        if n in cube:
            alive += 1

    # Just subtract 1 here if we also counted the given coordinates, since we
    # don't filter them out in neighbors()
    if coords in cube:
        alive -= 1

    return alive
```

We can simplify the nested loops in the above `neighbors` function with the help
of [`itertools.product()`][py-itertools-product], using the pretty cool
"generator delegation" sytax [`yield from`][py-yield-from]:

```python
from itertools import product

def neighbors(x, y, z):
    yield from product(range(x-1, x+2), range(y-1, y+2), range(z-1, z+2))
```

The `alive_neighbors()` function can also be simplified using
[`sum()`][py-builtin-sum] along with a
[generator expression][py-generator-expr], since all it's doing is counting the
number of times the condition `n in cube` is `True`:

```python
def alive_neighbors(cube, coords):
    alive  = sum(p in cube for p in neighbors(*coords))
    alive -= coords in cube
    return alive
```

Now we need to evolve the cells. The cells in our `cube` are enclosed in a
limited cube in space. We want to iterate over each cell of said cube. In
addition to this, as we noticed earlier, each generation there's also a
possibility that this limited cube "expands" or even moves around, because dead
neighbors which are not considered in our set can come to life if they are near
enough alive cells.

For example, in an analogous 2D situation (sorry, can't really do 3D ASCII-art):

```
. . . . .      . . . . .
. . . . .      . . . . .
. # # . .      . # # . .
. . # . .  =>  . . . . .
. # # # .      . # # # .
. . . . .      . . # . . <-- expansion
. . . . .      . . . . .
```

This means that each generation, in addition to checking all the cells in our
`cube`, we also need to check their neighbors. To determine the neighbors of all
the cells we can simply iterate over all the coordinates and call the
`neighbors()` function we just wrote for each of them: this time the fact that
the function also returns the given coordinates is useful. Since there's a high
chance of having cells close to each other, and therefore considering the same
neighbors more than once, to avoid wasting time we'll filter all duplicate
coordinates out using a `set()`.

```python
def all_neighbors(cube):
    return set(n for p in cube for n in neighbors(*p))
```

Now that we figured this out, all we have to do is iterate over all the
coordinates returned from `all_neighbors()`, and check the evolution rules each
time.

```python
def evolve(cube):
    new = set()

    for p in all_neighbors(cube):
        alive = alive_neighbors(cube, p)

        if p in cube:
            if alive == 2 or alive == 3:
                # alive cell stays alive only if exactly 2 or 3 neighbors are alive
                new.add(p)
        elif alive == 3:
            # dead cell becomes alive only if exactly 3 neighbors are alive
            new.add(p)

    return new
```

The checks for evolving a cell can be simplified a lot by noticing that cells
which have 3 alive neighbors will become (or stay) alive regardless of their
previous state, while cells that are already alive will also stay alive if they
have exactly 2 neighbors:

```python
def evolve(cube):
    new = set()

    for p in all_neighbors(cube):
        alive = alive_neighbors(cube, p)

        if alive == 3 or (alive == 2 and p in cube):
            new.add(p)

    return new
```

Beautiful! Now that we have all we need, we can finally start simulating. We
want to simulate 6 generations, then stop and count alive cells. Since our
`cube` is just a set of coordinates of alive cells, to count the final number of
alive cells we can simply take its `len()` after the last evolution.

```python
for _ in range(6):
    cube = evolve(cube)

total_alive = len(cube)
print('Part 1:', total_alive)
```

Well, that was nice! Onto the second part.

### Part 2

For this second part... nothing changes, except that we now have *four*
dimensions.

Oh no! The code we wrote works with 3 dimensions, do we need to rewrite
everything? Well, not quite, the only function that would need to be updated is
`neighbors()`, since it takes exactly 3 arguments. We can make a small change to
generalize it to work with any dimension.

To generate neighbor coordinates, we would need to take an additional parameter
`w` for the fourth dimension, but since we want this to be general, taking a
tuple of `coords` instead is the way to go. For each coordinate `c` we will
create a tuple `(c - 1, c, c + 1)`, then pass all those tuples to
[`itertools.product()`][py-itertools-product] (we could even do this using
[`range()`][py-builtin-range], but for only three values we won't really see any
difference).

The new general function is literally just one more line than before:

```python
def neighbors(coords):
    ranges = ((c - 1, c, c + 1) for c in coords)
    yield from product(*ranges)
```

We also need to remove the [unpacking operator][py-unpacking] (`*`) when calling
the new `neighbors()` function since now it can take the entire tuple as one
argument:

```python
def alive_neighbors(cube, coords):
    alive  = sum(p in cube for p in neighbors(coords)) # changed *coords to coords
    alive -= coords in cube
    return alive

def all_neighbors(cube):
    return set(n for p in cube for n in neighbors(p)) # changed *p to p
```

The solution for part 1 stays the same since we did not touch `evolve()`, while
for part 2 all we have to do is create another cube with an additional
coordinate set to `0` for all initial points:

```python
hypercube = set()

for x, row in enumerate(grid):
    for y, cell in enumerate(row):
        if cell == '#':
            hypercube.add((x, y, 0, 0))
```

And then simply simulate again:

```python
for _ in range(6):
    hypercube = evolve(hypercube)

total_alive = len(hypercube)
print('Part 2:', total_alive)
```

What a nice puzzle!


Day 18 - Operation Order
------------------------

[Problem statement][d18-problem] — [Complete solution][d18-solution] — [Back to top][top]

### Part 1

Today's problem is about math, *but* a slightly different math than the one we
are used to!

The assignment is really simple: we are given a list of mathematical expressions
which only use natural numbers, parentheses (`()`), addition (`+`) and
multiplication (`*`). We need to evaluate each of the expressions giving the
same precedence to multiplication and addition. Parentheses are the only thing
that establishes precedence of operations. Once the results of all expressions
are calculated, we need to compute their sum.

You may have already noticed that ignoring the precedence of multiplication
(`*`) over addition (`+`) does not make this problem solvable with a simple
[`eval()`][py-builtin-eval]. While in normal math something like `1 + 2 * 3`
evaluates to `7`, ignoring the precedence of `*` over `+` the result is `9`
instead, because we first compute `1 + 2 = 3` and then `3 * 3 = 9`.

Since there is no precedence between operators, it's easy to solve an expression
which does not contain parentheses: just scan the expression and execute each
operation as soon as you encounter it, keeping the result in an accumulator.
Let's start getting to that point, and we'll see how to take into account
parentheses later.

First of all, let's write a very simple [tokenizer][wiki-lexical-analysis] to
extract numbers, parentheses and operators from each expression, and construct a
list of "tokens" that we'll use later for the actual evaluation.

Our expressions are pretty simple: we can use a single
[regular expression][misc-regexp] to match all tokens at once. We want to match:
numbers (`\d+`), parentheses (`(`, `)`) and operators (`+`, `*`), so a simple
pipe operator and a character class (`[]`) will suffice. We'll use
[`re.findall()`][py-re-findall] to extract all tokens at once.

```python
import re

def tokenize(expr):
    return re.findall(r'\d+|[+*()]', expr)

# tokenize('(1 + 2) * 3') -> ['(', '1', '+', '2', ')', '*', '3']
```

Now that we have tokens we can start by writing a simple evaluation function to
calculate the value of an expression without parentheses. For simplicity, before
passing the `list` returned by `tokenize()`, we'll turn it into a
[`deque`][py-collections-deque], so that we can just pop tokens from the start
of the `deque` without having to worry about indexing or iterating. For the
operations, we can import [`add`][py-operator-add] and [`mul`][py-operator-mul]
from the [`operator`][py-operator] module.

Our algorithm will do the following:

- Start with an `accumulator` initialized to `0`, and an operation `op`
  initialized to `add`.
- While we still have tokens, pop one at a time:
  - If the token is a number, convert it to `int`, then perform the operation
    stored in `op` between the `accumulator` and the value we just obtained,
    storing the result in `accumulator`.
  - If the token is a `+`, change `op` to `add`.
  - If the token is a `*`, change `op` to `mul`.
- Return the `accumulator` which now contains the result of the expression.

To check if a token is a number (of one or more decimal digits) we can use
[`str.isdigit()`][py-str-isdigit]. Here's the code:

```python
def evaluate(tokens):
    accumulator = 0
    op = add

    while tokens:
        tok = tokens.popleft()

        if tok.isdigit():
            val = int(tok)
            accumulator = op(accumulator, val)
        elif tok == '+':
            op = add
        elif tok == '*':
            op = mul

    return accumulator
```

Now we also need to account for parentheses. If we think about it for a second,
a sub-expression enclosed in parentheses is not different from a normal
expression. Whenever we encounter an open parenthesis (`(`) we can make a
recursive call to our function and let it calculate the value of the
sub-expression, then perform the needed operation like we do for normal numbers.
Whenever we encounter a closed parenthesis (`)`) we can just assume that we need
to return a value to the caller because we were called to solve a
sub-expression.

In terms of code, this translates into two additional `elif` branches:

```python
def evaluate(tokens):
    accumulator = 0
    op = add

    while tokens:
        tok = tokens.popleft()

        if tok.isdigit():
            val = int(tok)
            accumulator = op(accumulator, val)
        elif tok == '+':
            op = add
        elif tok == '*':
            op = mul
        elif tok == '(':
            val = evaluate(tokens)
            accumulator = op(accumulator, val)
        elif tok == ')':
            break

    return accumulator
```

Now we can use our tokenizer to turn each expression in the input into a list of
tokens, then turn it into a `deque` and finally pass it to the `evaluate()`
function we just wrote. We can use [`map()`][py-builtin-map] to conveniently
tokenize all input lines in one go.

```python
fin = open(...)
exprs = map(tokenize, fin)

total = 0
for expr in exprs:
    total += evaluate(deque(expr))
```

The above loop can be further simplified with the help of
[`sum()`][py-builtin-sum] down to a single line:

```python
exprs = map(tokenize, fin)
total = sum(map(evaluate, map(deque, exprs)))

print('Part 1:', total)
```

And sure enough we get a ridicolously high number which is our solution.

### Part 2

For the second part of the problem, we still need to calculate the sum of all
the results of the input expressions, but this time we want `+` to have
precedence over `*`. That's right, it's exactly the opposite you would normally
do to solve an expression. For example, now `1 * 2 + 3` evaluates to `5`,
because we first need to compute `2 + 3 = 5`, and then `1 * 5 = 5`.

Okay, this isn't that simple anymore. There are different ways to solve the
problem, and three main approaches that I know of (of which we're going to use
the third):

1. The textbook approach: building a simple expression evaluator using the
   [Shunting-yard algorithm][wiki-shunting-yard] to turn the expressions from
   [infix notation][wiki-infix-notation] to
   [postfix notation][wiki-postfix-notation] (also called reverse-polish
   notation), which makes them very easy to evaluate using a simple stack later.

   This is the most complex yet most general approach, which can be used to
   calculate almost any kind of mathematical expression, using any order of
   precedence for the operators. I'm not going to use it here, but I've
   nonetheless written an alternative solution which does exactly this just for
   fun. You can find it [**here**][d18-alternative-1] if you are interested.

2. The hacker's approach: exploit the ability of defining Python classes with
   customized methods for basic operators such as `+` and `*`.

   Build a custom class `K` implementing an [`__add__`][py-object-add] method
   which actually computes the product, and a [`__mul__`][py-object-mul] method
   which computes the sum. Then, replace each number `N` in the expression with
   an instantiation of the class (`K(N)`) and swap each `+` with a `*` (and
   vice-versa). Finally, let Python take care of operator precedence and
   evaluate the whole thing using `eval()`, which will give precedence to `*`,
   which will in turn be treated as a `+` by our custom class. This can also be
   applied to part 1 swapping each `*` with a `-` and implementing a custom
   [`__sub__`][py-object-sub] operator.

   This is a... pretty interesting approach which I've seen used by a lot of
   people on the daily Reddit solution thread, but it feels a little bit like
   cheating. Nonetheless, you guessed it: I've implemented this too because it
   was just too fun of an idea (and also really the simplest solution in terms
   of actual code). You can find this solution [**here**][d18-alternative-2] if
   you are interested.

3. The "smart" solution: realize that we can apply the
   [distributive property][wiki-distributive-property] to solve everything in a
   single scan, similarly to what we did for part 1. This is the approach I'll
   be using and describing now.

Let's again think for a moment about what we should do if we had to evaluate the
an expression without parentheses. We have an expression that is only composed
of additions and multiplications, and additions have precedence over
multiplications, for example:

```
1 * 2 * 3 + 4    (should evaluate to 2 * 7 = 21)
```

It seems pretty clear that if it weren't for the `+` in there, we could still
use the same approach as we did before. Just continue multiplying values
together accumulating the resulting value. A problem however arises when we
encounter an addition: we must stop blindly multiplying and solve that first
before continuing.

If we find a way to "pre-calculate" all additions and replace them with their
result, then we can just calculate the product of everything. This seems
reasonable, but isn't *that simple*, as it involves scanning the entire
expression back and forth.

However, we can take advantage of the
[distributive property][wiki-distributive-property] of multiplication. In
"normal" math, we can *distribute* a multiplication over multiple terms of a sum
if those terms are enclosed in parentheses:

```
2 * (3 + 4 + 5) = (2 * 3) + (2 * 4) + (2 * 5) = 24
```

In our case, since the addition has precedence over the multiplication, we can
also do the same thing even when the terms of the sum are *not* enclosed in
parentheses:

```
2 * 3 + 4 + 5 = (2 * 3) + (2 * 4) + (2 * 5) = 24
```

If we have more terms to multiply before encountering a series of sums, the
result is similar:

```
  2 * 3 * 4 + 5 = (2 * 3 * 4) + (2 * 3 * 5) =
=   6   * 4 + 5 = (  6   * 4) + (  6   * 5) = 54
```

We can perform distribution of all the multiplications by keeping a "multiplier"
value and use it to multiply every value we encounter in our way, adding the
result into an accumulator. Updating this multiplier value in a smart way will
get us to the solution.

The algorithm is the following:

- Start with `multiplier = 1` and `accumulator = 0`.
- While we still have tokens, pop one at a time:
  - If the token is a number, multiply it with the `multiplier` and add the
    result to the `accumulator`.
  - If the token is a `*`, set the `multiplier` to the value of the
    `accumulator`, and reset the `accumulator` to `0`.
  - If the token is a `+`, simply ignore it.
- Return the `accumulator` which contains the result of the expression.

Doing this, we are "pausing" multiplication unless we encounter `*` operators,
updating the `multiplier` in the meantime. This effectively distributes the
multiplication over every single operand of any addition, even at the beginning
when we start with `multiplier = 1` (which does nothing).

To make it simpler to understand, here's an example:

```
Expression to evaluate: 2 * 3 + 1 * 5 * 6 + 1 + 3   (expected result: 400)

TOKEN   MULT   ACC   Operation performed
         1      0
  2      1      2    ACC += 2 * 1
  *      2      0    MULT = ACC; ACC = 0
  3      2      6    ACC += 3 * 2
  +      2      6
  1      2      8    ACC += 1 * 2
  *      8      0    MULT = ACC; ACC = 0
  5      8     40    ACC += 5 * 8
  *     40      0    MULT = ACC; ACC = 0
  6     40    240    ACC += 6 * 40
  +     40    240
  1     40    280    ACC += 1 * 40
  +     40    280
  3     40    400    ACC += 3 * 40
```

Turning the above algorithm into Python code, we have:

```python
def evaluate2(tokens):
    multiplier  = 1
    accumulator = 0

    while tokens:
        tok = tokens.popleft()

        if tok.isdigit():
            val = int(tok)
            accumulator += val * multiplier
        elif tok == '*':
            multiplier  = accumulator
            accumulator = 0

    return accumulator
```

Now to also account for sub-expressions inside parentheses (`()`) we can do the
exact same thing we did for part 1: do a recursive call when we encounter an
open parenthesis, and return immediately when we encounter a closed one.

```python
def evaluate2(tokens):
    multiplier  = 1
    accumulator = 0

    while tokens:
        tok = tokens.popleft()

        if tok.isdigit():
            val = int(tok)
            accumulator += val * multiplier
        elif tok == '*':
            multiplier  = accumulator
            accumulator = 0
        elif tok == '(':
            val = evaluate2(tokens)
            accumulator += val * multiplier
        elif tok == ')':
            break

    return accumulator
```

Sweet as pie. We can now calculate the solution again exactly how we did for
part 1:

```python
total = sum(map(evaluate2, map(deque, exprs)))
print('Part 2:', total)
```

If we want, we can further simplify this turning the two functions for part 1
and part 2 into a single one, deciding which strategy to apply using an
additional argument and a couple more `if` statements. This is what I did in my
complete solution for today's problem.


Day 19 - Monster Messages
-------------------------

[Problem statement][d19-problem] — [Complete solution][d19-solution] — [Back to top][top]

### Part 1

Do you like regular expressions? I really do, the art of writing regular
expressions to automate simple tasks is really useful when programming and
processing data. Today's problem is about regular *and not-so-regular*
expressions.

Let's get straight to the point. Our input is split in two parts by an empty
line: the second part is a list of messages that are strings which are only
composed of the letters `a` and `b`, and which we need to match according to the
list of rules defined in the first part of the input.

The rules are as follows (each uppercase letter here represent a rule ID, which
is a number uniquely identifying a rule):

1. `X: A B C ...` - match one or more rules in the exact given order.
2. `X: A B | C D` - match either the first list of rules in the given order, or
   the second one (always in the given order).
3. `X: "a"` or `X: "b"` - match the character `a` or `b` respectively.

Our task is to figure out how many of the messages are matched by the rule `0`.
The messages need to be matched entirely, that is, we need to match every single
character of a message for it to be considered as matched.

To give an example, suppose we have the following rules:

```
0: 1 2 | 1 3
1: "a"
2: "b"
3: 2 1
```

The first option of rule `0` here means *"match rule `1` followed by rule `2`"*.
If we look at those, this translates to *"match `a` followed by `b`"*, so rule
`0` would match the message `ab`.

The second option of rule `0` means *"match rule `1` followed by rule `3`"*, and
if we look at rule `3` it means *"match rule `2` followed by rule `1`"*. Rules
`1` and `2` match `a` and `b` respectively, therefore this second option of rule
`0` means *"match `a` followed by `b` followed by `a`"*. Hence, rule `0` would
also match the message `aba`.

Any other message (e.g. `a`, `aa`, `bb`, `abb`, `abab`, etc.) would not be
matched by rule `0`.

The input we are given looks very much like a huge
[regular expression][misc-regexp] which has been parsed into some kind of
[tree][wiki-tree] of rules. This is
**assuming that there are no cycles in the given rules** (e.g. `1: 2 1`), which
is true for our input.

If we draw a diagram of the above example, we get the following:

```
      (0)
     /   \
    /     \
(1  2)    (1  3)
 |  |      |   \
 a  b      a    \
                (2  1)
                 |  |
                 b  a
```

Now it's simple to see the tree, and even simpler to see which strings can be
matched by the rule.

As I mentioned earlier, it looks like this has something to do with regular
expressions. Indeed, following the rules outlined by the input is equivalent to
matching a huge regular expression which only uses capture
[groups][misc-regexp-group] (i.e. parentheses `()`) and
[alternations][misc-regexp-pipe] (i.e. pipes `|`). Turning the above example
into a regular expression using only those two special operators is simple
enough: `^(ab|aba)$`. The `^` and `$` are [anchors][misc-regexp-pipe] used to
match the start and the end of the string respectively (writing just `(ab|aba)`
would match anything starting with `ab` or `aba`).

If we find a nice way to turn the tree of rules we have into a regular
expression, we can then just let [`re.match()`][py-re-match] match the messages
and do the job for us.

First of all, let's parse the input into a tree structure. We can use a simple
dictionary for this, where each key is the ID of a rule, containing either a
list of tuples (the various options) or a single character to match
(`'a'` or `'b'`).

Input parsing is kind of convoluted, so let's write a function for it. We'll
iterate over the input line by line, stopping when we encounter the empty line
which separates rules and messages. For each line we'll get the rule ID and its
content, splitting on `: `. Then, if the rule contains a `"`, we'll simply
extract the character to match from it, otherwise we'll split the rule again on
`|` to get a list of options, then [`map()`][py-builtin-map] each option
(consisting of multiple rule IDs) into a `tuple` of `int`, storing all the
tuples in a list. Finally, we'll store everything into a dictionary, which will
have the form `{rule_id: [(id1, id2, ...), (id3, id4, ...), ...]}` (and for the
final rules `{rule_id: 'a'}`).

```python
def parse_input(fin):
    rules = {}

    for line in map(str.rstrip, fin):
        if not line:
            break

        rule_id, options = line.split(': ')
        rule_id = int(rule_id)

        if '"' in options:
            rule = options[1:-1]
        else:
            rule = []
            for option in options.split('|'):
                rule.append(tuple(map(int, option.split())))

        rules[rule_id] = rule

    return rules
```

[Cool, cool, cool, cool, coool][misc-cool]. Now to the actual program: in order
to turn the whole tree of rules into a regular expression, we'll write a
recursive solution. If we think about it for one second, it's quite simple:

1. If a rule is a "final" rule, that is `rules[rule_id]` is a string (`'a'` or
   `'b'`), then the corresponding regular expression is just the rule itself.
2. Otherwise, the regular expression we need to compose is a capturing group
   `(...)` of multiple options separated by `|`, where each options is the
   concatenation of the regular expressions of each of the rules in the option.

Applying the above idea, it's only a matter of [joining][py-str-join] strings in
the right way:

```python
def build_regexp(rules, rule=0):
    rule = rules[rule]
    if type(rule) is str:
        return rule

    options = []
    for option in rule:
        option = ''
        for sub_rule in option:
            option += build_regexp(rules, rule)
        options.append(option)

    return '(' + '|'.join(options) + ')'
```

We can further simplify the inner loop above using a
[generator expression][py-generator-expr]:

```python
    # ...
    options = []
    for option in rule:
        option = ''.join(build_regexp(rules, r) for r in option)
        options.append(option)
    # ...
```

We could also go further and compress the entire block of code above into a
single line, but let's stop here before it becomes unreadable (ok, fine, you
really wanna know? Here you go:
`options = map(''.join, (map(partial(build_regexp, rules), o) for o in rule))`).

Now we can finally parse the input file to build the `rules` tree, then use it
to build and [`compile()`][py-re-compile] a regular expression (adding the two
anchors `^` and `$` to only match whole strings), and then use that expression
to [`match()`][py-re-match] every single message.

```python
import re

fin   = open(...)
rules = parse_input(fin)
rexp  = re.compile('^' + build_regexp(rules) + '$')
valid = 0

for msg in map(str.rstrip, fin):
    if rexp.match(msg):
        valid += 1
```

Well, that's just a "if x then increment" kind of loop, we can really turn it
into a single line using [`sum()`][py-builtin-sum] and
[`map()`][py-builtin-map]. We need to convert matches to `True` or `False`
though, as `re.match()` returns a `match` object if the match is successful: we
can simply use [`bool()`][py-builtin-bool] for that.

```python
valid = sum(map(bool, map(rexp.match, map(str.rstrip, fin))))
print('Part 1:', valid)
```

### Part 2

The task is the same as part 1, but we need to modify two of the rules we have.
In particular, rule `8` becomes `8: 42 | 42 8`, and rule `11` becomes
`11: 42 31 | 42 11 31`.

Whelp, now we've got a problem! Remember when in part 1 I said:
***"assuming that there are no cycles in the given rules"***? Well, that's not
the case anymore now! The two new rules do actually include cycles! So we cannot
simply generate a regular expression out of them using our previous function.

There are three main alternative solutions here:

1. [The "hacky" solution](#part-2---hacky-solution): still solve this using
   Python's regular expressions only, in a way similar to what we did for the
   first part. This can be done because it's actually possible to turn the two
   new recursive rules into (rather ugly) regular expressions after noticing a
   couple of properties. This is not the solution I've used, but it's
   nonetheless funny enough that I wrote an alternative solution using this
   approach, which you can find [**here**][d19-alternative].

2. [The "real" solution](#part-2---real-solution): write a matching function
   capable of matching messages given a tree of rules. This is basically like
   building a limited expression engine capable of handling a very limited
   subset of regular expressions *plus* recursive rules. This is the most
   optimal and general solution, which is the one I linked as the complete clean
   solution for today's problem.

3. The "lazy" solution: use a third party regular expression library/engine
   which is capable of handling recursive rules (like the 3rd party
   [`regex`][misc-regex-module] module).

I will now explain both alternative 1 and 2 in detail, while I will not discuss
the third solution as I don't find it interesting. Feel free to skip to your
favorite using the above links.

### Part 2 - Hacky solution

We can understand the high-level meaning of the new rules by taking them apart.
Let's look at them in detail:

- `8: 42 | 42 8`: this means that rule `8` can either directly translate to rule
  `42`, or to rule `42` followed by rule `8` again. To make it simpler to
  understand, let's imagine that rule `42` is just `"a"`. In such case, rule `8`
  would be equivalent to: `8: "a" | "a" 8`, meaning that we can match one `a`
  followed by an arbitrary amount of `a`, or in other words *one or more `a`*.

  This rule *can* actually be expressed through a regular expression using the
  `+` operator: convert whatever rule `42` is into its regexp, then simply wrap
  it in parentheses `()` and add a `+`, like this: `(<rule_42_regexp>)+`.

- `11: 42 31 | 42 11 31`: this... is not as simple. Translating it again using
  letters to make it easier it becomes: `11: "a" "b" | "a" 11 "b"`. This is
  *similar* to the previous rule, except that in the second option the recursion
  happens in the middle of `a` and `b`. This means "match `ab`, or `a` and `b`
  with something in the middle", where that "something in the middle" is again
  either `ab` or `a` and `b` with something in the middle... What this ends up
  translating to is:
  *"match one or more `a` followed by **the same amount** of `b`"*.

  This rule is a bit of a problem! Regular expressions are not powerful enough
  to count and *remember* the number of previously matched characters. However,
  we can get around the issue by abusing the fact that we are in reality only
  dealing with a limited set of messages, of which we know the maximum possible
  length. We can therefore translate rule `42` and rule `31` into their
  respective regexps, then construct a big capture group with a sequence of
  pipe-delimited options with a number of repetitions from 1 up to half the
  maximum length of a message.

  For example (using `a` for rule `42` and `b` for rule `31` for simplicity), if
  our maximum message length was 16 characters, we could translate rule `11`
  into the following regexp:

  ```
  (ab|aabb|aaabbb|aaaabbbb|aaaaabbbbb|aaaaaabbbbbb|aaaaaaabbbbbbb|aaaaaaaabbbbbbbb)
  ```

  Or a little bit more concisely, using curly brackets `{}` for
  [repetition][misc-regexp-repetition]:

  ```
  (a{1}b{1}|a{2}b{2}|a{3}b{3}|a{4}b{4}|a{5}b{5}|a{6}b{6}|a{7}b{7}|a{8}b{8})
  ```

We'll create a new function copying the `build_regexp()` function we wrote for
part 1, adding the two special cases mentioned above for rules `8` and `11`. For
rule `8`, we'll simply build the regexp for rule `42` and then wrap it around
parentheses adding a `+`. For rule `11`, we'll build the regexps for rule `42`
and `31`, then build a huge capture group joining together every possible number
of repetitions from 1 to 40 (our maximum message length seems to be 80). We'll
use [`str.format()`][py-str-format] for this.

```python

def build_regexp_special(rules, rule=0):
    if rule == 8:
        return '(' + build_regexp_special(rules, 42) + ')+'

    if rule == 11:
        a = build_regexp_special(rules, 42)
        b = build_regexp_special(rules, 31)

        options = []
        for n in range(1, 40):
            options.append('{a}{{{n}}}{b}{{{n}}}'.format(a=a, b=b, n=n))

        return '(' + '|'.join(options) + ')'

    rule = rules[rule]
    if type(rule) is str:
        return rule

    options = []
    for option in rule:
        option = ''.join(build_regexp_special(rules, r) for r in option)
        options.append(option)

    return '(' + '|'.join(options) + ')'
```

The above function will generate a rather long and extremely complex regular
expression (75869 characters for my input!), so Python's regular expression
engine will not exactly be thrilled to run it... and indeed it will be very slow
when matching. In any case, it's fun and also probably the "simplest" solution
to write using vanilla Python 3.

Now we can do the exact same thing we did in part 1, building, compiling and
then using the new regexp. We can actually also check each message for both part
1 and part 2 regular expressions in the same loop.

```python
rules  = parse_input(fin)
rexp1  = re.compile('^' + build_regexp(rules) + '$')
rexp2  = re.compile('^' + build_regexp_special(rules) + '$')
valid1 = 0
valid2 = 0

for msg in map(str.rstrip, fin):
    if rexp1.match(msg):
        valid1 += 1
    if rexp2.match(msg):
        valid2 += 1

print('Part 1:', valid1)
print('Part 2:', valid2)
```

You can find a complete solution using this approach
[**here**][d19-alternative], but as I said this is not the one I ended up using,
so let's continue on with the *real* solution.

### Part 2 - Real solution

We need to stop taking shortcuts and build a real matching function. How can we
do it? A straightforward way to define such a function would be to take 4
parameters: the tree of rules, the string to match, the current rule and an
index in the string to start matching from. As per the return value, it will be
a list of indexes from which the matching should continue.

As I explained at the very beginning of [part 1](#part-1-18), we have three main
kind of rules which at this point we should already be familiar with. Let's
analyze them further and see how each of them can be translated if we want to
write such a matching function.

1. `X: "a"` or `X: "b"` - this is the simplest kind of rule: match a single
   character literally. If the type of the rule we are matching is a string,
   we'll simply return either 1 or zero indexes: the current index plus 1 if the
   character matches, and an empty list otherwise.

2. `X: A B C ...` - a rule which only consists of a single option of multiple
   other rules to match in order. We'll need to make one recursive call for each
   rule in the option, starting to match from the current index we have, and
   accumulating all possible indexes where to continue from for each recursive
   call, passing them on to the next one, then return those.

   As an example, assume we want to match the rule `X: A B C` and we are called
   with index `1`. We will make the following recursive calls, in order
   (omitting the first two arguments which are always the same for simplicity):

   - `match(A, 1)`: assume this returns `[2]`. We can then continue matching
     rule `B` from index `2`.
   - `match(B, 2)`: assume this returns `[3, 4, 7]`. We can now continue
     matching rule `C`, but be careful, we need to try and continue matching
     from all possible indexes returned, so we'll make one call for each:
     - `match(C, 3) -> [5]`
     - `match(C, 4) -> []` (matching failed)
     - `match(C, 7) -> [8, 11]`

   Finally, the result we would return is `[5, 8, 11]`, indicating we can
   continue matching from any of those indexes of the string onward.

3. `X: A B | C D` - this is actually the same as the previous case, but since we
   have multiple options we'll have to do the same thing one time per option,
   accumulating all indexes returned by each of the options. We can just use a
   `for` loop for this. Actually, we can simply "join" this and the previous
   case together and use a loop regardless, given that the rule tree we build
   will have a list of options (tuples of other rules) regardless.

Putting the above in terms of code, with the help of some comments, we have:

```python
def match(rules, string, rule=0, index=0):
    # If we are past the end of the string, we can't match anything anymore
    if index >= len(string):
        return []

    # If the current rule is a simple character, match that literally
    rule = rules[rule]
    if type(rule) is str:
        # If it matches, advance 1 and return this information to the caller
        if string[index] == rule:
            return [index + 1]
        # Otherwise fail, we cannot continue matching
        return []

    # If we get here, we are in the case `X: A B | C D`
    matches = []

    # For each option
    for option in rule:
        # Start matching from the current position
        sub_matches = [index]

        # For any rule of this option
        for sub_rule in option:
            # Get all resulting positions after matching this rule from any of the
            # possible positions we have so far.
            new_matches = []
            for idx in sub_matches:
                new_matches += match(rules, string, sub_rule, idx)

            # Keep the new positions and continue with the next rule, trying to match all of them
            sub_matches = new_matches

        # Collect all possible matches for the current option and add them to the final result
        matches += sub_matches

    # Return all possible final indexes after matching this rule
    return matches
```

The function we just wrote is a general solution which is also capable of
correctly handling recursive rules. We cannot fall into infinite recursion from
recursive rules because a rule can either (1) not match, returning an empty list
(in this case we'll stop there), or (2) match and *advance* the current index
returning one or more indexes (greater than the current). If a recursive rule
keeps matching, we'll advance each time and eventually reach the end of the
string, stopping if we get past it.

Now how do we check if a message is a positive match? Simple, just call the
above function and see if any of the returned indexes is *exactly* equal to the
length of the message: this means that at least one path of rules in the tree
matched all characters of the message, and returned the length of the entire
message after matching the last index.

We can use the above function to solve both parts (this is what I do in my
complete solution linked [at the beginning][d19] of today's walkthrough). The
only thing we need to do first is make sure that we build two different rule
trees, manually modifying rule `8` and `11` of the second one replacing them
with the new ones given in the problem statement. We can do this easily using
[`deepcopy()`][py-copy-deepcopy] to clone the initial rules, and then modify
those two.

```python
from copy import deepcopy

fin = open(...)

rules1 = parse_input(fin)
rules2 = deepcopy(rules1)
rules2[8]  = [(42,), (42, 8)]
rules2[11] = [(42, 31), (42, 11, 31)]
valid1 = 0
valid2 = 0

for msg in map(str.rstrip, fin):
    if len(msg) in match(rules1, msg):
        valid1 += 1
    if len(msg) in match(rules2, msg):
        valid2 += 1

print('Part 1:', valid1)
print('Part 2:', valid2)
```

You will still like regular expressions after today right? Right? I never
stopped loving them... I mean... as long as they are *simple enough!*


Day 20 - Jurassic Jigsaw
------------------------

[Problem statement][d20-problem] — [Complete solution][d20-solution] — [Back to top][top]

### Part 1

Today's puzzle is a literal puzzle, a jigsaw puzzle to be precise. Strap in
because this is going to get wild. I'd recommend reading the problem statement
linked above before continuing, in order to better understand what we're dealing
with.

We are given a list of ASCII-art tiles as input. Each tile is a little grid of
10x10 characters and has an unique ID. We are told that these tiles compose a
larger square image (we have 144 tiles, so the image is going to be 12x12
tiles).

The tiles we are given are in no particular order, and are also randomly flipped
and rotated. The only thing that we know is that tiles which are supposed to be
next to each other in the final image have matching edges, and the edge of each
tile only matches exactly one other tile.

For the first part of the problem we need to identify the four corner tiles of
the image and calculate the product of their IDs.

We're gonna write a lot of code, so better start using functions. The very first
thing to do is of course parsing the input. Simple enough, there's one empty
line between tiles, so we can split the input on a double newline (`\n\n`), then
take the ID from the first line of each tile and the actual character grid from
the others. I'll build a dictionary `{id: tile}`, where `tile` is a grid of
characters (`list` of strings). I'll use [`map()`][py-builtin-map] to split each
tile in lines through [`str.splitlines()`][py-str-splitlines], then simply
iterate over those.

```python
def parse_input(fin):
    raw_tiles = fin.read().rstrip().split('\n\n')
    raw_tiles = map(str.splitlines, raw_tiles)
    tiles = {}

    for t in raw_tiles:
        tid = int(t[0][5:-1])
        tiles[tid] = t[1:]

    return tiles

fin = open(...)
tiles = parse_input(fin)
```

A function to extract an edge given a tile and a side (north, south, east, west)
would be really useful. It will simply take two parameters: tile and side. Based
on the side, we'll iterate over all the characters of the corresponding edge and
return a string. For north and south it's straightforward, we already have the
string as a row of the tile. For east or west we need to join together all
characters of the first or last column respectively.

```python
def edge(matrix, side):
    if side == 'n':
        return matrix[0] # north == first row
    if side == 's':
        return matrix[-1] # south == last row

    res = ''
    if side == 'e':
        for row in matrix:
            res += row[-1] # east == last column
    else:
        # 'w'
        for row in matrix:
            res += row[0] # east == first column

    return res
```

The above function can be simplified further taking advantage of
[`operator.itemgetter()`][py-operator-itemgetter] to extract all characters with
a single `map()`:

```python
from operator import itemgetter

def edge(matrix, side):
    if side == 'n':
        return matrix[0]
    if side == 's':
        return matrix[-1]
    if side == 'e':
        return ''.join(map(itemgetter(-1), matrix))
    # 'w'
    return ''.join(map(itemgetter(0), matrix))
```

Now that we have a dictionary of tiles and a function to extract edges, we can
start matching them together based on their edges. If we count the number of
matching sides for each tile, we can easily distinguish between three different
kinds of tiles:

- Corner tiles: the ones we are actually looking for. These will only have two
  matching tiles, since two of their sides will compose the outer border of the
  image.
- Side tiles: tiles that are on an edge, but are not corner tiles. These will
  match exactly 3 other tiles, since one side is on the outside border of the
  image.
- Center tiles: tiles that are not on an edge and will therefore have a tile
  connected to each of their edges, matching exactly 4 other tiles.

It's easy to notice the above with a simple drawing:

```
+---+---+---+
| 1 | 2 | 3 |
+---+---+---+   Corner tiles: 1, 3, 7, 9
| 4 | 5 | 6 |   Side tiles  : 2, 4, 6, 8
+---+---+---+   Center tiles: 5
| 7 | 8 | 9 |
+---+---+---+
```

In order to do the matching, we can look at every possible pair of tiles, and
for each pair check if any two edges match. It's important to remember that
tiles can be in any orientation and could even be flipped. Trying to match each
pair of edges for every couple of tiles we are already taking into account
different orientations, but we also need to take into account flipping. We can
do this by also checking if pairs of edges match when either one is flipped
(i.e. the string representing it is reversed).

The function we're going to write takes our `tiles` dictionary as only
parameter, and spits out a list of corner IDs as result. To track the number of
matches per tile, we'll use a [`defaultdict`][py-collections-defaultdict] of
integers (which simplifies the addition of new items). In order to iterate over
all possible pairs of different tiles we'll use the very handy
[`combinations()`][py-itertools-combinations] from the
[`itertools`][py-itertools] module.

```python
from collections import defaultdict
from itertools import combinations

def match_tiles(tiles):
    matching_sides = defaultdict(int)
    corners = []

    # For every pair of distinct tiles
    for id_a, id_b in combinations(tiles, 2):
        a, b = tiles[id_a], tiles[id_b]

        # For each possible pair of sides
        for side_a in 'nsew':
            for side_b in 'nsew':
                # Extract the edges correspoinding to these sides
                edge_a, edge_b = edge(a, side_a), edge(b, side_b)

                # Check if they match
                if edge_a == edge_b or edge_a == edge_b[::-1]:
                    matching_sides[id_a] += 1
                    matching_sides[id_b] += 1

    # Find the corner tiles by checking tiles that only match two other tiles
    for tid, n_sides in matching_sides.items():
        if n_sides == 2:
            corners.append(tid)

    assert len(corners) == 4 # Sanity check
    return corners
```

Now we can just call the above function and get our answer using
[`math.prod()`][py-math-prod] to easily compute the product of the returned list
of corner IDs:

```python
corners = match_tiles(tiles)
ans = prod(corners)
print('Part 1:', ans)
```

Well, that was easy. Now comes the fun part...

### Part 2

For this second part we actually need to reconstruct the whole image. This means
solving the jigsaw puzzle of tiles, rotating and flipping each one of them until
all of them match together.

After all tiles are matched, we need to strip away their outermost edges (the
ones that we used to match them together). The resulting tiles will be 8x8, and
will constitute the final image. Once we have the final image, we need to find
and count the number of times a specific pattern appears.

The pattern we need to count is the one of a "sea monster":

```
                  #
#    ##    ##    ###
 #  #  #  #  #  #
```

Each `#` in the pattern must match a `#` in the image, while spaces can be
ignored. Important detail: we don't know which way the final image should be
oriented/flipped. We must check each orientation of each side until we find the
right one containing sea monsters.

After counting the number of sea monsters in the final image, we need to
calculate the "water roughness" of the sea, which corresponds to the number of
`#` that are *not* part of any sea monster.

This is not a simple task. Well, it's not complicated either, it's just a really
tedious process. We need to master the art of tile manipulation in order to go
through all the steps needed to recompose the image without mistakes, which are
pretty easy to make in such a scenario.

The first thing to notice is that we cannot really say which corner tile should
go where since the tiles are arbitrarily rotated/flipped. It's not a problem
though, we can just pick any of the corner tiles we found earlier, and then
start matching one tile after the other, matching one edge at a time.

We'll start by picking an arbitrary top left corner tile, and then rotate it
until the two matching edges are on the right (east) and bottom (south). This
way, the tile will be in the correct position, and we can start attaching tiles
to either of the two edges. In order to know how many times we need to rotate
the top left tile we need to first know which on which sides we matched it.
Let's modify the `match_tiles()` function defined in part 1 to also return the
matching sides for the corner tiles, the only real change is turning the
`matching_sides` dictionary into a `defaultdict` of strings instead of integers.

```python
def match_tiles(tiles):
    matching_sides = defaultdict(str) # changed
    corners = {}                      # changed

    for id_a, id_b in combinations(tiles, 2):
        a, b = tiles[id_a], tiles[id_b]

        for side_a in 'nsew':
            for side_b in 'nsew':
                edge_a, edge_b = edge(a, side_a), edge(b, side_b)

                if edge_a == edge_b or edge_a == edge_b[::-1]:
                    matching_sides[id_a] += side_a  # changed
                    matching_sides[id_b] += side_b  # changed

    for tid, sides in matching_sides.items():
        if len(sides) == 2:      # changed
            corners[tid] = sides # changed

    assert len(corners) == 4
    return corners

corners = match_tiles(tiles)
# Something like: {1453: 'nw', 2897: 'nw', 1439: 'se', 2477: 'sw'}
```

In order to rotate a tile 90 degrees, we can write a simple helper function.
Rotating 90 degrees clockwise can be done by iterating over each column from the
bottom and turning it into a string, appending it to a new tile as a row.

```python
# A A A    C B A
# B B B -> C B A
# C C C    C B A

def rotate90(tile):
    new = []
    for c in range(len(tile[0])):
        new_row = ''
        for row in tile[::-1]: # rows in reverse order
            new_row += row[c]
        new.append(new_row)

    return new
```

The above can then be simplified using [`str.join`][py-str-join] and a
[generator expression][py-generator-expr]:

```python
def rotate90(tile):
    new = []
    for c in range(len(tile[0])):
        new_row = ''.join(row[c] for row in tile)[::-1]
        new.append(new_row)
    return new
```

And even more exploiting the [`zip()`][py-builtin-zip] function along with
[unpacking][py-unpacking] as a way to easily iterate over all characters of each
row at once:

```python
def rotate90(matrix):
    return tuple(''.join(reversed(x)) for x in zip(*matrix))
```

Now let's take an arbitrary top-left corner, and rotate it until the two
matching edges are south and east (we technically could already have one that is
correctly oriented (e.g. `1439` in the code above), but we want to write a
general solution.

```python
top_left_id, matching_sides = corners.popitem()
top_left = tiles[top_left_id]

if matching_sides in ('ne', 'en'):   # North & East edges match other tiles, rotate 90 degrees clockwise
    top_left = rotate90(top_left)
elif matching_sides in ('nw', 'wn'): # North & West edges match other tiles, rotate 180 degrees clockwise
    top_left = rotate90(rotate90(top_left))
elif matching_sides in ('sw', 'ws'): # South & West edges match other tiles, rotate 270 degrees clockwise
    top_left = rotate90(rotate90(rotate90(top_left)))
```

We could have also written specific functions to rotate a tile more than 90
degrees, but this is the only time we'll need to do more than one 90 degree
rotation at once, so it's no issue.

Now the top-left corner tile is oriented in the right direction, and we can
start thinking about matching other tiles on its east and south edges.


Let's calculate the dimensions (in tiles) of the final image (yes, we already
know it should be 12x12 tiles, but let's not "cheat" and determine it from the
input instead). Since the image is a square, we can calculate the square root of
the number of tiles to know its dimension. The [power operator][py-power] (`**`)
in Python can be used to compute roots by providing exponents smaller than `1`.

```python
image_dimension = int(len(tiles) ** 0.5)
```

Now onto the real task: building the image. First and foremost, in order to find
a tile to match one edge of the top-left corner (or to match any other tile
really), we must have a way of rotating and flipping tiles in each of the
*eight* possible arrangements:

```
A X   B A   X B   X X
B X   X X   X A   A B

B X   X X   X A   A B
A X   B A   X B   X X
```

We already wrote `rotate90()`, now we only need a function to flip a tile.
Well... flipping vertically is really just reversing the `tuple`/`list`
representing a tile, and this can just be done through [slicing][py-slice]
(`[::-1]`). To compute all the possible arrangements of a tile we can just
rotate it around, then flip it, and rotate it around again. Let's write a couple
of generator functions for this. It's always satisfying to find an use case for
the [`yeild from`][py-yield-from] syntax.

```python
def orientations(tile):
    yield tile
    for _ in range(3):
        tile = rotate90(tile)
        yield tile

def arrangements(tile):
    yield from orientations(tile)
    yield from orientations(tile[::-1])
```

Now we can write a function that finds a matching tile given a tile, a set of
tiles to choose from, and the two desired sides to match. We can use the
previously written `edge()` function to extract the first edge from the tile we
want to match, then iterate over each one of the tiles in the given set,
arranging them in every possible way, extracting the second edge each time,
until we find a match.

```python
def matching_tile(tile, tiles, side_a, side_b):
    prev_side = edge(tile, side_a)

    # Iterate over all possible tiles
    for other_id, other in tiles.items():
        if tile is other:
            continue

        # Arrange second tile in any possible way
        for other in arrangements(other):
            # Until the two sides match
            if prev_side == edge(other, side_b):
                tiles.pop(other_id)
                return other

# matching_tile(x, tiles, 'e', 'w') -> tile whose west edge matches x's east edge
```

The tile returned by the above function will already be oriented and flipped in
the correct way. This function also pops the matched tile out of the given
dictionary of tiles, so that we don't even need to worry about it.

Now that we have a way of matching arbitrary tiles, we can write a function
which finds all matching tiles of an entire row of the image. It's pretty simple
using the above function. We'll take the first row tile as parameter and then
keep matching tiles on the east edge of the last one. I'll write this as a
generator function to make it lighter since we'll only need to iterate over the
tiles of a row once (we'll see why later).

```python
def matching_row(prev, tiles, tiles_per_row):
    yield prev
    for _ in range(tiles_per_row - 1):
        tile = matching_tile(prev, tiles, 'e', 'w')
        prev = tile
        yield prev
```

Now, as we should remember, each tile of the final image needs to be stripped of
its outermost edges after being correctly placed. We'll go from 10x10 tiles to
8x8 tiles. Let's write yet another helper function to "strip" the edges of a
tile. It's quite straightforward: take every row except the first and last, and
again for each row take all characters except the first the last. It's really
only one line of code using a [list comprehension][py-list-comprehension]:

```python
def strip_edges(tile):
    return [row[1:-1] for row in tile[1:-1]]
```

Now we can actually start building the image: we'll start from the top left
corner, and keep adding rows using `matching_row()` until tiles run out. Each
tile of each row will be passed through `strip_edges()`, building a completely
new row of stripped tiles (and this is why we only need to iterate over the rows
returned by `matching_row()` once).

After matching and stripping all tiles of a row, we can "join" them together
into 8 rows of the final image using [`zip()`][py-builtin-zip] plus
[unpacking][py-unpacking] again to concatenate each i-th row of each tile into a
single big row of the final image using `str.join`.

```python
def build_image(top_left_tile, tiles, image_dimension):
    # Start from the top left
    first = top_left_tile
    image = []

    while 1:
        # Get a row of matching tiles
        image_row = matching_row(first, tiles, image_dimension)
        # Strip the outermost edges from each of them
        image_row = map(strip_edges, image_row)
        # Add together each row of the tiles into a single big row, and add it to the final image
        image.extend(map(''.join, zip(*image_row)))

        # Do this until tiles run out
        if not tiles:
            break

        # Match the first tile of the next row, which is south of the first tile of the current row
        first = matching_tile(first, tiles, 's', 'n')

    return image
```

Woah, almost there. We can finally build the image!

```python
# Remove top-left tile from the tiles to match first. We need to do this since
# our `top_left` is the result of rotations, hence it will no longer be equal to
# the one in the `tiles` dictionary.
tiles.pop(top_left_id)

image = build_image(top_left, tiles, image_dimension)
```

The "only" thing left to do is trying all possible `arrangements()` of the image
and check if we can find any monsters. Let's write the last function of today's
puzzle: a function which takes the image and a pattern as input, and returns the
number of times that pattern was matched.

To do this we can first find all characters of the pattern which are `#`, and
build a set of "deltas" from the top left corner of the pattern. Then, iterate
over each cell of the image and try matching the entire pattern considering that
cell as the top-left cell of the pattern.

To convert a pattern into deltas we can just iterate through it using
`enumerate()` and construct a list:

```python
deltas = []
for r, row in enumerate(pattern):
    for c, cell in enumerate(row):
        if cell == '#':
            deltas.append((r, c))
```

Consider for example the monster pattern:

```
            1111111111
  01234567890123456789
0                   #
1 #    ##    ##    ###
2 #  #  #  #  #  #
```

The result would be the following (yeah we could even hardcode this, but where's
the fun in that?).

```python
[(0, 18), (1, 0), (1, 5), (1, 6), (1, 11), (1, 12), (1, 17), (1, 18), (1, 19), (2, 1), (2, 4), (2, 7), (2, 10), (2, 13), (2, 16)]
```

Now to try counting the matches of the pattern on the image, taking advantage of
the [`all()`][py-builtin-all] function (one of my favorite built-ins):

```python
pattern_h, pattern_w = len(pattern), len(pattern[0])
image_sz = len(image)

n = 0
for r in range(image_sz - pattern_h):
    for c in range(image_sz - pattern_w):
        if all(image[r + dr][c + dc] == '#' for dr, dc in deltas):
            n += 1
```

Putting everything we said together, and also testing all possible arrangements
of the image, this is the resulting function:

```python
def count_pattern(image, pattern):
    pattern_h, pattern_w = len(pattern), len(pattern[0])
    image_sz = len(image)
    deltas = []

    for r, row in enumerate(pattern):
        for c, cell in enumerate(row):
            if cell == '#':
                deltas.append((r, c))

    for img in arrangements(image):
        n = 0
        for r in range(image_sz - pattern_h):
            for c in range(image_sz - pattern_w):
                if all(img[r + dr][c + dc] == '#' for dr, dc in deltas):
                    n += 1

        if n != 0:
            return n
```

The number of `#` characters can be counted with a simple combination of
[`sum()`][py-builtin-sum] plus [`str.count()`][py-str-count].

```python
MONSTER_PATTERN = (
    '                  # ',
    '#    ##    ##    ###',
    ' #  #  #  #  #  #   '
)

monster_cells = sum(row.count('#') for row in MONSTER_PATTERN)
water_cells   = sum(row.count('#') for row in image)
n_monsters    = count_pattern(image, MONSTER_PATTERN)
roughness     = water_cells - n_monsters * monster_cells

print('Part 2:', roughness)
```

We can now ***finally*** get our second star and hopefully also something for
the headache. Jeez, I've got mixed feelings about this one.

### Reflections

While the solution I adopted and explained above is nothing short of a
bruteforce approach, it is still really fast on such a "small" input (144
tiles), and I decided to keep it that way without overcomplicating it just for a
minimal performance gain.

In any case, it's worth mentioning that we can do better: when making the
initial matches between tiles we could keep the information of which tiles match
which, and then instead of looking for one tile at a time in all the left tiles,
use this information to limit our search for a specific matching tile to at most
4 other tiles (one per side).

This would basically mean building and making good use of an
[undirected graph][wiki-undirected-graph] of matches (using a simple
dictionary), where tiles are vertexes and edges mean "matching". It's pretty
similar to what we are already doing in the first function we wrote called
`match_tiles()`, we would only need to also remember the IDs of the matches for
each matched side.

Applying this approach would solve the second part of the problem in
[linear time][wiki-linear-time] (proportional to the number of tiles), although
it would result in a little bit more complicated program to implement. However
for the first part, finding all the matches for each tile would still take
[quadratic time][wiki-polynomial-time], and therefore the final solution would
still be *O*(*n<sup>2</sup>*) overall.


Day 21 - Allergen Assessment
----------------------------

[Problem statement][d21-problem] — [Complete solution][d21-solution] — [Back to top][top]

### Part 1

We are given a menu of recipes, one per line: each recipe consists of a list of
ingredients and a list of allergens. Each allergen is contained in exactly one
ingredient amongst *all* ingredients of the menu (that is, there is a global
1-to-1 association between allergens and ingredients). While allergens are
listed in English, ingredient names are in an unknown language, so we cannot
simply deduce which allergen may be contained in which ingredient simply by its
name.

We know that each recipe contains at least the listed allergens, but it could
also contain more allergens which are not explicitly listed. Given our input, we
must determine which ingredients are safe and definitely *don't* contain
allergens, and count the number of times any of those ingredients appear in the
menu.

Our task is not obvious, but we can understand it better through an example.
Suppose we're at an Italian restaurant, we don't know Italian, and we're
presented with the following menu:

```
stoccafisso maionese aceto origano (contains dairy, fish)
riso maionese tofu patate (contains dairy)
stoccafisso tofu (contains soy)
stoccafisso maionese patate (contains fish)
```

By looking at the above recipes (pretty strange Italian restaurant by the way,
never seen such dishes to be honest!), we can see that the first contains at
least two allergens: `dairy` and `fish`, so we know that `aceto` could contain
either one of those allergens. If we look at the other recipes, we can't see
`aceto` anywhere, even though the second dish contains `dairy` and the fourth
dish contains `fish`.

Remember that there is a 1-to-1 association between allergens and ingredients,
so if `aceto` was the ingredient containing `dairy`, we should see `aceto` in
every dish which contains `dairy`. The same reasoning goes for `fish`. Since we
see two other plates with `dairy` or `fish`, but none of them has `aceto` as an
ingredient, we can conclude that `aceto` can contain neither of those, and does
not contain any allergen at all.

In short, *all the ingridients missing from a specific recipe cannot possibly
contain any of the allergenes listed in the recipe*. This appears to be the only
deduction that we are allowed to make based on the given menu, and indeed it is
enough to solve the problem.

Applying this reasoning to all the ingredients of the above example menu, we can
come to the conclusion that none of `aceto`, `origano`, `riso` and `patate`
contain allergens. Counting the occurrences of those, the answer would be `5`.

We can now apply the reasoning to each ingredient of the real menu to find out
which ingredients don't contain allergens.

Let's start with input parsing. We could use a regex, but the recipe format is
simple enough: for each line of input we'll first separate ingredients and
allergens by removing the trailing closed parentheses and newlines and splitting
on the string `" (contains "`. Then, we'll split both the ingredient and the
allergens into a `list` and build a `set` out of each list. The reason for using
a `set` will be clear soon.

In order to solve the problem, we need to keep a set of "possible" allergens
for each ingredient, and we also need to keep track of which recipes contain a
given allergen. We'll do this by creating two dicrionaries:
`{ingredient: set_of_allergens}` and `{allergen: list_of_recipes}`. To simplify
the creation of new entries we can use two
[`defaultdict`][py-collections-defaultdict]. We'll write a function to parse the
input and extract all this information:

```python
def parse_input(fin):
    recipes = []
    possible_allers = defaultdict(set)
    recipes_with    = defaultdict(list)

    for i, line in enumerate(fin):
        ingredients, allergens = line.rstrip(')\n').split(' (contains ')

        ingredients = set(ingredients.split())
        allergens   = set(allergens.split(', '))
        recipes.append(ingredients)

        for aller in allergens:
            recipes_with[aller].append(i)

        for ingr in ingredients:
            possible_allers[ingr] |= allergens

    return recipes, possible_allers, recipes_with

fin = open(...)
recipes, possible_allers, recipes_with = parse_input(fin)
```

Now `possible_allers[ingr]` contains the set of possible allergens for the
ingredient `ingr`, and `recipes_with[aller]` contains a list of indexes of
recipes containing the allergen `aller`.

Perfect, we just need to apply the above reasoning to find safe ingredients. For
each ingredient we'll check all its possible allergens: if any of the recipes
containing such allergen does not include the ingredient we are checking, then
we can safely exclude the allergen from the set of possible allergens for the
ingredient.

```python
def safe_ingredients(recipes, possible_allers, recipes_with):
    safe = []

    for ingr, possible in possible_allers.items():
        impossible = set()

        for aller in possible:
            for i in recipes_with[aller]:
                if ingr not in recipes[i]:
                    impossible.add(aller)
                    break

        # Difference between sets: remove all the items of `impossible` from `possible`
        possible -= impossible

        # If no possible allergens are left, the ingredient does not contain allergens
        if not possible:
            safe.append(ingr)

    return safe

safe = safe_ingredients(recipes, possible_allers, recipes_with)
```

The continuous checking `if ingr not in recipes[i]` is the reason we used sets
instead of lists for recipe ingredients.

We can simplify the innermost `for` loop above using [`any()`][py-builtin-any],
and replacing the `for` with a simple [generator expression][py-generator-expr],
since all it's doing is checking if the ingredient `ingr` is in any of the
recipes containing the allergen `aller`, stopping at the first negative match:

```python
def safe_ingredients(recipes, possible_allers, recipes_with):
# ... unchanged ...
        for aller in possible:
            if any(ingr not in recipes[i] for i in recipes_with[aller]):
                impossible.add(aller)
# ... unchanged ...
```

Now that we have a list of ingredients with no allergens, we can just count the
number of times each of them appears in the menu, summing up each count. To do
this easily we can use [`sum()`][py-builtin-sum]:

```python
tot = 0
for ingr in safe:
    tot += sum(ingr in r for r in recipes)
```

We can actually also compress the outer `for` into `sum()`:

```python
tot = sum(ingr in r for r in recipes for ingr in safe)
print('Part 1:' tot)
```

Hope you are not allergic to `peanuts`, it would be a shame if you couldn't
taste the delicious `tjbngs` with `jrhvk`! Typical Advent of Code recipe.

### Part 2

For the second part of today's puzzle, for each allergen we need to determine
the ingredient wihch contains it. Our answer must be a comma separated list of
ingredient names, sorted alphabetically by their allergen.

We need to do something very similar to what we did for
[day 16 part 2](#part-2-15). It's the exact same algorithm, just with a
different associated meaning. First, remove all empty sets from our dictionary
of possible allergens:

```python
for ingr in safe:
    del possible_allers[ingr]
```

Now we'll write a function to simplify the sets of possible allergens for each
ingredient down to a single allergen per ingredient:

1. Start with a set of possible allergens per ingredient (`possible_allers`).
2. Find a set with only one allergen left: assign that allergen to the
   ingredient associated with the set, then remove the set from our dictionary.
3. Cycle through all the other sets and remove the matched allergen from each
   of them.
4. Check if all the sets are empty: if so, we assigned all allergens to an
   ingredient and we are done. If not, go back to step 2.

Using our innate ability to translate English sentences into Python code, we
come up with this function:

```python
def simplify(possible_allers):
    assigned = {}

    while possible_allers:
        for ingr, possible in possible_allers.items():
            if len(possible) == 1:
                break

        aller = possible.pop()
        assigned[aller] = ingr
        del possible_allers[ingr]

        for ingr, possible in possible_allers.items():
            if aller in possible:
                possible.remove(aller)

    return assigned
```

All we have to do now is get the assignments calling this function and then sort
them according to the requirements. We need to sort the assignments in
alphabetical order according to the allergen name. To do this, we can sort the
keys of the `assigned` dictionary returned by the above function using
[`sorted()`][py-builtin-sorted] and then `map()` each key (allergen) into its
value (ingredient). Finally, [`join()`][py-str-join] the values together
separating them with commas (`,`).

```python
assigned = simplify(possible_allers)
lst = ','.join(map(assigned.get, sorted(assigned)))

print('Part 2:', lst)
```

You may not be able to enjoy `tjbngs` if you're allergic to `peanuts`, but you
can simply go with the `mlqnfs` as a `peanut`-free alternative (which is also
vegan as the name obviously implies).


Day 22 - Crab Combat
--------------------

[Problem statement][d22-problem] — [Complete solution][d22-solution] — [Back to top][top]

### Part 1

Today we've got to emulate a two-player card game. Cards are positive integer
numbers, and the rules of the game are pretty straightforward:

- Each player starts with their own deck of cards.
- Then, each turn:
  - Both players draw the top card of their deck.
  - The player who drew the higher-valued card wins the round and keeps both
    cards, inserting them at the bottom of their deck, their card first.
  - If either player is left with no cards, the game ends and the winner is the
    player with all the cards. Otherwise the game keeps going.

We need to determine the score of the winner, which is calculated as the sum of
the product of each card with its position from the bottom of the deck (the last
card's position is 1).

As usual, let's get input parsing out of the way. Cards are given one by line
for each player, with an empty newline between the two decks, and a seemingly
unneeded "heading" line before the list of cards of each player. We can split
the entire input on a double newline (`\n\n`), then split again both parts into
separate lines using [`str.splitlines()`][py-str-splitlines], throwing away the
first line of each part. We can do this in a rather compact way with the help of
[`map()`][py-builtin-map].

```python
deck1, deck2 = map(str.splitlines, fin.read().split('\n\n'))
```

We'll end up with two lists of strings representing the decks of player 1 and
player 2 which we can easily `map()` again into lists of `int`. However, since
the game involves continuously moving cards around from the top to the bottom of
the decks, we should avoid using `list` to represent decks, since popping the
first element from a `list` takes [linear time][wiki-linear-time] proportional
to the length of the list. A [`deque`][py-collections-deque] is the perfect data
structure, supporting fast removal and insertion of elements on both ends.

```python
deck1 = deque(map(int, deck1[1:]))
deck2 = deque(map(int, deck2[1:]))
```

Now let's actually write the code to play this game. We'll create a simple
function which does nothing more than following the rules outlined in the
problem statement. Each turn we'll [`.popleft()`][py-deque-popleft] the first
card of each deck, then compare the two and [`.extend()`][py-deque-extend] the
winner's deck with both cards (in the right order). It's not clear what happens
should the two cards have the same value, so we'll just assume that's impossible
(we can [`assert`][py-assert] that this never happens just to be sure).

```python
def play(deck1, deck2):
    while deck1 and deck2:
        c1, c2 = deck1.popleft(), deck2.popleft()

        if c1 > c2:
            deck1.extend((c1, c2))
        else:
            deck2.extend((c2, c1))

    return deck1 if deck1 else deck2
```

The function we just wrote returns the final deck of the winner (using a
[conditional expression][py-conditional-expression]), now let's write another
function to calculate the winner's score (spoiler: we are writing a function
just because we'll need it again for part 2).

For each card in the winner's deck, start from the bottom and multiply it by its
position (from the bottom), summing up every value. To reverse the deck, since
we are dealing with a `deque` and `deque` objects do not support
[slicing][py-slice], we cannot simply use `[::-1]`, we need to resort to the
built-in [`reversed()`][py-builtin-reversed] function. Once the deck is
reversed, we can then use [`enumerate`][py-builtin-enumerate] counting from `1`
to iterate over both the values and their positions.

```python
def score(deck):
    tot = 0
    for pos, card in enumerate(reversed(deck), 1):
        tot += card * pos
    return tot
```

As always, a simple loop that is only summing up values can be simplified down
to a single line using [`sum()`][py-builtin-sum]:

```python
def score(deck):
    return sum(p * c for p, c in enumerate(reversed(deck), 1))
```

All that's left to do is use the functions we defined to simulate the game and
get our answer:

```python
winner_deck  = play(deck1.copy(), deck2.copy())
winner_score = score(winner_deck)

print('Part 1:', winner_score)
```

Note: we're passing a `.copy()` here just because we'll need to re-use the same
decks for part 2.

### Part 2

Now the rules change, and the game becomes *recursive*. Oh no, we'll need to
write another recursive function!

The new rules to apply each turn are the following:

- Before each turn, avoid entering an infinite loop by checking the current
  decks. If the current decks have ever been seen before in this game with the
  same length and the exact same cards in the same order, stop playing: player 1
  automatically wins.
- Both players draw the top card of their deck.
- If for both players the value of the drawn card is less than or equal to the
  number of remaining cards in deck, the winner of the round is determined by
  playing a new game. Take a number of cards equal to the drawn card from the
  top of each deck, and start a new sub-game to determine the winner of this
  round.
- Otherwise (one or both cards have values higher than the number of cards left
  in the corresponding deck) play normally. The player who drew the
  higher-valued card wins the round and keeps both cards, inserting them at the
  bottom of their deck, their card first.
- If either player is left with no cards, the game ends and the winner is the
  player with all the cards. Otherwise the game keeps going.

There does not seem much to think about, all we need to do is follow the rules
again, creating a new function to play the game recursively.

In order to check for the first rule above, we can use a simple `set` to keep
track of seen decks. Before each turn, we'll check if the current pair of decks
is in the set, and stop declaring player 1 the winner if that's the case.
Otherwise, we'll turn the current decks into a pair of `tuple` and add them to
the set of seen decks.

For the recursive part, all we need to do each turn is again apply the rules
literally: draw two cards and check if they both have values higher than the
length of the two decks. If so, cut the decks by temporarily turning them into
tuples or lists (`deque` objects do not support slicing) and do a recursive call
to determine the winner of the round. Otherwise, the winner of the round is the
one who drew the higher-valued card.

Since we now also need to know who won (and not only the winner's deck), we'll
return two values from our recursive function: the winner and its deck, ignoring
the deck in the case of a recursive call. To identify the winner we'll simply
return `True` in case player 1 wins and `Fales` otherwise.

```python
def recursive_play(deck1, deck2):
    seen = set()

    while deck1 and deck2:
        key = tuple(deck1), tuple(deck2)
        if key in seen:
            return True, deck1

        seen.add(key)
        c1, c2 = deck1.popleft(), deck2.popleft()

        if len(deck1) >= c1 and len(deck2) >= c2:
            sub1, sub2 = tuple(deck1)[:c1], tuple(deck2)[:c2]
            p1win, _ = recursive_play(deque(sub1), deque(sub2))
        else:
            p1win = c1 > c2

        if p1win:
            deck1.extend((c1, c2))
        else:
            deck2.extend((c2, c1))

    return (True, deck1) if deck1 else (False, deck2)
```

Done, now let's call the function and [call it a day][misc-call-day]:

```python
_, winner_deck = recursive_play(deck1, deck2)
winner_score   = score(winner_deck)

print('Part 2:', winner_score)
```


Day 23 - Crab Cups
------------------

[Problem statement][d23-problem] — [Complete solution][d23-solution] — [Back to top][top]

### Part 1

Another game with numbers, how cool! This time we'll be playing with cups. We
have 10 cups labeled with values from 1 to 9 in a specific order (our puzzle
input). These cups are arranged *in a circle*, that is, after the last cup we
find the first one again. We are going to shuffle them according to a set of
precise rules.

We start with the first cup in our input list as the "current" cup. Each round,
the following actions are performed to move cups around:

- Pick up (removing them from the circle) the 3 cups right after the current
  one.
- Take the value of the current cup and subtract 1 from it. Keep subtracting 1
  until the value is not amongst the values of the 3 cups we picked up. Whenever
  the value goes below the minimum value amongst all cups, set it to the maximum
  value.
- Find the cup with the value we just calculated, and place the 3 cups we picked
  up earlier right after it, in the same order in which they were picked up.
- Select the cup right after the current one as the new current.

After performing the above actions for 100 rounds, we need to find the cup with
value 1, and concatenate all the values of the other cups after it, in order.
This will be the answer for part 1.

Hopefully the explanation is clear enough, but let's look at a small example of
5 rounds anyway. This is the same as the one provided in the problem statement
linked above, with input `389125467`, just rearranged in a way I find easier to
understand. The current cup is surrounded by parentheses `( )`, and the 3 picked
up cups are surrounded by square brackets `[ ]`.

```
Round 1:  (3) [8   9   1]  2   5   4   6   7
               \_______/     ↑
                    └────────┘

Round 2:   3  (2) [8   9   1]  5   4   6   7
                   \_______/                 ↑
                       └─────────────────────┘

Round 3:   3   2  (5) [4   6   7]  8   9   1
             ↑         \_______/
             └─────────────┘

Round 4:   3]  4   6   7   2   5  (8) [9   1
       ..._/             ↑             \_____...
                         └─────────────────┘

Round 5:  (4) [6   7   9]  1   3   2   5   8
               \_______/         ↑
                   └─────────────┘

Final:     4   1   3   6   7   9   2   5   8
Values after 1: 3 6 7 9 2 5 8 4
```

As you can see from above, moving the 3 picked up cups in round 1 is simple
enough, we take `3 - 1 = 2`, so we place the cups after cup `2`. In the second
round though we have `2 - 1 = 1`, and `1` is amongst the cups we picked up, so
we subtract 1 wrapping back up to 9, which is *still* in the picked-up cups, we
do this two more times and end up with `7` which is not amongst the picked up
cups, so we place them after cup `7`.

Parsing our input today couldn't be simpler, just [`map()`][py-builtin-map] the
digits of the only line of input into integers:

```python
orig = tuple(map(int, fin.readline().rstrip()))
```

We keep the original list in a `tuple` because we'll need it later for part 2.

Since we need to continuously remove and insert elements, and we are dealing
with a cyclic list, we can use a [`deque`][py-collections-deque] to hold the
values of the cups. We highly prefer a `deque` over a `list` because it supports
fast insertion and deletions, while inserting and deleting elements from a list
costs proportionally to the length of the list.

A `deque` can be easily "rotated" through [`.rotate()`][py-deque-rotate]. If we
keep our current cup always at the first spot in the `deque`, we can just use
`.rotate()` to reposition the cups whenever we need to pop some out or add them
back in. All the "rotations" we need to make are to the right, so the numbers
passed to `.rotate()` will have to be negative since this method rotates to the
left.

The operations to perform in a round can be easily translated in terms of
[`.popleft()`][py-deque-popleft], `.rotate()` and
[`.appendleft()`][py-deque-appendleft] (or
[`.extendleft()`][py-deque-extendleft]):

- Looking at the current cup value simply means checking at `[0]`.
- Picking 3 cups up after the current means `.rotate(-1)` then `.popleft()` 3
  times.
- Inserting the 3 cups back means `.rotate(-dest - 1)` then `.appendleft()` 3
  times (or just `.extendleft()`).

Let's write a function to play the game given a `deque` of cups. All we need to
do is apply the rules, translating them to operations on the `deque` as
explained above.

```python
def play(cups, n_moves):
    mincup, maxcup = min(cups), max(cups)

    for move in range(n_moves):
        cur = cups[0]

        # Pick up 3 cups after the current
        cups.rotate(-1)
        picked = [cups.popleft() for _ in range(3)]

        # Select the destination cup value, after which we'll insert the 3 picked cups
        dst = cur - 1
        while dst in picked or dst < mincup:
            if dst < mincup:
                dst = maxcup
            else:
                dst -= 1

        # Find the position of the destination cup and rotate the deque so that we are right after it
        pos = cups.index(dst) + 1
        cups.rotate(-pos)
        # Insert the 3 picked up cups there (extendleft inserts backwards so we need to reverse them [::-1])
        cups.extendleft(picked[::-1])
        # Go back to where we were, so that the next current cup is at position 0
        cups.rotate(pos)

    # Move right at the cup with value 1
    cups.rotate(1)
    pos = cups.index(1)
    cups.rotate(-pos)

    # Discard cup 1 and concatenate the values of all subsequent cups to get the answer
    cups.popleft()
    return ''.join(map(str, cups))

```

The above loop adjusts the "destination" value according to the rules can be
simplified using [conditional expressions][py-conditional-expression]:

```python
        dst = maxcup if cur == mincup else cur - 1
        while dst in picked:
            dst = maxcup if dst == mincup else dst - 1
```

If we also start the values from `0` instead of `1` we can simplify the formula
a little bit, but let's keep it this way to keep the calculation of the final
value simple.

Now we just need to call the function with the appropriate parameters:

```python
cups = deque(orig)
ans  = play(cups, 100)

print('Part 1:', ans)
```

That was simple enough. Onto part 2!

### Part 2

Now we are told that we need to add *some more* cups... precisely, all cups
valued from 10 to 1000000 (1 million). We also need to play the game for 10
million rounds instead of 100. After the last round, we need to multiply
together the values of the two cups right after the cup with value 1.

Well... needless to say, we can't use a `deque` anymore. Shifting around 1
million elements is quite slow; doing it 10 million times is just impossible (it
would take ages). There are two main problems with our part 1 approach:

1. Finding the index of a cup through `.index()` means scanning the entire
   `deque`. This is way too slow on a large `deque`, and we need to do it every
   single round. We need this operation to be as fast as possible, taking
   [constant time][wiki-constant-time] instead of
   [linear time][wiki-linear-time].
2. Rotating around using `.rotate()` also takes linear time in the worst case
   (i.e. rotate of the entire length of the deque). We also need this operation
   to be performed in constant time if we want to solve this before the
   [heat death of the universe][wiki-heat-death-universe].

The two above points weren't really noticeable with only 100 rounds with 10
items, since the operation is nearly instantaneous with such small numbers, but
become a huge problem when the number of elements increases.

Say hello to [linked lists][wiki-linked-list], the most beautiful data structure
ever invented! In particular, we'll be building and using a circular linked list
to make the above issues disappear. We'll see how shortly.

In Python, the concept of an explicit "pointer" does not exist, so we don't have
"conventional" linked lists out of the box, since we cannot not explicitly point
to values. However, one can implicitly point to a value by wrapping it inside an
instance of a "wrapper" `class` and taking a reference to that instance.
Instancing a class and assigning it to a variable merely means keeping a
reference to the instance of the class, which is akin to keeping a "pointer" to
the instance.

We can create a wrapper class for linked list nodes in the following way:

```python
class Node:
    def __init__(self, value):
        self.value = value # actual value of this node
        self.next  = None  # pointer to next Node of the linked list
```

However, since we have to play for *10 million* rounds, we might want to find a
little bit more efficient way of representing a linked list. This is because,
unluckily for us, accessing attributes of an object is one of the slowest
primitive operations in Python, so before going on, let's see if we can do
better.

Thankfully, we can, as it just so happens that in our case the cups (and
therefore the nodes of our linked list) will assume all values from 1 to 1
million. Therefore all we need to keep track of the `next` of a given cup is
just a big list of integers, let's call it `next_cup`, storing at index `i` the
value of the cup after the cup with value `i`. That is, `next_cup[i]` is the
the cup which follows cup `i`.

This `next_cup` list will have 1 million plus 1 elements, and will be
initialized according to the initial 9 values we have as input plus another
999991 values from 10 to 1000000. We add that 1 additional element in the list
because we don't want to worry about calculating the correct indexes, and adding
one more element while ignoring `next_cup[0]` makes us able to just use cup
values as indexes. Finally, the last entry of the list will be the value of the
first cup in our input, making the 1-millionth cup have the first one as "next",
therefore making our linked list also *circular*.

Keeping cups in a linked list removes the problem of having to shift everything
around just to remove and insert an arbitrary contiguous chunk of cups:

- To remove cups from the list, we only need to update *one* value, the "next"
  of the cup right before the first cup we remove, replacing it with the value
  of the "next" of the last cup we remove.
- To insert cups back into the list between two other cups, we only need to
  update *two* values: the "next" of the cup before the insertion point (setting
  it to the value of the first inserted cup), and the "next" of the last
  inserted cup (setting it to the value of the cup after the insertion point.

Here's a bonus ASCII-art diagram to visualize the removal of elements (and also
insertion if you read it from the bottom up) from a linked list:

```
+---+------+    +---+------+    +---+------+    +---+------+    +---+------+
| A | next |--->| B | next |--->| C | next |--->| D | next |--->| E | next |--+
+---+------+    +---+------+    +---+------+    +---+------+    +---+------+  |
  ^                                                                           |
  +---------------------------------------------------------------------------+

+---+------+                                                    +---+------+
| A | next |--------------------------------------------------->| E | next |--+
+---+------+                                                    +---+------+  |
  ^                                                                           |
  +---------------------------------------------------------------------------+
```

The first 9 cups will just be linked one to the other from left to right, we can
use [`zip()`][py-builtin-zip] to iterate over a pair of consecutive cups and set
up the "next" of each. Then, we'll add the values from 10 to 1 million (in
order, since they are initially sorted this way, and finally add the first value
of our original list at the end of the list, so that the "next" cup of the last
one is the first (effectively making the list circular).

```python
def build_list(cups):
    next_cup = [0] * len(cups)

    for prev, cur in zip(cups, cups[1:]):
        next_cup[prev] = cur

    next_cup[cups[-1]] = len(next_cup)
    next_cup += list(range(len(next_cup) + 1, 1000000 + 2))
    next_cup[n] = cups[0]

    return next_cup
```

Now we can write a new `play()` function to actually play the game. There isn't
really much more to say except what I explained above, so I'll let the code
mainly speak for itself, with the help of some comments.

```python
def play(cur, next_cup, n_rounds):
    max_cup = len(next_cup) - 1

    for _ in range(n_rounds):
        # Pick up 3 cups
        first  = next_cup[cur]
        mid    = next_cup[first]
        last   = next_cup[mid]
        picked = (first, mid, last)

        # Remove them from the list
        next_cup[cur] = next_cup[last]

        # Select the destination cup value, after which we'll insert the 3 picked-up cups
        dst = max_cup if cur == 1 else cur - 1
        while dst in picked:
            dst = max_cup if dst == 1 else dst - 1

        # Insert the picked cups right after it
        next_cup[last] = next_cup[dst]
        next_cup[dst]  = first

        # Advance to the next cup after the current
        cur = next_cup[cur]
```

Lastly, let's build the linked list and pass it to the above function to
simulate 10 million rounds of the game:

```python
next_cup = build_list(orig, 1000000)
play(orig[0], next_cup, 10000000)
```

The answer will just be the product of the values of the two cups after the cup
with value `1`:

```python
ans = next_cup[1] * next_cup[next_cup[1]]
print('Part 2:', ans)
```

With minor modifications, we can make the `build_list()` more generic to create
a linked list of an arbitrary number of cups

```python
def build_list(cups, n=None):
    initial_sz = max(cups) + 1
    next_cup   = [0] * initial_sz

    for prev, cur in zip(cups, cups[1:]):
        next_cup[prev] = cur

    if n is None:
        next_cup[cups[-1]] = cups[0]
    else:
        next_cup += list(range(initial_sz + 1, n + 2))
        next_cup[n] = cups[0]
        next_cup[cups[-1]] = initial_sz

    return next_cup
```

Then we can use our new `play()` function to also solve part 1, discarding the
previous suboptimal solution. The only thing that we'll need to change is the
calculation of the final value, since we'll have to iterate over the list
manually.

```python
next_cup = build_list(orig)
play(orig[0], next_cup, 100)

ans = ''
cur = next_cup[1]
while cur != 1:
    ans += str(cur)
    cur = next_cup[cur]

print('Part 1:', ans)
```

### Reflections

Today is kind of a bad day for our poor Python. The solution isn't really as
fast as I'd like it to be. On my machine I get a total execution time of roughly
7s with [CPython][wiki-cpython] 3.9 using a big `list` to keep track of the
"next" of each node (like I explained in the part 2 solution above), and of
course even worse times using classes instead. However, [PyPy][misc-pypy] 7.3.3
(Python 3.7.9) comes to the rescue as always and obliterates CPython again with
its optimized list operations, taking a little less than 700ms for both parts.

Overall, what really affects performance in CPython is the slowness of indexing
and/or accessing properties of Python objects, which apparently is a downside
intrinsic in the implementation. Sad.


Day 24 - Lobby Layout
---------------------

[Problem statement][d24-problem] — [Complete solution][d24-solution] — [Back to top][top]

### Part 1

Today we have to navigate through an [*hexagonal grid*][wiki-hexgrid], how cool!

We have a room with a hexagonally-tiled floor. All the tiles of the floor have
one black side and one white side, and they are initially all placed with the
white side facing up. We need to flip specific tiles according to a list of
directions.

Each entry in our list of direction is a string consisting of multiple moves
concatenated together: each move can be either `e`, `se`, `sw`, `w`, `nw`, or
`ne`. There is no space between two moves, as it's not needed to identify the
moves. Each string of moves in our list represents the steps to make to arrive
to the tile we need to flip, always starting from the same reference tile.

We need to determine how many tiles will have the black side up after flipping
in order all the tiles following the directions. *Note that* we could also end
up flipping the same tile more than once.

Not that difficult of a problem, all we need is a decent coordinate system to
uniquely identify the position of a tile relative to the reference tile.

Even though it might seem that we can move in more than two directions, we
really are not. Even dealing with a hexagonal grid, we are still in a
2-dimensional space, so each tile's position can be uniquely identified by
exactly two integer coordinates `(x, y)`. If we concentrate enough, we can
actually look at tiles as if they were arranged in rows and (slightly slanted)
columns.

Here's how we can represent tile coordinates (bear with me on this one,
ASCII-art hexagonal tiles are really only pretty when drawn in the perpendicular
orientation, unfortunately):

```
       / \     / \     / \     / \     / \     /#\
     /     \ /     \ /     \ /     \ /     \ /#####\
    | -1,-1 |  0,-1 |  1,-1 |  2,-1 |  3,-1 |#######|
    |       |       |       |       |       |#######|
   / \     / \     / \     / \     / \     /#\#####/ \
 /     \ /     \ /     \ /     \ /     \ /#####\#/     \
| -1,0  |  0,0  |  1,0  |  2,0  |  3,0  |#######|  5,0  |
|       |  REF  |       |       |       |#######|       |
 \     / \     / \     / \     / \     /#\#####/ \     /
   \ /     \ /     \ /     \ /     \ /#####\#/     \ /
    |  0,1  |  1,1  |  2,1  |  3,1  |#######|  5,1  |
    |       |       |       |       |#######|       |
   / \     / \     / \     / \     /#\#####/ \     / \
 /     \ /     \ /     \ /     \ /#####\#/     \ /     \
|  0,2  |  1,2  |  2,2  |  3,2  |#######|  5,2  |  6,2  |
|       |       |       |       |#######|       |       |
 \     / \     / \     / \     / \#####/ \     / \     /
   \ /     \ /     \ /     \ /     \#/     \ /     \ /
```

In the above representation rows are clearly visible, and I've highlighted the
column `y=4` filling it with `#`. The reference cell is at `(0,0)` and marked
with `REF`.

A movement *east* or *west* using such a coordinate system is nothing special,
we stay on same row, and just need to change the `x` coordinate. However, a
north or south movement could either change one coordinate only or both
coordinates, depending on the direction. Moving *south west* only changes `y`,
while moving or *south east* changes both `x` and `y`! Similarly, moving
*north east* changes only `y`, while moving *north west* changes both `x` and
`y`!

Now that we have a clear coordinate system to follow, we can start working.
Let's write a function which, given a list of moves, "walks" the hexagonal grid
and returns the coordinates of the final cell relative to the reference cell. In
order to do this, a global dictionary representing the deltas to apply to each
coordinate comes in handy, and lets us avoid writing 6 different `if/elif`
branches.

```python
MOVEMAP = {
    'e' : ( 1,  0),
    'w' : (-1,  0),
    'se': ( 1,  1),
    'sw': ( 0,  1),
    'ne': ( 0, -1),
    'nw': (-1, -1)
}

def walk(moves):
    x, y = 0, 0

    for move in moves:
        dx, dy = MOVEMAP[move]
        x += dx
        y += dy

    return x, y
```

That was straightforward. Now all that's left to do is parse the input
directions and apply them.

In order to split each string of directions into a list of moves, we can use a
simple [regular expression][misc-regexp] consisting of only 6 alternatives
separated by pipes (`|`):

```python
import re

rexp = re.compile(r'e|w|se|sw|ne|nw')
```

Applying [`.findall()`][py-re-findall] on a line of input using the above regexp
will split each time one of the alternatives matches and return a list of moves
to follow to get to the wanted tile to flip.

The code we're going to write from now on is very similar to the one we wrote
for [day 17][d17]: the only thing we care about a specific coordinate of our
grid, is if that coordinate represents a black tile or not. To keep track of
this information, all we need is a set of coordinates representing black tiles,
assuming any coordinate that is not in the set represents a white tile.

Initially, the set will be empty. Then we'll parse each line of input into a
list of directions using the previously written regexp and pass it through
`walk()` to get the final coordinates of the tile to flip. Finally, to "flip"
the tile we'll simply add the coordinates to our set *if and only if* they
aren't in the set already (meaning the tile is being flipped from white to black
side), or remove them if they *are* already in the set (meaning the tile is
being flipped from black to white side).

```python
grid = set() # coords of tiles with black side up

for line in fin:
    moves = rexp.findall(line)
    p = walk(moves)

    if p in grid:
        grid.remove(p)
    else:
        grid.add(p)
```

All that's left to do is "calculate" the number of black tiles in our set:

```python
n_black = len(grid)
print('Part 1:', n_black)
```

### Part 2

For the second part of the puzzle, now the hexagonal grid of tiles becomes... a
[cellular automaton][wiki-cellular-automaton], because why not!?

We should already know the drill, it's the third time we are dealing with a
cellular automaton this year (the other two being [day 11][d11] and
[day 17][d17]). The rules to evolve each tile based on its color and the state
of the 6 adjacent tiles are simple:

- Any black tile with 0 or more than 2 black tiles immediately adjacent to it
  is flipped to white.
- Any white tile with exactly 2 black tiles immediately adjacent to it is
  flipped to black.

We need to "evolve" our hexagonal grid of tiles for 100 generations, then count
the final number of tiles with the black side facing up.

I usually avoid using complex one-liners. Today feels to good to not simplify
everything down into a couple of lines of code though. I'll limit myself and try
to explain each step in the best way I can.

Like for [day 17][d17], it's important to consider that when "evolving" our
tiles, our set of black tiles can actually "expand" outwards. If a tile that is
not black (and therefore not in our `grid`) is adjacent to exactly 2 black
tiles, it will be flipped and will become black. For this reason, when evolving
the grid, we need to also check all tiles surrounding the ones we already have,
even if they are not in our `grid` set.

We can compute all coordinates that we need to check using a generator function
which iterates over all adjacent coordinates of any coordinate in our `grid`.
This is as simple as iterating over every point in `grid` and adding each
possible "delta" to it (that is, stepping one unit forward in each possible
direction).

```python
def all_neighbors(grid):
    deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))

    for x, y in grid:
        for dx, dy in delta:
            yield (x + dx, y + dy)
```

Simple enough. The coordinates we need to check to evolve the grid should be the
ones already in `grid` plus all the neighbors returned by the above function.
However, as per the rules, black tiles with no adjacent black tiles will always
be flipped to white. This means that no tile whose coordinates aren't already
included in the ones yielded by `all_neighbors()` will have the chance of
staying black, as this function generates all the coordinates of tiles which
have at least one adjacent black tile. We can therefore only consider the ones
returned by the above function as candidates for our "new" grid after evolving
one generation.

We now also need to count the number of adjacent black tiles for each tile. The
above generator function could actually `yield` the same coordinates multiple
times. For example, if a tile at `(x, y)` has 4 adjacent black tiles, then for
each one of those we will compute the same `(x, y)`, and we'll end up yielding 4
copies of the same coordinate.

This means that the above function, with a minor modification, can already tell
us both (1) all the coordinates of the tiles we should check and (2) how many
adjacent black tiles does each one of them have. We can do this by simply
counting duplicate coordinates.

Here's a new function which does just that, using a
[`defaultdict`][py-collections-defaultdict] to count the number of times we see
the same coordinate:

```python
from collections import defaultdict

def all_neighbors(grid):
    deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
    counts = defaultdict(int)

    for x, y in grid:
        for dx, dy in deltas:
            counts[x + dx, y + dy] += 1

    return counts
```

Counting duplicate elements in an iterable sequence can actually be done using a
[`Counter`][py-collections-counter] object from the
[`collections`][py-collections] module, which takes an iterable as parameter and
returns a dictionary of the form `{element: count}`. Combining this with a
[generator expression][py-generator-expr] to compress the two above `for` loops
into a single line, the result is the following:

```python
def all_neighbors(grid):
    deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
    return Counter((x + dx, y + dy) for x, y in grid for dx, dy in deltas)
```

All we need to do to evolve our `grid` now is iterate over all the coordinates
and counts in the dictionary returned by the above function, following the rules
on the number of adjacent black tiles to determine whether each tile should stay
(or turn) black.

```python
def evolve(grid):
    new = set()

    for p, n in all_neighbors(grid).items():
        if p in grid and not (n == 0 or n > 2):
            new.add(p)
        elif p not in grid and n == 2:
            new.add(p)

    return new
```

The above checks, which are a literal translation of the given rules into
logical formulas, can be simplified a lot noticing two things: if the number of
black adjacent tiles is `2`, the current tile will be black regardless of its
previous state; otherwise, if its previous state was black, the tile can also
keep being black if the number of adjacent black tiles is exactly `1`.

```python
def evolve(grid):
    new = set()

    for p, n in all_neighbors(grid).items():
        if n == 2 or (n == 1 and p in grid):
            new.add(p)

    return new
```

Since we extract the `.items()` from the `Counter` returned by `all_neighbors()`
right away, we can just incorporate that into the function itself:

```python
def all_neighbors(grid):
    deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
    return Counter((x + dx, y + dy) for x, y in grid for dx, dy in deltas).items()
```

Secondly, since all we are doing in `evolve()` is constructing a set of new
coordinates filtering the ones returned by `all_neighbors()` based on a
condition, we can even simplify `evolve` down to a single line using a generator
expression with an additional `if` condition:

```python
def evolve(grid):
    return set(p for p, n in all_neighbors(grid) if n == 2 or (n == 1 and p in grid))
```

Finally, since we just wrote two "one-liner" functions, let's just merge them
together as they are not needed anywhere else:

```python
def evolve(grid):
    deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
    near = Counter((x + dx, y + dy) for x, y in grid for dx, dy in deltas)
    return set(p for p, n in near.items() if n == 2 or n == 1 and p in grid)
```

A `for` loop to eveolve the grid 100 times is all that's left to do:

```python
for _ in range(100):
    grid = evolve(grid)

n_black = len(grid)
print('Part 2:', n_black)
```

I don't know about you, but I find hexagonal tilings quite satisfying.


Day 25 - Combo Breaker
----------------------

[Problem statement][d25-problem] — [Complete solution][d25-solution] — [Back to top][top]

The last puzzle of this year's Advent of Code is a pretty simple one, dealing
once again with [modular arithmetic][wiki-modular-arithmetic].

We need to crack the secret keys exchanged in a handshake between two devices.
The handshake involves *transforming* numbers according to the following
transformation, which takes two numbers as input: the number we want to
transform, called *"subject number"*, and a *"loop size"*.

- Start with a value of `1`, then perform the following operation a number of
  times equal to the *loop size*:
  - Multiply the value by the *subject number*.
  - Set the value to itself modulo `20201227`.
- The result is the value after performing the above two steps *loop size*
  times.

Each device initially sends a public key to the other. We are able to intercept
both of them (our puzzle input). We know that those public keys are the result
of transforming the number `7` using a *secret*, unknown loop size (different
for each device). Then, each device calculates a *secret key* by transforming
(always according to the above) the other device's public key using their own
secret loop size.

We need to figure out the secret key based on either one of the two public keys,
by first finding the loop size used to calculate one of the two public keys, and
then use it to transform the other public key.

There are two main solutions to today's problem. One is a simple and very
straightforward bruteforce approach, while the other is a faster and more
general purely mathematical solution. I ended up implementing the latter when
initially solving the problem, but I nonetheless will explain both of them in
detail.

### Bruteforce solution

We will follow the given directions to implement the "transformation" that is
described by the problem statement one step at a time, in order to find the
secret "loop size" of one of the two devices. To do so, we'll start from `1` and
then keep multiplying by `7` and doing modulo `20201227` until we find a value
equal to one of the two public keys. That value will be the secret "loop size"
of one of the the two devices.

```python
fin = open(...)
A, B = map(int, fin)

x = 1
v = 7
while v != A and v != B:
    v = (v * 7) % 20201227
    x += 1
```

It's easy to notice by looking at the above loop that the "transformation" we
are applying is nothing more than the [modular exponentiation][wiki-modular-exp]
of a given number (the "subject number", in the above case `7`) to the power of
*x* (the "loop size") modulo *20201227*. Python can actually do modular
exponentiation using [`pow()`][py-builtin-pow] passing a third argument (the
modulus), so we could also have written something like this:

```python
x = 1
v = 7
while v != A and v != B:
    x += 1
    v = pow(7, x, 20201227)
```

However it must be noted that this is a lot slower. This is because we are
calling `pow()` every single time, which does the full exponentiation for us,
while in the above "manual" solution we do one single arbitrarily large
exponentiation *one step at a time*, stopping when needed. This is not really a
big issue since Python uses a fast exponentiation algorithm to do this
calculation, called [exponentiation by squaring][wiki-binary-exponentiation],
but it's slower nonetheless since we cannot just supply a big number to `pow()`
and make it "stop" when we want (we need to call it once for each attempt).

Either way, regardless of the method we use, once the loop is finished and we
have found a value for `x`, depending on whether we have found a match for the
public key `A` or `B`, we can then use that value to apply the transformation to
the other public key and calculate the secret key as the problem statement
explains:

```python
if v == A:
    # x is the "loop size" of the device with public key A
    secret_key = pow(B, x, 20201227)
else:
    # x is the "loop size" of the device with public key B
    secret_key = pow(A, x, 20201227)

print('Part 1:', secret_key)
```

Or more consicely using a [conditional expression][py-conditional-expression]:

```python
secret_key = pow(B if v == A else A, x, 20201227)
print('Part 1:', secret_key)
```

This is probably what most people did, and it's a prefectly valid solution which
does not really require any background knowledge. I implemented it
[**here**][d25-alternative] for reference.

This solution is however quite slow, a lot slower than the optimal solution, and
also really boring! So let me go ahead and explain the *real* solution to this
problem.

### Purely mathematical solution

As we said in the previous section, it's easy to notice by writing it down as a
simple loop in really any programming language (or even in pseudocode on paper),
that the above "transformation" is nothing more than the [modular
exponentiation][wiki-modular-exp] of a given number (the "subject number") to
the power of *x* (the "loop size") modulo *20201227*.

Let *A* and *B* be the two public keys given as our input. We want to find
either one of two unknown values *a* and *b* such that *7<sup>a</sup>* mod
*20201227* = *A* or *7<sup>b</sup>* mod *20201227* = *B*. In other words, we
want to compute the [discrete logarithm][wiki-discrete-log] modulus *20201227*
of either *A* or *B* to base *7*.

There are known algorithms for computing the discrete logarithm of a number
given a modulus and a base. If you want, you can scroll right to the solution
below, but first I would like to give some background information on what is
actually happening here. Some [modular arithmetic][wiki-modular-arithmetic]
knowledge would be useful to understand what I'm going to explain, but I'll try
to be as clear as possible either way.

What was described in the problem statement in a rather verbose manner is an
algorithm best known as [Diffie-Hellman key exchange][wiki-diffie-hellman]. This
algorithm allows two parties to securely compute the same secret key, using a
pre-established common base *g* and modulus *p*, and exchanging each other's
public keys over an insecure channel. In the above explanation *p = 20201227*
(which must be a prime number, and indeed it is), and *g = 7* (which must be a
[primitive root][wiki-primitive-root] modulo *p*). As we just said, the
described "transformation" of a number is nothing more than a modular
exponentiation, which is the fundamental modular transformation that the
Diffie-Hellman key exchange algorithm is based upon.

We can rewrite the problem statement as follows:

> Given the public base *g = 7*, the public modulo *p = 20201227*, and the two
> public keys *A* and *B* (obtained as *A = g<sup>a</sup>* mod *p*,
> *B = g<sup>b</sup>* mod *p*), calculate the secret key *s* = *A<sup>b</sup>*
> mod *p* = *B<sup>a</sup>* mod *p*.

The Diffie-Hellman key exchange algorithm works because since
*A ≡ g<sup>a</sup>* (mod *p*) and *B ≡ g<sup>b</sup>* (mod *p*), we have
*s ≡ A<sup>b</sup>* ≡ *B<sup>a</sup>* ≡ *g<sup>ab</sup>* (mod *p*), no matter
the values chosen for the two secret exponents *a* and *b*.

When intercepting the public keys exchanged between the two devices, we are
performing what is known as [eavesdropping][wiki-eavesdropping]. We then want to
use the obtained information (the public keys), knowing the already public
information (*p* and *g*). What we are really being asked is in fact just
*"please crack this Diffie-Hellman key exchange and find the shared secret key
given two [sniffed][wiki-sniffing] public keys"*.

The Diffie-Hellman key exchange is a secure algorithm whose primary purpose is
*exactly* to be resistant against such an attack, **given that "good enough"
values for *p*, *a* and *b* are chosen** (as explained towards the end of the
"Cryptographic explanation" section of the wikipedia article). The resistance of
the Diffie-Hellman key exchange against an attempt to discover the computed
common secret key comes from the fact that, in order to do so, one must be able
to solve the [discrete logarithm][wiki-discrete-log] modulo *p* of *A* to base
*g*.

To put it in simple terms: no efficient method exists to compute the discrete
logarithm of a given number when *g* (and therefore *p*) are effectively chosen
to be large enough, as there is no known "general" algorithm with a reasonable
[time complexity][wiki-time-complexity] to compute the discrete logarithm. For
large enough values of *p* (hundreds of digits), it is therefore humanly
impossible to compute the discrete logarithm (and by that I mean that no
existing computer could solve the problem in less than thousands of years).

**Back to the problem now.**

As it turns out, the numbers chosen for today's puzzle are very far from being
cryptographically secure. In fact, they are extremely small, and make the
solution very easily computable with the right algorithm even using just pen and
paper (I should know this very well because this was one of the exercises given
in the "foundamentals of network security" course at my university).

The most commonly known algorithm for computing the discrete logarithm is the
[baby-step giant-step algorithm][wiki-bsgs]. I will not get into the details of
the algorithm, as its demonstration (and therefore understanding) requires a
decent background of modular algebra. Nonetheless, countless implementations
both in actual code and in pseudo-code are available online through a simple
Google search.

Here's my Python implementation of the baby-step giant-step algorithm. Note that
the discrete logarithm does *not* always have a solution, and that `p` must be
prime for the following to work.

```python
def bsgs(base, n, p):
    m     = ceil(sqrt(p))
    table = {pow(base, i, p): i for i in range(m)}
    inv   = pow(base, (p - 2) * m, p) # base^(-m) mod p == base^(m*(p-2)) assuming p is prime
    res   = None

    for i in range(m):
        y = (n * pow(inv, i, p)) % p
        if y in table:
            res = i * m + table[y]
            break

    return res
```

Aaand... that's basically it, now we can easily calculate the private exponent
(`a`) of either party by using baby-step giant-step to compute the discrete
logarithm (base `7` modulo `20201227`) of one of the public keys (`A`), and then
compute the secret key by modular exponentiation (modulo `20201227`) of the
other key (`B`) to the power of `a`. It literally takes more time to say it than
to write it.

```python
fin = open(...)

A, B = map(int, fin)
a    = bsgs(7, A, 20201227)
key  = pow(B, a, 20201227)

print('Part 1:', key)
```

As usual, there is no part 2 for the 25th day of Advent of Code, so our magical
journey for this year is over. Merry Christmas!

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
[d08]: #day-8---handheld-halting
[d09]: #day-9---encoding-error
[d10]: #day-10---adapter-array
[d11]: #day-11---seating-system
[d12]: #day-12---rain-risk
[d13]: #day-13---shuttle-search
[d14]: #day-14---docking-data
[d15]: #day-15---rambunctious-recitation
[d16]: #day-16---ticket-translation
[d17]: #day-17---conway-cubes
[d18]: #day-18---operation-order
[d19]: #day-19---monster-messages
[d20]: #day-20---jurassic-jigsaw
[d21]: #day-21---allergen-assessment
[d22]: #day-22---crab-combat
[d23]: #day-23---crab-cups
[d24]: #day-24---lobby-layout
[d25]: #day-25---combo-breaker

[d01-problem]: https://adventofcode.com/2020/day/1
[d02-problem]: https://adventofcode.com/2020/day/2
[d03-problem]: https://adventofcode.com/2020/day/3
[d04-problem]: https://adventofcode.com/2020/day/4
[d05-problem]: https://adventofcode.com/2020/day/5
[d06-problem]: https://adventofcode.com/2020/day/6
[d07-problem]: https://adventofcode.com/2020/day/7
[d08-problem]: https://adventofcode.com/2020/day/8
[d09-problem]: https://adventofcode.com/2020/day/9
[d10-problem]: https://adventofcode.com/2020/day/10
[d11-problem]: https://adventofcode.com/2020/day/11
[d12-problem]: https://adventofcode.com/2020/day/12
[d13-problem]: https://adventofcode.com/2020/day/13
[d14-problem]: https://adventofcode.com/2020/day/14
[d15-problem]: https://adventofcode.com/2020/day/15
[d16-problem]: https://adventofcode.com/2020/day/16
[d17-problem]: https://adventofcode.com/2020/day/17
[d18-problem]: https://adventofcode.com/2020/day/18
[d19-problem]: https://adventofcode.com/2020/day/19
[d20-problem]: https://adventofcode.com/2020/day/20
[d21-problem]: https://adventofcode.com/2020/day/21
[d22-problem]: https://adventofcode.com/2020/day/22
[d23-problem]: https://adventofcode.com/2020/day/23
[d24-problem]: https://adventofcode.com/2020/day/24
[d25-problem]: https://adventofcode.com/2020/day/25

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
[d23-solution]: solutions/day23.py
[d24-solution]: solutions/day24.py
[d25-solution]: solutions/day25.py

[d08-better-solution]:  https://www.reddit.com/r/adventofcode/comments/k8zdx3
[d12-alternative]:      misc/day12/complex.py
[d13-alternative]:      misc/day13/modular_arithmetic.py
[d18-alternative-1]:    misc/day18/shunting_yard.py
[d18-alternative-2]:    misc/day18/hack.py
[d19-alternative]:      misc/day19/regexp_hack.py
[d25-alternative]:      misc/day25/brute.py
[2019-d05]:             https://github.com/mebeim/aoc/blob/master/2019/README.md#day-5---sunny-with-a-chance-of-asteroids
[2019-vm]:              https://github.com/mebeim/aoc/blob/master/2019/lib/intcode.py#L283
[2019-d16-reflections]: https://github.com/mebeim/aoc/blob/master/2019/README.md#reflections-1

[utils-selective-cache]: https://github.com/mebeim/aoc/blob/bd28a12be5444126dc531e8594181e0275424ee8/utils/decorators.py#L21

[py-assert]:                  https://docs.python.org/3/reference/simple_stmts.html#the-assert-statement
[py-complex]:                 https://docs.python.org/3/library/stdtypes.html#numeric-types-int-float-complex
[py-conditional-expression]:  https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-dict-comprehension]:      https://www.python.org/dev/peps/pep-0274/
[py-format-string]:           https://docs.python.org/3/library/string.html#formatstrings
[py-generator-expr]:          https://www.python.org/dev/peps/pep-0289/
[py-lambda]:                  https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-list-comprehension]:      https://docs.python.org/3/tutorial/datastructures.html#list-comprehensions
[py-power]:                   https://docs.python.org/3/reference/expressions.html#the-power-operator
[py-raw-string]:              https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
[py-slice]:                   https://docs.python.org/3/library/functions.html?highlight=slice#slice
[py-unpacking]:               https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists
[py-yield-from]:              https://docs.python.org/3.9/whatsnew/3.3.html#pep-380

[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-bool]:            https://docs.python.org/3/library/functions.html#bool
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-eval]:            https://docs.python.org/3/library/functions.html#eval
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-pow]:             https://docs.python.org/3/library/functions.html#pow
[py-builtin-range]:           https://docs.python.org/3/library/functions.html#range
[py-builtin-reversed]:        https://docs.python.org/3/library/functions.html#reversed
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-counter]:     https://docs.python.org/3/library/collections.html#collections.Counter
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-copy]:                    https://docs.python.org/3/library/copy.html
[py-copy-deepcopy]:           https://docs.python.org/3/library/copy.html#copy.deepcopy
[py-deque-appendleft]:        https://docs.python.org/3/library/collections.html#collections.deque.appendleft
[py-deque-extend]:            https://docs.python.org/3/library/collections.html#collections.deque.extend
[py-deque-extendleft]:        https://docs.python.org/3/library/collections.html#collections.deque.extendleft
[py-deque-popleft]:           https://docs.python.org/3/library/collections.html#collections.deque.popleft
[py-deque-rotate]:            https://docs.python.org/3/library/collections.html#collections.deque.rotate
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-cache]:         https://docs.python.org/3/library/functools.html#functools.cache
[py-functools-lru-cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-itertools]:               https://docs.python.org/3/library/itertools.html
[py-itertools-chain]:         https://docs.python.org/3/library/itertools.html#itertools.chain
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-itertools-product]:       https://docs.python.org/3/library/itertools.html#itertools.product
[py-itertools-combinations]:  https://docs.python.org/3/library/itertools.html#itertools.combinations
[py-list-count]:              https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-math]:                    https://docs.python.org/3/library/math.html
[py-math-inf]:                https://docs.python.org/3/library/math.html#math.inf
[py-math-ceil]:               https://docs.python.org/3/library/math.html#math.ceil
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
[py-math-lcm]:                https://docs.python.org/3/library/math.html#math.lcm
[py-math-prod]:               https://docs.python.org/3/library/math.html#math.prod
[py-object-add]:              https://docs.python.org/3/reference/datamodel.html#object.__add__
[py-object-contains]:         https://docs.python.org/3/reference/datamodel.html#object.__contains__
[py-object-init]:             https://docs.python.org/3/reference/datamodel.html#object.__init__
[py-object-mul]:              https://docs.python.org/3/reference/datamodel.html#object.__mul__
[py-object-sub]:              https://docs.python.org/3/reference/datamodel.html#object.__sub__
[py-operator]:                https://docs.python.org/3/library/operator.html
[py-operator-add]:            https://docs.python.org/3/library/operator.html#operator.add
[py-operator-mul]:            https://docs.python.org/3/library/operator.html#operator.mul
[py-operator-itemgetter]:     https://docs.python.org/3/library/operator.html#operator.itemgetter
[py-re]:                      https://docs.python.org/3/library/re.html
[py-re-compile]:              https://docs.python.org/3/library/re.html#re.compile
[py-re-findall]:              https://docs.python.org/3/library/re.html#re.findall
[py-re-match]:                https://docs.python.org/3/library/re.html#re.match
[py-set]:                     https://docs.python.org/3/library/stdtypes.html#set
[py-set-intersection]:        https://docs.python.org/3/library/stdtypes.html#frozenset.intersection
[py-set-intersection-u]:      https://docs.python.org/3/library/stdtypes.html#frozenset.intersection_update
[py-set-union]:               https://docs.python.org/3/library/stdtypes.html#frozenset.union
[py-set-union-u]:             https://docs.python.org/3/library/stdtypes.html#frozenset.union_update
[py-str-count]:               https://docs.python.org/3/library/stdtypes.html#str.count
[py-str-format]:              https://docs.python.org/3/library/stdtypes.html#str.format
[py-str-isdigit]:             https://docs.python.org/3/library/stdtypes.html#str.isdigit
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-replace]:             https://docs.python.org/3/library/stdtypes.html#str.replace
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-strip]:               https://docs.python.org/3/library/stdtypes.html#str.strip
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[algo-manhattan]:          https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:           https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-extended-euclidean]: https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
[algo-bfs]:                https://en.wikipedia.org/wiki/Breadth-first_search
[algo-dfs]:                https://en.wikipedia.org/wiki/Depth-first_search
[algo-kahn]:               https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
[algo-binsrc]:             https://en.wikipedia.org/wiki/Binary_search_algorithm
[algo-wall-follower]:      https://en.wikipedia.org/wiki/Maze_solving_algorithm#Wall_follower

[wiki-2d-rotation]:           https://en.wikipedia.org/wiki/Rotations_and_reflections_in_two_dimensions
[wiki-binary-exponentiation]: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
[wiki-bitmask]:               https://en.wikipedia.org/wiki/Mask_(computing)
[wiki-bitwise-and]:           https://en.wikipedia.org/wiki/Bitwise_operation#AND
[wiki-bitwise-or]:            https://en.wikipedia.org/wiki/Bitwise_operation#OR
[wiki-bsgs]:                  https://en.wikipedia.org/wiki/Baby-step_giant-step
[wiki-cartesian-coords]:      https://en.wikipedia.org/wiki/Cartesian_coordinate_system
[wiki-cellular-automaton]:    https://en.wikipedia.org/wiki/Cellular_automaton
[wiki-chinese-remainder]:     https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Statement
[wiki-closure]:               https://en.wikipedia.org/wiki/Closure_(computer_programming)
[wiki-complex-numbers]:       https://en.wikipedia.org/wiki/Complex_number
[wiki-complex-rotation]:      https://en.wikipedia.org/wiki/Rotation_(mathematics)#Complex_numbers:~:text=This%20can%20be%20rotated%20through%20an%20angle
[wiki-constant-time]:         https://en.wikipedia.org/wiki/Time_complexity#Constant_time
[wiki-coprime]:               https://en.wikipedia.org/wiki/Coprime_integers
[wiki-coprime-set]:           https://en.wikipedia.org/wiki/Coprime_integers#Coprimality_in_sets
[wiki-cpython]:               https://en.wikipedia.org/wiki/CPython
[wiki-dag]:                   https://en.wikipedia.org/wiki/Directed_acyclic_graph
[wiki-diffie-hellman]:        https://en.wikipedia.org/wiki/Diffie%E2%80%93Hellman_key_exchange
[wiki-distributive-property]: https://en.wikipedia.org/wiki/Distributive_property
[wiki-discrete-log]:          https://en.wikipedia.org/wiki/Discrete_logarithm
[wiki-dynamic-programming]:   https://en.wikipedia.org/wiki/Dynamic_programming
[wiki-euclidean-division]:    https://en.wikipedia.org/wiki/Euclidean_division
[wiki-exponential-time]:      https://en.wikipedia.org/wiki/Time_complexity#Exponential_time
[wiki-functional-prog]:       https://en.wikipedia.org/wiki/Functional_programming
[wiki-heat-death-universe]:   https://en.wikipedia.org/wiki/Heat_death_of_the_universe
[wiki-hexgrid]:               https://en.wikipedia.org/wiki/Hexagonal_tiling
[wiki-hypercube]:             https://en.wikipedia.org/wiki/Hypercube
[wiki-infix-notation]:        https://en.wikipedia.org/wiki/Infix_notation
[wiki-jit]:                   https://en.wikipedia.org/wiki/Just-in-time_compilation
[wiki-john-horton-conway]:    https://en.wikipedia.org/wiki/John_Horton_Conway
[wiki-lcm]:                   https://en.wikipedia.org/wiki/Least_common_multiple
[wiki-lexical-analysis]:      https://en.wikipedia.org/wiki/Lexical_analysis
[wiki-linked-list]:           https://en.wikipedia.org/wiki/Linked_list
[wiki-linear-time]:           https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-manhattan-dist]:        https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[wiki-memoization]:           https://en.wikipedia.org/wiki/Memoization
[wiki-eavesdropping]:         https://en.wikipedia.org/wiki/Eavesdropping
[wiki-modular-arithmetic]:    https://en.wikipedia.org/wiki/Modular_arithmetic
[wiki-modular-congruence]:    https://en.wikipedia.org/wiki/Modular_arithmetic#Congruence
[wiki-modular-exp]:           https://en.wikipedia.org/wiki/Modular_exponentiation
[wiki-modular-inverse]:       https://en.wikipedia.org/wiki/Modular_multiplicative_inverse
[wiki-plane]:                 https://en.wikipedia.org/wiki/Plane_(geometry)
[wiki-polynomial-time]:       https://en.wikipedia.org/wiki/Time_complexity#Polynomial_time
[wiki-postfix-notation]:      https://en.wikipedia.org/wiki/Reverse_Polish_notation
[wiki-primitive-root]:        https://en.wikipedia.org/wiki/Primitive_root_modulo_n
[wiki-rubiks-cube]:           https://en.wikipedia.org/wiki/Rubik%27s_Cube
[wiki-running-total]:         https://en.wikipedia.org/wiki/Running_total
[wiki-set-intersection]:      https://en.wikipedia.org/wiki/Intersection_(set_theory)
[wiki-set-union]:             https://en.wikipedia.org/wiki/Union_(set_theory)
[wiki-shunting-yard]:         https://en.wikipedia.org/wiki/Shunting-yard_algorithm
[wiki-sniffing]:              https://en.wikipedia.org/wiki/Sniffing_attack
[wiki-sum-range]:             https://en.wikipedia.org/wiki/1_%2B_2_%2B_3_%2B_4_%2B_%E2%8B%AF
[wiki-time-complexity]:       https://en.wikipedia.org/wiki/Time_complexity
[wiki-tree]:                  https://en.wikipedia.org/wiki/Tree_(data_structure)
[wiki-undirected-graph]:      https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph
[wiki-vector]:                https://en.wikipedia.org/wiki/Euclidean_vector
[wiki-vm]:                    https://en.wikipedia.org/wiki/Virtual_machine

[misc-aoc-bingo]:         https://www.reddit.com/r/adventofcode/comments/k3q7tr/
[misc-call-day]:          https://dictionary.cambridge.org/dictionary/english/call-it-a-day
[misc-cool]:              https://www.youtube.com/watch?v=zDcbpFimUc8
[misc-man1-tr]:           https://man7.org/linux/man-pages/man1/tr.1.html
[misc-pypy]:              https://www.pypy.org/
[misc-regex-module]:      https://pypi.org/project/regex/
[misc-regexp]:            https://www.regular-expressions.info/
[misc-regexp-anchors]:    https://www.regular-expressions.info/anchors.html
[misc-regexp-group]:      https://www.regular-expressions.info/brackets.html
[misc-regexp-pipe]:       https://www.regular-expressions.info/alternation.html
[misc-regexp-repetition]: https://www.regular-expressions.info/repeat.html
[misc-van-eck]:           https://oeis.org/A181391
