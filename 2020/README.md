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

[Problem statement][d08-problem] — [Complete solution][d08-solution] ([current VM][d08-vm]) — [Back to top][top]

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

**NOTE**: I'll try to create a simpler VM implementation than my last year's
[`IntcodeVM`][2019-vm]. Since the VM implementation will likely change and I
will keep updating the same file, I'll just link to the exact version of the
code at the time of writing, containing the current VM implementation, which
we'll be writing ritht now. You can find the link above.

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

            # If somehow the program counter gets outside vm.prog bounds we cannot continue
            if not (0 <= self.pc < self.prog_len):
                raise VMRuntimeError('bad program counter')

            steps -= 1
```

That `VMRuntimeError` is a custom `Exception` which I'll `raise` when things go
bad. It will help debugging if placed in the correct places when the code gets
more complicated. It's defined like this for now:

```python
class VMRuntimeError(Exception):
    pass
```

Now let's actually solve the problem! We can finally `import` our `VM` and put
it to good use. To detect when an instruction is executed again, we can save the
values of the program counter (`vm.pc`) in a [`set`][py-set], since the program
counter uniquely identifies an instruction in the whole program, and stop if we
ever get a value that was already seen.

```python
from lib.vm import VM

fin = open(...)
source = fin.read()
vm = VM(source)

seen = set()
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
(on my machine where one execution of the program takes less than 300
microseconds).

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

Long story short: we are given a list of numbers and we were told (with a
reeeeally long explanation) that these numbers respect a certain rule: when
sorted, the difference between any pair of consecutive numbers is always
between at least 1 and at most 3.

We want to count how many of these numbers have a difference of (A) exactly 1
and (B) exactly 3. The answer we must give is the product of these two counts.

Looks pretty simple: in order to do this we can sort the input sequence and then
scan it starting from the second number. Let's do the sorting right away using
the built-in [`sorted()`][py-builtin-sorted] function:

```python
nums = map(int, fin.readlines())
nums = sorted(nums)
```

Then, we can cycle through the numbers and check each of them against its
successor to see if their difference is `1` or `3`. Beware though: the first
time we find a match (for distance 1 and 3) it means we actually have *two*
numbers matching. After that, each match only discovers one new number at a
time. This means that we need to add 1 to both counters. I do this by
initializing them to `1`.

To iterate over pairs of consecutive numbers we can take advantage of the
[`zip()`][py-builtin-zip] function passing `nums, nums[1:]` as arguments. The
checks are straightforward.

```python
dist1, dist3 = 1, 1

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
We also need to start each sequence with a `0` (which is not in our input) and
end it with the maximum value we have plus 3.

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

Our list is kind of long, and we are told that the solution is inthe order of
trillions, so we can't really use bruteforce testing all possible subsets of
numbers. This problem can be solved using
[dynamic programming][wiki-dynamic-programming].

Let's start by adding `0` and `max + 3` to our list, since we always need those:

```python
nums = [0] + nums + [max(nums) + 3]
```

Remember that our numbers are still sorted. For each number, we have the
possibility to chose betwee 1 and 3 successors. For example if we have
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
times, our recursive call will end up being called with the same `i`, therefore
calculating the same value multiple times. If we [memoize][wiki-memoization] the
results (just like we did to optimize [day 7][d07] part 2) we can save an
*enormous* amount of work.

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
    since calling `possible_solutions()` multiple times from the outside just
    creates new copies of `real_fn()`, which *don't* share the same cache.

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
   use as keys for memoization. This solution a lot cooler, but it obviously
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

For each bus, we can to calculate the amount of time that we would need to wait
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

There are two approaches to solving this problem: one is simpler, with a
combination of math and bruteforce, the second one is purely mathematical and
involves modular arithmetic. While the first is simpler to explain in practice,
I'll explain both step by step, since I cannot pick a favorite and really enjoy
both approaches.

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
between the two, whch is `6`.

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
[modular arithmetic][wiki-modular-arithmetic] is required, so go ahead and read
the Wikipedia articles I'll be linking from now on if you have never heard of
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
simplest algorithm to explain, but nonetheless I've implemented this in
[my solution][d13-alternative], so you can check that out if you want, or just
let Google be your friend.

We could simplify the calculation of `P` above using a simple
[`functools.reduce()`][py-functools-reduce] with
[`operator.mul()`][py-operator-mul] plus a [`lambda`][py-lambda] to extract the
moduli from the equations:

```python
from functools import reduce
from operator import mul

P = reduce(mul, map(lambda e: e[1], equations))
```

Or even better also using [`operator.itemgetter()`][py-operator-itemgetter]:

```python
from functools import reduce
from operator import mul, itemgetter

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
bits at the same position in the value. Therefore, we can create a *real mask*
which has a `1` for each `X` in the mask, and a `0` anywhere else.

Here's an example with only 8 bits to make it simple, the operation can be
performed with any number of bits:

```
     mask  X11XXX0X
real mask  10011101
```

We can then use this real mask to actually mask the input value with a
[*bitwise AND*][wiki-bitwise-and] (`&` in Python), zeroing out every bit of
`value` that needs to be overwritten by the corresponding `0` or `1` bit in the
mask. Then, we can extract an actual number (let's call it *addend*) from the
original mask (ignoring all `X`) and add it to the value. This has the effect of
overwriting all value bits at the same position of zeros and ones in the mask,
with the value they have in the mask.

To make it clear, here's an example:

```
     mask  X11XXX0X
real mask  10011101
   addend  01100000

Suppose value = 42

       value  00101010 &
   real mask  10011101 =
masked value  00001000

masked value  00001000 +
      addend  01100000 =
 final value  01101000   --> write this to memory
```

Now to extract two values from the mask:

- For the *real mask* we need to perform 2 replacements: `1` with `0` and `X`
  with `1`, then turn the string into an `int`. We can use
  [`str.maketrans()`][py-str-maketrans] plus
  [`str.translate()`][py-str-translate] for this, just like we did in
  [day 5][d05].
- For the *addend* we just need to replace every `X` with `0` and then turn the
  string into an `int`.

Finally, when writing to memory, we'll calculate the value as we did in the
above example. The code is quite simple really:

```python
table = str.maketrans('1X', '01')
mem = {}

for line in lines:
    if line.startswith('mask'):
        mask      = line[7:].rstrip()
        real_mask = int(mask.translate(table), 2)
        addend    = int(mask.replace('X', '0'), 2)
    else:
        addr, value = map(int, rexp.findall(line)[0])
        mem[addr] = (value & real_mask) | addend
```

I use `|` as a bitwise alternative to `+`, the operation really is the same in
this case.

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

All that's left to do is parse each line and use the above function. To
transform the decimal addresses that we read from the input into a binary string
we can use a [format string][py-format-string] specifying `036b` as format.

```python
mem = {}
for line in lines:
    if line.startswith('mask'):
        mask = line[7:].rstrip()
    else:
        addr, value = map(int, rexp.findall(line)[0])
        addr = '{:036b}'.format(addr)

        for a in all_addrs(addr, mask):
            mem[a] = value

total = sum(mem.values())
print('Part 2:', total)
```

An alternative manual implementation of the `product()` function for our
specific use case would be a recursive generator function that takes an already
masked address and yields an integer if the address does not contain any `X`,
otherwise does a recursive call to get all possible values replacing that `X`
with a `0` and a `1`. The [`yield from`][py-yield-from] "generator delegation"
syntax comes in handy.

```python
def all_addrs(addr):
    if 'X' in addr:
        yield from all_addrs(addr.replace('X', '0', 1))
        yield from all_addrs(addr.replace('X', '1', 1))
    else:
        yield int(addr, 2)

# list(all_addrs('1XX')) -> [0b100, 0b101, 0b110, 0b111] -> [4, 5, 6, 7]
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
            # Before the previous turn, prev was seen at turn last_sen[prev]
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
from 360MB to 404MB on my machine using CPython).

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
`cur = prev_turn - last_seen[prev]` right away, then if the number was already
seen we'll have `last_seen[prev]` and therefore `cur == prev_turn`.

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
very detailed plane tickets.

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
    field_rexp = re.compile(r'(.+): (\d+)-(\d+) or (\d+)-(\d+)')

    for line in map(str.rstrip, fin):
        if not line:
            break

        field, *numbers = field_rexp.findall(line)[0]
        numbers = map(int, numbers)
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
for each of the valid ticket, for all fields we want to check if any of the
ticket values violate the field validity requirements. If it does, we'll remove
the index of that value as a possible index for the field.

We can iterate over `ranges` and `possible` pairwise using
[`zip()`][py-builtin-zip], and use [`enumerate()`][py-builtin-enumerate] to scan
the values of each ticket while also keeping track of their index.

```python
# For each valid ticket
for ticket in filter(is_valid, tickets):
    # For every field and its possible indexes
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
    # Start with None for all fields so that we can catch errors later if some
    # None is not replaced.
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

Now, simply look at the correct index in our ticket for the first 6 fields. In
order to multiply the values together we can use the helpful
[`math.prod()`][py-math-prod].

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
cells are dead, except of a few in the [plane][wiki-plane] `z=0`.

Our input consists of the initial state of the cells at `z=0`: we are given a
grid of characters (`#` for alive, `.` for dead) which is 8 columns wide and 8
rows tall, representing a portion of 3D space from `(0, 0, 0)` to `(7, 7, 0)`.

We need to simulate life according to two simple rules of evolution from one
generation to the next:

- If a cell is dead (`.`) and exactly 3 of its neighbors are alive, the cell
  becomes alive (`#`).
- If a cell is alive (`#`) and exactly 2 or 3 of its neighbors are alive, the cell
  *stays alive*, otherwise it dies (`.`).

In 3D space, "neighbors" of a cell means any of the 26 other cells where any of
their coordinates differ by at most 1. That is, the entire 3x3 cube of cells
centered at the cell, except the cell itself. You can also see this as the 26
pieces of a [Rubik's cube][wiki-rubiks-cube].

After evolving for 6 generations, we need to count the number of cells that are
alive.

Let's get the input parsing out of the way. We have a grid of characters as
input, so we can just [`rstrip`][py-str-rstrip] each line of input to remove
trailing newlines using [`map()`][py-builtin-map] and turn the whole thing into
a `tuple`.

```python
grid = tuple(map(str.rstrip, fin))
```

Before we begin writing any more code, we need to think about which data
structure to use to hold information about cells. It's important to notice that
we can expand in *any* of the three dimensions, so using matrixes (i.e. nested
`list`s) to represent each level of our 3-dimensional space is not as simple as
it looks.

After all, we do not really care how cells are arranged. The only thing we care
about is being able to tell if a given point `(x, y, z)` in space represents a
cell that is alive or not. In other words, we only want to keep track of the
points in space that represent alive cells; we can consider anything else dead.

To do this, we can simply use a `set` of coordinates. Our initial `grid`
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
is in our `cube`. We don't need to do any bound checking since we don't actually
have bounds. Doing `coords in cube` is enough to check if a cell at `coords` is
alive.

```python
def alive_neighbors(cube, x, y, z):
    alive = 0
    for xx in range(x - 1, x + 2):
        for yy in range(y - 1, y + 2):
            for zz in range(z - 1, z + 2):
                # Avoid checking the same cell as the one with the given coordinates
                if xx != x or yy != y or zz != z:
                    if (xx, yy, zz) in cube:
                        alive += 1
    return alive
```

We can simplify the above nested loops with the help of
[`itertools.product()`][py-itertools-product]:

```python
from itertools import product

def alive_neighbors(cube, x, y, z):
    alive = 0
    for coords in product(range(x-1, x+2), range(y-1, y+2), range(z-1, z+2)):
        if coords in cube:
            alive += 1

    # Avoid the checking in the above loop and just subtract 1 if we counted the given cell
    if (x, y, z) in cube:
        alive -= 1

    return alive
```

Now we need to evolve the cells. The cells in our `cube` are enclosed in a
limited cube in space. We want to iterate over each cell of said cube. In
addition to this, as we noticed earlier, each generation there's also
possibility that this limited cube "expands". Any of the cells that are adjacent
to the faces of the cube could potentially become alive if there are exactly 3
alive cells near it on the face.

For example, in an analogous 2D situation (sorry, can't really do 3D ASCII-art):

```
.......      .......
.......      .......
..##...      ..##...
...#...  =>  .......
..###..      ..###..
.......      ...#... <-- expansion
.......      .......
```

To determine the bounds of our limited cube, we need to check the minimum and
maximum of each dimension (`x`, `y`, `z`) of all the coordinates we have. In
order to do this, we can use [`max()`][py-builtin-max] plus `map()` to extract a
given coordinate from each point. Since we also want to check around the cube,
we'll subtract `1` from each minimum coordinate and add `1` to each maximum
coordinate (actually `2` since we'll iterate using [`range()`][py-builtin-range]
which stops one earlier).

```python
def bounds(cube):
    lox = min(map(lambda p: p[0], cube)) - 1
    loy = min(map(lambda p: p[1], cube)) - 1
    loz = min(map(lambda p: p[2], cube)) - 1
    hix = max(map(lambda p: p[0], cube)) + 2
    hiy = max(map(lambda p: p[1], cube)) + 2
    hiz = max(map(lambda p: p[2], cube)) + 2
    return range(lox, hix), range(loy, hiy), range(loz, hiz)
```

We can also use [`operator.itemgetter()`][py-operator-itemgetter] to simplify
the above:

```python
def bounds(cube):
    lox = min(map(itemgetter(0), cube)) - 1
    # ...
```

Now that we figured this out, all we have to do is iterate over all possible
coordinates from `(minx-1, miny-1, minz-1)` to `(maxx+1, maxy+1, maxz+1)` and
apply the rules. Let's write a function for this:

```python
def evolve(cube):
    new = set()
    rangex, rangey, rangez = bounds(cube)

    for x in rangex:
        for y in rangey:
            for z in rangez:
                alive = alive_neighbors(cube, x, y, z)

                if (x, y, z) in cube:
                    if alive == 2 or alive == 3:
                        # alive cell stays alive only if exactly 2 or 3 neighbors are alive
                        new.add((x, y, z))
                elif alive == 3:
                    # dead cell becomes alive only if exactly 3 neighbors are alive
                    new.add((x, y, z))

    return new
```

Hmm... That's kind of ugly. Those `3` ranges we return are the perfect use case
for `itertools.product()`, so let's simplify:

```python
def evolve(cube):
    new = set()

    for coords in product(*bounds(cube)):
        # coords is (x, y, z)
        alive = alive_neighbors(cube, *coords)

        # Simplified conditions from above
        if (coords in cube and alive in (2, 3)) or alive == 3:
            new.add(coords)

    return new
```

That's nice. We can even turn the `bounds()` function into a generator for added
coolness:

```python
def bounds(cube):
    for i in range(3):
        lo = min(map(itemgetter(i), cube)) - 1
        hi = min(map(itemgetter(i), cube)) + 2
        yield range(lo, hi)
```

Beautiful! The other code needs no change.

Now that we have all we need, we can finally start simulating. We want to
simulate 6 generations, then stop and count alive cells: since our `cube` is
just a set of coordinates of alive cells, we can just take its size after the
final evolution.

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

Oh no! All the code we wrote works with 3 dimensions, do we need to rewrite
everything? Well, not quite. We can make the functions a little bit more
general, adding the number of dimensions as parameter. The code of each function
stays almost the same, we only need minor changes.

To count alive neighbors, we would need to take an additional parameter `w` for
the fourth dimension. Let's make it general, taking a tuple of `coords` instead.
For each coordinate `c` we will create a tuple `(c - 1, c, c + 1)`, then pass
all those tuples to `itertools.product()`.

```python
def alive(cube, coords):
    alive  = 0
    ranges = ((c - 1, c, c + 1) for c in coords)

    for coords2 in product(*ranges):
        if coords2 in cube:
            alive += 1

    if coords in cube:
        alive -= 1

    return alive
```

The loop we are doing can really just be simplified down to a single `sum()`:

```python
def alive_neighbors(cube, coords):
    ranges = ((c - 1, c, c + 1) for c in coords)
    alive = sum(p in cube for p in product(*ranges))
    if coords in cube:
        alive -= 1
    return alive
```

To determine the bounds of our cube (which is now an
[hypercube][wiki-hypercube]), we can make `bounds()` more general and just
accept the number of dimensions as parameter:

```python
def bounds(cube, n_dims):
    for i in range(n_dims):
        lo = min(map(itemgetter(i), cube)) - 1
        hi = max(map(itemgetter(i), cube)) + 2
        yield range(lo, hi)
```

Finally, we'll also pass the number of dimensions to `evolve()`, in order to be
able to pass it to `bounds()`:

```python
def evolve(cube, n_dims):
    new = set()

    for coord in product(*bounds(cube, n_dims)):
        alive = alive_neighbors(cube, coord)

        if (coord in cube and alive in (2, 3)) or alive == 3:
            new.add(coord)

    return new
```

The loop for part 1 now becomes:

```python
for _ in range(6):
    cube = evolve(cube, 3)
```

And for part 2 all we have to do is create another cube with an additional
coordinate set to `0` for all initial points:

```python
hypercube = set()

for x, row in enumerate(grid):
    for y, cell in enumerate(row):
        if cell == '#':
            hypercube.add((x, y, 0, 0))
```

Finally we can simulate again passing `n_dims=4` and get our answer:

```python
for _ in range(6):
    hypercube = evolve(hypercube, 4)

total_alive = len(hypercube)
print('Part 2:', total_alive)
```

What a nice puzzle!

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

[d08-vm]:              https://github.com/mebeim/aoc/blob/4d718c58358c406b650d69e259fff7c5c2a6e94c/2020/lib/vm.py
[d08-better-solution]: https://www.reddit.com/r/adventofcode/comments/k8zdx3
[d12-alternative]:     misc/day12/complex.py
[d13-alternative]:     misc/day13/modular_arithmetic.py

[2019-d05]:             https://github.com/mebeim/aoc/blob/master/2019/README.md#day-5---sunny-with-a-chance-of-asteroids
[2019-vm]:              https://github.com/mebeim/aoc/blob/master/2019/lib/intcode.py#L283
[2019-d16-reflections]: https://github.com/mebeim/aoc/blob/master/2019/README.md#reflections-1

[utils-selective-cache]: https://github.com/mebeim/aoc/blob/bd28a12be5444126dc531e8594181e0275424ee8/utils/decorators.py#L21

[py-complex]:                 https://docs.python.org/3/library/stdtypes.html#numeric-types-int-float-complex
[py-dict-comprehension]:      https://www.python.org/dev/peps/pep-0274/
[py-format-string]:           https://docs.python.org/3/library/string.html#formatstrings
[py-generator-expr]:          https://www.python.org/dev/peps/pep-0289/
[py-lambda]:                  https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-raw-string]:              https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals
[py-unpacking]:               https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists
[py-yield-from]:              https://docs.python.org/3.9/whatsnew/3.3.html#pep-380
[py-list-count]:              https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
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
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate
[py-object-init]:             https://docs.python.org/3/reference/datamodel.html#object.__init__
[py-object-contains]:         https://docs.python.org/3/reference/datamodel.html#object.__contains__
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-pow]:             https://docs.python.org/3/library/functions.html#pow
[py-builtin-range]:           https://docs.python.org/3/library/functions.html#range
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-copy]:                    https://docs.python.org/3/library/copy.html
[py-copy-deepcopy]:           https://docs.python.org/3/library/copy.html#copy.deepcopy
[py-itertools]:               https://docs.python.org/3/library/itertools.html
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-itertools-product]:       https://docs.python.org/3/library/itertools.html#itertools.product
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-cache]:         https://docs.python.org/3/library/functools.html#functools.cache
[py-functools-lru-cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-math]:                    https://docs.python.org/3/library/math.html
[py-math-inf]:                https://docs.python.org/3/library/math.html#math.inf
[py-math-ceil]:               https://docs.python.org/3/library/math.html#math.ceil
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
[py-math-lcm]:                https://docs.python.org/3/library/math.html#math.lcm
[py-math-prod]:               https://docs.python.org/3/library/math.html#math.prod
[py-operator-mul]:            https://docs.python.org/3/library/operator.html#operator.mul
[py-operator-itemgetter]:     https://docs.python.org/3/library/operator.html#operator.itemgetter
[py-re]:                      https://docs.python.org/3/library/re.html
[py-re-findall]:              https://docs.python.org/3/library/re.html#re.findall

[algo-manhattan]:          https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:           https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-extended-euclidean]: https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
[algo-bfs]:                https://en.wikipedia.org/wiki/Breadth-first_search
[algo-dfs]:                https://en.wikipedia.org/wiki/Depth-first_search
[algo-kahn]:               https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
[algo-binsrc]:             https://en.wikipedia.org/wiki/Binary_search_algorithm
[algo-wall-follower]:      https://en.wikipedia.org/wiki/Maze_solving_algorithm#Wall_follower

[wiki-2d-rotation]:         https://en.wikipedia.org/wiki/Rotations_and_reflections_in_two_dimensions
[wiki-bitmask]:             https://en.wikipedia.org/wiki/Mask_(computing)
[wiki-bitwise-and]:         https://en.wikipedia.org/wiki/Bitwise_operation#AND
[wiki-cartesian-coords]:    https://en.wikipedia.org/wiki/Cartesian_coordinate_system
[wiki-cellular-automaton]:  https://en.wikipedia.org/wiki/Cellular_automaton
[wiki-chinese-remainder]:   https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Statement
[wiki-closure]:             https://en.wikipedia.org/wiki/Closure_(computer_programming)
[wiki-complex-numbers]:     https://en.wikipedia.org/wiki/Complex_number
[wiki-complex-rotation]:    https://en.wikipedia.org/wiki/Rotation_(mathematics)#Complex_numbers:~:text=This%20can%20be%20rotated%20through%20an%20angle
[wiki-coprime]:             https://en.wikipedia.org/wiki/Coprime_integers
[wiki-coprime-set]:         https://en.wikipedia.org/wiki/Coprime_integers#Coprimality_in_sets
[wiki-cpython]:             https://en.wikipedia.org/wiki/CPython
[wiki-dag]:                 https://en.wikipedia.org/wiki/Directed_acyclic_graph
[wiki-dynamic-programming]: https://en.wikipedia.org/wiki/Dynamic_programming
[wiki-euclidean-division]:  https://en.wikipedia.org/wiki/Euclidean_division
[wiki-exponential-time]:    https://en.wikipedia.org/wiki/Time_complexity#Exponential_time
[wiki-functional-prog]:     https://en.wikipedia.org/wiki/Functional_programming
[wiki-hypercube]:           https://en.wikipedia.org/wiki/Hypercube
[wiki-jit]:                 https://en.wikipedia.org/wiki/Just-in-time_compilation
[wiki-john-horton-conway]:  https://en.wikipedia.org/wiki/John_Horton_Conway
[wiki-lcm]:                 https://en.wikipedia.org/wiki/Least_common_multiple
[wiki-linear-time]:         https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-manhattan-dist]:      https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[wiki-memoization]:         https://en.wikipedia.org/wiki/Memoization
[wiki-modular-arithmetic]:  https://en.wikipedia.org/wiki/Modular_arithmetic
[wiki-modular-congruence]:  https://en.wikipedia.org/wiki/Modular_arithmetic#Congruence
[wiki-modular-inverse]:     https://en.wikipedia.org/wiki/Modular_multiplicative_inverse
[wiki-plane]:               https://en.wikipedia.org/wiki/Plane_(geometry)
[wiki-polynomial-time]:     https://en.wikipedia.org/wiki/Time_complexity#Polynomial_time
[wiki-reduction]:           https://en.wikipedia.org/wiki/Reduction_Operator
[wiki-rubiks-cube]:         https://en.wikipedia.org/wiki/Rubik%27s_Cube
[wiki-running-total]:       https://en.wikipedia.org/wiki/Running_total
[wiki-set-intersection]:    https://en.wikipedia.org/wiki/Intersection_(set_theory)
[wiki-set-union]:           https://en.wikipedia.org/wiki/Union_(set_theory)
[wiki-sum-range]:           https://en.wikipedia.org/wiki/1_%2B_2_%2B_3_%2B_4_%2B_%E2%8B%AF
[wiki-vector]:              https://en.wikipedia.org/wiki/Euclidean_vector
[wiki-vm]:                  https://en.wikipedia.org/wiki/Virtual_machine

[misc-aoc-bingo]: https://www.reddit.com/r/adventofcode/comments/k3q7tr/
[misc-man1-tr]:   https://man7.org/linux/man-pages/man1/tr.1.html
[misc-pypy]:      https://www.pypy.org/
[misc-regexp]:    https://www.regular-expressions.info/
[misc-van-eck]:   https://oeis.org/A181391
