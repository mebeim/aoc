Advent of Code 2024 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Historian Hysteria][d01]
- [Day 2 - Red-Nosed Reports][d02]
- [Day 3 - Mull It Over][d03]
- [Day 4 - Ceres Search][d04]
- *Day 5 - Print Queue: TODO*
- *Day 6 - Guard Gallivant: TODO*
- *Day 7 - Bridge Repair: TODO*
- [Day 8 - Resonant Collinearity][d08]
- *Day 9 - Disk Fragmenter: TODO*
- *Day 10 - Hoof Itxxx: TODO*
- [Day 11 - Plutonian Pebbles][d11]
<!--
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


Day 2 - Red-Nosed Reports
-------------------------

[Problem statement][d02-problem] — [Complete solution][d02-solution] — [Back to top][top]

### Part 1

We have small list of integers, one per line, and we must count how many of them
respect a certain property. The numbers in a list are supposed to be either all
increasing or all decreasing and the absolute different between any two
consecutive numbers must be between 1 and 3.

Let's write a function to do it. To check whether the pairwise differences
respect the property we can do a quick scan. We can use
[`zip(ints, ints[1:])`][py-builtin-zip] to conveniently iterate over consecutive
pairs of numbers.

```python
def safe(ints):
    for a, b in zip(ints, ints[1:]):
        if not 1 <= abs(b - a) <= 3:
            return False
    return True
```

At a glance, the above function only checks half of the property. We still need
to check whether the `ints` are sorted in increasing or decreasing order. To do
this, we can scan the numbers a couple more times, or we can get rid of the
[`abs()`][py-builtin-abs] so that the sign of the difference will tell us the
order:

```python
def safe(ints):
    for a, b in zip(ints, ints[1:]):
        if not 1 <= b - a <= 3:
            return False
    return True
```

Now if `safe()` returns `True` we know the list is sorted in increasing order
and respects the difference property. To check whether it's sorted in decreasing
order we can simply reverse the list and check again (or pass a reversed
iterator, up to us). This can be done by the caller.

If we want, the function can also be simplified down to a single
[`all()`][py-builtin-all] call plus a [generator expression][py-gen-expr]:

```python
def safe(ints):
    return all(1 <= b - a <= 3 for a, b in zip(ints, ints[1:]))
```

Now let's take the input and count how many lists are safe. It's only a matter
of reading the file line by line, splitting and mapping to `int` as we did
[yesterday][d01]:

```python
fin = open(...)

n_safe = 0

for line in fin:
    ints = list(map(int, line.split()))

    # Check both ascending and descending by reversing the list
    if safe(ints) or safe(ints[::-1]):
        n_safe += 1

print('Part 1:', n_safe)
```

### Part 2

Now, for each list, we also want to allow for *at most* one number that does not
respect the property. This means we can remove one number from the list and if
the rest is "safe", the list is still considered "safe".

The simplest thing to do is to just blindly try removing each number and check
all possibilities. We can be smarter though, and do this in a single pass. Well,
at least if we don't count slices as passes because Python likes to make copies
all the time when slicing :').

We'll have to drop the nice `all()` call and go back to an archaic and seemingly
anti-pythonic `for` loop over indices:

```python
def safe(ints):
    for i in range(len(ints) - 1):
        if not 1 <= ints[i + 1] - ints[i] <= 3:
            return False
    return True
```

The above accomplishes the same thing as the previous version. Now let's also
account for the part 2 condition: we can pass a boolean flag for that.

In case we encounter an "bad" number and the condition
`1 <= ints[i + 1] - ints[i] <= 3` does not hold, we can `break` out of the loop
instead of returning immediately and give it another go, trying to remve exactly
one number. We don't know if the "bad" number is `ints[i]` or `ints[i + 1]`, but
we can test one at a time.

The [`for ... else`][py-loop-else] construct comes in handy; it can be used to
check whether the loop was broken with a `break`. If not, the `else` branch will
be executed.

```python
def safe(ints, allow_removal=False):
    for i in range(len(ints) - 1):
        if not 1 <= ints[i + 1] - ints[i] <= 3:
            # One rule violation, try removing one of the two numbers
            break
    else:
        return True

    if not allow_removal:
        return False

    # Try removing ints[i]
    rest = ints[i - 1:i] + ints[i + 1:]

    for j in range(len(rest) - 1):
        if not 1 <= rest[j + 1] - rest[j] <= 3:
            # Rule violation, maybe the other number is the problem
            break
    else:
        return True

    # Last chance, try removing ints[i + 1]
    rest = ints[i:i + 1] + ints[i + 2:]

    for j in range(len(rest) - 1):
        if not 1 <= rest[j + 1] - rest[j] <= 3:
            # Rule violation again, list is not safe
            return False

    return True
```

We can optimize this a little bit further by checking whether the the second
violation happens immediately (and therefore `ints[i + 1]` is the bad one) or
if it happens later (`j > 0`) and therefore there are multiple bad numbers. In
the latter case we can return `False` immediately.

```diff
 def safe(ints, allow_removal=False):
     # ... unchanged

     # Try removing ints[i]
     rest = ints[i - 1:i] + ints[i + 1:]

     for j in range(len(rest) - 1):
         if not 1 <= rest[j + 1] - rest[j] <= 3:
             # Rule violation, maybe the other number is the problem
-            break
+            if j > 0:
+                # Nope, there are multiple bad numbers
+                return False
+            else:
+                break
     else:
         return True

     # ... unchanged
```

Cool. We can now compute both part 1 and part 2 in a single pass over the input:

```python
n_safe = n_safe_with_removal = 0

for line in fin:
    ints = list(map(int, line.split()))

    if safe(ints) or safe(ints[::-1]):
        n_safe += 1
        n_safe_with_removal += 1
        continue

    if safe(ints, True) or safe(ints[::-1], True):
        n_safe_with_removal += 1

print('Part 1:', n_safe)
print('Part 2:', n_safe_with_removal)
```


Day 3 - Mull It Over
--------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution] — [Back to top][top]

### Part 1

Task looks simpler than yesterday's. We have a bunch of data that almost looks
like garbage in input, but hidden in there are some strings that look like
`mul(X,Y)`, where `X` and `Y` are non-negative integers. We need to extract
those, compute the `mul`tiplications and sum them up.

Regular expressions come in handy here. If we write the appropriate regexp, the
[`re.findall()`][py-re-findall] function will do the heavy lifting for us and
nicely extract all the `X` and `Y` pairs of integers. All we need is a couple of
capture groups (`(...)`) in the expression: `re.findall()` will return a bunch
of lists of matches (each list contains one match per capture group).

The regexp we want is `mul\((\d+),(\d+)\)`. The `\d+` part matches one or more
digits, and the `(...)` part captures the match. Actual literal parentheses to
match are escaped with `\`.

```python
from re import findall

fin = open(...)
total = 0

for a, b in findall(r"mul\((\d+),(\d+)\)", fin.read()):
	total += int(a) * int(b)

print('Part 1:', total)
```

That's it! Wow. If we feel like code-golfind, we can even use
[`sum()`][py-builtin-sum] plus a [generator expression][py-gen-expr] to make it
a one-liner:

```python
total = sum(int(a) * int(b) for a, b in findall(r"mul\((\d+),(\d+)\)", fin.read()))
print('Part 1:', total)
```

### Part 2

Now we also need to toggle the multiplications on or off based on what we find
the input. Initially they need to be performed, but if we encounter the string
`don't()` we need to stop performing subsequent multiplications until we
encounter the string `do()`. A small modification to the regular expression we
wrote earlier and a bit more logic will do the trick.

We can match either `mul(X,Y)`, `do()` or `don't()` with the regexp by simply
using the `|` operator. Put the `do()` and `don't()` strings inside their own
capture groups and we will have 4 elements per match.

```python
for a, b, do, dont in findall(r"mul\((\d+),(\d+)\)|(do\(\))|(don't\(\))", fin.read()):
    # ...
```

Now even though we have 4 values, some of them can be empty strings. In our case
we can either have `a` and `b` together, or `do` alone, or `dont` alone. Based
on this, with the help of a boolean flag to remember whether we should be
multiplying or not, we can finalize our solution:

```python
enabled = True

for a, b, do, dont in findall(r"mul\((\d+),(\d+)\)|(do\(\))|(don't\(\))", fin.read()):
    if do or dont:
        # Encountered either do() or don't(), enable if we matched do()
        # (i.e. the do variable is not empty)
        enabled = bool(do)
    else:
        # Encountered a multiplication
        x = int(a) * int(b)
        # For part 1, always perform it
        total1 += x
        # For part 2, perform it only if enabled
        # (multiplying by a bool is the same as multiplying by 1 or 0)
        total2 += x * enabled

print('Part 1:', total1)
print('Part 2:', total2)
```

6 stars and counting!


Day 4 - Ceres Search
--------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution] — [Back to top][top]

### Part 1

Ah yes, grids of ASCII characters are back. We need to perform a simple word
search puzzle on a grid of letters, counting how many times the word "XMAS"
appears in any possible direction, including overlaps.

First of all input parsing. It doesn't really take much: read the file and use
[`.splitlines()`][py-str-splitlines] it to get a list of lines. Let's save the
grid and its dimensions in global variables for convenience:

```python
fin = open(...)

GRID = fin.read().splitlines()
HEIGHT, WIDTH = len(GRID), len(GRID[0])
```

Now to the counting. There isn't much to do except iterate over the whole grid.
For each cell, we'll check each possible direction and see if the word "XMAS" is
present. Since we'll have to constantly perform bounds-checking on the grid,
let's start by writing a helper function to retrieve a grid character with bound
checking:

```python
def grid_char(r, c):
    global GRID, WIDTH, HEIGHT

    if 0 <= r < HEIGHT and 0 <= c < WIDTH:
        return GRID[r][c]
    return ''
```

Now we can write a second function to perform the actual counting. Given the
coordinates of a starting cell, we can look for 4 characters in all 8
directions, accumulate them in a string and check if it's equal to `'XMAS'`.
Checking for a single direction is simple enough:

```python
# Example of checking the right direction
r, c = 10, 10
word = ''

for i in range(3):
    c += 1
    word += grid_char(r, c)

if word == 'XMAS':
    ...
```

Checking for multiple directions is just a matter of repeating the above code,
but using different deltas for the row and column. We can use a list of tuples
with the deltas of each direction for this.

```python
def count_xmas(r, c):
    global GRID

    deltas = ((0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1))
    count = 0

    for dr, dc in deltas:
        word = ''
        rr, cc = r, c

        for i in range(4):
            word += grid_char(rr, cc)
            rr += dr
            cc += dc

        if word == 'XMAS':
            count += 1

    return count
```

The above function works and returns a number between 0 and 8. However, it is
pretty slow because it always checks all the characters: for example, even if
`GRID[r][c]` is different from `'X'`, it will still compose 8 words and check
them, querying up to 32 characters. We can optimize this by returning early if
the first character is not `'X'`.

```diff
 def count_xmas(r, c):
     global GRID

+    if GRID[r][c] != 'X':
+        return 0
+
     # ... rest of the code unchanged
```

Additionally, we can also optimize the inner loop getting rid of the temporary
`word` variable and make it check the characters one by one with a constant.
Since we now already know the first character is `'X'`, we can also perform one
less iteration. The [`for ... break`][py-loop-else] construct comes in handy
once again for simpler exit condition handling.

```diff
 def count_xmas(r, c):
     global GRID

     if GRID[r][c] != 'X':
         return 0

     deltas = ((0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1))
     count = 0

     for dr, dc in deltas:
-        word = ''
         rr, cc = r, c

-        for i in range(4):
-            word += grid_char(rr, cc)
-            rr += dr
-            cc += dc
-
-        if word == 'XMAS':
-            count += 1
+        for i in range(3):
+            rr += dr
+            cc += dc
+            if grid_char(rr, cc) != 'MAS'[i]:
+                break
+        else:
+            count += 1

     return count
```

Now all that's left to do is iterate over the grid coordinates and call the
`count_xmas()` function in a loop:

```python
total1 = 0

for r in range(HEIGHT):
    for c in range(WIDTH):
        total1 += count_xmas(r, c)

print('Part 1:', total1)
```

The above code can be shrinked down to a single line using
[`sum()`][py-builtin-sum] plus a [generator expression][py-gen-expr]:

```python
total1 = sum(count_xmas(r, c) for r in range(HEIGHT) for c in range(WIDTH))
print('Part 1:', total1)
```

### Part 2

For the second part we need to count a special arrangement of characters, that
is, two occurrences of the word "MAS" written in an cross shape:

```
M.S  S.M  S.S
.A.  .A.  .A.  (... other options possible)
M.S  S.M  M.M
```

This seems almost simpler than the first part: just make sure that the center
is an `'A'`, extract the other 4 characters and check that the two pairs are
equal to either `'MS'` or `'SM'`. Let's write a new function for this second
check:

```python
def check_xmas(r, c):
    global GRID

    if GRID[r][c] != 'A':
        return False

    word = grid_char(r - 1, c - 1) + grid_char(r + 1, c + 1)
    if word != 'MS' and word != 'SM':
        return False

    word = grid_char(r + 1, c - 1) + grid_char(r - 1, c + 1)
    return word == 'MS' or word == 'SM'
```

Now we can again iterate over the grid and count the occurrences. Since the X
shape covers a 3x3 section, we can also start the iteration from the second row
and column and stop at the second-to-last row and column.

In golfing-style, we can again use the same one-liner as before:

```python
total2 = sum(check_xmas(r, c) for r in range(1, HEIGHT - 1) for c in range(1, WIDTH - 1))
print('Part 2:', total2)
```

Sweet! 8 stars.


Day 8 - Resonant Collinearity
-----------------------------

[Problem statement][d08-problem] — [Complete solution][d08-solution] — [Back to top][top]

### Part 1

We are given a grid with a bunch of "antennas" each of a given frequency. For
each pair of antennas with the same frequency, we need to find any existing
"antinodes". An antinode is a point within the grid that is on the line
connecting a pair of antennas of the same frequency and is exactly at some
distance *d* from the first antenna and *2d* from the second antenna. We need to
count how many unique antinodes we have.

Parsing the grid is again simple: read everything and split by line. Let's also
immediately calculate the grid dimensions and store them in global variables for
convenience.

```python
fin = open(...)
grid = fin.read().splitlines()
HEIGHT, WIDTH = len(grid), len(grid[0])
```

Now let's find the antennas. Each character different than `.` is an antenna and
the character itself indicates the frequency. Let's group all antennas of the
same frequency in a dictionary. We can use a
[`defaultdict`][py-collections-defaultdict] for this, with the key being the
frequency and the values being sets of coordinates. It will have the form
`{freq: {(r1, c1), (r2, c2), ...}}`.

To iterate over the grid, we can use two nested loop with [`enumerate()`][py-builtin-enumerate]:

```python
from collections import defaultdict

frequencies = defaultdict(set)
for r, row in enumerate(grid):
    for c, cell in enumerate(row):
        if cell != '.':
            frequencies[cell].add((r, c))
```

Let's look again at the definition of "antinode": it is a point on the line
connecting the two antennas that is exactly at distance *d* from the first and
*2d* from the second. Let's say we have two antennas `a = (r1, c1)` and
`b = (r2, c2)`. Breaking it down from two dimensions to one, this means that we
want to find:

- A row `R` such that `abs(r1 - R) == dr` and `abs(r2 - R) == 2*dr`.
- A column `C` such that `abs(c1 - C) == dc` and `abs(c2 - C) == 2*dc`.

If we only look in one direction we can get rid of the absolute values and we
have:

- A row `R` such that `r1 - R == dr` and `r2 - R == 2*dr`.
- A column `C` such that `c1 - C == dc` and `c2 - C == 2*dc`.

This means that:

- `r1 + d == r2 - 2*dr`, therefore `dr = r2 - r1`.
- `c1 + d == c2 - 2*dc`, therefore `dc = c2 - c1`.

Come to think about it, the result is intuitive: given the two antennas A and B,
the antinode on the B side is at *A + 2(B - A) = 2B - A*. The same goes for the
opposite side, but with a negative sign.

```none
A----------------B----------------X
|      B - A     |     B - A      |
                                  A + 2(B - A) = 2B - A
```

Given the above, let's write a function that calculates the coordinates of an
antinode given the coordinates of two antennas. We will write a generator
function using `yield` to make it convenient to add the results (if any) to a
set later.

```python
def antinode(r1, c1, r2, c2):
    global HEIGHT, WIDTH

    r = 2 * r2 - r1
    c = 2 * c2 - c1
    if 0 <= r < HEIGHT and 0 <= c < WIDTH:
        yield r, c

    r = 2 * r1 - r2
    c = 2 * c1 - c2
    if 0 <= r < HEIGHT and 0 <= c < WIDTH:
        yield r, c
```

For all pairs `(a, b)` of antennas with the same frequency, we can call the
function using the [unpack operator][py-unpacking] as `antinode(*a, *b)` and add
the results to a set. The final count of unique antinodes will be the size of
this set.

```python
points = set()

for antennas in frequencies.values():
    for a in antennas:
        for b in antennas:
            if a != b:
                points.update(antinodes(*a, *b))
```

This can be simplified using
[`itertools.combinations`][py-itertools-combinations] to avoid the `a != b`
check and also to avoid checking the same pair twice:

```python
from itertools import combinations

points = set()

for antennas in frequencies.values():
    for a, b in combinations(antennas, 2):
        points.update(antinodes(*a, *b))

print('Part 1:', len(points))
```

### Part 2

For the second part we now need to find all points within the grid that are on
the line connecting two antennas of the same frequency. Needless to say, for
each pair of same-frequency antennas, this will include the antennas themselves.

The logic is simple: for each pair of antennas, we can calculate the slope of
the line connecting them and iterate over all points on the line, stoppig if we
ever get out of bounds. Since we are dealing with integer coordinates, this
means iterating over all possible integer multiples of the distance between the
two antennas.

Let's write another generator function for this. We can use the
[`itertools.count`][py-itertools-count] to conut upwards from `0` and stop at
the first point that is out of bounds of the grid.

```python
from itertools import count

def points_on_line(r1, c1, r2, c2):
    global HEIGHT, WIDTH

    # Slope is (dr, dc)
    dr = r2 - r1
    dc = c2 - c1

    # Each point is at (r1 + mult*dr, c1 + mult*dc)
    for mult in count(0):
        r = r1 + mult * dr
        c = c1 + mult * dc

        if 0 <= r < HEIGHT and 0 <= c < WIDTH:
            yield r, c
        else:
            break
```

Both part 1 and part 2 answers can be calculated in the same loop, we only need
an additional set for part 2. The `points_on_line()` function we wrote only
checks in one direction (mult is always positive), so we need to call it twice
for each pair of antennas.

```python
points1 = set()
points2 = set()

for antennas in frequencies.values():
    for a, b in combinations(antennas, 2):
        points1.update(antinodes(*a, *b))
        points2.update(points_on_line(*a, *b))
        points2.update(points_on_line(*b, *a))

print('Part 1:', len(points1))
print('Part 2:', len(points2))
```


Day 11 - Plutonian Pebbles
--------------------------

[Problem statement][d11-problem] — [Complete solution][d11-solution] — [Back to top][top]

### Part 1

We are given a list of integers and a simple set of rules to follow to transform
them. We need to apply the rules 25 times in a row to all integers and count how
many there are at the end.

The rules are simple enough and the first that applies is used. For each integer
`n`:

1. If `n == 0`, it is replaced by `1`.
2. If `n` has an even number of digits, it is replaced by two numbers: one made
   from the higher half and one from the lower half of its digits (discardind
   leading zeroes).
3. Otherwise, it is multiplied by `2024`.

Let's stop and think for a second, maybe with a piece of paper. The second rule
is clearly the painful one: if we keep applying it, it makes the number of
numbers we are dealing with grow exponentially. For example, if we start with
just a single number with 32 digits, after only 5 iterations we will have 64
numbers. 25 iterations don't look like much, just a few million numbers to deal
with in the worst case, but still, that's a lot. Let's find a way around it.

Looking at the first and third rules, it is clear that some sort of cycle will
happen when we reach `0`: we will get `0 -> 1 -> 2024 -> ...`. That `2024` will
then be split into `[20, 24]`, then `[2, 0, 2, 4]`. Now we are back to square
one: the `0` in there will produce exactly the same list in a few more
iterations.

The key takeaway is that fixed a number `n` and a number of iterations to
perform, the result will always be the same. For each unique pair
`(n, iterations_left)` we will have a different result. Well, almost: some pairs
may lead to the same result, but the important thing is that equal pairs will
*always* lead to the same result.

Given the above, we can implement our solution using
[memoization][wiki-memoization]: we will keep a dictionary of results for each
pair `(n, iterations_left)` and if we ever encounter the same pair again, we can
return the result immediately. The result to keep track of is the final number
of integers (when `iterations_left` hits `0`).

We can either write this as a recursive function or in an iterative way using a
queue. The recursive approach seems more natural and concise, so I'm going to go
with that. The function we want to write will take a single number `n` and the
number of `blinks` (i.e. what the problem statement calls the iterations) to
perform. It will then return the total number of integers at the end.

Following the rules, we have:

1. If we reach 0 `blinks` left, return `1` (we only track one number).
2. If `n == 0`, make a recursive call with `n=1` and one less blink.
3. If `n` has an even number of digits, split it in half. Then, make two
   recursive calls with (one for each half) with one less blink, and return the
   sum of the two results.
4. Otherwise, make a recursive call with `n * 2024` and one less blink.

To count digits and split the number, I used [`math.log10()`][py-math-log10].
Here's the code:

```python
from math import log10

def calc(n, blinks):
    if blinks == 0:
        return 1

    if n == 0:
        return calc(1, blinks - 1)

    n_digits = int(log10(n)) + 1
    if n_digits % 2 == 0:
        power = 10**(n_digits // 2)
        hi_half = n // power
        lo_half = n % power
        return calc(hi_half, blinks - 1) + calc(low_half, blinks - 1)

    return calc(n * 2024, blinks - 1)
```

This works fine. All we are missing is the memoization part. We are currently
not "remembering" the results of the recursive calls, so we are recalculating
them over and over. To do this, we can use a dictionary to store the results and
check it at the start of the function, or we can whip out our best friend
[`@functools.lru_cache()`][py-functools-lru_cache]: a decorator that can
magically do this for us (behind the scenes, it also uses a dictionary).

```diff
 from math import log10
+from functools import lru_cache

+@lru_cache(max_size=None)
 def calc(n, blinks=25):
     # ... code unchanged ...
```

From Python 3.9 onwards we also have the [`functools.cache`][py-functools-cache]
decorator which is a simpler version of `lru_cache`.

Now we can actually get to parsing the input and calculating the result. We have
a list of integers so a simple [`.split()`][py-str-split] plus
[`map()`][py-builtin-map] will do the trick.

```python
fin = open(...)
numbers = list(map(int, fin.read().split()))
```

The result can then be calculated applying our `calc()` function to each number,
either with a loop, or with [`sum()`][py-builtin-sum] plus a
[generator expression][py-gen-expr]:

```python
total = sum(calc(n, 25) for n in numbers)
print('Part 1:', total)
```

### Part 2

Since we were smart in part 1, we now have part 2 for free! The only thing that
changes is the numbe of iterations, or "blinks": we need to perform 75.

It's only a matter of calling our function with a different `blink` count:

```python
total2 = sum(calc(n, 75) for n in numbers)
print('Part 2:', total2)
```

---

*Copyright &copy; 2024 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)


[top]: #advent-of-code-2024-walkthrough
[d01]: #day-1---historian-hysteria
[d02]: #day-2---red-nosed-reports
[d03]: #day-3---mull-it-over
[d04]: #day-4---ceres-search
[d05]: #day-5---print-queue
[d06]: #day-6---guard-gallivant
[d07]: #day-7---bridge-repair
[d08]: #day-8---resonant-collinearity
[d09]: #day-9---disk-fragmenter
[d10]: #day-10---hoof-itxxx
[d11]: #day-11---plutonian-pebbles
[d12]: #day-12---
[d13]: #day-13---
[d14]: #day-14---
[d15]: #day-15---
[d16]: #day-16---
[d17]: #day-17---
[d18]: #day-18---
[d19]: #day-19---
[d20]: #day-20---
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


[py-gen-expr]:  https://docs.python.org/3/reference/expressions.html#generator-expressions
[py-loop-else]: https://docs.python.org/3/tutorial/controlflow.html#else-clauses-on-loops
[py-unpacking]: https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-functools-cache]:         https://docs.python.org/3/library/functools.html#functools.cache
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-itertools-combinations]:  https://docs.python.org/3/library/itertools.html#itertools.combinations
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-list-count]:              https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:               https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-math-log10]:              https://docs.python.org/3/library/math.html#math.log10
[py-re-findall]:              https://docs.python.org/3/library/re.html#re.findall
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines

[wiki-memoization]: https://en.wikipedia.org/wiki/Memoization
