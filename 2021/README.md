Advent of Code 2021 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Sonar Sweep][d01]
- [Day 2 - Dive!][d02]
- [Day 3 - Binary Diagnostic][d03]
- [Day 4 - Giant Squid][d04]
- [Day 5 - Hydrothermal Venture][d05]
- [Day 6 - Lanternfish][d06]
- [Day 7 - The Treachery of Whales][d07]
- [Day 8 - Seven Segment Search][d08]
- [Day 9 - Smoke Basin][d09]
- [Day 10 - Syntax Scoring][d10]
- [Day 11 - Dumbo Octopus][d11]
- [Day 12 - Passage Pathing][d12]


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

Let's just write a simple loop: we can use `zip` again to group the numbers in
triplets and then `map()` with `sum` to convert the triplets into their sum.

```python
tot  = 0
prev = float('inf')

for cur in map(sum, zip(nums, nums[1:], nums[2:])):
    if cur > prev:
        tot += 1
    prev = cur
```

Ok, can we do better though? Yes we can. Consider the numbers `a b c d`: the
first triplet would sum up to `a+b+c`, while the second one to `b+c+d`. We want
to know if `a+b+c < b+c+d`. If we simplify the expression, we see that
`a+b+c < b+c+d` becomes `a < d` after removing `b+c` from both sides. Nice, we
can simply check `a` and `d`: that is, pairs of numbers 4 positions apart. Thus,
the second part can be solved exactly as the first one, only changing a single
character in the code:

```python
tot = sum(b > a for a, b in zip(nums, nums[3:])) # changed nums[1:] -> nums[3:]
print('Part 2:', tot)
```

Well, well, well. Welcome to Advent of Code 2021!


Day 2 - Dive!
-------------

[Problem statement][d02-problem] — [Complete solution][d02-solution] — [Back to top][top]

### Part 1

2D coordinates! We start with a depth of 0 and horizontal posizion of 0, and we
are given a list of commands of the form `direction X`, one per line, where the
direction can be either `forward`, `down` or `up`, while `X` is a number of
units. For each `forward` we must increase our horizontal position by `X`, while
for each `down`/`up` we must increase/decreae our depth respectively by `X`.
Finally, we need to answer with our depth multiplied by the horizontal position.

Seems simple enough. Let's just get the input file and iterate over it to get
the lines one by one, [splitting][py-str-split] each line in two parts and
converting `X` into an integer. After we do that, we can simply take a look at
the first part with a couple of `if` statements to determine what to do. It's
easier to code it than it is to explain it really:

```python
aim = horiz = depth = 0

for line in fin:
    cmd, x = line.split()
    x = int(x)

    if cmd == 'down':
        depth += x
    elif cmd == 'up':
        depth -= x
    else:
        horiz += x

answer = horiz * depth
print('Part 1:', answer)
```

### Part 2

For the second part, we also have an "aim" to keep track of, and the commands
change meaning. `down X`/`up X` now increase/decrease our *aim* by `X`, while
`forward X` means two things: first increse the horizontal posizion by `X`, then
increase the depth by the current aim multiplied by `X`.

Nothing absurd. We can actually integrate this in the same loop we just wrote,
by creating two new variables for the aim and the new depth. Since the aim is
actually updated exactly like the original depth, we can also cheap out on
variables and just add one ([thanks @NimVek for noticing][misc-issue-11]). Other
than that, it's just additions and multiplications.

```python
aim = horiz = depth = 0

for line in fin:
    cmd, x = line.split()
    x = int(x)

    if cmd == 'down':
        aim += x
    elif cmd == 'up':
        aim -= x
    else:
        horiz += x
        depth += aim * x

answer1 = horiz * aim
answer2 = horiz * depth

print('Part 1:', answer1)
print('Part 2:', answer1)
```

Ta-dah! As simple as that, we now have two more gold stars.


Day 3 - Binary Diagnostic
-------------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution] — [Back to top][top]

### Part 1

Lots of binary numbers. Our first task today looks rather simple: given a list
of binary numbers expressed using a fixed number of bits, find the most common
bit (0 or 1) amongst all the numbers for each position (from most significant
to least significant bit). Then, do the same to find the least common bit at
each position. Finally, convert the found most common and least common bits into
two numbers and compute their product.

There are lots of different ways to solve today's problem, depending on how we
want to actually treat the input numbers. Do we want to convert them to integers
and use bitwise operations to extract and compare the bits? Or maybe we want to
keep them as characters or bytes? Do we want to work line-wise or column-wise?
How much are concerned about speed? Depending on the choice, we can end up with
really different-looking code. I chose to go with the bitwise operations for my
clean solution today, which I think gives a good compromise between clarity,
speed and concisenes.

First of all, let's get the input and convert each line into an integer, while
also computing the (fixed) number of bits used to represent the numbers. We want
to know this because not all numbers start with a `1` as most significant digit,
and converting those to integers will make us lose track of the original number
of bits.

To convert a binary string to integer we can easily use [`int(s,
base=2)`][py-builtin-int]. To do this for every single line of code we can
simply [`map()`][py-builtin-map] the lines from our input file using a
[`lambda`][py-lambda] expression. We'll gather everything into a `tuple` so that
we can iterate over it multiple times (which we may needed for part 2).

```python
fin    = open(...)
lines  = fin.readlines()
n_bits = len(lines[0].strip())
nums   = tuple(map(lambda l: int(l, 2), lines))
```

The last expression can be also written with the help of
[`partial()`][py-functools-partial] from the [`functools`][py-functools] module
to replace the `lambda`. As the name suggests, `partial` "partially applies"
arguments to a function, returning a new function where the chosen arguments are
fixed and need not be supplied:

```python
from functools import partial
# ...
nums = tuple(map(partial(int, base=2), lines))
```

Now onto the real task. Let's break this down into smaller problems and start
counting how many bits at a given position (a given *shift*) are set in an
iterable of integers. A bit at a given position (where 0 means least signidicant
position) can be tested by shifting the number down and doing a binary AND (`&`)
with `1`:

```python
# Is bit 3 (4th bit) set?
(number >> 3) & 1
```

Now, for example, to count how many 4th bits are set in an iterable we can wrap
the above expression in a [`sum()`][py-builtin-sum] using a
[generator expression][py-generator-expr]:

```python
n_set = sum(((n >> 3) & 1) for n in nums)
```

If we want to know the most common bit set now we can just compare the `n_set`
with the length of `nums`. We'll consider `1` to be most common in case of a
tie.

```python
def most_common_bit(nums, shift):
    n_set = sum(((n >> shift) & 1) for n in nums)

    if n_set > len(nums) // 2 - 1:
        return 1

    return 0
```

Now we can do this for each possible `shift` from `n_bits - 1` down to `0`. We
will simply accumulate the most common bits into a new integer, shifting left by
one and adding the new most common bit each time, since that's what the puzzle
asks us:

```python
def most_common_bits(nums, n_bits):
    res = 0

    for shift in range(n_bits - 1, -1, -1):
        res <<= 1
        res += most_common_bit(nums, shift)

    return res
```

Now, as an example, if the most common bits in the 3rd, 2nd and 1st positions
amongst `nums` were `1`, `0` and `1` respectively, the above function would
return `0b101` i.e. `5`.

We are half-way through. How can we calculate the *least*-common bits for each
position now? Well, they will just be the opposite of the most common, of
course! We can simply perform a binary negation of the obtained number from the
above function: `0b101 -> 0b010 == 2`. How do you binary negate in Python? There
isn't an operator that can do this directly like in other languages
unfortunately, but we can simply do `0b1111 - 0b101 == 0b010`, calculating the
`0b1111` as `(1 << n_bits) - 1`. That's it, we have all we need to calculate the
answer now:

```python
gamma = most_common_bits(nums, n_bits)
eps   = (1 << n_bits) - 1 - gamma
power = gamma * eps

print('Part 1:', power)
```

### Part 2

Our task gets a little trickier now. We need to filter out numbers based on a
certain criteria:

1. Star with all numbers, find the most common significant bit and only keep the
   numbers which have that same most significant bit.
2. Further filter these numbers by looking at the second most significant bit,
   only keeping those with the most common second most significant bit.
3. Keep going, each time looking at the next position, filtering out numbers
   that don't have the most common bit at that position until we are only left
   with one number.

We need to also do the same for least common bits, to obtain a second number.
Multiplying the two together will give us the answer.

Okay, we alraedy have a `most_common_bit()` function which tells us if the most
common bit at a given shift (position) in a set of numbers is either `1` or `0`:
we can use it in a loop for filtering. We'll start with a `set` containing all
numbers, then check the most common MSB and filter out those that have a
different MSB. Then look at the second MSB, and so on... we'll keep filtering
until our set only contains one number.

```python
# From MSB (shift = n_bits - 1) to LSB (shift = 0)
for shift in range(n_bits - 1, -1, -1):
    # Get the most common bit at this shift
    bit  = most_common_bit(nums, shift)
    keep = list()

    # Only keep numbers that have this bit set at this shift
    for n in nums:
        if (n >> shift) & 1 == bit:
            keep.append(n)

    nums = keep
    if len(nums) == 1:
        break

# Now we should only have one number left
only_one_left = nums[0]
```

Yeah... Python's reverse range notation is kind of awkward.

We can simplify the above loop using [`filter()`][py-builtin-filter], which
takes a function to check whether we want to keep a certain item or not, and
does the filtering for us. In this case we'll use a simple `lambda`. Let's also
wrap everything into a function to re-use it later while we're at it:

```python
def filter_numbers(nums, n_bits):
    for shift in range(n_bits - 1, -1, -1):
        bit  = most_common_bit(nums, shift)
        nums = tuple(filter(lambda n: (n >> shift) & 1 == bit, nums))

        if len(nums) == 1:
            break

    return nums[0]
```

Okay, we have the first of the two magic numbers we needed. Now we have to do
the exact same job checking the *least common* bits instead. Well, we can write
a `least_common_bit()` function and do the same as the above. To do this, we'll
also generalize `filter_numbers` to take a `predicate` function as thirt
argument that will determine the bit to keep for us:

```python
def least_common_bit(nums, shift):
    return 1 - most_common_bit(nums, shift)

def filter_numbers(nums, n_bits, predicate):
    for shift in range(n_bits - 1, -1, -1):
        bit  = predicate(nums, shift)
        nums = tuple(filter(lambda n: (n >> shift) & 1 == bit, nums))

        if len(nums) == 1:
            break

    return nums[0]
```

We can now call `filter_numbers()` two times with the two different functions
we wrote and calculate our answer:

```python

oxy    = filter_numbers(nums, n_bits, most_common_bit)
co2    = filter_numbers(nums, n_bits, least_common_bit)
rating = oxy * co2

print('Part 2:', rating)
```

In case you're wondering about those variable names... well, they were just the
names of the values that our problem asked to find.

Interesting puzzle today, I spent quite some time to keep the solution
reasonably concise while still being Pythonic and easy enough to explain. My
[original solution][d03-orginal], written in a hurry without thinking too much,
is a literal dumpster fire in comparison, oof! And you? What beautiful piece of
code did you write today?


Day 4 - Giant Squid
-------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution] — [Back to top][top]

### Part 1

Today we play [American bingo][wiki-bingo] (not to be confused with
[Advent of Code bingo][misc-aoc-bingo]). As you probably already know, bingo is
a relatively boring game which works like this:

1. Each player starts with one or more 5x5 bingo cards with 25 random numbers
   written on them.
2. The game host draws one number at a time from a box and calls it out. Every
   player marks the number on their cards.
3. The first player to mark an entire row or column of one of their cards wins.

In today's puzzle we are given a list of drawn numbers and some cards. Our first
task is to determine which of those cards would be the first winning card
according to the drawn numbers. The winning card has a "score" (this is not a
standard bingo rule, in bingo cards don't have scores), which is calculated
summing up all the remaining unmarked numbers on the card and multiplying this
sum by the number which was marked last.

How do we parse our input? We have various sections delimited by empty lines
(i.e. two consecutive line feeds `\n`). The first row contains the drawn numbers
separated by commas, so let's get them with a classic [`.split()`][py-str-split]
plus [`map()`][py-builtin-map]:

```python
fin   = open(...)
drawn = map(int, fin.readline().split(','))
```

Now we can `.split()` the remaining input on empty lines (`\n\n`) and parse each
piece into a matrix. We can also do this using `map()` after writing an
appropriate function to transform a raw section of lines into a matrix: for each
section, first split it again into lines (we can also do this through
[`.splitlines()`][py-str-splitlines]), then split lines on whitespace and
convert each piece to `int`:

```python
def into_matrix(raw):
    lines = raw.strip().splitlines()
    res = []
    for l in lines:
        res.append(list(map(int, l.split())))
    return res

cards = list(map(into_matrix, fin.read().split('\n\n')))
```

We can further simplify the above `for` loop into a
[generator expression][py-generator-expr] since it is merely constructing a
`list`:

```python
def into_matrix(raw):
    lines = raw.strip().splitlines()
    return list(list(map(int, l.split())) for l in lines)
```

It seems obvious that we need a way to identify marked numbers. Since the final
score does not depend on them (except the last one), we can replace marked
numbers with `-1` in the cards.

Now how can we find out if a certain card wins? Simply scan through each row and
column of the card counting the occurrences of `-1`: if any row/col has 5 of
them, the card just won. We can use [`sum()`][py-builtin-sum] and `map()` to
easily do this given a card. Let's writa a function:

```python
def check_win(card):
    # Any row containing -1 five times?
    for row in card:
        if sum(x == -1 for x in row) == 5:
            return True

    # Any column containing -1 five times?
    for c in range(len(card[0])):
        if sum(row[c] == -1 for row in card) == 5:
            return True

    return False
```

Can we optimize the above function? Yes, we'll do it soon, first let's write yet
another function to mark a number on a card. Since we potentially need to modify
the contents of a cell in the board, we'll need to iterate over each cell while
keeping track of row and column indexes, so that we can do `card[r][c] = -1` to
mark the cell if the number matches. The [`enumerate()`][py-builtin-enumerate]
built-in function comes in handy. Finally, since all we do is mark numbers, this
function might as well also directly tell us if the number we marked made the
given board win, and we can call `check_win()` for that.

```python
def mark(card, number):
    for r, row in enumerate(card):
        for c, cell in enumerate(row):
            if cell == number:
                card[r][c] = -1
                return check_win(card, row, c)
    return False
```

You might have noticed that `check_win()` iterates over the entire card every
time. Since when we find a number we automatically know its row and column, we
can skip checking any other row and column and make our function way simpler by
passing the indices of the marked cell:

```python
def check_win(card, r, c):
    # Row
    if sum(x == -1 for x in card[r]) == 5:
        return True

    # Column
    if sum(row[c] == -1 for row in card) == 5:
        return True

    return False
```

We could even directly pass the `row` since we already have it available in
`mark()`:

```python
def check_win(card, row, c):
    if sum(x == -1 for x in row) == 5:
        return True
    if sum(r[c] == -1 for r in card) == 5:
        return True
    return False
```

The last function we'll write today will calculate the score of a winning card
as defined by the puzzle rules. Not much to be said, just sum up all numbers
which are not `-1` and multiply by the last marked number:

```python
def winner_score(card, last_number):
    unmarked_tot = 0

    for row in card:
        for x in row:
            if x == -1:
                unmarked_tot += 1

    return unmarked_tot * last_number
```

The above inner loop can be simplified through a [`filter()`][py-builtin-filter]
to skip every `-1` plus a `sum()` to sum the remaining numbers:

```python
def winner_score(card, last_number):
    unmarked_tot = 0

    for row in card:
        unmarked_tot += sum(filter(lambda x: x != -1, row))

    return unmarked_tot * last_number
```

Since all we do in the loop now is a sum, we can also wimplify that:

```python
def winner_score(card, last_number):
    unmarked_tot = sum(sum(filter(lambda x: x != -1, row)) for row in card)
    return unmarked_tot * last_number
```

We have all we need. Now it's only a matter of iterating over all the drawn
numbers and checking them one by one:

```python
for number in drawn:
    for card in cards:
        win = mark(card, number):
        if win:
            score = winner_score(card, number)
            break

    if win:
        break

print('Part 1:', score)
```

### Part 2

Simply enough, now we want to know the score of the *last* card to win according
to the drawn numbers. We can simply keep track of who won by removing winning
cards from our list of cards (i.e. setting them to `None`) and keep track of the
number of winners. We can integrate all this in the same loop we just wrote for
part 1:

```python
n_cards = len(cards)
n_won   = 0

for number in drawn:
    for i, card in enumerate(cards):
        if card is None:
            continue

        if mark(card, number):
            n_won += 1

            if n_won == 1:
                first_winner_score = winner_score(cards[i], number)
            elif n_won == n_cards:
                last_winner_score = winner_score(cards[i], number)

            cards[i] = None

print('Part 1:', first_winner_score)
print('Part 2:', last_winner_score)
```

Not a big fun of bingo, it's kind of a boring game to be honest. However, coding
a bingo game simulation is pretty fun!


Day 5 - Hydrothermal Venture
----------------------------

[Problem statement][d05-problem] — [Complete solution][d05-solution] — [Back to top][top]

### Part 1

Lines on the [Cartesian plane][wiki-cartesian-coords]... familiar with those? I
hope so. Today we are "drawing" a bunch of them: we have a list of pairs of 2D
coordinates in the form `ax,ay -> bx,by`. Each pair represents a line going from
point `(ax, ay)` to point `(bx, by)` (actually a line segment, since lines are
infinite). We are dealing with an indefinitely large 2D rectangular grid of
equally spced points, so we only need to consider integer coordinates.

For now we need to consider only pairs of points which make horizontal or
vertical lines, ignoring other pairs. We are asked to determine the total number
of points where two or more lines overlap.

Let's parse the pairs of points that make the lines from our input. It's just a
question of splitting each line on `->`, then splitting again each piece on `,`
and converting the numbers to `int`. We can use [`map()`][py-builtin-map] after
splitting on commas to convert both coordinates to integer at once.

```python
lines = []

for raw_line in fin:
    a, b = raw_line.split('->')
    ax, ay = map(int, a.split(','))
    bx, by = map(int, b.split(','))
    lines.append((ax, ay, bx, by))
```

The simplest solution now is to actually "draw" these lines and then count the
intersections: for each horizontal line, go through all the integer points that
compose it, and mark them on the grid. Let's write a
[generator function][py-generator-function] which, given the coordinates of the
starting and ending point of a line segment, yields all the coordinates of the
points on the line (ends included).

We have two possible scenarios:

1. Vertical lines: fixed `x` (`ax == bx`) and varying `y`. In this case we can
   have `ay > by` or `by > ay`: we can simply use `min()`[py-builtin-min] and
   `max()`[py-builtin-max] to always go from the lowest to the highest `y`
   coordinate.
2. Horizontal lines: fixed `y` (`ay == by`) and varying `x`. Again, we can
   either have `ax > bx` or `bx > ax`: same logic as the previous case.

```python
def horiz(ax, ay, bx, by):
    if ax == bx:
        for y in range(min(ay, by), max(ay, by) + 1):
            yield ax, y
    elif ay == by:
        for x in range(min(ax, bx), max(ax, bx) + 1):
            yield x, ay

    # Ignore anything else that is no an horizontal or vertical line, if we
    # don't return anything the generator will just stop immediately.
```

Since all we are doing in the above `for` loops is `yield` pairs of numbers, we
could actually use `yield from` instead. To repeat the fixed coordinate we can
use [`itertools.repeat()`][py-itertools-repeat]. Then, [`zip()`][py-builtin-zip]
together the repeating coordinate with the `range()` to get pairs of
coordinates, and `yield from` those:

```python
from itertools import repeat

def horiz(ax, ay, bx, by):
    if ax == bx:
        yield from zip(repeat(ax), range(min(ay, by), max(ay, by) + 1))
    elif ay == by:
        yield from zip(range(min(ax, bx), max(ax, bx) + 1), repeat(ay))

# horiz(1, 1, 1, 4) -> (1, 1), (1, 2), (1, 3), (1, 4)
```

Since we want to detect intersections, we can start with a grid filled with
counters, all starting at `0`. Then, each time we pass on a point, increment its
counter. This way, when we finish drawing all the lines, we can easily count the
number of points with a counter higher than `1` to get the total number of
intersections.

Ideally we would want to do something like this:

```python
# Initialize grid as all zeroes...

for ax, ay, bx, by in lines:
    for x, y in horiz(ax, ay, bx, by):
        grid[x][y] += 1
```

How big should our grid be, though? If we want to represent our grid as a matrix
(i.e. list of lists) we will have to calculate its dimensions first. We could do
that, but there's a simpler solution: use a dictionary as a *sparse matrix*, by
indexing it with a tuple of coordinates (`d[x, y]`). This way, we don't have to
worry about going out of bounds, and we will only store the needed counters.


```python
space = {}

for ax, ay, bx, by in lines:
    for x, y in horiz(ax, ay, bx, by):
        if (x, y) not in space:
            space[x, y] = 0
        space[x, y] += 1
```

The [`defaultdict`][py-collections-defaultdict] comes in handy to avoid that
annoying check and initialization to zero for every single number:
`defaultdict(int)` is a dictionary which when accessed with a key that is not
present automatically inserts it calling `int()` to get the initial value
(`int()` without any argument returns `0`).

```python
space = defaultdict(int)

for line in lines:
    for x, y in horiz(*line):
        space[x, y] += 1
```

The star (`*`) operator in `horiz(*line)` performs
[argument unpacking][py-unpacking] passing the four elements in `line` as four
separate arguments to `horiz`.

We could also avoid splitting the coordinate into two variables and just use
one:

```python
for line in lines:
    for p in horiz(*line):
        space[p] += 1
```

All that's left to do is count all the points where lines overlap, that is all
points `(x, y)` where `space[x, y] > 1`. We can do this with
[`sum()`][py-builtin-sum] plus a [generator expression][py-generator-expr]:

```python
overlapping = sum(x > 1 for x in space.values())
print('Part 1:', overlapping)
```

### Part 2

For part 2 the goal does not change: find the total number of overlapping
points. However, now we also have to consider diagonal lines. We are guaranteed
by the input format that our diagonal lines can only have a slope of `1`, i.e.
they always form 45 degree angles with the Cartesian plane axes. This simplifies
things a lot over the more general case where you can have any possible slope,
since in such case we would be unsure about how to handle integer coordinates.

We can do the same as before. Just create a function which generates all points
on a diagonal line. We have to be careful though: in order to do this, we need
to take into account the direction and the orientation of the lines. If we don't
want to become insane thinking about how to correctly iterate over the
coordinates to generate the points, we need to abstract this complexity away.

We can have four possibilities:

```none
a       b            b       a
 ↘...    ↖...    ...↗    ...↙
 .↘..    .↖..    ..↗.    ..↙.
 ..↘.    ..↖.    .↗..    .↙..
 ...↘    ...↖    ↗...    ↙...
     b       a  a       b
```

In any case, regardless of the values of the coordinates of `ax, ay, bx, by`, we
always want to go from `ax` to `bx` and from `ay` to `by`. In case `ax < bx` we
need to step *up* in steps of `+1` from `ax` to `bx`, and in case `ax > bx` we
need to step *down* in steps of `-1` from `ax` to `bx`. The same reasoning goes
for the `y` coordinate.

Let's write an `autorange()` generator function which does exactly this: takes
two integers, and regardless of their values iterates from the first up/down to
the second in increments of `+1` or `-1` (as needed):

```python
def autorange(a, b):
    '''Go from a to b in steps of +/-1 regardless if a > b or b > a'''
    if a > b:
        yield from range(a, b - 1, -1)
    yield from range(a, b + 1)
```

Applying the above function to both the `x` and `y` coordinates of our pairs of
points will give us exactly what we want. Let's write a function to generate
points for diagonal lines:

```python
def diag(ax, ay, bx, by):
    if ax != bx and ay != by:
        yield from zip(autorange(ax, bx), autorange(ay, by))

    # Ignore anything else that is not a diagonal line, if we don't return
    # anything the generator will just stop immediately.
```

We can also use our `autorange()` function to simplify `horiz()`, replacing the
ranges with min/max:

```python
def horiz(ax, ay, bx, by):
    if ax == bx:
        yield from zip(repeat(ax), autorange(ay, by))
    elif ay == by:
        yield from zip(autorange(ax, bx), repeat(ay))
```

All that's left to do for part 2 is increment the counters for all points on
horizontal lines and re-count the overlapping points again:

```python
for line in lines:
    for p in diag(*line):
        space[p] += 1

overlapping = sum(x > 1 for x in space.values())
print('Part 2:', overlapping)
```

### One last stretch

We can make use of [`itertools.starmap()`][py-itertools-starmap] and
[`itertools.chain()`][py-itertools-chain] to simplify the main `for` loops of
our solution.

- `starmap()` does the same job as `map()`, but unpacks the arguments to pass to
   the mapping function first:

   ```python
   from itertools import starmap

   def func(a, b, c):
       return a + b + c

   tuples = [(1, 2, 3), (4, 5, 6), range(7, 10)]
   for x in starmap(func, tuples):
       print(x, end=' ')

   # Will print: 6 15 24
   ```

- `chain()` simply *chains* iterable objects together int one long generator:

   ```python
   from itertools import chain

   for x in chain(range(1, 4), range(4, 7), (7, 8, 9)):
       print(x, end=' ')

   # Will print: 1 2 3 4 5 6 7 8 9
   ```

Applying `starmap()` we have:

```python
for points in starmap(diag, lines):
    for p in points:
        space[p] += 1
```

Coupling this with `chain()` we can compress the double `for` into a single one:

```python
for p in chain(starmap(horiz, lines)):
    space[p] += 1

overlapping = sum(x > 1 for x in space.values())
print('Part 1:' overlapping)

for p in chain(starmap(diag, lines)):
    space[p] += 1

overlapping = sum(x > 1 for x in space.values())
print('Part 2:' overlapping)
```

This code is not necessarily better than the original in terms of performance.
In fact, there's a chance this could even perform slightly worse. For such small
inputs however there isn't much difference. A benchmark would be interesting:
I'll leave that as an exercise to the reader.


Day 6 - Lanternfish
-------------------

[Problem statement][d06-problem] — [Complete solution][d06-solution] — [Back to top][top]


### Part 1

Lanternfish. Amazing creatures, aren't they? I always found them fascinating.
Today's puzzle asks us to track the evolution of a population of fish. We know
each fish produces a new one each 7 days. We can interpret this as the fish
having a "timer" of days left until reporoduction starting at 6 and going down
to 0; once at 0, the next day the fish will give birth to a new one and reset
its timer to 6.

We are told that any newborn fish will initially start with a timer of 8
(instead of 6), but after giving birth they will keep resetting it to 6. We are
given a list of timer values: the initial timers of our population of fish at
day zero. We want to know how many fish will be there on day 80.

Quite simple problem, it seems. Getting our input is, as usual, just a matter of
[`.split()`][py-str-split] plus [`map()`][py-builtin-map]:

```python
fin  = open(...)
fish = list(map(int, fin.read().split(',')))
```

How can we evolve the fish? Well, simple: just follow the rules and simulate the
80 days! Each day we'll create a new `list` of fish, and for each fish of the
previous day we'll decrement its timer and check whether it's below `0`: if so,
append two fish to the new list (one with timer ot `6` and one with timer of
`8`); otherwise, just append the decremented value back.

```python
for _ in range(80):
    newfish = list()

    for timer in fish:
        timer -= 1

        if timer < 0:
            newfish.append(8)
            newfish.append(6)
        else:
            newfish.append(timer)

    fish = newfish
```

Finally, `len()` will give us the answer:

```python
n = len(fish)
print('Part 1:', n)
```

### Part 2

Now we want to know how many fish will be there in **256 days**.

Okay... can't we just change the limit of our `range()`? How many could there
ever be? Taking a look at the example input which starts with *only 5 fish*, we
are told that after 256 days there will be approximately *27 billion!* Our
initial population consists of 300 fish... needless to say, we'll never be able
to hold such a large list in memory, let alone iterate over it in a decent
amount of time. We need to find a better solution.

The rules are simple enough. Each fish that has the same timer value will behave
exactly the same. If at day `0` there are 5 fish with a timer of `1`, the next
day there will be exactly 5 fish with a timer of `0`, and the following day
exactly 5 fish with a timer of `6` and 5 new fish with a timer of `8`. Noticing
this, we can group fish by their timer value and batch the operation to make it
a lot faster.

A [`defaultdict`][py-collections-defaultdict] comes in handy for this purpose.
The logic is exactly the same as the one used in part 1, only that this time
we'll keep fish in a `defaultdict` of the form `{timer: number_of_fish}`.

We can use this solution for part 1 too, so let's just write an evolution
function to use two times. It will take a dictionary of fish and a number of
days to simulate, and return the final state as a new dictionary plus the total
count of fish (for convenience). The only thing that really changes from our
initial list-based solution is that updating the new dictionary will be an
operation of the form `newfish[timer] += n`, and to calculate the final total
number of fish we'll need to [`sum()`][py-builtin-sum] up all the values in the
dictionary.

```python
def evolve(fish, days):
    for _ in range(days):
        newfish = defaultdict(int)

        for t, n in fish.items():
            t -= 1

            if t < 0:
                newfish[6] += n
                newfish[8] += n
            else:
                newfish[t] += n

        fish = newfish

    return fish, sum(fish.values())
```

To create the initial dictionary we can iterate over the input integers after
parsig them with `.split()` + `map()`:

```python
timers = map(int, fin.read().split(','))
fish   = defaultdict(int)

for t in timers:
    fish[t] += 1
```

The above operation of counting the number of occurrences of each distinct value
in an iterable can be also done in a much more concise way using a
[`Counter`][py-collections-counter] object from the
[`collections`][py-collections] module, which given an iterable returns a
dictionary-like object of the form `{value: num_of_occurrences}`.

```python
from collections import Counter
fish = Counter(map(int, fin.read().split(',')))
```

Now we can use `evolve()` to get the answers for both part 1 and 2:

```python
fish, n1 = evolve(fish, 80)
_   , n2 = evolve(fish, 256 - 80)

print('Part 1:', n1)
print('Part 2:', n2)
```

Really simple and enjoyable puzzle!


Day 7 - The Treachery of Whales
-------------------------------

[Problem statement][d07-problem] — [Complete solution][d07-solution] — [Back to top][top]

### Part 1

Today's problem is a rather simple minimization problem, but the math behind it
that gets us to a simple, non-bruteforce solution is not as simple to digest.

We are given a list of numbers, and we are told that we need to find some
integer *X* such that the sum of the absolute differences between *X* and each
number is lowest. The value of such lowest sum is our answer.

Visualizing the problem, this is like asking us to minimize the sum of the
lengths of the following segments (from each `o` to the line denoted by `X`):

```none
  ^
  |
  |         o
  |  o      |      o
  |  |      |      |
X +---------------------
  |     |      |     |
  |     |      |     o
  |     o      |
  |            o
0 +
```

Of course, we could brute-force our way to the answer without thinking about it
one more second, as I did in my [original solution][d07-orginal]. After all, a
simple loop is enough to calculate the sum of differences for a given value of
*X*:

```python
def distance_sum(numbers, x):
    tot = 0
    for n in numbers:
        tot += abs(n - x)
    return tot
```

... and another `for` loop over all the possible values is enough to find the
minimum possible sum:

```python
best = float('inf')

for n in range(min(numbers), max(numbers) + 1):
    s = distance_sum(ints, x)

    if s < best:
        best = f
```

This is far from the optimal solution however. As it turns out, the best way to
find *X* is to simply calculate the [median][wiki-median] of the input numbers.
The median is the number which is higher than half the numbers and lower than
the other half (excluding the median itself). In other words, after sorting all
the numbers we have, the median is the number which sits right in the middle (in
case we have an odd amount of numbers).

To understand *why* the median, let's try to see what would happen in case we
do *not* chose the median:

Let's say that we have *N* numbers (*N* odd for simplicity) amongst which *X* is
the median, and *S* is the sum of the absolute deviations of our numbers from
*X*. Note that as per the definition of median, we have exactly *(N-1)/2*
numbers above and below the median. Now, what happens if we deviate from *X*?

- If we *increment* *X* by one, we are getting closer to exactly *(N-1)/2*
  numbers (i.e. all the numbers above the median), so the absolute sum of
  deviations (*S*) decreases by *(N-1)/2*. However, at the same time we are
  getting farther away from *(N-1)/2* ***+ 1*** numbers (i.e. all the numbers
  below the median, plus the median itself), so *S* also increases by
  *(N-1)/2 + 1*. In the end, we have that as a result of incrementing *X* by 1,
  *S* also increases by 1.

- If we *decrement* *X* by one instead, the exact same thing happens. We are
  getting closer to exactly *(N-1)/2* numbers (i.e. all the numbers below the
  median), but again farther away from *(N-1)/2* ***+ 1*** numbers at the same
  time (i.e. all the numbers above the median, plus the median itself). So as
  a result of decrementing *X* by 1, *S* still increases by 1.

No matter which direction we move, the median represents the point where we have
the lowest possible absolute sum of deviations from our set of input numbers.
This reasoning still holds when *N* is even, only that in such case we have two
medians (i.e. two middle values), and we will have a wider range of possible
values for *X*: all the numbers in the range of these two medians (ends
included). [This post on Math StackExchange][misc-median-math-se] gives
different explanations as well as mathematical proof of the above.

Okay... enough with the thinking. How do we calculate the median? The most
optimal way to do this would be to use a function similar to C++'s
[`std::nth_element`][misc-cpp-nth-element]. This function is able to calculate
the value of the Nth largest element of a sequence of numbers in [linear
time][wiki-linear-time] i.e. *O(n)*, and does not need to sort the entire
sequence of numbers. It is a modified version of [quicksort][algo-quicksort]
where each step the search only proceeds on one of the two halves of the data.
[Here's a StackOverflow post][misc-cpp-nth-element-so] with some additional
explanation about this algorithm.

Unfortunately Python does not have any similar cool function to optimally find
the n-th largest element of an iterable. Instead, if we
[take a look in CPython's source code][misc-cpython-median-low] for
[`statistics.median_low()`][py-statistics-median-low] from the standard library,
we can see that the implementation simply sorts the input iterable and then
indexes it right at the middle to get the median.

Since we are dealing with a small amount of numbers, re-implementing
`std::nth_element` in Python would simply be too slow. We are much better off
sorting and indexing our input list once.

So, coming to the actual code, all we need to do is parse the input with our
usual [`.split()`][py-str-split] + [`map()`][py-builtin-map], find the median by
sorting with [`.sort()`][py-list-sort] and then [`sum()`][py-builtin-sum] up all
the [`abs`][py-builtin-abs]olute differences from the median. Woah, it literally
takes ten times as long to explain it than to write it:

```python
nums = list(map(int, fin.readline().split(',')))
nums.sort()

median = nums[len(nums) // 2]
answer = sum(abs(x - median) for x in nums)

print('Part 1:', answer)
```

### Part 2

For part 2 things get spicier. We need to do the same thing as before, but this
time minimizing a different value. For each number *n*, the distance metric from
our chosen *X* value now becomes the sum of all the integers from 1 up to
*X - n*. We still need to sum up this distance metric for all the numbers we
have after choosing *X*, and then answer with the lowest possible such sum.

As an example, if we have three numbers `[1, 3, 10]` and we choose *X = 3* we
have a distance from 1 equal to the sum of all the numbers from 1 to 2 (3 - 1),
that is 2 + 3 = 5; then we have a distance from 10 equal to the sum of all the
numbers from 1 to 7 (10 - 1) , equal to 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28. The sum
of these is 33.

How can we easily calculate this distance metric for a given value of *X* and a
given number *n*? We want to sum numbers from 1 to *|n - X|*. The sum of all the
integers from 1 up to a certain integer *n* (included) is given by the n-th
[triangular number][wiki-triangular-number], and it's equal to *n(n + 1)/2*, or
*(n<sup>2</sup> + n)/2*. We want to minimize the sum of
*((n<sub>i</sub> - X)<sup>2</sup> + (n<sub>i</sub> - X))/2* for each
*n<sub>i</sub>* in our input numbers.

Let's take a step back and simplify this a bit. What if our distance metric was
merely *(n - X)<sup>2</sup>* instead? In such case, looking for a value which
minimizes the sum of deviations from our given numbers is as simple as
calculating the average of those numbers. Our problem looks awfully similar to a
[linear least squares][wiki-linear-least-squares] approximation. In our case,
there are two differences:

1. While normal least squares approximation has the goal of minimizing the sum
   *∑(n<sub>i</sub> - X)<sup>2</sup>*, in our case we need to minimize
   *∑((n<sub>i</sub> - X)<sup>2</sup>/2 + (n<sub>i</sub> - X)/2)* instead.
   Finding an *X* which minimizes *∑(n<sub>i</sub> - X)<sup>2</sup>* or finding
   an *X* which minimizes *∑(n<sub>i</sub> - X)<sup>2</sup>/2* would yield the
   same result as we are merely multiplying the objective function to minimize
   by a constant (the minimum changes, but its position doesn't). However, we
   also have an additional *(n<sub>i</sub> - X)/2* in our way. As it turns out,
   this additional linear term means that using the least squares method is not
   exactly accurate for our goal, but it still gives us a very good
   approximation of the value of *X* we want to find.

2. We are not interested in a real 2D linear regression, but merely some sort of
   *average*, as our problem is one dimensional. It can also be seen as looking
   for a horizontal line in space which has the minimum sum of squared distances
   from the given points (as seen in the example diagram in part 1). We don't
   care about the slope of the line, we know that it is zero. All we care about
   is its height (intercept of the y axis).

To summarize the above, the value of *X* we are looking for is very close to the
average (i.e. the *mean*) of our input numbers. How close? Well, it could
coincide, or it could be in the range of [+1/2, -1/2] from the mean. A pretty
nice and extensive explanation has also been given by Reddit user
[u/throwaway7824365346][d07-reddit-paper-author] in
[this beautiful post][d07-reddit-paper] in the form of a short 4-pages paper
signed *"CrashAndSideburns"*. This has also been discussed on AoC's subreddit
[in this post][d07-reddit-discussion] and also in the
[daily solution megathread][d07-reddit-megathread] for today's problem.

We can calculate the [floor][wiki-floor-ceil] of the average with a sum plus an
integer division, then check whether the minimum value we want actually sits at
this value or at the immediately next value. Let's write a function to do the
sum for us given a value for *X*, using the triangular number formula:

```python
def sum_distances(nums, x):
    tot = 0
    for n in nums:
        delta = abs(n - x)
        tot += (delta * (delta + 1)) // 2
    return tot
```

Now all we have to do is take the mean and check:

```python
mean   = sum(nums) // len(nums)
answer = min(sum_distances(nums, mean), sum_distances(nums, mean + 1))

print('Part 2:', answer)
```


Day 8 - Seven Segment Search
----------------------------

[Problem statement][d08-problem] — [Complete solution][d08-solution] — [Back to top][top]

### Part 1

Today we're dealing with [seven-segment displays][wiki-seven-segment-display]!
In order to identify the state of a digit in a seven-segment display, we use the
letters from `a` to `g` to indicate the different segments. After assigning each
letter to a specific segment, we are capable of identifying the number
associated with the segment as a string of characters, each of which is a letter
identifying a segment that is ON.

For example, given the following mapping of letters to segments:

```none
 aaaaaa
b      c
b      c
 dddddd
e      f
e      f
 gggggg
```

We are able to identify the number `0` with the pattern `abcefg`, the number `1`
with the pattern `cf`, the number `2` with `acdeg`, and so on:

```none
   0:        1:        2:       3:        4:
 aaaaaa    ......    aaaaaa   aaaaaa    ......
b      c  .      c  .      c .      c  b      c
b      c  .      c  .      c .      c  b      c
 ......    ......    dddddd   dddddd    dddddd
e      f  .      f  e      . .      f  .      f
e      f  .      f  e      . .      f  .      f
 gggggg    ......    gggggg   gggggg    ......

   5:        6:        7:        8:        9:
 aaaaaa    aaaaaa    aaaaaa    aaaaaa    aaaaaa
b      .  b      .  .      c  b      c  b      c
b      .  b      .  .      c  b      c  b      c
 dddddd    dddddd    ......    dddddd    dddddd
.      f  e      f  .      f  e      f  .      f
.      f  e      f  .      f  e      f  .      f
 gggggg    gggggg    ......    gggggg    gggggg
```

Our input consists of lines of the following form:

```none
<pattern> <pattern> ... (10 times) | <pattern> <pattern> <pattern> <pattern>

Example:
acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb ab | cdfeb fcadb cdfeb cdbaf
```

The first 10 patterns are strings representing the 10 different unique ways in
which each digit can light up to represent a number, while the last 4 (after the
pipe `|`) represent a 4-digit number that we want to decode. The problem is that
*we do not know the mapping between letters in the patterns and segments on the
display!* For each line, the mapping is different, and we must deduce it through
some kind of logic just by observing those first 10 unique patterns.

For the first part of the problem, we want to merely count, amongst the second
part of each line, how many times the digits `1`, `4`, `7` and `8` are
represented. This should be rather easy: as the problem statement explains,
those four digits are *the only digits* that have a unique number of segments
ON to be represented. Indeed `1` has 2 segments ON, `4` has 4, `7` has 3 and `8`
has all 7 segments ON.

Let's get the input and parse it first. We'll extract the second part of each
line (since right now that's all we care about) and count the lengths of the
patterns it includes. We can simply [`.split()`][py-str-split] each line on the
pipe `|`, then `.split()` again on whitespace to separate the four patterns.

```python
fin = open(...)

for line in fin:
    digits = line.split('|')[1]
    digits = digits.split()
```

Now we can [`map()`][py-builtin-map] each digit pattern to its
[`len()`][py-builtin-len], and then count the number of times we see the lengths
we are looking for. We'll do this all in the same loop:

```python
to_count = {2, 4, 3, 7} # pattern lengths we want to count
count    = 0

for line in fin:
    digits = line.split('|')[1]
    digits = map(len, digits.split())

    for pattern_length in digits:
        if pattern_length in to_count:
            count += 1
```

The inner `for` loop can be simplified into a `sum()` plus a
[generator expression][py-generator-expr] as it is merely summing based on a
condition:

```python
to_count = {2, 4, 3, 7}
count    = 0

for line in fin:
    digits = line.split('|')[1]
    digits = map(len, digits.split())
    count += sum(pl in to_count for pl in digits)

print('Part 1:', count)
```

### Part 2

Now the problem gets more complicated. For each line of input, we need to
actually understand the mapping used based on the given 10 unique patterns and
then decode the 4-digit number. The sum of all the decoded numbers is our
answer.

Okay, first let's re-parse the input. As you may already have noticed, the
patterns in our input have different orders each time they appear, even within
the same line, for example:

```none
be cfbegad cbdgef fgaecd cgeb fdcge agebfd fecdb fabcd edb | fdgacbe cefdb cefbgd gcbe
   ^^^^^^^                                                   ^^^^^^^
```

The two patterns highlighted above actually represent the same digit, but the
letters are in different orders. Each letter only means that a particular
segment is ON, the order does not matter, however if we want to match them
between each other we will need to convert them into some identifier that is the
same no matter the letter order. We could do this in different ways, but for our
purpose transforming each of those strings into a [`frozenset`][py-frozenset] of
letters will be the most helpful later on.

We'll convert each pattern we encounter into a `frozenset` of letters, and also
precalculate its length for later.

```python
for line in fin:
    raw_patterns, raw_digits = map(str.split, line.split('|'))
    patterns, digits = [], []

    for p in raw_patterns:
        patterns.append((frozenset(p), len(p)))

    for d in raw_digits:
        digits.append((frozenset(d), len(d)))
```

The two inner `for` loops we just wrote merely construct two lists, so we can
reduce them into a `list(map(...))` expression, or better `tuple(map(...))`
since we'll not need to modify their content. Using a
[`lambda` expression][py-lambda] makes us able to easily construct the tuples of
`(frozenset(p), len(p))` while using `map()`.

```python
for line in fin:
    patterns, digits = map(str.split, line.split('|'))
    patterns = tuple(map(lambda p: (frozenset(p), len(p)), patterns))
    digits   = tuple(map(lambda p: (frozenset(p), len(p)), digits))

    # ... do something ...
```

Now to the real problem: deducing which pattern corresponds to which digit and
creating a mapping to decode the numbers. We'll write a `deduce_mapping()`
function which takes the `petterns` extracted from each line of input as
argument and returns a pattern-to-digit mapping `p2d` of the form
`{pattern: digit}`, to be used to decode our `digits` by simply doing
`p2d[digit_pattern]`.

First of all, we can make some easy deductions based only on the length of a
pattern:

1. If the pattern's length is any of `2 4 3 7`, we already know from part
   1 that those lengths univocally correspond to the digits `1 4 7 8`
   respectively.
2. There are only 3 digits with 5 out of 7 segments ON, so if the pattern's
   length is `5`, we know the digit can only be one of `2`, `3` or `5`.
3. There are only 3 digits with 5 out of 7 segments ON, so if the pattern's
   length is `6`, we know the digit can only be one of `0`, `6` or `9`.

Let's start by calculating an initial incomplete mapping for the four digits
with unique pattern lengths:

```python
def deduce_mapping(patterns):
    # pattern to digit mapping
    p2d = {}

    for p, plen in patterns:
        if plen == 2:
            p2d[p] = 1
        elif plen == 3:
            p2d[p] = 7
        elif plen == 4:
            p2d[p] = 4
        elif plen == 7:
            p2d[p] = 8
```

Here's the first reason why I chose to use `frozenset`s to represent patterns:
they are immutable, and thus hashable, therefore they can be used as dictionary
keys (as we are doing above).

Now we can further examine the unmapped patterns.

```python
    # ... continues from above ...

    for p, plen in patterns:
        if p in p2d:
            # pattern already known
            continue

        if plen == 5:
            # 2 or 3 or 5
            pass
        else:
            # 0 or 6 or 9
            pass

    return p2d
```

Now we have two cases: in the first one we need to distinguish between `2`, `3`
and `5`, while in the second one between `0`, `6` and `9`. To do this, we can
use similarities between these and the four already known digits (refer to the
ASCII art in part 1 and see for yourself):

- To distinguish between `2`, `3` and `5`:

  1. The digit `3` is the only one amongst those that has exactly 2 segments in
     common with `1`: so if at this point the pattern we are looking at has
     exactly two letters in common with the pattern for `1`, we just found the
     pattern for `3`.
  2. Otherwise... `5` is the only one amongst `2` and `5` which has exactly 3 ON
     segments in common with `4`, so if at this point the pattern we are looking
     at has exactly 3 letters in common with the pattern for `4`, we just fount
     the pattern for `5`.
  3. Otherwise... the pattern we are looking at is for the digit `2`.

- To distinguish between `0`, `6` and `9`, the same logic can be used:

  1. `9` is the only one to have 4 ON segments in common with `4`.
  2. `6` is the only one to have 2 ON segments in common with `7`.
  3. If none of the above two applies, we found the pattern for `0`.

It's clear that we temporarily also need a reverse mapping `d2p` (digit to
pattern) to do the above calculations. We can invert our mapping with a simple
[dictionary comprehension][py-dict-comprehension] expression:

```python
d2p = {v: k for k, v in p2d.items()}
```

How do we check the number of common segments (i.e. letters) amongst two
patterns? Here comes the second reason why I chose `frozenset`s: like normal
`set`s, `frozenset`s in Python support
[quick and easy intersection][py-set-intersection] through the binary `&`
operator (or the `.intersection()` method). If we intersect two patterns (which
are both `frozenset`s) we will get a `frozenset` only holding the letters in
common between the two: we can then check the `len()` of that `frozenset` to
see how many of them there are. This isn't in general the most optimal way of
accomplishing such a task, but it's surely simple and concise. In our case where
sets can contain at most 7 letters, this is perfectly doable.

All that's left to do is apply the deduction rules outlined above using our
`d2p` mapping and set intersections:

```python
def deduce_mapping(patterns):
    # pattern to digit mapping
    p2d = {}

    for p, plen in patterns:
        if plen == 2:
            p2d[p] = 1
        elif plen == 3:
            p2d[p] = 7
        elif plen == 4:
            p2d[p] = 4
        elif plen == 7:
            p2d[p] = 8

    # digit to pattern mapping
    d2p = {v: k for k, v in p2d.items()}

    for p, plen in patterns:
        if p in p2d:
            continue

        if plen == 5:
            # 2 or 3 or 5
            if len(p & d2p[1]) == 2:
                # 3 has 2 ON segments in common with 1
                p2d[p] = 3
            elif len(p & d2p[4]) == 3:
                # 5 has 3 ON segments in common with 4
                p2d[p] = 5
            else:
                p2d[p] = 2
        else:
            # 0 or 6 or 9
            if len(p & d2p[4]) == 4:
                # 9 has 4 ON segments in common with 4
                p2d[p] = 9
            elif len(p & d2p[7]) == 2:
                # 6 has 2 ON segments in common with 7
                p2d[p] = 6
            else:
                p2d[p] = 0

    return p2d
```

Now that we have a function to deduce the pattern-to-digit mapping, we can use
it in our main loop to calculate the mapping for every line of input and then
use it to get the values of the digits we need. We'll also include the part 1
calculation in our loop.

```python
total    = 0
count    = 0
to_count = {2, 4, 3, 7}

for line in fin:
    patterns, digits = map(str.split, line.split('|'))
    patterns = tuple(map(lambda p: (frozenset(p), len(p)), patterns))
    digits   = tuple(map(lambda p: (frozenset(p), len(p)), digits))

    p2d = deduce_mapping(patterns)

    count += sum(l in to_count for _, l in digits)
    total += p2d[digits[0][0]] * 1000
    total += p2d[digits[1][0]] * 100
    total += p2d[digits[2][0]] * 10
    total += p2d[digits[3][0]]

print('Part 1:', count)
print('Part 2:', total)
```

Nice! 16 stars and counting... oh yeah, I like powers of 2.


Day 9 - Smoke Basin
-------------------

[Problem statement][d09-problem] — [Complete solution][d09-solution] — [Back to top][top]

### Part 1

First problem that has to do with graph theory of the year! We are given a grid
of single-digit numbers, and we are told to find all the numbers in the grid
which are lower than all of their neighbors. The neighbors of a number in the
grid are defined as four numbers directly above, below, left and right. Once we
find all the numbers that satisfy this criterion, we need to compute their sum,
also adding 1 to the sum for each number (this +1 for each number honestly feels
like a rule that was added to make you get a wrong solution, hehehe).

Let's parse the input into a matrix (grid) of numbers. We can
[`map()`][py-builtin-map] each character on each line of input into an `int`,
and construct a `tuple` of `tuple`s with a
[generator expression][py-generator-expr]:

```python
fin   = open(...)
lines = map(str.rstrip, fin)
grid  = tuple(tuple(map(int, row)) for row in lines)
```

The problem seems simple enough. Since we are gonna need it later too, let's
write a [generator function][py-generator-function] that yields all the
neighbors of a given grid cell given the grid and the cell's coordinates. For
each possible delta of +/-1 in the two directions from the current cell
coordinates, check if the coordinates plus the delta are in bounds of the grid,
and if so `yield` them. We've written this function a bunch of times on last
year's AoC too.

```python
def neighbors4(grid, r, c):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        rr, cc = (r + dr, c + dc)
        if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
            yield (rr, cc)
```

Since we merely need coordinates, we can just pass heigh and width of the grid
as arguments and avoid calling `len()` every single time:

```python
def neighbors4(r, c, h, w):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        rr, cc = (r + dr, c + dc)
        if 0 <= rr < w and 0 <= cc < h:
            yield (rr, cc)
```

Now we can iterate over the entire grid and check every single cell for the
property we are looking for. If all neighbors of a given cell are higher than
the cell itself, we'll add the cell's value plus 1 to the total. The
[`enumerate()`][py-builtin-enumerate] built-in comes in handy to get both the
coordinates and the cell values at the same time.

```python
h, w  = len(grid), len(grid[0])
total = 0

for r, row in enumerate(grid):
    for c, cell in enumerate(row):
        ok = True
        for nr, nc in neighbors4(r, c, h, w):
            if grid[nr][nc] <= cell:
                ok = False
                break

        if ok:
            total += cell + 1
```

The innermost `for` loop is looking for any neighbor which does not respect the
given constraint. This is the naïve way through which one would normally check
if all values in an iterable respect a constraint. We're in Python though, and
we have the amazing [`all()`][py-builtin-all] built-in that does exactly this
for us!

```python
for r, row in enumerate(grid):
    for c, cell in enumerate(row):
        if all(grid[nr][nc] > cell for nr, nc in neighbors4(r, c, h, w)):
            total += cell + 1

print('Part 1:', total)
```

Part one completed, let's move on to the real problem now!

### Part 2

We are told that cells with value lower than `9` in the grid are isolated in
"basins", which are groups of cells surrounded by walls of `9`. All cells that
are not `9` can be seen as being connected together amongst the four directions.
For example in the following grid we have four basins, highlighted with `.` on
the right (do not get confused, cells are *not* connected diagonally):

```
2199943210       ..99943210  21999.....  2199943210  2199943210
3987894921       .987894921  398789.9..  39...94921  3987894921
9856789892  -->  9856789892  985678989.  9.....9892  9856789.92
8767896789       8767896789  8767896789  .....96789  876789...9
9899965678       9899965678  9899965678  9.99965678  98999.....
```

We are asked to find the sizes of the 3 largest basins and multiply them
together to get the answer.

What the puzzle is basically asking us is to find the three largest
[connected components][wiki-graph-component] in our grid.

How can we find a single connected component? Or in other words, given the
coordinates of a cell, how can we find the coordinates of all the cells
reachable from this one? [Breadth-first search][algo-bfs] (BFS) is the simplest
way: given a cell's coordinates, explore all the reachable cells using BFS,
avoiding walls (`9`), and when the search stops return the set of visited
coordinates. Let's write a function that does exactly this. The algorithm is
plain and simple BFS, with the use of a [`deque`][py-collections-deque] as
queue:

```python
def bfs(grid, r, c, h, w):
    queue   = deque([(r, c)])
    visited = set()

    # while there are cells to visit
    while queue:
        # get the first one in the queue and visit it
        rc = queue.popleft()
        if rc in visited:
            continue

        visited.add(rc)

        # for each neighbor of this cell
        for nr, nc in neighbors4(*rc, h, w):
            # if it's not a wall and it has not been visited already
            if grid[nr][nc] != 9 and (nr, nc) not in visited:
                # add it to the queue
                queue.append((nr, nc))

    return visited
```

To find *all* connected components, we could simply call the above `bfs()`
function for every single cell, accumulating the set of visited cells to ignore
them later. However, the problem statement gives an hint that can help us
simplify the search for connected components:

> **A basin is all locations that eventually flow downward to a single low
> point**. Therefore, every low point has a basin, although some basins are very
> small. Locations of height 9 do not count as being in any basin, and **all
> other locations will always be part of exactly one basin**.

It seems that there is exactly one basin per low point, and one low point per
basin. We already have the code to find low points from part 1, we can store all
their coordinates in a list and use them later to start a BFS from each one of
them, without having to worry about exploring the same basin (i.e. connected
component) twice.

Let's modify the code for part 1 first:

```diff
+sinks = []

 for r, row in enumerate(grid):
     for c, cell in enumerate(row):
         if all(grid[nr][nc] > cell for nr, nc in neighbors4(r, c, h, w)):
+            sinks.append((r, c))
             total += cell + 1
```

After modifying the above BFS function to just return the size of each
component:

```patch
-def bfs(grid, r, c, h, w):
-    queue   = deque([(r, c)])
+def component_size(grid, src, h, w):
+    queue   = deque([src])
     ...
-    return visited
+    return len(visited)
```

Now we can call the above function for each low point to get the sizes using
`map()` plus a [`lambda`][py-lambda], and after getting them
[`sorted()`][py-builtin-sorted] in descending order (`reverse=True`), get the
first 3 sizes and multiply them together to get our answer:

```python
sizes  = map(lambda s: component_size(grid, s, h, w), sinks)
sizes  = sorted(sizes, reverse=True)
answer = sizes[0] * sizes[1] * sizes[2]

print('Part 2:', answer)
```


Day 10 - Syntax Scoring
-----------------------

[Problem statement][d10-problem] — [Complete solution][d10-solution] — [Back to top][top]

### Part 1

Today we need to validate sequences of open and closed parentheses, and I love
me some [Dyck Language][wiki-dyck-language] validation first thing in the
morning!

We are given a bunch of lines consisting of only open and close parentheses of
four different types: `([{<>}])`. We are then asked to evaluate each line to
find out if it's "corrupted". A corrupted line is one where there is a syntax
error consisting of a close parenthesis of the wrong kind. For example, in the
string `[()<[]}]` the `}` which is closing the `<` is wrong and should be a `>`
instead.

Each kind of parenthesis has a different "syntax error score" when mismatched:
an illegal `)` gives 3 points, `]` 57 points, `}` 1197 points, and `>` 25137
points. We need to sum up all the scores of all corrupted lines, stopping at the
first syntax error for each line.

Let's define the scores as a global dictionary:

```python
SYNTAX_SCORE = {')': 3, ']': 57, '}': 1197, '>': 25137}
```

The least-powerful class of automata that can recognize a Dyck Language is the
[pushdown automata][wiki-pushdown-automata]. We can write one ourselves to
validate the strings:

- For every character:
  - If it's an open parenthesis, push the matching *close* parenthesis onto the
    stack.
  - If it's a close parenthesis, pop the last pushed parenthesis from the stack
    and check if it's equal to the current character: if not, we have a syntax
    error.

To translate each open parenthesis in its close counterpart, we can make use of
[`str.maketrans()`][py-str-maketrans] to build a translation table once, and
then [`str.translate()`][py-str-translte] to use the table to translate the
characters.

```python
TRANS_TABLE = str.maketrans('([{<', ')]}>')

# '('.translate(TRANS_TABLE) -> ')'
# '(([{[<'.translate(TRANS_TABLE) -> '))]}]>'
```

Let's write a function that takes a string of parentheses and scans it for the
first syntax error. We'll use a [`deque`][py-collections-deque] as stack.
Following the above algorithm, if we ever stop for a syntax error we'll simply
return the score, otherwise we'll return `0`.

```python
def check(s):
    stack = deque()

    for c in s:
        if c in '([{<':
            stack.append(c.translate(TRANS_TABLE))
        elif stack.pop() != c:
            return SYNTAX_SCORE[c]

    return 0
```

All that's left to do is call the function for each line of input and
[`sum()`][py-builtin-sum] up all the values. We can use
[`map()`][py-builtin-map] directly on the input file after stripping each line
of trailing newlines (`\n`) with [`str.rstrip`][py-str-rstrip]:

```python
fin   = open(...)
total = sum(map(check, map(str.rstrip, fin)))

print('Part 1:', total)
```

### Part 2

Now we are concerned about *unterminated* sequences of parentheses. Amongst
those that are not corrupted, there are some sequences ending prematurely
without closing all the parenthesis that were opened. We must find such
sequences and calculate an "autocompletion score" for each one of them. Then,
take the [median][wiki-median] of those scores.

To calculate the "autocompletion score" we assign a value to each kind of close
parenthesis. Starting with an initial score of zero, from the first to the last
autocompleted close parenthesis, multiply the current score by 5, then add the
current parenthesis value to the score.

This time the values of parenthesis are given by the following dictionary:

```python
COMPL_SCORE = {')': 1, ']': 2, '}': 3, '>': 4}
```

The algorithm to use is almost unchanged. We still need to parse sequences using
a stack, and we still need to prematurely stop on corrupted ones since we don't
want to calculate an autocompletion score for those. We can modify our `check()`
function to return two scores at once.

Calculating the autocompletion score is simple: after we scanned all the
characters in a sequence, check if we still have some left in the stack: if so,
those are the ones that we should use to autocomplete the sequence. We can pop
them one by one and calculate the score as described.


The updated `check()` function is as follows:

```python
def check(s):
    stack = deque()

    for c in s:
        if c in '([{<':
            stack.append(c.translate(TRANS_TABLE))
        elif stack.pop() != c:
            return SYNTAX_SCORE[c], 0

    score2 = 0
    while stack:
        score2 *= 5
        score2 += COMPL_SCORE[stack.pop()]

    return 0, score2
```

Our main prograrm changes shape. We won't be able to have `map()` one-liner for
the first part anymore. Let's write a `for` loop instead, where we sum all
syntax error scores and we save all autocompletion scores in a list:

```python
tot_syntax = 0
autocompl_scores = []

for l in map(str.rstrip, fin):
    score1, score2 = check(l)
    tot_syntax += score1

    if score2 > 0:
        autocompl_scores.append(score2)

print('Part 1:', tot_syntax)
```

For the median, we'll simply sort `autocompl_scores` and take the middle value:

```python
autocompl_scores.sort()
mid_autocompl = autocompl_scores[len(autocompl_scores) // 2]
print('Part 2:', mid_autocompl)
```

Really nice puzzle. I used to love dealing with pushdown automata when studying
for my "Formal languages and compilers" University course.


Day 11 - Dumbo Octopus
----------------------

[Problem statement][d11-problem] — [Complete solution][d11-solution] — [Back to top][top]

### Part 1

And here it comes the first "evolve this grid N times" kind of puzzle of the
year. We are dealing with a grid of digits (integers between 0 and 9). Given the
initial state of the grid, we need to "evolve" it 100 times, given the following
rules to evolve it once:

- All cells increase their value by 1.
- All cells above 9 "flash", and start a chain reaction:

  1. All neighbors of a flashing cell increase by 1 (again).
  2. If any of them also gets above 9, they also flash.
  3. Repeat from point 1 until no cells flash anymore.

- All cells that flashed reset their value to 0.

After applying the above rules 100 times, we want to know how many flashes
happened in total.

First things first: let's get our input in the same way we did for [day 9][d09].
Read the file, [`rstrip`][py-str-rstrip] newlines, [`map()`][py-builtin-map]
each character of each row into an `int`, and construct a `list` of `list`:

```python
lines = map(str.rstrip, fin)
grid  = list(list(map(int, row)) for row in lines)
```

First and foremost, we'll definitely need to iterate over the *eight* neighbors
(diagonals are included this time) of a given cell. Let's write a
[generator function][py-generator-function] that yields all the coordinates of
the neighbors of a cell. This is again almost the same function we wrote for
[day 9][d09], only that this time we'll have 8 coordinate deltas instead of 4:

```python
def neighbors8(r, c, h, w):
    deltas = (
        (1, 0), (-1,  0), ( 0, 1), ( 0, -1),
        (1, 1), ( 1, -1), (-1, 1), (-1, -1)
    )

    for dr, dc in deltas:
        rr, cc = (r + dr, c + dc)
        if 0 <= rr < h and 0 <= cc < w:
            yield rr, cc
```

It's pretty clear that the core of the problem is in the "flashing" of the
cells, which creates a chain reaction among neighboring cells. The important
thing to notice is that, once one cell flashes, its job is done for the day; it
will no longer flash until the next step.

There are different ways to do this: we could scan the entire grid until we find
that no more cells will flash, we could enqueue new cells to flash in a queue
and keep going until it's empty, or we could use a recursive function.

My initial solution simply scanned through the whole grid until all cells were
lower or equal than `9`. For such a small grid, that's a perfectly reasonable
solution. However, this is one of the few times where I'd prefer to use
recursion to simplify the problem. Let's write a function to "flash" all cells
that need to, and then keep recursively flashing neighboring cells.

Since we do not want to flash the same cell more than once, we'll use `-1` as a
placeholder for cells that we have already "flashed", so that we can avoid doing
it twice. The code is straightforward. Given a cell:

- If this cell does not need to flash (`<= 9`), do nothing.
- Otherwise:
  - Mark it as "flashed" (`-1`).
  - For each neighbor of the cell which did not flash yet, increment its value
    and recursively call the function on it.

```python
def flash(grid, r, c, h, w):
    if grid[r][c] <= 9:
        return

    grid[r][c] = -1

    for nr, nc in neighbors8(r, c, h, w):
        if grid[nr][nc] != -1:
            grid[nr][nc] += 1
            flash(grid, nr, nc, h, w)
```

We could also have wrapped the entire function body inside an
`if grid[r][c] > 9`, it's just a matter of style.

Now that we sorted out the complex part of the problem, we can just follow the
rest of the rules. Let's write an `evolve()` function to evolve the grid of one
step, and return the number of flashes that happened:

```python
def evolve(grid, h, w):
    flashes = 0

    # First increment every single cell
    for r in range(h):
        for c in range(w):
            grid[r][c] += 1

    # Then flash the ones that need to
    for r in range(h):
        for c in range(w):
            flash(grid, r, c, h, w)

    # Then reset their value to 0
    for r in range(h):
        for c in range(w):
            if grid[r][c] == -1:
                grid[r][c] = 0
                flashes += 1

    return flashes
```

Those are a lot of `for` loops there... that's annoying. We can use
[`itertools.product()`][py-itertools-product] to simplify things a bit:

```python
def step(grid, h, w):
    flashes = 0

    for r, c in product(range(h), range(w)):
        grid[r][c] += 1

    for r, c in product(range(h), range(w)):
        flash(grid, r, c, h, w)

    for r, c in product(range(h), range(w)):
        if grid[r][c] == -1:
            grid[r][c] = 0
            flashes += 1

    return flashes
```

We could also cache the coordinates yielded by `product()` into a `tuple` and
iterate over the tuple multiple times, but our grid is so small that this kind
of optimization wouldn't give us any real advantage.

**Note that** although it seems like the three loops could be fused into one,
that would be wrong: we specifically need to do each of the three steps
separately, otherwise the values in our grid will get mixed up in an
inconsistent state and we'll not get what we want.

Now we can finally call `evolve()` 100 times and [`sum()`][py-builtin-sum] the
total number of flashes with a [generator expression][py-generator-expr] to get
our answer:

```python
h, w = len(grid), len(grid[0])
tot_flashes = sum(evolve(grid, h, w) for _ in range(100))

print('Part 1:', tot_flashes)
```

### Part 2

For the second part of the problem, we are asked to keep evolving the grid step
by step until we reach a point where *all* cells flash in the same step. We need
to find out how many steps it takes to reach such a state.

Well... we can just keep calling `evolve()` until the number of flashing cells
returned is equal to the number of cells in the grid. Easy peasy. To count from
101 onwards we can use [`itertools.count()`][py-itertools-count], which is
essentially like an infinite `range`.

```python
n_cells = h * w

for sync_step in count(101):
    if evolve(grid, h, w) == n_cells:
        break

print('Part 2:', sync_step)
```

That only took `354` steps, nice. I was already getting worried that the number
would have been enormous and impossible to simulate without some major smart
simplification such as finding periodic patterns, as it usually happens for
these kind of problems. Thankfully Eric decided to spare us the pain this time
:').


Day 12 - Passage Pathing
------------------------

[Problem statement][d12-problem] — [Complete solution][d12-solution] — [Back to top][top]

### Part 1

As you probably already guessed by the name of today's puzzle, we'll be dealing
with paths and graphs. The request is simple: we are given an undirected graph,
and we are told to count the number of different paths that exist betweeen the
`start` node and the `end` node. Our paths must only satisfy one property: they
can only visit nodes that have a lowercase name once (per node).

My favorite way to represent graphs in Python is to use what I became used to
call a "graph dictionary", which is a dictionary of the form
`{node: list_of_neighbors}`. For an undirected graph, if we have an edge `a-b`,
our graph dictionary will both contain `b` in the list of neighbors of `a`, and
`a` in the list of neighbors of `b`.

The input format is simple to parse, just [`.rstrip()`][py-str-rstrip] newlines
and [`.split()`][py-str-split] on dashes (`-`) to get the two nodes of an edge.
We'll start with an empty [`defaultdict`][py-collections-defaultdict] of `list`
for simplicity. Since we cannot visit `start` more than once, we'll simply avoid
adding it as a neighbor of any node, this way we won't have to add a special
case to skip it in whatever algorithm we'll use to visit the graph.

```python
fin = open(...)
G = defaultdict(list)

for edge in fin:
    a, b = edge.rstrip().split('-')

    if b != 'start':
        G[a].append(b)
    if a != 'start':
        G[b].append(a)
```

To give an idea of what `G` looks like, considering this simple input and the
corresponding graph it represents (on the right):

```none
start-A
start-b           start
A-c               /   \
A-b           c--A-----b--d
b-d               \   /
A-end              end
b-end
```

After parsing the above, graph dictionary `G` would look like this:

```python
{
    'start': ['A', 'b'],
    'A': ['c', 'b', 'end'],
    'b': ['A', 'd', 'end'],
    'c': ['A'],
    'd': ['b'],
    'end': ['A', 'b']
}
```

Now, if the task was to just find any [single] path from `start` to `end`, we
could have simply used either [depth-first search][algo-dfs] (DFS) or
[breadth-first search][algo-bfs] (BFS) to explore the graph starting from `start`
until we reach `end`, and stop there. Surely enough, to find *all* possible
paths we should not stop as soon as `end` is reached, but continue exploring
other paths.

However, there are still two caveats:

1. In "classic" DFS/BFS we don't usually want to pass multiple times through the
   same node. In fact, in both algorithms we usually keep a set of "visited"
   nodes to avoid loops. In this case though, in case of uppercase nodes we
   don't really care: we can avoid adding those to the visited set.
2. Since we want to find *all* possible paths, we cannot use a global set to
   keep track of visited nodes, otherwise the first path that gets to a given
   node will just mark it visited and make it "unavailable" to any different
   path that could pass through the same node. We will have to keep one visited
   set *per path*.

One interesting thing to notice (or actually, deduce) is that if the problem is
asking us to *count* the number of different paths passing through any uppercase
node any number of times, then there must be a finite number of them. This means
that our graph *must not* contain edges that connect two uppercase nodes
together. In such a case, we would have a cycle of uppercase nodes, and since we
can pass through them any number of times, there would be an *infinite* amount
of possible paths! If we also wanted to handle this case, we would have to
implement a [cycle detection][wiki-cycle-detection] algorithm. Fortunately, this
is unneeded.

We can easily verify that the above condition holds (no edge in our input
connects two uppercase nodes). This also means that no matter how we get to the
destination, since we can only touch each lowercase edge at most once and we
must visit a lowercase edge after an uppercase one, the longest path from
`start` to `end` will visit a number of nodes which is at most around double the
number of lowercase nodes (doing lower-UPPER-lower-UPPER-... an so on).

The only real difference between "classic" BFS and DFS is that BFS uses a
[queue][wiki-queue] to keep track of nodes to visit, while DFS uses a
[stack][wiki-stack] (which is also why it's very common to implement DFS
recursively, while for BFS [not so much][misc-so-recursive-bfs]). In both cases,
a [`deque`][py-collections-deque] can be used as queue/stack.

So, which one should we choose between BFS and DFS? The number of possible paths
is likely to grow big: if we pick DFS we'll probably waste less memory on
keeping a large queue (even though the paths are short, there can still be a lot
of them). My solution will be iterative, even though a recursive one is
absolutely feasible, so this is just personal preference.

Given all we discussed above, the implementation is straightforward:

```python
def n_paths(G, src, dst):
    # Our stack will contain tuples of the form:
    # (node_to_visit, set_of_visited_nodes_to_get_here)
    stack = deque([(src, {src})])
    total = 0

    # while we have nodes to visit
    while stack:
        # get the most recently added node and the set of visited nodes in the
        # path to reach it
        node, visited = stack.pop()

        # if we reached the destination, we found 1 additional path
        # increment the count and stop going forward
        if node == dst:
            total += 1
            continue

        # otherwise, for each neighbor of this node
        for n in G[node]:
            # if we already visited this neighbor AND it's a lowercase node,
            # skip it: we can't advance this path forward
            if n in visited and n.islower():
                continue

            # add the neighbor to the stack and mark it as visited in this
            # particular path
            stack.append((n, visited | {n}))

    return total
```

The `|` operator in `visited | {n}` performs the union of two sets.

A single call to the above function will give us the answer we are looking for:

```python
n = n_paths(G, 'start', 'end')
print('Part 1:', n)
```

### Part 2

The rules change slightly. Previously we were not allowed to visit the same
lowercase node twice. Now, we can visit *at most one lowercase node twice* in
any given path (except for `start`, which we can still only visit once). The
question remains the same: how many different paths are there from `start` to
`end`?

It seems like we also need to keep track of how many times we visit lowercase
nodes. Do we actually need to keep a count for each lowercase node though? Not
really. The only additional constraint says that we can visit a single lowercase
node twice. This thing can only happen once in any given path, therefore all we
need is an additional boolean variable (for each path) to remember if this ever
happened or not.

Let's write a second function very similar to the first one. The algorithm is
the same; the only two things that really change are:

1. We need to add a third element to the tuples in our stack: a boolean
   variable (let's call it `double`), which will be `True` if we ever visited a
   lowercase node twice in the path to this particular node.
2. The check before adding neighbors to the stack gets a little bit more
   complex: if a neighbor has already been visited and it is lowercase, this
   time we can visit it again, but only if `double` is `False` (the actual logic
   we'll use is the exact opposite just to make the control flow of the function
   simpler).

Here it is:

```python
def n_paths2(G, src, dst):
    stack = deque([(src, {src}, False)])
    total = 0

    while stack:
        node, visited, double = stack.pop()
        if node == dst:
            total += 1
            continue

        for n in G[node]:
            # if we didn't already visit this neighbor OR it's an uppercase
            # node, we can surely visit it
            if n not in visited or n.isupper():
                stack.append((n, visited | {n}, double))
                continue

            # otherwise, this neighbor must be a lowercase node that we ALREADY
            # visited: if double == True we already visited some lowercase node
            # twice in this path before, don't advance this path forward
            if double:
                continue

            # in this case we don't even need to add the node to the visited set
            # since we already know it was visited
            stack.append((n, visited, True))

    return total
```

Again we're just one function call away from the answer:

```python
n = n_paths2(G, 'start', 'end')
print('Part 2:', n)
```

As "easy" as that!

---

*Copyright &copy; 2021 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2021-walkthrough
[d01]: #day-1---sonar-sweep
[d02]: #day-2---dive
[d03]: #day-3---binary-diagnostic
[d04]: #day-4---giant-squid
[d05]: #day-5---hydrothermal-venture
[d06]: #day-6---lanternfish
[d07]: #day-7---the-treachery-of-whales
[d08]: #day-8---seven-segment-search
[d09]: #day-9---smoke-basin
[d10]: #day-10---syntax-scoring
[d11]: #day-11---dumbo-octopus
[d12]: #day-12---passage-pathing

[d01-problem]: https://adventofcode.com/2021/day/1
[d02-problem]: https://adventofcode.com/2021/day/2
[d03-problem]: https://adventofcode.com/2021/day/3
[d04-problem]: https://adventofcode.com/2021/day/4
[d05-problem]: https://adventofcode.com/2021/day/5
[d06-problem]: https://adventofcode.com/2021/day/6
[d07-problem]: https://adventofcode.com/2021/day/7
[d08-problem]: https://adventofcode.com/2021/day/8
[d09-problem]: https://adventofcode.com/2021/day/9
[d10-problem]: https://adventofcode.com/2021/day/10
[d11-problem]: https://adventofcode.com/2021/day/11
[d12-problem]: https://adventofcode.com/2021/day/12

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

[d03-orginal]:             original_solutions/day03.py
[d07-orginal]:             original_solutions/day07.py
[d07-reddit-discussion]:   https://www.reddit.com/r/adventofcode/comments/rars4g/
[d07-reddit-megathread]:   https://www.reddit.com/rar7ty
[d07-reddit-paper]:        https://www.reddit.com/r/adventofcode/comments/rawxad
[d07-reddit-paper-author]: https://www.reddit.com/user/throwaway7824365346/

[py-dict-comprehension]:      https://www.python.org/dev/peps/pep-0274/
[py-lambda]:                  https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-generator-function]:      https://wiki.python.org/moin/Generators
[py-generator-expr]:          https://www.python.org/dev/peps/pep-0289/
[py-unpacking]:               https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[py-builtin-abs]:             https://docs.python.org/3/library/functions.html#abs
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-len]:             https://docs.python.org/3/library/functions.html#len
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-counter]:     https://docs.python.org/3/library/collections.html#collections.Counter
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-frozenset]:               https://docs.python.org/3/library/stdtypes.html#frozenset
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-itertools-product]:       https://docs.python.org/3/library/itertools.html#itertools.product
[py-itertools-repeat]:        https://docs.python.org/3/library/itertools.html#itertools.repeat
[py-itertools-starmap]:       https://docs.python.org/3/library/itertools.html#itertools.starmap
[py-itertools-chain]:         https://docs.python.org/3/library/itertools.html#itertools.chain
[py-list-sort]:               https://docs.python.org/3/library/stdtypes.html#list.sort
[py-set-intersection]:        https://docs.python.org/3/library/stdtypes.html#frozenset.intersection
[py-statistics-median-low]:   https://docs.python.org/3/library/statistics.html#statistics.median_low
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[algo-bfs]:       https://en.wikipedia.org/wiki/Breadth-first_search
[algo-dfs]:       https://en.wikipedia.org/wiki/Depth-first_search
[algo-quicksort]: https://en.wikipedia.org/wiki/Quicksort

[wiki-bingo]:                 https://en.wikipedia.org/wiki/Bingo_(American_version)
[wiki-cartesian-coords]:      https://en.wikipedia.org/wiki/Cartesian_coordinate_system
[wiki-cycle-detection]:       https://en.wikipedia.org/wiki/Cycle_detection
[wiki-dyck-language]:         https://en.wikipedia.org/wiki/Dyck_language
[wiki-floor-ceil]:            https://en.wikipedia.org/wiki/Floor_and_ceiling_functions
[wiki-graph-component]:       https://en.wikipedia.org/wiki/Component_(graph_theory)
[wiki-linear-least-squares]:  https://en.wikipedia.org/wiki/Linear_least_squares
[wiki-linear-time]:           https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-median]:                https://en.wikipedia.org/wiki/Median
[wiki-pushdown-automata]:     https://en.wikipedia.org/wiki/Pushdown_automaton
[wiki-queue]:                 https://en.wikipedia.org/wiki/Queue_(abstract_data_type)
[wiki-seven-segment-display]: https://en.wikipedia.org/wiki/Seven-segment_display
[wiki-stack]:                 https://en.wikipedia.org/wiki/Stack_(abstract_data_type)
[wiki-triangular-number]:     https://en.wikipedia.org/wiki/Triangular_number

[misc-aoc-bingo]:            https://www.reddit.com/r/adventofcode/comments/k3q7tr/
[misc-issue-11]:             https://github.com/mebeim/aoc/issues/11
[misc-cpp-nth-element]:      https://en.cppreference.com/w/cpp/algorithm/nth_element
[misc-cpp-nth-element-so]:   https://stackoverflow.com/q/29145520/3889449
[misc-cpython-median-low]:   https://github.com/python/cpython/blob/ddbab69b6d44085564a9b5022b96b002a52b2f2b/Lib/statistics.py#L549-L568
[misc-median-math-se]:       https://math.stackexchange.com/q/113270
[misc-so-recursive-bfs]:     https://stackoverflow.com/q/2549541/3889449
