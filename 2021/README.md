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
- [Day 13 - Transparent Origami][d13]
- [Day 14 - Extended Polymerization][d14]
- [Day 15 - Chiton][d15]
- [Day 16 - Packet Decoder][d16]
- [Day 17 - Trick Shot][d17]
- [Day 18 - Snailfish][d18]
- Day 19 - Beacon Scanner (TODO)
- [Day 20 - Trench Map][d20]
- [Day 21 - Dirac Dice][d21]
- [Day 22 - Reactor Reboot][d22]
- [Day 23 - Amphipod][d23]
- [Day 24 - Arithmetic Logic Unit][d24]
- [Day 25 - Sea Cucumber][d25]


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
for p in chain(*starmap(horiz, lines)):
    space[p] += 1

overlapping = sum(x > 1 for x in space.values())
print('Part 1:' overlapping)

for p in chain(*starmap(diag, lines)):
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


Day 13 - Transparent Origami
----------------------------

[Problem statement][d13-problem] — [Complete solution][d13-solution] — [Back to top][top]

### Part 1

Today we need to fold a sheet of paper a bunch of times. Interesting. We are
given a list of points in space (i.e. dots of ink on our paper sheet) in the
form `x,y`. Our coordinate system starts from the top-left corner of our paper
sheet, with X coordinates growing right, and Y coordinates growing *down*. After
this, we are given a list of directions of two possible forms:

- `fold along x=XXX` we need to "fold" our paper sheet along the axis `x=XXX`,
  which means folding *up* the bottom half of the sheet.
- `fold along y=YYY` we need to "fold" our paper sheet along the axis `y=YYY`,
  which means folding *left* the right half of the sheet.

Our sheet is transparent, so when folding, if two points end up being on top of
each other we will only see one. For the first part, we only need to perform the
first fold instruction, and then count the number of visible points.

Let's start by building our transparent paper sheet. Since it is transparent
and, as the problem statement says, we need to count any overlapping points as a
single point after folding, we can use a `set` of tuples `(x, y)` to represent
the sheet. This will make it easy to ignore overlaps.

For each line of input, [`.split()`][py-str-split] it in half and turn the two
numbers into a `tuple` of `int` with the help of [`map()`][py-builtin-map].
Then, add the tuple to the set. Since folding instructions are separated from
the list of coordinates by an empty line, when we found one we'll `break` and
stop processing coordinates.

```python
sheet = set()

for line in fin:
    if line == '\n':
        break

    coords = tuple(map(int, line.split(',')))
    sheet.add(coords)
```

Folding our paper sheet is nothing more than a [reflection][wiki-reflection]
along an axis that is only applied to the points past the axis. Since our
reflection axes can only be horizontal or vertical, and since we only need to
reflect points *past* the axis, the operation is quite simple. Reflecting a
point is nothing more than "moving it" as far on the opposite side of the axis
as its original distance from the axis.

- For a vertical reflection with axis `x=A`, the `x` coordinate of a point
  becomes `A - (x - A)` or `2*A - x`.
- For an horizontal reflection with axis `y=A`, the `y` coordinate of a point
  becomes `A - (y - A)` or `2*A - y`.

Let's write a `fold()` function to do this. For simplicity, this function will
take 3 arguments: the sheet, the distance of the reflection axis from the X or Y
axis, and a boolean value to indicate whether we are folding vertically or
horizontally. For each point of the sheet, depending on the folding direction,
we'll move the X or Y coordinate as defined above, add the "moved" point to a
new sheet.

```python
def fold(sheet, axis, vertical=False):
    folded = set()

    for x, y in sheet:
        if vertical:
            if x > axis:
                x = axis - (x - axis)
        elif y > axis:
            y = axis - (y - axis)

        folded.add((x, y))

    return folded
```

Now we can parse the first folding instruction and perform the fold. To only get
one line of input we can either call [`next()`][py-builtin-next] on the input
file or use [`.readline()`][py-io-readline]. The axis coordinate can be
extracted by locating the `=` with [`.index()`][py-str-index], and the folding
direction can be determined by checking whether the instruction contains `'x'`
or not.

```python
line     = next(fin)
axis     = int(line[line.index('=') + 1:])
vertical = 'x' in line
sheet    = fold(sheet, axis, vertical)
n_points = len(sheet)

print('Part 1:', n_points)
```

### Part 2

Predictably enough, now we need to apply *all* folding instructions. The point
visible on the final folded paper sheet will line up to form a sequence of
letters, which is our answer.

We already have all we need for folding... it's only a matter of wrapping it
inside a loop:

```python
for line in fin:
    axis  = int(line[line.index('=') + 1:])
    sheet = fold(sheet, axis, 'x' in line)
```

After applying all folds, we can print out the resulting sheet and read the
letters by hand. After determining the maximum X and Y coordinates for the
points in the sheet, we can use a trivial double `for` loop to iterate over all
the coordinates from `(0, 0)` to the maximum X and Y, printing one `#`
symbol for every point that is present in the sheet, and one space for every
point that is not.

We can use [`max()`][py-builtin-max] along with a generator expression to get
the maximum values for the X and Y coordinates in our `sheet`. Note that we need
to first iterate over Y and then over X to get the sheet printed in the proper
direction!

```python
def print_sheet(sheet):
    maxx = max(p[0] for p in sheet)
    maxy = max(p[1] for p in sheet)

    out = ''
    for y in range(maxy + 1):
        for x in range(maxx + 1):
            out += '#' if (x, y) in sheet else ' '
        out += '\n'

    print(out, end='')
```

We can also use [`itemgetter()`][py-operator-itemgetter] to extract the
coordinates from our points when calculating the minimum and maximum:

```diff
 def print_sheet(sheet):
-    maxx = max(p[0] for p in sheet)
-    maxy = max(p[1] for p in sheet)
+    maxx = max(map(itemgetter(0), sheet))
+    maxy = max(map(itemgetter(1), sheet))
     ...
```

Okay, let's print it!

```python
print('Part 2:')
print_sheet(sheet)
```

```
Part 2:
###   ##  #  # ###  #  # #    #  # #
#  # #  # #  # #  # # #  #    # #  #
#  # #    #### #  # ##   #    ##   #
###  # ## #  # ###  # #  #    # #  #
#    #  # #  # # #  # #  #    # #  #
#     ### #  # #  # #  # #### #  # ####
```

Cool puzzle! Today was also my first day of the year on the leaderboard (rank 37
for P1). Phew, that took some time :')


Day 14 - Extended Polymerization
--------------------------------

[Problem statement][d14-problem] — [Complete solution][d14-solution] — [Back to top][top]

**NOTE**: today's part 1 and 2 can be solved using the same algorithm, however
part 1 is simpler and allows for different, less optimal algorithms to
accomplish the same task. The algorithm implementation here in part 1 is far
from optimal, and in fact unsuitable for part 2. Nonetheless, I've decided to
describe it for educational purposes. You can directly skip to [part 2][d14-p2]
for the actual solution.

### Part 1

For today's problem, we are given a string of letters representing a "polymer
template" where each letter is an element, and a set of reaction rules. Each
rule has the form `AB -> C` meaning that the element `C` should be inserted in
the middle of any [contiguous] pair of elements `AB`. In one "step", all the
rules are applied to the polymer and a new, longer polymer is formed.

The rules are applied simultaneously and do not influence each other nor chain
together. For example, let's say we have the polymer `ABC` and the rules
`AB -> X`, `BC -> Y`, `AX -> Z`. After one step, the new polymer is `AXBYC`.
Notice how the `AX` did not immediately react to create `AZX`, this will only
happen in the *next* step.

After applying the rules and transforming the polymer 10 times, we are asked to
count the number of the most and least common elements and compute their
difference.

The task seems... quite simple. After all, how long can our polymer ever become?
In the puzzle example the polymer `NNCB` after 10 steps has a length of 3073.
Our polymer is 5 times longer... a lowball estimate gives us a length of 15000,
that doesn't seem so bad. We can easily emulate the whole thing with a list. Or,
better, since inserting elements in the middle of a `list` is quite slow, a
[singly linked list][wiki-linked-list]!

> *Narrator voice: «the author later quickly came to the conclusion that this
was a very bad choice...»*

Let's get to work. Python does not have a native linked list object type, but we
can create a `class` for this:

```python
class Node:
    def __init__(self, v, nxt=None):
        self.value = v
        self.next = nxt
```

Now let's parse our first line of input and create a linked list representing
the polymer. For each character in the initial template, we'll create a new
`Node`. Starting with a head node created from the first character, we'll then
iterate over the rest and append the characters to the list:

```python
fin = open(...)
template = fin.readline().rstrip()

head = Node(template[0])
cur  = head

for c in template[1:]:
    cur.next = Node(c)
    cur = cur.next
```

Parsing the reaction rules is just a matter of splitting each line of input on
arrows `->` and storing them in a dictionary with the reactants as keys for easy
lookup. We can [`.rstrip()`][py-str-rstrip] newlines from each line of input
using [`map()`][py-builtin-map] as usual.

```python
rules = {}
next(fin) # skip empty line

for line in map(str.rstrip, fin):
    ab, c = line.split(' -> ')
    rules[ab] = c
```

A single step of reactions can now be performed as follows:

1. Start iterating from the `head` of the linked list.
2. Each iteration, check if `cur.value + cur.next.value` is in the reaction
   `rules`:

   - If so, insert the new element between `cur` and `cur.next`.
   - Otherwise keep going.

3. Stop iterating when we no longer have a `.next` (since we always need two
   elements to react).

```python
for _ in range(10):
    cur = head

    while cur.next:
        nxt = cur.next
        ab  = cur.value + nxt.value

        if ab in rules:
            cur.next = Node(rules[ab], nxt)

        cur = nxt
```

Pretty straightforward. Now we can count the number of elements of each kind
with another loop. We'll use a [`defaultdict`][py-collections-defaultdict] to
make our life easier:

```python
counts = defaultdict(int)

cur = head
while cur:
    counts[cur.value] += 1
    cur = cur.next
```

Finally, to get our answer we just need to find the minimum and maximum counts
using [`min()`][py-builtin-min] and [`max()`][py-builtin-max]:

```python
answer = max(counts.values()) - min(counts.values())
print('Part 1:', answer)
```

### Part 2

For the second part, we still need to do the same thing, but this time we want
***40 steps*** of reactions. In the problem statement we are told that just for
the simple example polymer and rules, after 40 steps the most common element is
`B` with a whopping 2192039569602 occurrences (that's 2 *trillions*)! Needless
to say, we can 100% forget to even store such an insane amount of linked list
nodes in RAM, let alone iterate over it before the
[heat death of the universe][wiki-heat-death-universe]. Sadly, our naïve linked
list solution must be thrown away, we must find a much better one.

We cannot hold the entire polymer in memory... and we are asked about the number
of occurrences of the most and least common elements. Can we get away with just
storing counts of elements? How?

Well, if we only store single element counts, we will completely lose any
information regarding which pairs are present in the polymer. What we can do
however is store counts of *pairs* of elements. After all, whenever a rule
`AB -> C` is applied, *every single pair* of `AB` becomes `ACB`, so in the new
polymer we will have an additional number of `AC` and `CB` pairs equal to the
original number of `AB` pairs before the reaction. Grouping element pairs is a
winning strategy: it requires very little memory and makes calculations an order
of magnitude easier.

Let's start again. This time, for ease of use we will parse the rules into a
different kind of dictionary, where keys are pairs of two characters (the pair
of reactants) and values are pairs of pairs of characters (the two resulting
pairs of products):

```python
rules = {}

for line in map(str.rstrip, fin):
    (a, b), c = line.split(' -> ') # (a, b) here automagically matches 'AB' into ('A', 'B')
    rules[a, b] = ((a, c), (c, b))
```

The initial number of each pair of elements can be calculated with a
`defaultdict` and `for` a loop over the template polymer. The
[`zip()`][py-builtin-zip] built-in comes in handy for iterating over overlapping
pairs of characters:

```python
poly = defaultdict(int)

for pair in zip(template, template[1:]):
    poly[pair] += 1
```

The above can be simplified down to a single line with the help of a
[`Counter`][py-collections-counter] object from the
[`collections`][py-collections] module, which does exactly what we need:

```python
poly = Counter(zip(template, template[1:]))
```

A single step of reactions can now be performed as follows:

- Create a new empty polymer (an empty `defaultdict` of `int`).
- For each pair of elements in the old polymer (i.e. the keys of `poly`):

  - Check if there is a rule for this pair (i.e. reactant):

    - If so, get the products of the rule, and add them to the new polymer as
      many times as the reactant appears in the old polymer (by simply
      incrementing their count).
    - Otherwise, just add the old count of reactant to the new polymer.

Doing the above in a loop `10` times for part 1, and an additional `30` times
for part 2 should give us what we want. Let's write a `react()` function to do
this.

```python
def react(poly, rules, n):
    for _ in range(n):
        newpoly = defaultdict(int)

        for pair in poly:
            products = rules.get(pair)

            if products:
                n = poly[pair]
                newpoly[products[0]] += n
                newpoly[products[1]] += n
            else:
                newpoly[pair] = poly[pair]

        poly = newpoly

    return poly
```

Now for part 1 we can call `react()` with `n=10` to get the final polymer:

```python
poly = react(poly, rules, 10)
```

How can we count the occurrences of each kind of element now? All we have is a
`poly` dictionary of the form `{pair: count}`. All those pairs in there are
overlapping pairs of elements. For example, for `ABCD` we will find `AB BC CD`
in the dictionary. Each character appears *twice* (in two different pairs). We
can therefore iterate over each pair, check the first element kind and get its
count.

```python
counts = defaultdict(int)
for (a, _), n in poly.items():
    counts[a] += n
```

There's a little problem, however: the last element of the polymer (of kind `D`
in the above example) only appears in one pair. Given the way the polymer
reacts, this last element will never move from the tail of the polymer (the same
thing happens for the first element, but we are actually counting it above). We
can just add `1` to the count of elements of its kind to compensate for this. As
you can imagine, this kind of off-by-one problem can be very funny to debug!

```python
counts[template[-1]] += 1
```

Since we need to do this twice anyway, let's incorporate the final counting in
the `react()` function we have and make it directly return the answer.

```python
def react(poly, rules, n, last):
    # ... unchanged ...

    counts = defaultdict(int, {last: 1})
    for (a, _), n in poly.items():
        counts[a] += n

    return poly, max(counts.values()) - min(counts.values())
```

All that's left to do is call our function twice in a row to get the answers for
both parts:

```python
poly, answer1 = react(poly, rules, 10, template[-1])
poly, answer2 = react(poly, rules, 30, template[-1])

print('Part 1:', answer1)
print('Part 2:', answer2)
```


Day 15 - Chiton
---------------

[Problem statement][d15-problem] — [Complete solution][d15-solution] — [Back to top][top]

### Part 1

We are given a grid of digits, each digit representing the "risk level" of a
cell of the grid. We are then told that we want to find a path from the top-left
corner of the grid to the bottom-right corner, only moving up, down, left and
right (not diagonally).

Paths have a total risk level equal to the sum of risk levels of the cells they
enter. Starting with risk level 0 in the top-left cell, each time we "enter" a
cell in our path, we need to add its risk level to the total risk level for the
path. We want to know the lowest possible total risk level for a path that gets
from the entrance (top-left) to the exit (bottom-right), passing through any of
the cells in the grid.

We can think about the grid as a directed graph with as much nodes as there are
cells in the grid, connected between each others just like cells are connected
to their neighboring cells.

What about the edges? Moving from a given cell A to a neighboring cell B (thus
entering B) costs us as much as the risk level of B: we can represent this an
edge from A to B with weight equal to the risk level of B. Analogously, moving
from B to A costs us the risk level of A, which may be different from the risk
level of B, and thus we have another different edge going from B to A with a
weight equal to the risk level of B. In other words, the edges entering a node
have the same weight as the risk level of the cell corresponding to that node.

Do you see consider the following example with a small grid and its
corresponding graph representation (`S` = entrance, `E` = exit):

```none
           SS <-1-- OO <-2-- OO
           SS --2-> OO --1-> OO
           |^       |^       |^
121        5|       3|       6|
536        |1       |2       |1
           v|       v|       v|
           OO --3-> OO --6-> EE
           OO <-5-- OO <-3-- EE
```

The solution to our problem should now be pretty clear: we just want to find the
shortest path from the entrance (`S`) to the exit (`E`). Good ol' Dijkstra comes
to the rescue! We can implement [Dijksta's algorithm][algo-dijkstra] and run it
on our grid.

Before continuing, let's actually read and parse the input into a grid of
integers. This is basically the same thing we did for [day 9][d09], as the input
is in the same format: [`map()`][py-builtin-map] each character on each line of
input into an `int`, and construct a `list` of `lists`s with a
[generator expression][py-generator-expr]:

```python
fin   = open(...)
lines = map(str.rstrip, fin)
grid  = list(list(map(int, row)) for row in lines)
```

The nodes we are going to work with are going to be pairs of coordinates
`(row, col)`. It's clear that we need a function to get the coordinates of the
neighbors of a given cell. Again, we can just borrow the `neighbors4()`
[generator function][py-generator-function] we wrote for [day 9 part 1][d09]:

```python
def neighbors4(r, c, h, w):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        rr, cc = (r + dr, c + dc)
        if 0 <= rr < w and 0 <= cc < h:
            yield rr, cc
```

Similarly to what we did two years ago for [2019 day 6 part 2][2019-d06-p2], we
will implement Dijkstra's algorithm using a [min-heap][wiki-min-heap] as a
[priority queue][wiki-priority-queue] to hold the nodes to visit and always pop
the one with the shortest distance from the source. The [`heapq`][py-heapq]
module is exactly what we need. A `defaultdict` that returns `float('inf')`
(also provided by `math.inf`) as the default value is also useful to treat
not-yet-seen nodes as being infinitely distant (positive floating point infinity
compares greater than any integer).

The algorithm is pretty well-known and also well-explained in the Wikipedia page
I just linked above, so I'm not going into much detail about it, I'll just add
some comments to the code.

```python
import heapq
from collections import defaultdict
from math import inf as INFINITY

def dijkstra(grid):
    h, w = len(grid), len(grid[0])
    source = (0, 0)
    destination = (h - 1, w - 1)

    # Start with only the source in our queue of nodes to visit and in the
    # mindist dictionary, with distance 0.
    queue = [(0, source)]
    mindist = defaultdict(lambda: INFINITY, {source: 0})
    visited = set()

    while queue:
        # Get the node with lowest distance from the queue (and its distance)
        dist, node = heapq.heappop(queue)

        # If we got to the destination, we have our answer.
        if node == destination:
            return dist

        # If we already visited this node, skip it, proceed to the next one.
        if node in visited:
            continue

        # Mark the node as visited.
        visited.add(node)
        r, c = node

        # For each unvisited neighbor of this node...
        for neighbor in neighbors4(r, c, h, w):
            if neighbor in visited:
                continue

            # Calculate the total distance from the source to this neighbor
            # passing through this node.
            nr, nc  = neighbor
            newdist = dist + grid[nr][nc]

            # If the new distance is lower than the minimum distance we have to
            # reach this neighbor, then update its minimum distance and add it
            # to the queue, as we found a "better" path to it.
            if newdist < mindist[neighbor]:
                mindist[neighbor] = newdist
                heapq.heappush(queue, (newdist, neighbor))

    # If we ever empty the queue without entering the node == destination check
    # in the above loop, there is no path from source to destination!
    return INFINITY
```

The `for` loop which iterates over the neighbors skipping already visited ones
can be simplified with a [`filter()`][py-builtin-filter] plus a lambda:

```python
        # ...
        for neighbor in filter(lambda n: n not in visited, neighbors4(r, c, h, w)):
            nr, nc  = neighbor
            newdist = dist + grid[nr][nc]
            # ...
```

Or using [`itertools.filterfalse()`][py-itertools-filterfalse], exploiting the
already existing `.__contains__()` built-in method of the `visited` set:

```python
from itertools import filterfalse
# ...

        # ...
        for neighbor in filterfalse(visited.__contains__, neighbors4(r, c, h, w)):
            nr, nc  = neighbor
            newdist = dist + grid[nr][nc]
            # ...
```

All that's left to do is call the function we just wrote on our grid:

```python
minrisk = dijkstra(grid)
print('Part 1:', minrisk)
```

### Part 2

For this second part the goal does not change... only the grid does. The
*actual* grid is actually five times larger in both dimensions.

The grid we have as input is merely a *tile*, and the actual grid is composed of
5x5 tiles. Our tile repeats to the right and downward, and each time the tile it
repeats, all of its "risk levels" are 1 higher than the tile immediately up or
left of it. If any risk level gets above 9 in the process, it wraps back to 1.

It's only a matter of enlarging our grid and re-running `dijkstra()` on it.
Let's call the tile width and height `tilew` and `tileh` for simplicity:

```python
tilew = len(grid)
tileh = len(grid[0])
```

We'll first expand the grid to the right: for each row of the grid, take the
last `tilew` cells, increment them by 1, and append them to the row. This should
be done a total of 4 times (not 5 since we already have the starting tile).

```python
for _ in range(4):
    for row in grid:
        tail = row[-tilew:] # last tilew elements of the row

        for x in tail:
            if x < 9:
                x += 1
            else:
                x = 1

            row.append(x)
```

The inner `for` loop can be simplified using the [`.extend()`][py-list-extend]
method of lists plus a generator expression and a
[conditional expression][py-cond-expr]:

```python
for _ in range(4):
    for row in grid:
        tail = row[-tilew:]
        row.extend((x + 1) if x < 9 else 1 for x in tail)
```

Now that we have a full row of 5 tiles, we can extend it downwards another 4
times. The code is pretty similar to the above, only that this time we will
build a new row with the generator expression, and then `.append()` that to the
grid.

```python
for _ in range(4):
    for row in grid[-tileh:]:
        row = [(x + 1) if x < 9 else 1 for x in row]
        grid.append(row)
```

And as simple as that, we have our part 2 solution:

```python
minrisk = dijkstra(grid)
print('Part 2:', minrisk)
```

Pretty straightforward problem today; second day of the year where I managed to
get on the global leaderboard, this time for both parts (79th and 62nd), yay!


Day 16 - Packet Decoder
-----------------------

[Problem statement][d16-problem] — [Complete solution][d16-solution] — [Back to top][top]

### Part 1

Today's problem is about binary data parsing. We are given the specifications of
a rather bizarre recursive binary data format, and we need to parse our input
(which is a hexadecimal string representing the data).

The data we are going to parse is composed of packets. Each packet has a header
of 6 bits composed of a 3-bit *version* and a 3-bit *type ID*, plus additional
data depending on the type.

There are two main kinds of packets:

- Type `4` packets, which only contain an integer value. The value is encoded in
  the packet data an unknown number of groups of 5 bits. The most significant
  bit (MSB) of each group tells us if there are any additional groups; the
  remaining 4 bits of each group should be concatenated to form the value.
- Operator packets (any other type), which may contain an arbitrary number of
  nested packets.

Operator packets are encoded as follows:

- The first data bit is a *length type ID* (`ltid`):
- If `ltid=0`, the next 15 bits are an integer that represents the total length
  in bits of the sub-packets contained by this packet.
- Otherwise (`ltid=1`), then the next 11 bits are an integer that represents
  the number of sub-packets contained by this packet.
- The rest of the data are concatenated sub-packets.

Our input data consists of only one very large operator packet, containing a lot
of nested packets. Any leftover bits after parsing this big "root" packet need
to be ignored.

For the first part of today's problem, we need to calculate the sum of the
versions of all packets (including those of sub-packets at any level).

The data structure we need to parse can be parsed in a single pass from start to
finish, keeping track of the current position while parsing. Nested packets are
annoying to deal with, but with the appropriate amount of recursion we can make
our life easier.

Let's define a `Bitstream` [class][py-class] to do the job. It will directly
take a file object as the only argument of its constructor, which will read all
the data in the file and convert it from a hexadecimal string to a binary
string.

We can convert the hexadecimal input string into a [`bytes`][py-bytes] object we
can use [`bytes.fromhex()`][py-bytes-fromhex]. Then, to convert every byte into
a binary string we can use [`str.format()`][py-str-format] with a field
`{:08b}`, which converts an integer into a zero-padded binary string of 8
characters.

```python
class Bitstream:
    def __init__(self, file):
        hexdata = file.read()
        rawdata = bytes.fromhex(hexdata)

        self.pos = 0
        self.bits = ''

        for byte in rawdata:
            self.bits += '{:08b}'.format(byte)
```

We can simplify the loop with the help of [`str.join()`][py-str-join] and
[`map()`][py-builtin-map]:

```python
self.bits = ''.join(map('{:08b}'.format, rawdata))
```

The first method we want to implement is `decode_int()`, which will take a
number `nbits` as parameter, decode an integer of the specified number of bits
from the stream (`self.bits`) starting at the current position (`self.pos`), and
then advance the position. To convert a bit string into an integer we can just
use [`int()`][py-builtin-int] with `base=2`.

```python
def decode_int(self, nbits):
    res = int(self.bits[self.pos:self.pos + nbits], 2)
    self.pos += nbits
    return res
```

Now we can start parsing actual packets. We'll represent packets as 3-element
tuples of the form `(version, tid, data)`. Let's write a `decode_one_packet()`
method to decode a single packet. It will read the packet version and type using
`.decode_int()`, and then decide what to do based on the type:

```python
def decode_one_packet(self):
    version = self.decode_int(3)
    tid     = self.decode_int(3)
    data    = self.decode_packet_data(tid)
    return (version, tid, data)
```

For now, let's assume we already have the `.decode_packet_data()` method above
at our disposal. We will build it from the bottom up, writing simpler methods
first and then composing them.

The data of value packets (`tid=4`) is the easiest to parse: just start reading
integers of 5 bits each and accumulate the 4 least significant bits (using the
binary AND operator `&`), stopping when the most significant bit is `0` (again
extracted using `&`). We can use binary integer constants with the `0b` prefix
to make our life easier.

```python
def decode_value_data(self):
    value = 0
    group = 0b10000

    while group & 0b10000:
        group = self.decode_int(5)
        value <<= 4
        value += group & 0b1111

    return value
```

Now for operator packets' data... the first bit of data is the `ltid`, which
tells us if the next bits need to be interpreted as a *number of packets*
(`ltid=1`) or a *total length* (`ltid=0`).

The first case is straightforward, we can recursively call `decode_one_packet()`
the specified number of times and return a `list` of packets. Let's write a
function that does just that for convenience. A simple
[generator expression][py-generator-expr] is all we need:

```python
def decode_n_packets(self, n):
    return [self.decode_one_packet() for _ in range(n)]
```

For `ltid=0` we have no other choice than to decode one packet at a time until
we reach the specified total length. Let's also write a method for this:

```python
def decode_len_packets(self, length):
    end = self.pos + length
    pkts = []

    while self.pos < end:
        pkts.append(self.decode_one_packet())

    return pkts
```

Now we can easily decode the data contained in operator packets:

```python
def decode_operator_data(self):
    ltid = self.decode_int(1)

    if ltid == 1:
        return self.decode_n_packets(self.decode_int(11))

    return self.decode_len_packets(self.decode_int(15))
```

And finally, we can easily implement `decode_operator_data()` as follows:

```python
def decode_packet_data(self, tid):
    if tid == 4:
        return self.decode_value_data()
    return self.decode_operator_data()
```

We have all we need to parse the entire input into an appropriate data
structure. Once we do so, we can recursively iterate over it to sum all the
packet versions. Let's write a function that does just that. Given how we
structured packets, this is simpler than one might think. We only have two
possible cases:

1. Value packets (`tid == 4`) that don't contain any sub-packet, for these we
   can just return the version.
2. Operator packets (`tid != 4`) that contain sub-packets: iterate over each
   packet and make a recursive call, summing everything up. This can be done in
   a single line with [`sum()`][py-builtin-sum] plus [`map()`][py-builtin-map].

```python
def sum_versions(packet):
    v, tid, data = packet

    if tid == 4:
        return v

    return v + sum(map(sum_versions, data))
```

It's cool to notice that the only piece of code which advances the position of
our `Bitstream` is in `decode_int()` (`self.pos += nbits`). Any other function
is just going to end up calling `decode_int()` somehow!

That's it! A couple of function calls and we are done:

```python
fin    = open(...)
stream = Bitstream(fin)
packet = stream.decode_one_packet()
vsum   = sum_versions(packet)

print('Part 1:', vsum)
```

### Part 2

For the second part, we are given the specifications of all operator packets:

- `tid=0` means "sum": the value of this packet is the sum of the values of all
  its sub-packets.
- `tid=1` means "product": the value of this packet is the product of the values
  of all its sub-packets.
- `tid=2` means "minimum": ... minimum amongst all sub-packets' values.
- `tid=3` means "maximum": ... maximum amongst all sub-packets' values.
- `tid=5` means "greater than": this packet always contains 2 sub-packets and
  its value is `1` if the first sub-packet's value is greater than the second
  sub-packet's value.
- `tid=6` means "less than": ... `1` if 1st sub-packet has lower value than the
  2nd.
- `tid=7` means "equals": ... `1` if 1st sub-packet has equal value to the 2nd.

We need to calculate the value of the "root" packet.

Yet another recursive function! There isn't much to do except follow directions
here. In case of plain value packets (`tid=4`) we'll just return the packet's
value. In all other cases, we'll first make one recursive call per sub-packet to
calculate all sub-packet values, then apply whatever operation is needed on the
values based on the packet type. We have built-ins for everything (`sum()`,
`min()`, `max()`) except the product: we'll use [`math.prod()`][py-math-prod]
for that (Python >= 3.8).

```python
from math import prod

def evaluate(packet):
    _, tid, data = packet

    if tid == 4:
        return data

    values = map(evaluate, data)

    if tid == 0: return sum(values)
    if tid == 1: return prod(values)
    if tid == 2: return min(values)
    if tid == 3: return max(values)

    a, b = values

    if tid == 5: return int(a > b)
    if tid == 6: return int(a < b)
    return int(a == b) # tid == 7
```

That was straightforward. Let's get that second star:

```python
result = evaluate(packet)
print('Part 2:', result)
```


Day 17 - Trick Shot
-------------------

[Problem statement][d17-problem] — [Complete solution][d17-solution] — [Back to top][top]

### Part 1

Cool mathematical problem today. We are working with a slight variation of the
classical [projectile motion][wiki-projectile-motion]. We have a probe living in
the [Cartesian plane][wiki-cartesian-coords] which starts at the origin (0, 0)
and needs to be shot with a certain initial velocity (V<sub>0,x</sub>,
V<sub>0,y</sub>) in order to hit a known target.

All coordinates are integers. The target to hit is a rectangle which is placed
in the 4th quadrant of the Cartesian plane at (positive xs, negative ys). It
spans from x<sub>min</sub> to x<sub>max</sub> horizontally and from
y<sub>min</sub> to y<sub>max</sub> vertically. NOTE that y<sub>min</sub> and
y<sub>max</sub> are lower than 0. This seems to be an assumption that we are
allowed to make, which as we'll see simplifies the problem. We'll
[`assert`][py-assert] it just to be sure.

Let's get input parsing out of the way immediately, it's merely one line of
code. We'll use a [regular expression][misc-regexp] for convenience, with
[`re`][py-re] module. And of course, what would we do without our beloved
[`map()`][py-builtin-map] to convert the matches to `int` right away...

```python
xmin, xmax, ymin, ymax = map(int, re.findall(r'-?\d+', fin.read()))
assert ymin < 0 and ymax < 0
```

The time is also finite, and each instant the probe moves given the following
rules:

- The probe's x position increases by its x velocity.
- The probe's y position increases by its y velocity.
- Due to drag, the probe's x velocity changes by 1 toward the value 0; that is,
  it decreases by 1 if it is greater than 0, increases by 1 if it is less than
  0, or does not change if it is already 0.
- Due to gravity, the probe's y velocity decreases by 1.

The starting velocity (V<sub>0,x</sub>, V<sub>0,y</sub>) is chosen by us, and we
want to determine the highest possible y coordinate that the probe can reach
while still hitting the target afterward.

Here's a visual representation of the problem we are talking about:

```none
 Y ^............#....#............
   |......#..............#........
   |..............................
---O------------------------#-------> X
   |..............................
   |..............................
   |..........................#...
   |..............................
   |...................TTTTTTTTTTT
   |...................TTTTTTTT#TT <-- hit
   |...................TTTTTTTTTTT
```

Of course, we could brute force the solution, but there is actually a smart way
to solve the problem with a single mathematical expression (a
[closed-form expression][wiki-closed-form-expr]) given the input.

If it wasn't for the drag affecting the horizontal speed (V<sub>x</sub>), the
whole thing would be pretty straightforward: a simple parabola, textbook
projectile motion. This second example given in the problem statement makes us
understand the effect of the drag:

```none
 Y ^..............#..#............
   |..........#........#..........
   |..............................
   |.....#..............#.........
   |..............................
   |..............................
---O--------------------#-----------> X
   |..............................
   |..............................
   |..................TTTTTTTTTTTT
   |..................TT#TTTTTTTTT <-- hit
   |..................TTTTTTTTTTTT
```

Let's start reasoning...

First of all, given the way the probe moves, we can agree right away on the fact
that the starting V<sub>x</sub> and V<sub>y</sub> must be positive integers,
otherwise we're never going to hit the target.

Given that both V<sub>0,x</sub> and V<sub>0,y</sub> must be positive, the
behavior of the x and y coordinates of the probe is pretty similar: in both
directions, we have a constant acceleration of A<sub>x</sub> = A<sub>y</sub> =
−1. The only difference is that the x coordinate will stop advancing when
V<sub>x</sub> becomes 0, while the y coordinate will keep moving. Let's tabulate
some example values to get an idea of what is going on:

```none
(x0, y0) = (0, 0); (V0x, V0y) = (5, 0);

|   t |  Vx |   x |  Vy |   y |
+-----+-----+-----+-----+-----+
|   0 |   5 |   0 |   0 |   0 |
|   1 |   4 |   5 |  -1 |   0 |
|   2 |   3 |   9 |  -2 |  -1 |
|   3 |   2 |  12 |  -3 |  -3 |
|   4 |   1 |  14 |  -4 |  -6 |
|   5 |   0 |  15 |  -5 | -10 |
|   6 |   0 |  15 |  -6 | -15 |
|   7 |   0 |  15 |  -7 | -21 |
```

From the above table we can clearly see that V<sub>y</sub>(t) = 0 − t. If we
also consider a generic starting value we have V<sub>y</sub>(t) =
V<sub>0,y</sub> − t. Analogously, we have V<sub>x</sub>(t) = V<sub>0,x</sub> −
t. As per the x and y coordinates... their value at some t is just the sum of
all the *previous* velocities:

- For y, we have: y(t) = sum from n = 0 to t of V<sub>y</sub>(n).
- For x, it's a little different. If we look at which point x stop increasing,
  which is when V<sub>x</sub> = 0, we have x equal to the sum of all the natural
  numbers from V<sub>0,x</sub> to 1. This is a
  [triangular number][wiki-triangular-number]! Remember those? We have x(t) =
  sum from n = 0 to t of n, which is equal to n(n + 1)/2.

We can easily see this second point graphically if we plot a histogram for the
values of V<sub>x</sub>:

```none
Vx ^
   |##
   |## ##
   |## ## ##
   |## ## ## ##
   |## ## ## ## ##
   +-----------------> t
    0  1  2  3  4  5
```

The value of x is exactly the sum of all the previous values of V<sub>x</sub>,
so the area of the above triangle.

Okay, now, about the highest point: when will we reach it? If we start with some
V<sub>0,y</sub> > 0, since we subtract 1 each step, we will inevitably end up
with V<sub>0,y</sub> = 0 after exactly V<sub>0,y</sub> steps, at which point, we
will stop going up and start going down. What would the y coordinate be? Well...
if we think about it for a second, up until the highest point, the y coordinate
is also a triangular number:

```none
y0 = 0; V0x = 5

|  t | Vy |   y |         Vy ^
+----+----+-----+            |##
|  0 |  5 |   0 |            |## ##
|  1 |  4 |   5 |            |## ## ##
|  2 |  3 |   9 |   ==>      |## ## ## ##
|  3 |  2 |  12 |            |## ## ## ## ##
|  4 |  1 |  14 |            +-----------------> t
|  5 |  0 |  15 |             0  1  2  3  4  5
```

We can think about the problem independently for x and y. Let's assume just for
a moment that they are not correlated at all, then we'll add in the correlation.
So, **what if we only had y?**

Given the above, we can draw some very important conclusions:

1. The highest point the probe will reach is always at
   T<sub>hi</sub>=V<sub>0,y</sub> and its height is exactly y =
   V<sub>0,y</sub>(V<sub>0,y</sub> + 1)/2.

2. We obviously want to start with a V<sub>0,y</sub> greater than 0, the higher
   the better, since y directly increases with V<sub>0,y</sub>.

3. After reaching the highest point, the probe will then fall down and always
   reach y=0 in exactly double the time it took to get to the highest point
   (T<sub>zero</sub> = 2T<sub>hi</sub>), and with exactly the opposite value of
   the initial speed: −V<sub>0,y</sub>.

4. At this point (when y=0), if │V<sub>y</sub>│ is greater than
   │y<sub>min</sub>│, it will overshoot the target immediately at the next
   instant of time. The highest possible value for │V<sub>y</sub>│ to not
   overshoot the target is exactly │y<sub>min</sub>│ (i.e. equal to the
   coordinate of the very bottom of the target). Both y<sub>min</sub> and
   V<sub>y</sub> are negative at this point: V<sub>y</sub>(T<sub>zero</sub>) =
   −V<sub>0,y</sub> = y<sub>min</sub>.

5. If V<sub>0,y</sub> = −y<sub>min</sub>, then we know that the will "hit" the
   target (at least with the y coordinate) exactly the instant after
   T<sub>zero</sub>, since at T<sub>zero</sub> we have y=0 and at the next step
   we will have y = 0 −(−y<sub>min</sub>) = y<sub>min</sub>. So T<sub>hi</sub>
   = T<sub>zero</sub> + 1 = 2T<sub>hi</sub> + 1 = 2V<sub>0,y</sub> + 1.

6. Given the above, the maximum height we will ever reach is
   y<sub>min</sub>(y<sub>min</sub> + 1)/2.

Now, all of the above reasoning makes sense alone for the y, but we must also
consider the other coordinate. After all, we are only guaranteed to hit the
target if we do it with *both* coordinates at the same time.

Let's think about it:

7. We know that given an initial V<sub>0,x</sub>, the x coordinate will *stop*
   moving forward and we will start falling *straight down*. When this happens,
   we will be at xstop = V<sub>0,x</sub>(V<sub>0,x</sub> + 1)/2, which is a
   triangular number, and is reached at exactly T<sub>stop</sub> =
   V<sub>0,x</sub>. So we could also say xstop =
   T<sub>stop</sub>(T<sub>stop</sub> + 1)/2.

8. Therefore, if there is a triangular number between x<sub>min</sub> and
   x<sub>max</sub> (the horizontal bounds of the target), and that triangular
   number is generated by a T<sub>stop</sub> value that is lower or equal than
   T<sub>hi</sub>, we are guaranteed to hit the target. This is because we will
   find ourselves falling down right above the target in a horizontal line with
   the right downwards velocity and acceleration, as we figured out in the
   previous paragraph.

**IMPORTANT note**: the existence of a triangular number between x<sub>min</sub>
and x<sub>max</sub> seems to be guaranteed by looking at the inputs for today's
puzzle, however it's still not explicitly stated in the problem statement. It's
an assumption that I decided to make for today's walkthrough just to make it
more entertaining. We can still easily solve the problem if it does not hold.
For this purpose, we'll also include a "generic" part 1 calculation in the code
for part 2 later.

Since this is an assumption that must hold for the above reasoning to make
sense, we'll better `assert` that. We can check this by computing N using the
[inverse triangular number formula][misc-inverse-triangular] for
x<sub>min</sub>, rounding down, and then checking if either the Nth triangular
number is equal to x<sub>min</sub> or the (N+1)th triangular number is less
than or equal to x<sub>max</sub>.

```python
def tri(n):
    return n * (n + 1) // 2

def invtri(x):
    return int((x * 2)**0.5)

assert tri(invtri(xmin)) == xmin or tri(invtri(xmin) + 1) <= xmax, 'No triangular number in [xmin, xmax]'
```

We did our homework. We can now *finally* calculate the solution!

```python
yhi = tri(ymin)
print('Part 1:', yhi)
```

### Part 2

For the second part, we are now told to *count* the number of possible starting
values for the velocity vector (V<sub>0,x</sub>; V<sub>0,y</sub>) which will
cause the probe to hit the target.

Okay. There isn't much we can do here, except maybe an "educated" brute force
search. While for part 1 we can avoid a lot of useless calculations by being
smart, apparently here the choice is between (A) doing plain brute force given
reasonable bounds or (B) somehow finding valid xs (or ys) first, and then
finding valid ys (or xs) based on those, matching the number of steps between
the two.

The second kind of solution, also discussed by multiple people in the
[daily Reddit megathread][d17-reddit-megathread], involves the use of
maps/sets/dictionaries to remember values. The thing is, the search space is so
small that the cost of using a set of complex objects most probably outweighs a
simple double nested `for` scanning all possible values within reasonable
bounds. This is why I've decided to go with the first kind of solution.

Let's define a range to search in (remember that y<sub>min</sub> and
y<sub>max</sub> are both negative):

- The search bounds for V<sub>0,x</sub> are pretty obvious: since
  V<sub>0,x</sub> never goes below 0 and therefore x never decreases, we can be
  sure that starting with V<sub>0,x</sub> < 1 or V<sub>0,x</sub> >
  x<sub>max</sub> is guaranteed to make us fail.

  So 1 ≤ V<sub>0,x</sub> ≤ x<sub>max</sub>.

- As per V<sub>0,y</sub>, any value that is above −y<sub>min</sub> will
  immediately overshoot the target after reaching y=0 (as we discussed in part
  1), so V<sub>0,y</sub> <= −y<sub>min</sub>. The lowest we can shoot is
  V<sub>0,y</sub> = y<sub>min</sub> (i.e. directly hit the target at t=1).
  Anything lower and we'll miss it entirely with our probe going deep down
  towards negative infinity.

  So y<sub>min</sub> ≤ V<sub>0,x</sub> ≤ −y<sub>min</sub>.

All that's left to do is write a double nested loop, and simulate the trajectory
of the probe until we either hit the target or we get too far out and go beyond
it (in either direction, right or down).

To be safer in case part 1's assumption about the existence of a triangular
number between x<sub>min</sub> and x<sub>max</sub>, we can include the
calculation of the maximum y (`yhi` in part 1's code) in this brute force
solution as well.

Here's the function we need:

```python
def search(xmin, xmax, ymin, ymax):
    total = 0
    yhi   = 0

    # For every reasonable (v0x, v0y)
    for v0x in range(1, xmax + 1):
        for v0y in range(ymin, -ymin):
            x, y   = 0, 0
            vx, vy = v0x, v0y

            # While we are not past the target (on either axis)
            while x <= xmax and y >= ymin:
                # If we are inside the target, these v0x and v0y were good
                if x >= xmin and y <= ymax:
                    total += 1
                    break

                # Advance the trajectory following the rules
                x, y = (x + vx, y + vy)
                vy -= 1

                if vx > 0: # vx never goes below 0
                    vx -= 1

                # Update the maximum y found so far if needed
                if y > yhi:
                    yhi = y

    return yhi, total
```

There is one small improvement to make: the lower bound for V<sub>0,x</sub> can
be increased. We can start searching from the first inverse triangular number
that is smaller than x<sub>min</sub>. This is because, again as we discussed in
part 1, we cannot possibly reach the target in enough time without overshooting
it on the y axis if V<sub>0,x</sub> isn't *at least* the inverse of the smallest
triangular number contained between x<sub>min</sub> and x<sub>max</sub>.

```diff
 def search(xmin, xmax, ymin, ymax):
     total = 0
     yhi   = 0

     # For every reasonable (v0x, v0y)
-     for v0x in range(1, xmax + 1):
+     for v0x in range(invtri(xmin), xmax + 1):
         for v0y in range(ymin, -ymin):
     ...
```

Now we can call `search()` and get our solution:

```python
_, total = search(xmin, xmax, ymin, ymax)
print('Part 2:', total)
```

This "bruteforce" took 15 milliseconds on my machine. I'd say I'm satisfied :')


Day 18 - Snailfish
------------------

[Problem statement][d18-problem] — [Complete solution][d18-solution] — [Back to top][top]

### Part 1

Today's problem is quite intricate. We are dealing with nested pairs of numbers.
We are given a list of pairs as input: each pair contains two elements: the
left one and the right one. An element can either be a pair or just a plain
integer. We need to "add" together all the pairs given in our input.

To add two pairs, we need to first concatenate them into a new one: `a + b`
becomes `(a, b)`. After doing this, we need to *simplify the result*. The
simplification to perform is defined as follows:

1. If there is any pair nested inside four parent pairs, it needs to "explode".
   The leftmost such pair "explodes".
2. If there are still pairs that need to explode, go back to step 1 and explode
   them.
3. If any number in the pair (at any depth) is greater than or equal to 10, it
   needs to "split". The leftmost such pair "splits".
4. Go back to step 1 and perform the same actions again. Keep doing this until
   no more explosions nor splits happen.

What does it mean to "explode" a pair? Well, that's... odd:

1. The left number of the pair is added to the first number which appears to the
   left of the exploded pair, *regardless of depth!* If there is no number on
   the left, we just discard the left number.
2. The right number of the pair is added to the first number which appears to
   the right of the exploded pair, *regardless of depth!* If there is no number
   on the right, we just discard the right number.
3. The pair itself becomes `0`.

That *"regardless of depth"* part is what makes this operation quite complex.
Here's an example:

```none
          [1,[[[[2,3],4],5],6]]
                /   \
               /     \
2 added to 1  /       | 3 added to 4
             /        |
            /         |
          [3,[[[  0  ,7],5],6]]
                  ^
                  old pair
```

In the above example, the pair `[2, 3]` explodes because it is nested inside 4
outer pairs. As a result of the explosion, the pair itself is replaced with a
`0`, the `2` is added to the `1` on the left, and the `3` is added to the `4` on
the right. If there was no other number on the left, the `2` would have been
lost, and analogously the `3` would have been lost in case there was no number
on the right.

There are plenty of examples in today's problem statement, so I would advise to
go ahead and check them out if the above is not clear.

As per the "split", this means dividing the number by two and replacing it with
a pair where the left part is the rounded down result of the division, while the
right part is what is the rounded up result:

```
[10,[1,2]] --- split the 10 --> [[5,5],[1,2]]
[13,[1,2]] --- split the 13 --> [[6,7],[1,2]]
```

After performing the addition of all the pairs in our input (in the given order)
we are asked to compute the "magnitude" of the final resulting pair, which is
defined recursively:

- The magnitude of a number is the number itself.
- The magnitude of a pair is double the magnitude of the left part plus triple
  the magnitude of the right part.

It is worth mentioning that our input consists of already simplified pairs.
Therefore, we do not need to simplify them before performing the addition, only
after. We can also observe the following interesting properties of the two
operations:

- The "explode" operation will reduce the maximum depth of the pair by at most
  1, and at least 0. This is because exploding means getting rid of a pair and
  replacing with with `0` (and possibly modifying two other numbers).
- The "split" operation will increase the maximum depth of the pair by at most
  1, and at least 0.

In other words, throughout all the simplification operations, we will never
exceed a maximum nesting level of 4 for any pair.

There are different ways of solving today's problem, using different data
structures and algorithms. I've seen a lot of different approaches in
[today's Reddit megathread][d18-reddit-megathread], here's the three that make
the most sense to me:

1. The simplest, yet probably one of the slowest since we are using Python, is
   to directly operate on the input strings, or parse them into lists of tokens.
   For example turning `"[1,[69,3]]"` into `['[','[',69,3,']',']']` or even into
   `[(1,1),(69,2),(3,2)]` pairing numbers with their depths. Use of regular
   expressions is also an option here.

   The explode operation then becomes a search through the tokens, keeping track
   of the depth level either by counting the `[` and `]` while scanning or by
   having them stored along with the numbers. When a deep enough pair of numbers
   is found, we just pop the pair and then scan left and right to add the popped
   numbers to the first ones we find in either direction. The split operation
   becomes a pop of one element plus an insertion. This is straightforward and
   does not involve any kind of recursion, yet it requires moving back and
   forth, performing additions and removals. Using a linked-list instead of a
   list for storing tokens makes insertion painless.

   Modifying strings was [my original solution][d18-original]... after trying
   too hard to get a cool recursive one working, re-writing it a few times, and
   finally giving up on that to think about it later. It's decent, but nothing
   amazing.

   As seen implemented by:
   [u/jonathan_paulson](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0o2sr/),
   [u/timrprobocom](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0qwi6/),
   [u/yrkbzbo](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp17suu/),
   [u/willsmith28](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp3hnyi/),
   [u/Prudent_Candle](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0w57h/).

2. Slightly more complex: build a binary tree and parse the input pairs as trees
   where each node can either be a number or another node with two children.
   Explosion can be implemented recursively without much effort with parent
   references thinking using this method, and node addition/removal is only a
   matter of updating some "pointers".

   This is a good improvement on just scanning strings/lists of tokens (unless
   those tokens are organized in a linked list, then it's pretty similar), but
   it can be tricky to optimize as the basic operation we are doing is accessing
   class attributes and, yet again, Python can bite us in the back with some
   really bad performance drawbacks. This is probably my least favorite approach
   if I have to be honest, but nonetheless it makes a lot of sense.

   As seen implemented by:
   [u/mockle2](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp27mp6/),
   [u/StripedSunlight](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp3s03a/),
   [u/0b01](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp3lkif/),
   [u/leijurv](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0x7bw/),
   [u/seba_dos1](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp15uum/).

3. Some "smart" recursive solutions treating pairs as *actual pairs* (either
   lists of lists or tuples of tuples). Explosion and splitting can be
   implemented (similarly to the tree-based approach) as depth-first visit of
   the nested pairs. When a pair explodes/splits the nested pair containing it
   are re-constructed bottom-up by propagating the new elements through return
   values.

   The problem here lays in the logic for the explode function. It is definitely
   not trivial. This is the solution I spent a couple of hours trying to
   implement, getting close to make it work, but unsuccessfully. A fun thing
   about this kind of solution is that the code I've seen from other people
   implementing it is really, really similar. The solutions linked here which I
   found in the daily Reddit megathread helped me complete my initially broken
   code.

   As seen implemented by:
   [u/michaelgallagher](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp1zvkp/),
   [u/leijurv](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0x7bw/),
   [u/1vader](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0o32g/),
   [u/xoposhiy](https://www.reddit.com/r/adventofcode/comments/rizw2c/2021_day_18_solutions/hp0qv7k/).

So... as you might have guessed: we're going to implement a cool recursive
solution, with actual pairs (using `tuple`s).

Our input can be parsed into a tuple of tuples by simply replacing open and
close square brackets with parentheses. For these replacements we can use
[`str.maketrans`][py-str-maketrans]. Then, for the actual parsing, we can just be
lazy and let Python handle it for us using [`eval()`][py-builtin-eval]. You
shouldn't normally be using `eval()` in your code if you are doing anything else
that is not a solving programming puzzle for fun.

```python
fin   = open(...)
trans = str.maketrans('[]', '()')
pairs = []

for line in fin:
    pairs.append(eval(line.translate(trans)))
```

The above `for` can also be compressed down to a single line using a
[generator expression][py-generator-expr]:

```python
pairs = tuple(map(lambda line: eval(line.translate(trans)), fin))
```

Our `pairs` will look like this:

```python
(
    (1,2),
    ((1,2),3),
    (9,(8,7)),
    ((1,9),(8,5)),
    ((((1,2),(3,4)),((5,6),(7,8))),9),
    ...
)
```

So each element can either be an actual pair (`(1, 2)`) or a number. A function
to check whether a pair is actually a pair (i.e. a `tuple`) or a number (i.e. an
`int`) will be handy for the next parts:

```python
def is_number(p):
    return type(p) is int
```

Now, for the real problem: let's start from the "explode" operation since it's
the most complex. Anything else will be downhill from here. The way we want to
structure the logic of the function is as follows:

1. Take a pair and a depth as parameters.
2. If the pair is in reality just a number, return it.
3. Otherwise, if we are at a depth of 4, explode it into its left and right
   numbers, then return the extracted numbers along with a zero instead of the
   pair.
4. Otherwise, if we are at a lower depth, make two recursive calls passing an
   incremented depth: one to search for a pair to explode on the left, and then
   one to search for a pair to explode on the right.
5. If none of the two recursive calls find any pair to explode, just return the
   current pair.

To return information back to the caller in the recursive calls, we will need
4 return values: `left_num, mid, right_num, did_explode`:

- In case of a simple number, we return `_, number, _, False`. Nothing exploded,
  the two `_` values are really not important to the caller since nothing
  happened.
- In case of the explosion of a pair, we return `pair[0], 0, pair[1], True`.
  The two split values of the original pair will be propagated to the left and
  right respectively until they can be added to another number.
- In other cases... we'll see.

Here's a skeleton of the code for the above:

```python
def explode(pair, depth=0):
    if is_number(pair):
        return None, pair, None, False

    left, right = pair

    if depth == 4:
        return left, 0, right, True

    left_num, new_left, right_num, did_explode = explode(left, depth + 1)
    # Check results...
    # If did_explode == True then return, no more explosions.

    left_num, new_right, right_num, did_explode = explode(right, depth + 1)
    # Check results...
    # If did_explode == True then return, no more explosions.

    # None of the left and right parts exploded, just return the pair as is.
    return None, pair, None, False
```

How can we reconstruct the pair from the bottom up when returning after one of
the two recursive calls succeeded? We will have to examine both cases.

For the left part:

```python
left_num, new_left, right_num, did_explode = explode(left, depth + 1)
```

In case `did_explode == True`, how can we "move" `left_num` and `right_num`
to the left/right to add them to the correct position? We know we are looking at
the *left* part of some pair. We have two possible cases:

1. `[left, 123]`: the exploded left part of our `pair` has a number on the
   right. We can simply add `right_num` to this number.
2. `[left, [...]]`: the exploded left part of our `pair` has another pair to the
   right (`[...]`). We will need to add `right_num` to the rightmost number that
   we find in this other pair. Keep in mind that this other pair could consist
   of other nested pairs.

In both cases though, we have no idea what's *on the left of `left`* (outside
the current `pair` we are looking at), hence
**we cannot possibly know where `left_num` needs to end up**...
only the calling function has knowledge of this, so we'll have to
return it to the caller! If we were recursively called to explode the *right*
part of a pair, then the caller will know how where to place `left_num`. Indeed,
any `left_num` can only ever be added if there is some number something on the
right (at any level), in which case a right recursive call is made. If no right
recursive call is ever made, `left_num` will simply get returned back to the
first call and be discarded entirely. The same reasoning goes for `right_num` if
no left recursive call is performed.

Interestingly enough, given the way the pairs are structured, there will never
be a case in which both the left and the right number are discarded after an
explosion, because the explosion must have been caused either by a left
recursive call or a right recursive call.

Back to the problem after this short digression. How do we perform the addition
of `right_num` to the leftmost part of whatever is `right`? A simple recursive
function will suffice: this function will take a pair and a number, and add the
number to the leftmost element of the pair.

- If the "pair" is also a number: sum it with the given number and return it.
- Otherwise, recursively perform the addition on the left part of the pair,
  while keeping the right part untouched.

Translated into code:

```python
def add_to_leftmost(pair, num):
    if is_number(pair):
        return pair + num

    left, right = pair
    return (add_to_leftmost(left, num), right)
```

Now we have all we need to write the left recursion step:

```python
def explode(pair, depth=0):
    # ...

    left_num, new_left, right_num, did_explode = explode(left, depth + 1)

    if did_explode:
        new_right = add_to_leftmost(right, right_num)
        new_pair = (new_left, new_right)
        return left_num, new_pair, None, True

    # ...
```

ERR! There is a problem: since we "consume" `right_num` straight away, we are
returning `None` as third element to indicate that to the caller. However, we
ourselves could be "the caller": if we just get a `right_num` that is `None` we
must handle that, because it was already consumed before returning the result to
us. In this case, `new_left` already contains the added right number, since the
explosion took place deeper. We can solve this with a simple check:

```python
def explode(pair, depth=0):
    # ...

    left_num, new_left, right_num, did_explode = explode(left, depth + 1)

    if did_explode:
        if right_num is None:
            # right_num was already added to the leftmost element of new_left,
            # we merely need to propagate the result...
            return left_num, (new_left, right), None, True

        new_right = add_to_leftmost(right, right_num)
        new_pair = (new_left, new_right)

        # left_num always needs to be propagated up as we have no idea where to
        # place it right now...
        return left_num, new_pair, None, True

    # ...
```

The logic for the right recursive call is analogous:

```python
left_num, new_right, right_num, did_explode = explode(right, depth + 1)
```

In case `did_explode == True`, we only know how to handle `left_num` this time,
since adding `right_num` to the right would require knowledge of what's on the
right, which only the caller has. We have two possible cases:

1. `[123, right]`: the exploded right part of our `pair` has a number on the
   left. We can simply add `left_num` to this number.
2. `[[...], right]`: the exploded right part of our `pair` has another pair to
   the left (`[...]`). We will need to add `left_num` to the rightmost number
   that we find on in this other pair. Keep in mind that this other pair could
   consist of other nested pairs.

Here's the counterpart of `add_to_leftmost()` function which does exactly this:

```python
def add_to_rightmost(pair, num):
    if is_number(pair):
        return pair + num

    left, right = pair
    return (left, add_to_rightmost(right, num))
```

The code for the right recursive call is analogous to the one of the left one,
so I'd rather show the complete function instead. Here's the final commented
code:

```python
def explode(pair, depth=0):
    if is_number(pair):
        # Just a number, return as is, no explosion.
        return None, pair, None, False

    left, right = pair

    if depth == 4:
        # Too deep! Explode current pair and replace it with 0.
        return left, 0, right, True

    # Recursively explode on the left.
    left_num, new_left, right_num, did_explode = explode(left, depth + 1)

    if did_explode:
        # Something on the left exploded, stop here, return.

        if right_num is None:
            # right_num was already added to the leftmost element of new_left,
            # we merely need to propagate the result...
            return left_num, (new_left, right), None, True

        # Otherwise, add right_num to the leftmost element of right and then
        # return the new pair.
        new_right = add_to_leftmost(right, right_num)
        new_pair = (new_left, new_right)

        # left_num always needs to be propagated up as we have no idea where to
        # place it right now...
        return left_num, new_pair, None, True

    # Left part didn't explode, recursively explode on the right.
    left_num, new_right, right_num, did_explode = explode(right, depth + 1)

    if did_explode:
        # Something on the right exploded, stop here, return.

        if left_num is None:
            # left_num was already added to the leftmost element of new_right,
            # we merely need to propagate the result...
            return None, (left, new_right), right_num, True

        # Otherwise, add left_num to the rightmost element of left and then
        # return the new pair.
        new_left = add_to_rightmost(left, left_num)
        new_pair = (new_left, new_right)

        # right_num always needs to be propagated up as we have no idea where to
        # place it right now...
        return None, new_pair, right_num, True

    # None of the left and right parts exploded, just return the pair as is.
    return None, pair, None, False
```

That was... as complex to write as it was to explain it.

Let's implement the "splitting" now, again as a recursive function. This is
easy:

1. Take a pair, check if it's a number: if so, check if it's `>= 10`, and in
   such case split it into a pair and return it.
2. Otherwise, perform the split on the left part of the pair: if successful,
   stop here and return the result.
3. Otherwise, perform the split on the right part of the pair and return the
   result.

In order to "stop" and return whenever a split happens, we'll use another
boolean value, exactly as we did for `explode()`. Here's the code:

```python
def split(pair):
    if is_number(pair):
        if pair < 10:
            return pair, False

        left = pair // 2
        return (left, pair - left), True

    left, right = pair
    left, did_split = split(left)

    if not did_split:
        right, did_split = split(right)

    return (left, right), did_split
```

Now we need to perform addition and simplification. According to the rules, to
simplify the result of additions we need to keep exploding and splitting
repeatedly until no more exploding nor splitting is needed. Keep in mind that
exploding has precedence over splitting, so first we have to explode all pairs
from left to right, and only then split. This isn't much of a problem: both our
functions return a boolean value indicating whether the action (explode/split)
succeeded. If so, we will keep going.

```python
def simplify(pair):
    keep_going = True

    while keep_going:
        _, pair, _, keep_going = explode(pair)
        if keep_going:
            continue

        pair, keep_going = split(pair)

    return pair
```

The two values I am ignoring (`_`) from the `explode()` call are simply any
left/right numbers from the exploding pair which did not have any other number
to be added to, and so propagated all the way up to the initial call.

Adding is merely creating a pair from two existing pairs, and then simplifying
the result:

```python
def add(a, b):
    return simplify((a, b))
```

Lastly, we only miss one function to calculate the "magnitude" of a pair: for
numbers, it's simply their value; for pairs, it's 2 times the left magnitude
plus 3 times the right magnitude. Did anybody say recursion again???

```python
def magnitude(pair):
    if is_number(pair):
        return pair

    left, right = pair
    return 3 * magnitude(left) + 2 * magnitude(right)
```

Now we can add up all the pairs in our input, and calculate the "magnitude" of
the final result:

```python
res = pairs[0]

for pair in pairs[1:]:
    res = add(res, pair)

answer = magnitude(res)
```

What we just did is a [*reduction*][wiki-fold] (or *fold*). We have
[`functools.reduce()`][py-functools-reduce] for this:

```python
from functools import reduce

answer = magnitude(reduce(add, pairs))
print('Part 1:', answer)
```

### Part 2

Now we are asked to find the sum of any two pairs in our input which has the
highest possible magnitude. Well, let's just calculate all of them, why not?

```python
best = 0
for a in pairs:
    for b in pairs:
        if a is b:
            continue

        m = magnitude(add(a, b))
        if m > best:
            best = m
```

We can simplify the above *a lot*. First, using
[`itertools.permutations()`][py-itertools-permutations] instead of the boring
nested loops, which also avoids the check `a is b` to avoid summing pairs with
themselves. Since `permutations()` already returns a pair.. we can also
directly call `simplify()` instead of `add()`.

```python
for ab in permutations(pairs, 2):
    m = magnitude(simplify(ab))
    if m > best:
        best = m
```

Finally, a couple of [`map()`][py-builtin-map] plus [`max()`][py-builtin-max]
reduces the above to a single row, which puts the nail in the coffin in terms of
simplification:

```python
best = max(map(magnitude, map(simplify, permutations(pairs, 2))))
print('Part 2:', best)
```

What a day! Can't really say I enjoyed the problem itself that much, but I sure
did enjoy checking out solutions and optimizing mine for this walkthrough. If
you didn't already, you can check it out [here][d18-solution].


Day 20 - Trench Map
-------------------

[Problem statement][d20-problem] — [Complete solution][d20-solution] — [Back to top][top]

### Part 1

For today's puzzle, we need to compute
[image convolutions][wiki-image-convolution]. We are given a first input line
which is exactly 512 characters long and encodes the rules for the convolution,
plus an image as an ASCII-art grid, where each pixel can either be on (`#`) or
off (`.`).

For each pixel in the image, we need to look at the 3x3 region composed of the
pixel itself and its 8 neighbors. From top-left to bottom-right, each of the
cells in this region must be interpreted as a bit to compose a 9-bit number.
This 9-bit number will then be used as an index in the given rules: the new
value of the pixel will be the character at the calculated index in the rules.

The image we are working on extends infinitely in all directions, but we are
given the "center" which contains the only lit pixels. The transformation needs
to be applied *simultaneously* to every pixel of the image, two times in a row.
After doing so, we want to know how many pixels are ON in the final image.

The tricky part of today's puzzle resides in the *first rule*. This rule is
special, as it's ad index `0` and therefore represents the value which OFF
pixels surrounded by 8 other OFF pixels should assume after the transformation.
If this special rule is set to `#`, since our image is infinite, and the outer
space is filled with OFF pixels... this means that after only one iteration of
the transformation, we will have an infinite number of pixels that are ON.

This seems problematic. However, after two transformations all those pixels (ON
with 8 neighbors ON) will follow the last rule (since a 3x3 box of ON pixels
represents `111111111`). The last rule in our input is `.`, therefore all the
infinitely many outside pixels will turn off. In general, on every *odd* number
of transformations we will have infinitely many ON pixels, and on every *even*
number of transformations we will go back to a "normal" scenario with only the
"central" part of the image has pixels that are ON.

If both the first and the last rule are `#` though, we would be in trouble!
Well, at that point the problem wouldn't even make any sense: after the first
iteration, there would be infinite ON pixels, which would never turn off.

Let's parse the input. First the rules: for simplicity we'll convert every `#`
to a `True` and every `.` to a `False`. It's just a matter of converting each
character in the first line of input using a
[generator expression][py-generator-expr] after stripping it:

```python
fin = open(...)
rules = tuple(x == '#' for x in next(fin).rstrip())
```

Since as we said, in order for the problem to make any sense at all, we cannot
possibly have both the first and last rules set to `#`, we might as well
[`assert`][py-assert] that:

```python
assert not (rules[0] and rules[-1]), 'Invalid rules!'
```

Now the image. We are dealing with an expanding grid of pixels, so using a
matrix (e.g. `list` of `list`) is not practical at all, as it would require
either starting with a huge matrix or adding rows/columns as we go. Instead, our
image will simply be a `set` only containing coordinates of the pixels that are
ON. We can use [`enumerate()`][py-builtin-enumerate] in a classical a double
`for` loop to easily get both coordinates and values of the pixels.

```python
next(fin) # skip empty line of input
img = set()

for r, row in enumerate(fin):
    for c, char in enumerate(row):
        if char == '#':
            img.add((r, c))
```

Let's write a function to calculate the next state of a pixel given its
coordinates. It's just a matter of iterating over the 9 possible pixels and
checking if their coordinates are in the image, accumulating the bits into a
variable.

```python
def conv(img, rules, row, col):
    idx = 0

    for r in (row - 1, row, row + 1):
        for c in (col - 1, col, col + 1):
            idx <<= 1
            idx |= ((r, c) in img) # 1 if pixel is on, 0 otherwise

    return rules[idx]
```

Err... there is a problem with the above code. Remember about the first rule? It
turns out that for our input it's `#`... so `rules[0] == True`. We of course
don't want to have infinite pixels in our `img`. The above function however does
not take into account the fact that there could be an infinite number of ON
pixels outside the bounding box of `img`.

How do we fix this? We'll use a flag to remember if the outside pixels are all
ON. If so, when a row or column coordinate gets outside of the image, we need to
consider it as ON.

```python
def conv(img, rules, row, col, minr, maxr, minc, maxc, outside_on):
    idx = 0

    for r in (row - 1, row, row + 1):
        for c in (col - 1, col, col + 1):
            idx <<= 1
            idx |= ((r, c) in img)

            # If all the outside pixels are ON and (r,c) is outside
            # of the image, this pixel is also ON!
            idx |= outside_on and (r < minr or r > maxr or c < minc or c > maxc)

    return rules[idx]
```

To check whether the `(r,c)` coordinates are inside the image we had to pass the
[bounding box][wiki-bounding-box] (`minr, maxr, minc, maxc`) of our image to the
above function. This seems kind of an excessive amount of arguments... we'll
simplify things later.

Let's now define a function to apply one step of the "enhancement"
transformation to the whole image. First, find the bounding box that encloses
all the pixels in the image by simply doing a [`min()`][py-builtin-min] and
[`max()`][py-builtin-max] of both components of the coordinates in the image.
Then, iterate over all pixels and call `conv()` to determine whether each pixel
should become ON or OFF. We'll accumulate new ON pixels in a new set since we
need to apply the transformation simultaneously to all pixels.

```python
def enhance_once(img, rules, outside_on):
    minr, maxr = min(r for r, _ in img), max(r for r, _ in img)
    minc, maxc = min(c for _, c in img), max(c for _, c in img)
    new = set()

    for row in range(minr - 1, maxr + 2):
        for col in range(minc - 1, maxc + 2):
            if conv(img, rules, row, col, minr, maxr, minc, maxc, outside_on):
                new.add((row, col))

    return new
```

Those `- 1` and `+ 2` in the ranges above are because we also need to check the
outside perimeter of the image, as each enhancement iteration could potentially
expand the image by at most 1 pixel in any direction (up, down, left, right).

Okay, pretty nice, but I think it's time to drop that `conv()` function and
simply integrate it into `enhance_once()`... after all, that's the only place we
are ever going to call it from (and also it takes more arguments than I am
comfortable allowing my code to take).

```diff
 def enhance_once(img, rules, outside_on):
     minr, maxr = min(r for r, _ in img), max(r for r, _ in img)
     minc, maxc = min(c for _, c in img), max(c for _, c in img)
     new = set()

     for row in range(minr - 1, maxr + 2):
         for col in range(minc - 1, maxc + 2):
-            if conv(img, rules, row, col, minr, maxr, minc, maxc, outside_on):
+            idx = 0
+
+            for r in (row - 1, row, row + 1):
+                for c in (col - 1, col, col + 1):
+                    idx <<= 1
+                    idx |= ((r, c) in img)
+                    idx |= outside_on and (r < minr or r > maxr or c < minc or c > maxc)
+
+            if rules[idx]:
                 new.add((row, col))

     return new
```

It's only a matter of calling the above function twice now. After that, the
`len()` of our `img` will tell us how many pixels are ON. Remember: after the
first transformation all the outside pixels will turn on if the first rule of
the input is `#`: we need to first pass `outside_on=False`, and then
`outside_on=rules[0]` to account for this.

```python
img  = enhance_once(img, rules, False)
img  = enhance_once(img, rules, rules[0])
n_on = len(img)

print('Part 1:', n_on)
```

### Part 2

For the second part, not much changes. We need to apply the same transformation
50 times now.

Let's create a function that takes care of this for us. At each even step the
outside pixels will all be OFF, while at each odd step they will follow the
first rule.

```python
def enhance(img, rules, steps):
    for i in range(steps):
        img = enhance_once(img, rules, rules[0] and i % 2 == 1)
    return img
```

There is one small problem though: the `enhance_once()` function re-calculates
the bounding box of the entire image every single time. Should we optimize that?
Well, common sense says *"yes, definitely"*, but CPython disagrees. As it turns
out, there seems to be little-to-no difference in performance between
re-calculating the bounding box each step or checking if we exceed that and
updating it as we go with a bunch of `if` statements. At most, I was able to
gain 0.05 seconds. It could make sense to optimize for a larger input, but for
now there is really no incentive in doing so, except making the entire code
annoyingly more complex.

As simple as that, now we can use the above function for both parts:

```python
img  = enhance(img, rules, 2)
n_on = len(img)
print('Part 1:', n_on)

img  = enhance(img, rules, 48)
n_on = len(img)
print('Part 2:', n_on)
```

### Reflections

Today is a sad day for [CPython][wiki-cpython] apparently. My solution runs in
around 2 seconds, which I find kind of annoying. Unfortunately, there isn't much
to optimize in the code, apart from the obvious bounding-box calculation which
as I said does not really represent a performance bottleneck. I believe the
large amount of set insertions and checks is what makes the whole thing as slow
as it is. Using [PyPy][misc-pypy] 7.3.5 gives me a speedup of about 2.55x (780ms
vs 2s). I've fiddled around trying to optimize stuff here and there for a while,
but did not have much luck.

This is also true for other Python solutions I have tested: today's problem was
simple, and solutions are really similar (if you exclude those of people who
just used [SciPy][wiki-scipy] or [NumPy][wiki-numpy] to do everything in two
lines of code). In contrast, any Rust/C++ solution probably takes a few
tens of milliseconds at most. Oh well...


Day 21 - Dirac Dice
-------------------

[Problem statement][d21-problem] — [Complete solution][d21-solution] — [Back to top][top]

### Part 1

Today we need to emulate a 2-player turn-based game:

- Players play on a board with 10 slots numbered from 1 to 10.
- Each turn, a player rolls a die 3 times, sums up the rolled values, and moves
  of that amount of steps, wrapping back to slot 1 after slot 10.
- After rolling and moving, the player's score is incremented by their current
  slot number, and it's the other player's turn to play.

The die the players use is a [100-sided die][wiki-zocchihedron], but has a
peculiar characteristic: it rolls *deterministically*. In particular, it always
rolls the numbers from 1 to 100 in order, cyclically (not really that cool of a
die, to be honest).

The two players are starting from two given slots (our input). Player 1 plays
first, and the first player who reaches a score greater or equal to 1000 wins.
We need to calculate the total number of rolls in the whole game multiplied by
the score of the losing player.

We don't have to put much effort into it, we can just emulate the whole game!
Let's start with the die: we could model it as a
[generator function][py-generator-function] that loops indefinitely and yields
the values from 1 to 100 cyclically, resetting to 1 after 100. Well,
[`itertools.cycle()`][py-itertools-cycle] does exactly this, if we pass the
appropriate `range()` as argument.

```python
>>> die = itertools.cycle(range(1, 101))
>>> next(die)
1
>>> next(die)
2
...
>>> next(die)
100
>>> next(die)
1
```

We can also "cheat" and directly extract the `__next__` method of the generator
without having to deal with calling `next()` every time:

```python
>>> die = itertools.cycle(range(1, 101)).__next__
>>> die()
1
>>> die()
2
```

Perfect, we have our die... what else do we need? Not much really, just a
function which takes the starting positions of the players and emulates the
game:

1. Let the current player play by rolling the die 3 times, moving the player
   position increasing their score.
2. If the score reaches the limit, the player wins: return the total number of
   dice rolls performed and the other player's score.
2. Otherwise switch to the other player and repeat from step 1.

We need to be careful when moving the player positions: game tiles are numbered
from 1 to 10. Each time we increase a player's position we need to then decrease
it in steps of 10 until it reaches a value below 10. To make it easier, we could
use tile numbers from 0 to 9 instead: this way we can simply use the modulus
operator (`%`) to wrap the player's position around after increasing it. When
adding to the total score, we'll simply add the current position *plus 1* to
account for the fact that our tiles are all numbered 1 lower than the original
ones.

```python
from itertools import cycle

def play(p1_pos, p2_pos, score_limit):
    rolls = p1_score = p2_score = 0
    die   = cycle(range(1, 101)).__next__

    while 1:
        p1_pos    = (p1_pos + die() + die() + die()) % 10
        p1_score += p1_pos + 1
        rolls    += 3

        if p1_score >= score_limit:
            return rolls, p2_score

        p2_pos    = (p2_pos + die() + die() + die()) % 10
        p2_score += p2_pos + 1
        rolls    += 3

        if p2_score >= score_limit:
            return rolls, p1_score
```

We are basically only missing input parsing. It's quite simple given the input
format: just [`.split()`][py-str-split] each line and convert the last element
into `int`:

```python
with open(...) as fin:
    p1_pos = int(fin.readline().split()[-1]) - 1
    p2_pos = int(fin.readline().split()[-1]) - 1
```

And finally call the function we just wrote to calculate the answer:

```python
rolls, loser_score = play(p1_pos, p2_pos, 1000)
answer = rolls * loser_score
print('Part 1:', answer)
```

### Part 2

The situation drastically changes because now we use a very different kind of
die: a *"quantum die"*. It's a 3-sided die (faces numbered from 1 to 3), which
splits reality into 3 "parallel universes" every single time we roll it, one
copy for each possible rolling outcome. After the first and only initial game
starts, each dice roll it will "split" into 3 different games. We want to count
the number of universes in which each player wins, this time with a much lower
score limit of 21. Our answer needs to be the highest between the two counts.

Things got really ugly really quickly, but we can do it. Of course, we cannot
possibly simulate *all* those universes one by one. Each time a player plays, it
rolls the die *3 times*, meaning that every single turn we are looking at 3x3x3
= 27 different "alternative universes". If then we take another turn in each of
those, we are looking at 27x27 universes. In general, after N turns we will have
a total of 27<sup>N</sup> possible different universes. If N is 21, that is
1'144'561'273'430'837'494'885'949'696'427, which is... a little bit too large
for us to handle!

The logic behind the solution is quite similar to the one we used for
[day 6 part 2][d06-p2] and also [day 14 part 2][d14-p2]. We cannot advance all
universes one by one, they are too many, but we can *group them* if they are
"similar", and advance groups of universes instead.

How can we find similar universes though? Well, of course, if we somehow know
that two universes will end up making player 1 win... we can consider them as
the same one. Going a bit further, if for any reason any two parallel universes
have the same player positions, scores, and current player turn, they will
inevitably produce the same outcome. Players can have at most 10 different
positions and 21 different scores. Furthermore, the next player to play can
either be player 1 or player 2 at any given time. Therefore, the total number of
different states one game can be in is just *10×10×21×21×2 = 88200*. This
corresponds to the maximum possible number of *different* universes we can have.
That's a much, much more manageable number!

We can solve this in two different ways:

1. Iteratively, keeping a dictionary of states with a count of universes for
   each state. Every step of the game, play all 27 possible dice rolls and for
   each one calculate the new state and increment its count by the count of the
   old state.
2. Recursively through [dynamic programming][wiki-dynamic-programming], making
   good use of [memoization][wiki-memoization].

We are going to implement the second option. My
[original solution][d21-original] for today's part 2 implements the first option
though. and while the code is definitely not that "clean", it's still
comprehensible enough to be easily understood, in case you are curious.

As we said, our game state is defined as the current positions and scores of the
players, plus whether it's the turn of player 1 or player 2. We can represent a
state as a tuple `(my_pos, my_score, other_pos, other_score)`, meaning that the
player who needs to play the next turn is at `my_pos` and has score `my_score`,
while the other one is at `other_pos` and has score `other_score`. The
information about the turn is implicitly stored in our state by the order of the
items: if it's player 1's turn, then `my_pos` and `my_score` will refer to
player 1; otherwise they will refer to player 2.

Our function will take the four values of a state as arguments (so 4 arguments),
and return a tuple `(my_wins, other_wins)`, where `my_wins` will represent the
wins of the player whose position and score are passed as the first two
arguments.

To implement a recursive solution we necessarily need a "base case" to return a
known base result when needed. We know that if a player's score ever gets above
or equal to `21`, then that player wins. Quite simply, in case `my_score >= 21`
we'll return `(1, 0)`, meaning that the current player won this game. In case
`other_score >= 21` we'll return `(0, 1)` instead, meaning that the other player
won.

```python
def play2(my_pos, my_score, other_pos, other_score):
    if my_score >= 21:
        return 1, 0

    if other_score >= 21:
        return 0, 1

    # ...
```

In order to generate all 27 possible values to roll, we *could* use three nested
`for` loops. Since those are always going to be the same 27 values though, we
could simply cache them into a global `list` and iterate over that instead:

```python
QUANTUM_ROLLS = []

for die1 in range(1, 4):
    for die2 in range(1, 4):
        for die3 in range(1, 4):
            QUANTUM_ROLLS.append(die1 + die2 + die3)
```

We can compact the 3 loops into one using
[`itertools.product()`][py-itertools-product], using [`sum()`][py-builtin-sum]
over the 3-element tuples returned by that function:

```python
from itertools import product

QUANTUM_ROLLS = []
for dice in product(range(1, 4), range(1, 4), range(1, 4)):
    QUANTUM_ROLLS.append(sum(dice))
```

And since what we just wrote is nothing more than accumulating elements into a
list, at this point we can make use of [`map()`][py-builtin-map] to
automatically do the job of summing for us:

```python
QUANTUM_ROLLS = tuple(map(sum, product(range(1, 4), range(1, 4), range(1, 4))))
```

In general `itertools.product()` is a pretty cool function, but beware that it's
pretty slow. Using it just once in the whole program to pre-calculate some
values is completely fine, but in general, depending on what you are iterating
over, the performance of `product()` can get pretty bad compared to that of
multiple nested `for` loops.

Okay, let's keep going. We're almost finished, we only need to perform a single
turn for each of the different rolls in `QUANTUM_ROLLS` and recursively call our
function to let the other player play after us. Then, sum the returned numbers
of wins and return the total.


```python
def play2(my_pos, my_score, other_pos, other_score):
    if my_score >= 21:
        return 1, 0

    if other_score >= 21:
        return 0, 1

    my_wins = other_wins = 0

    for roll in QUANTUM_ROLLS:
        # Play one turn calculating the new score with the current roll:
        new_pos   = (my_pos + roll) % 10
        new_score = my_score + new_pos + 1

        # Let the other player play, swapping the arguments:
        ow, mw = play2(other_pos, other_score, new_pos, new_score)

        # Update total wins of each player:
        my_wins    += mw
        other_wins += ow

    return my_wins, other_wins
```

As it's currently written, the above function should do its job. However, there
is one very important detail missing: [memoization][wiki-memoization]! Remember?
The number of parallel universes grows exponentially, each turn they multiply by
27. We still aren't checking if we reached an already known state in any way,
and we definitely need to do that to instantly return the known outcome
associated with that state in case we do, avoiding *a lot* of unnecessary
calculations.

Normally this can be done through the use of a dictionary:

```python
# The cache={} dictionary here is only created once at the time of definition of
# the function! If we do not pass any value to overwrite it, it keeps being the
# same dictionary.
def expensive_function(a, b, c, cache={}):
    state = (a, b, c)

    # If the current state is already known, return the known result:
    if state in cache:
        return state[cache]

    # Otherwise, calculate the result from scratch:
    result = ...

    # Save the result for the current state before returning, so that it can be
    # re-used to avoid the expensive_calculation() later on:
    cache[state] = result
    return result
```

As it turns out, Python has (>= 3.2) has a very cool way of painlessly handling
memoization. All we need is the [`@lru_cache`][py-functools-lru_cache]
[decorator][py-decorator] from the [`functools`][py-functools] module, which
automagically does all of the above for us with a single line of code.
[LRU][wiki-lru-cache] is a caching policy that discards the least recently used
value when too many values are cached. If we don't need to disregard old values,
we can also use the [`@cache`][py-functools-cache] decorator as a shortcut for
`@lru_cache(maxsize=None)`.

We can apply the decorator our function like this:

```python
@lru_cache(maxsize=None)
def play2(my_pos, my_score, other_pos, other_score):
    # ... unchanged ...
```

Beautiful! We have all we need, let's get our part 2 answer:

```python
wins = play2(p1_pos, 0, p2_pos, 0, 21)
best = max(wins)

print('Part 2:', best)
```


Day 22 - Reactor Reboot
-----------------------

[Problem statement][d22-problem] — [Complete solution][d22-solution] — [Back to top][top]

### Part 1

We have a (sort of) geometrical problem to solve. We are given a list of cuboids
identifying regions of 3D space, each of which also has an associated command:
"on" or "off". We are working with a 3D space partitioned in cubes of size 1x1x1
which are initially all "off". Applying an "on" command means turning on all the
unit cubes contained in the cuboid, while applying an "off" command means
turning them off. We need to apply all commands, only focusing on the region of
cubes from -50 to 50 (inclusive) in all 3 directions, and figure out how many
unit cubes will be ON inside this region after all the commands are applied.

Needless to say, the cuboids provided in our input do overlap. This causes a
little bit of a problem: how do we deal with subsequent commands that involve
the same unit cube? There is a simple solution, which given the relatively small
range of -50/+50 will work just fine: keeping track of the state of *all* unit
cubes in the region, applying each command literally, turning ON of OFF all the
cubes involved by the command every time.

To extract coordinates from each line of input we can use a
[regexp][misc-regexp] that matches all sequences of digits optionally preceded
by a minus sign (`-`), converting each match in into an `int` through
[`map`][py-builtin-map].

```python
import re

regexp   = re.compile(r'-?\d+')
commands = []

for line in fin:
    on     = line.startswith('on') # True if the command is "on", False otherwise
    cuboid = tuple(map(int, regexp.findall(line)))
    commands.append((on, cuboid))
```

To keep track of the state of each unit cube we can either use a `set` of
coordinates or a 3D matrix (`list` of `list` of `list`). Using a `set`
simplifies things, as we do not need any initialization and we can only keep
track of ON cubes.

The first thing to check for each command is whether the cuboid in question
touches the -50/+50 region we are interested in. If so, we also need to limit
the range of coordinates of the cuboid in all directions to be inside -50/+50.
For example, if we get the command `on x=-200..200,...` it's clear that we do
not care about most of the range, so we can limit the low `x` to `-50` and the
high `x` to `50`. This can be done by simply applying
[`min()`][py-builtin-min]/[`max()`][py-builtin-max] as needed.

For "on" commands, we'll mark every integer coordinate (corresponding to a
single unit cube) inside the specified cuboid (limited to -50/+50) as ON by
adding it to a `set`. For "off" commands, we'll just discard all interested
coordinates from the set. Doing this, after processing all commands we will be
left with a set only containing the coordinates of unit cubes that are ON.

```python
on_cubes = set()

for on, (x1, x2, y1, y2, z1, z2) in commands:
    if on:
        for x in range(max(x1, -50), min(x2, 50) + 1):
            for y in range(max(y1, -50), min(y2, 50) + 1):
                for z in range(max(z1, -50), min(z2, 50) + 1):
                    on_cubes.add((x, y, z))
    else:
        for x in range(max(x1, -50), min(x2, 50) + 1):
            for y in range(max(y1, -50), min(y2, 50) + 1):
                for z in range(max(z1, -50), min(z2, 50) + 1):
                    on_cubes.discard((x, y, z))
```

To avoid duplicated code we can simplify the above by keeping the method to use
(`.add()` or `.discard()`) in a variable created before the 3 internal `for`
loops:

```python
for on, (x1, x2, y1, y2, z1, z2) in commands:
    method = on_cubes.add if on else on_cubes.discard

    for x in range(max(x1, -50), min(x2, 50) + 1):
        for y in range(max(y1, -50), min(y2, 50) + 1):
            for z in range(max(z1, -50), min(z2, 50) + 1):
                method((x, y, z))
```

The size of the `on_cubes` set will now tell us how many unit cubes are ON in
the end:

```python
n_on = len(on_cubes)
print('Part 1:', n_on)
```

### Part 2

As we could easily expect, we are now asked to work without bounds, considering
all cuboids in their entirety. All coordinates need to be considered.

Whelp! Our part 1 approach just became unfeasible. If we take a look at our
input (or even just at the examples given in the problem statement) we can see
that coordinates in all 3 directions go from around -100000 to around 100000.
This means 200k units for 3 directions which is up to 8×10<sup>15</sup>
different points to keep track of... a little bit too many to fit in memory
(and also to iterate over in a decent amount of time).

As usual, there are different ways to solve today's problem:

1. The most optimal solution in terms of time complexity is probably using
   [segment trees][wiki-segment-tree], however it also the most complex one to
   actually implement. There are other solutions that work just fine given the
   number of commands in our input isn't that large.

2. The simplest solution is to use coordinate compression (no Wikipedia entry
   for this technique unfortunately, but here are two useful links:
   [one][misc-coord-compression-so], [two][misc-coord-compression-quora]).
   Coordinate compression is intuitive and also simple to implement, and indeed
   it's probably what most people implemented at first to solve this problem,
   however, it's pretty bad in terms of both time and space complexity.

   [Here's my solution][d22-alternative] using coordinate compression, which I
   wrote just for fun. It runs in *O(N<sup>3</sup>)* (where *N* is the number of
   commands in the input) and uses around *O((2N)<sup>3</sup>)* space (on my
   machine it requires around 4GB of RAM, sigh).

3. Another possible approach is using an [Octree][wiki-octree] to partition the
   space, but this is unfeasible in terms of space (and probably also time).
   [I did implement this one too][d22-alternative-2], but did not test it that
   much as my implementation requires way too much memory and time, and the
   overhead of my `class`-based approach is quite large. The problem with
   octrees is that in the average case scenario it could actually get as bad as
   the brute-force approach (if not worse), segmenting the 3D space in too many
   unit cubes.

4. Lastly, the "smart" solution involves detecting and somehow handling overlaps
   between cuboids of subsequent commands. This is the solution we are going to
   discuss and implement today.

As I just said, we can solve the problem in a rather simple way if we are smart
enough about the overlaps of the cuboids in different commands, because
obviously this is what everything boils down to: figuring out how to handle
those annoying overlaps to correctly count ON/OFF cubes.

Let's simplify things and see how we could deal with the same problem, but only
in one dimension instead of three: what if our commands acted on segments of a
number line, and we wanted to figure out how many unit segments were ON after
applying all commands?

We will solve the problem by keeping two separate lists: "positive" segments,
which contribute a positive amount (equal to their length) to the final count,
and "negative" segments, which contribute a negative amount instead. Clearly, if
we only had non-overlapping ON commands we could just add all the segments to
the "positive" list, and sum their lengths. In case of overlaps, however, this
would cause double counts. To overcome this issue, whenever we encounter an
overlap we can also add the intersection of the two overlapping segments to the
"negative" list, so that the double-counting gets corrected.

As per OFF commands, the actions to perform are similar. In case of no overlaps
with any existing positive or negative segment, simply ignore the command. In
case of overlaps, any intersection with positive segments needs to be added to
the negative segments, and any intersection with negative segments needs to be
added to the positive segments instead, again to correct for double-counting.

Some visual examples can help us a lot. For simplicity, we'll add 1 to the
second number of each command (the end of the range), in order to be able to
compute the number of unit segments with a simple subtraction later
(`end - start`). Here it is:

```none
           0   1   2   3   4   5
on  0..3   |+++++++++++|
on  2..5           |+++++++++++|
off 1..4       |-----------|
on  1..2       |+++|

result     |+++++++|       |+++|
```

Now let's apply commands one by one and see how to handle them:

1. The first command is straightforward: we just have an ON segment, add it to
   the "positive" list. Positive segments: `0..3`.
2. The second command is trickier, as it overlaps with the first. If we simply
   count it as is, we have 3 more units ON, but we would be counting the segment
   `2..3` twice, so we'll also need to remove it from the count. Positive
   segments: `0..3`, `2..5`; negative segments: `2..3`.
3. The third command is OFF, and it overlaps with both the previous commands.
   Let's try applying it as is by removing all parts of previous ON segments
   that overlap with this one: we have `1..3` and `2..4` to remove. There is a
   problem again though, we are removing `2..3` twice. How could we possibly
   detect and correct this? Well, we have `2..3` in the negative list, so we
   know that it was the result of an earlier ON command overlapping with another
   one. Let's add it back in. Positive segments: `0..3`, `2..5`, `2..3`;
   negative segments: `2..3`, `1..3`, `2..4`. The `2..3` in the positive
   segments was added to prevent double-counting the `2..3` segment as negative.
4. Lastly, for the final ON command the reasoning is the same: if we just add it
   to the positive segments, we could potentially be double-counting. We also
   need to check for any overlap with other positive segments to add the
   intersection to the negative segments, and vice-versa check for any overlap
   with other negative segments and add the intersection to the positive ones.
   The final result is positive segments: `0..3`, `2..5`, `2..3`, `1..2`,
   `1..2`; negative segments: `2..3`, `1..3`, `2..4`, `1..2`. The second
   occurrence of `1..2` in the positive segments is a result of the intersection
   with the negative `1..3`, while the only occurrence of `1..2` in the negative
   segments is a result of the intersection with positive segment `0..3`. Both
   of these prevent double-counting (positively or negatively).

If we now take a look at our "positive" and "negative" lists, we can see that
adding together the lengths of positive segments and subtracting the lengths of
the negative segments we end up with *3+3+1+1+1-1-2-2-1 = 3*, which is exactly
the final number of ON unit segments we are left with.

The advantage of the above method is that it works with any number of
dimensions, as long as we are able to correctly detect overlaps and calculate
intersections. The intersection of two segments is straightforward: we take the
maximum of the two starting points as starting point and the minimum of the two
ending as ending point; if the calculated starting point is greater or equal to
the ending point, it means there is no intersection so we can just discard it.
In 3D it's pretty much the same, the only difference is that we need to do these
calculations and checks for all 3 dimensions.

With the above said, here's a function to calculate the intersection of two
cuboids given their starting and ending coordinates as tuples of 6 numbers:

```python
def intersection(a, b):
    ax1, ax2, ay1, ay2, az1, az2 = a
    bx1, bx2, by1, by2, bz1, bz2 = b

    ix1, ix2 = max(ax1, bx1), min(ax2, bx2)
    iy1, iy2 = max(ay1, by1), min(ay2, by2)
    iz1, iz2 = max(az1, bz1), min(az2, bz2)

    if ix1 < ix2 and iy1 < iy2 and iz1 < iz2:
        return ix1, ix2, iy1, iy2, iz1, iz2

    return None # there's no intersection if we get here
```

Now, using the `commands` list we created in part 1, which holds pairs of the
form `(on, (x1, x2, y1, ...))`, we can apply the steps we just described in the
previous paragraphs:

```python
positive = []
negative = []

for on, cuboid in commands:
    new_negative = []

    for other in positive:
        inter = intersection(cuboid, other)
        if inter is None:
            continue

        new_negative.append(inter)

    for other in negative:
        inter = intersection(cuboid, other)
        if inter is None:
            continue

        positive.append(inter)

    negative.extend(new_negative)

    if on:
        positive.append(cuboid)
```

The `new_negative` temporary list used above is to avoid adding intersections to
the `negative` list before we iterate over it with `for other in negative`, as
that would mean counting them twice
([thanks @atkinew0 for pointing this out][misc-issue-14]). Now all that's left
to do is sum up the volumes of all `positive` cuboids and then subtract the
volumes of all `negative` cuboids. We can write a function to calculate the
volume of a given cuboid:

```python
def volume(x1, x2, y1, y2, z1, z2):
    return (x2 - x1 + 1) * (y2 - y1 + 1) * (z2 - z1 + 1)
```

Using a couple of [generator expressions][py-generator-expr] along with
[`sum()`][py-builtin-sum] and [`starmap()`][py-itertools-starmap] (since the
`volume()` function we wrote takes 6 arguments and our cuboids are tuples of 6
values) the final calculation is just a single line of code:

```python
from itertools import starmap

total = sum(starmap(volume, positive)) - sum(starmap(volume, negative))
```

We ahve the answer we were looking for, however there is one significant
optimization that can be made. As we saw with the pretty small example on 1D
segments, it's quite common to end up calculating the same intersection more
than once. Since we are iterating over the entire list of negative and positive
cuboids for every new command, we can potentially end up with *O(N<sup>2</sup>)*
cuboids in our lists, with a lot of duplicates.

To make everything work faster, we can batch together operations that concern
already seen cuboids, using a dictionary of the form `{cuboid: count}` instead
of two lists. Whenever an intersection occurs between the current cuboid and
another one already present in the dictionary, we can then increment (or
decrement) the count of the intersection as much as the count of the existing
cuboid (since we are intersecting multiple copies of that same cuboid). Whether
to decrement or not is determined by the sign of the existing cuboid's count: if
positive, we decrement; if negative, we increment. In other words, just subtract
the count (regardless of its sign) every time.

We can use a [`defaultdict()`][py-collections-defaultdict] of `int` to make it
painless to add new entries with a default count of `0`. The only thing we need
to be careful about is iterating over old cuboids: we basically want to modify
the dictionary while iterating on its keys, which is not a good idea (and also
not possible, we would get a `RuntimeError`). We only need to iterate over
previously existing cuboids though, so we can take the
[`.items()`][py-dict-items] in the dictionary and turn them into an immutable
`tuple` before iterating.

Here's the updated code:

```python
from collections import defaultdict

counts = defaultdict(int)

for on, cuboid in commands:
    for other, count in tuple(counts.items()):
        inter = intersection(cuboid, other)
        if inter is None:
            continue

        counts[inter] -= count

    if on:
        counts[cuboid] += 1
```

The final calculation now becomes a sum of products `volume * count` for each
unique cuboid in the dictionary:

```python
total = sum(n * volume(*cuboid) for cuboid, n in counts.items())
print('Part 2:', total)
```

We can also use this code to calculate the answer for part 1, by writing another
function that only calculates the volume of cuboids that have coordinates in the
-50/+50 range, using the same `min()`/`max()` approach we used for part 1 to
limit the coordinates:

```python
def volume_small(x1, x2, y1, y2, z1, z2):
    if x1 > 50 or y1 > 50 or z1 > 50 or x2 < -50 or y2 < -50 or z2 < -50:
        return 0

    x1, x2 = max(x1, -50), min(x2, 50)
    y1, y2 = max(y1, -50), min(y2, 50)
    z1, z2 = max(z1, -50), min(z2, 50)

    return volume(x1, x2, y1, y2, z1, z2)
```

The final calculation for both parts now becomes:

```python
total = total_small = 0

for cuboid, n in counts.items():
    total       += n * volume(*cuboid)
    total_small += n * volume_small(*cuboid)

print('Part 1:', total_small)
print('Part 2:', total)
```

Day 23 - Amphipod
-----------------

[Problem statement][d23-problem] — [Complete solution][d23-solution] — [Back to top][top]

### Part 1

Today we're dealing with an [NP-complete][wiki-np-complete] problem, woah. We
are given a very small ASCII-art grid representing an hallway plus four rooms
which all contain two objects. There are four different kinds of objects
(letters from `A` to `D`), and two of each kind. Each kind of object should go
in its corresponding room (`A`s in the first, `B`s in the second, etc), but they
are initially misplaced into different rooms.

Each kind of object also has a different associated cost to be moved from one
cell to an adjacent one. Our task is to move these objects around, one at a
time, in order to get them all into the correct rooms with the lowest possible
total "cost", which is the answer we are looking for. There are some rules
though:

1. The only two moves that an object can make are either going from the room to
   a cell of the hallway (except cells that are *right above* rooms) or move
   from the hallway to *its assigned room*.
2. Once in the hallway, the object cannot be moved anywhere else other than its
   assigned room, and only if that room is either empty or only contains objects
   of the correct kind.
3. If an object finds itself in its assigned room alone or with other objects of
   the same kind, it cannot move from there anymore.

This problem seems like a variation to the very famous
[Tower of Hanoi][wiki-tower-of-hanoi] game. It's also "similar" to the one given
on [2019 day 18][2019-d18], meaning that it can be solved using the same
algorithm. As I said at the very beginning, we seem to be dealing with an
NP-complete problem: this means that the only way to solve it is to actually
"try" all possible moves until we find the sequence of moves that gets to the
solution with the lowest total cost.

First of all, we need to abstract away all the details and find a decent way to
represent the problem. What we are essentially doing is just moving around
objects from some container to another. We have 4 rooms and one hallway, which
can all be modeled as simple `tuple`s. Furthermore, since our hallway does not
allow placing objects in all its cells, we can simply ignore those for now.

We'll turn our map into 5 total tuples, of which one is the hallway. Since
objects from `A` to `D` respectively go to rooms 0 to 3 and have moving cost
from 10<sup>0</sup> (1) to 10<sup>3</sup> (1000), it's convenient to *translate
the objects `ABCD` into the integers `0`, `1`, `2`, `3`*.

Here's what the data structures we are going to use will look like given an
example map (the `x` are only there to mark illegal spots of the hallway):

```none
#############
#..x.x.x.x..# --> hallway: (None, None, None, None, None, None, None) (7 slots)
###B#C#B#D### --> rooms  : ((1, 0), (2, 3), (1, 2), (3, 0))
  #A#D#C#A#
  #########
```

When a solution is reached (regardless of total cost), we will be in the
following situation:

```none
#############
#..x.x.x.x..# --> hallway: (None, None, None, None, None, None, None)
###A#B#C#D### --> rooms  : ((0, 0), (1, 1), (2, 2), (3, 3))
  #A#B#C#D#
  #########
```

We're going to write a recursive function which explores all the possible
solutions in a [depth-first][algo-dfs] manner. Given the current state of the
game, we'll figure out every possible next move to make, try making it, and
check with a recursive call how good that choice was. A "move" here is the
movement of one of the objects from a room to a free spot in the hallway or from
the hallway to the correct room. It's important to remember that objects cannot
pass through each other, so if there's one blocking the hallway, other objects
cannot get past it until it moves.

Given the above representation of the state of the game, let's start writing
some functions to generate all possible moves given the current state. A move
will simply consist of a cost and a new state after the move.

First, moves that move objects from the hallway to a room: scan the hallway for
objects, and for each object:

1. Check if its corresponding room is only occupied by objects of the same kind.
2. If so, check if the path through the hallway from this object's position to
   the room is clear (no other objects in the way).
3. If so, calculate the cost of the move, and generate a new game state where
   the object has been removed from the hallway and inserted in the room.

We'll implement the above as a [generator function][py-generator-function]. The
[`enumerate()`][py-builtin-enumerate] built-in makes it convenient to iterate
over both indexes and objects in the hallway, while the
[`any()`][py-builtin-any] built-in is useful to concisely check whether a room
only contains objects of the right kind. Remember that according to our model,
objects are numbered from `0` to `3`, and their number also corresponds to the
index of the correct room they belong to in the tuple of rooms.

Here's a commented version of the code:

```python
from math import inf as INFINITY

def moves_to_room(rooms, hallway):
    # For any object in the hallway...
    for h, obj in enumerate(hallway):
        # Skip empty hallway spots.
        if obj is None:
            continue

        # Check the corresponding room: if it contains any other kind of object,
        # skip it, can't move this obj there yet.
        room = rooms[obj]
        if any(o != obj for o in room):
            continue

        # Calculate the cost of moving this object from this hallway spot
        # to its room.
        cost = move_cost(...)

        # If it's impossible to move the object to the room (i.e. there is some
        # other object in the way from this spot to the room), skip it.
        if cost == INFINITY:
            continue

        # Create a new state where this object has been moved from slot h of the
        # hallway to its room, and yield it along with the cost.
        new_rooms   = rooms[:obj] + ((obj,) + room,) + rooms[obj + 1:]
        new_hallway = hallway[:h] + (None,) + hallway[h + 1:]
        yield cost, (new_rooms, new_hallway)
```

The `move_cost()` function used above is something that we'll need to define
later. For now we'll just assume it will return an integer cost in case it is
possible to do the move and `INFINITY` otherwise.

Let's think about the "opposite" of the above function now: it will be a pretty
similar generator function which goes through all the possible moves from any
room to any free hallway spot, one at a time, and yields their cost plus the
corresponding next game state.

We'll have to scan each room, skipping those that are filled with objects of the
right kind (which cannot be moved anymore). Then, for each such room, and for
each hallway spot:

1. Check if the path through the hallway from this object's current room to the
   free hallway spot we found is clear (no other objects in the way).
2. If so, calculate the cost of the move, and generate a new game state where
   the object has been removed from the room and inserted in the hallway.

Again, here's the commented code:

```python
def moves_to_hallway(rooms, hallway):
    # For any room...
    for r, room in enumerate(rooms):
        # If the room we are looking at only contains the right objects,
        # those objects will not move from there, skip them.
        if all(o == r for o in room):
            continue

        # For any hallway spot...
        for h in range(len(hallway)):
            # Calculate the cost of moving this object from this room to this
            # hallway spot (h).
            cost = move_cost(...)

            # If it's impossible to move the object to this hallway spot (i.e.
            # there is some other object in the way), skip it.
            if cost == INFINITY:
                continue

            # Create a new state where this object has been moved from room r to
            # slot h of the hallway, and yield it along with the cost.
            new_rooms   = rooms[:r] + (room[1:],) + rooms[r + 1:]
            new_hallway = hallway[:h] + (room[0],) + hallway[h + 1:]
            yield cost, (new_rooms, new_hallway)
```

We can group the above two functions into a single one that given a state will
generate ALL possible moves to any next valid state. We can do this easily with
[`yield from`][py-yield-from]:

```python
def possible_moves(rooms, hallway):
    yield from moves_to_room(rooms, hallway)
    yield from moves_to_hallway(rooms, hallway)
```

It's worth noting that *whenever we can move an object from the hallway into its
room, that move will always be optimal*. Doing it as soon as we can or
postponing it later does not change the final cost. However, if we always
perform optimal moves right away when possible and ignore the other moves, we
can avoid wasting time trying other solutions that we already know can only
either cost the same (at best) or more (in the worst case), but never less.

To translate this into code: whenever our `moves_to_room()` generators yields at
least one possible move, we should `yield` the first one only, without wasting
time checking other moves. We can do this by calling [`next()`][py-builtin-next]
once, and then only `yield` other moves in case we receive a
[`StopIteration`][py-stopiteration] (i.e. no moves to rooms are available).

```python
def possible_moves(rooms, hallway):
    try:
        yield next(moves_to_room(rooms, hallway))
    except StopIteration:
        yield from moves_to_hallway(rooms, hallway)
```

Ok, now we can write the `move_cost()` function, which is probably the most
complex, due to the simplified nature of our state (rooms and hallways). We are
using a "compressed" hallway which is missing the illegal spots, so the
situation is the following:

```none
hallway spots:  0 | 1 | 2 | 3 | 4 | 5 | 6
                      ^   ^   ^   ^
rooms:                0   1   2   3
```

The first thing to do is check whether the path is clear or not. I will spare
anyone reading a pretty boring explanation, but long story short: some annoying
calculation using the two indexes (room index and hallway index) is needed. Once
we have a `start` and `end` position to move from/to in the hallway, we can
check if `hallway[start:end]` only contains empty spots (`None`) and if so
proceed.

The simplest way to keep track of the distance from each room to each hallway
step is to use a map (in our case a matrix made as a tuple of tuples), which can
then be indexed by the room index and the hallway index to get the number of
steps.

```python
ROOM_DISTANCE = (
    (2, 1, 1, 3, 5, 7, 8), # from/to room 0
    (4, 3, 1, 1, 3, 5, 6), # from/to room 1
    (6, 5, 3, 1, 1, 3, 4), # from/to room 2
    (8, 7, 5, 3, 1, 1, 2), # from/to room 3
)
```

Additionally, the number of steps needed to move in/out of a room varies
depending on how many objects are in the room. For example, if we are moving one
out while there are two, it will take only one move to move the top one out, and
it will take two moves to move the second one out later. In any case, the cost
of moving object N one step is 10<sup>N</sup>, so we'll multiply every distance
by the apprpriate power of 10 to get the cost.

Here's the complete code:

```python
def move_cost(room, hallway, r, h, to_room=False):
    # Here h is the hallway spot index and r the room index.

    if r + 1 < h:
        start = r + 2
        end   = h + (not to_room)
    else:
        start = h + to_room
        end   = r + 2

    # Ceck if hallway path is clear.
    if any(x is not None for x in hallway[start:end]):
        return INFINITY

    # If moving to the room, the obj is in the hallway at spot h,
    # otherwise it's the first in the room.
    obj = hallway[h] if to_room else room[0]

    return 10**obj * (ROOM_DISTANCE[r][h] + (to_room + 2 - len(room)))
```

The last utility function we'll need is one that will be able to tell us whether
we reached a final state (every object in the correct room) or not. This is just
a matter of checking if every room only contains two objects and those objects
are also equal to the room index.

```python
def done(rooms):
    for r, room in enumerate(rooms):
        if len(room) != 2 or any(obj != r for obj in room):
            return False
    return True
```

Now we can write the *real* funciton to solve all of this. Given the helpers we
just wrote, the task is straightforward:

1. Check if the current state is `done()`: if so, the cost to reach the final
   state is `0`, so `return 0`.
2. Otherwise, for each possible move, calculate the next state and make a
   recursive call to try and find the best solution from that state.
3. If that solution is better than our previous one, keep it as new best and
   keep checking.

```python
def solve(rooms, hallway):
    if done(rooms):
        return 0

    best = INFINITY

    for cost, next_state in possible_moves(rooms, hallway):
        cost += solve(*next_state)

        if cost < best:
            best = cost

    return best
```

There are *a lot* of different ways to end a game with the correct
configuration, but only one has the minimum cost. The number of different ways
to get to the end is probably really large, and it's unfeasible to explore the
complete tree of possible moves. This means that our `solve()` function, as it's
currently written, will take forever to finish. *However*, we know that if we
ever reach the same state (same `rooms` and same `hallway` state), the minimum
cost to reach the end will always be the same, no matter what moves were played
before that. We can therefore [memoize][wiki-memoization] the results of our
function to avoid unnecessary calculations if we ever reach the same state
twice, just like we did for [day 21 part 2][d21-p2]. It's merely a matter of
using the magic [`lru_cache`][py-functools-lru_cache] decorator:

```diff
+@lru_cache(maxsize=None)
 def solve(rooms, hallway, room_size):
     ...
```

We left input parsing as the last thing to do, and indeed today's input is kind
of annoying to parse to be honest. We're already assuming an hallway with 7 free
spots (see hardcoded values in the `ROOM_DISTANCE` dictionary), let's just
assume only four rooms are present. We can convert an object `ABCD` to its
corresponding number `0123` with a little trick using `'ABCD'.index(object)`.
Skipping the hallway, we have two lines of four objects per line (one per room).
After getting those and translating them into numbers, we'll need to "transpose"
them from 2 iterables of 4 elements to 4 tuples of 2 elements, using
[`zip()`][py-builtin-zip] plus an [unpacking operator][py-unpacking].

```python
def parse_rooms(fin):
    next(fin)
    next(fin)
    rooms = []

    for _ in range(2):
        l = next(fin)
        rooms.append(map('ABCD'.index, (l[3], l[5], l[7], l[9])))

    return tuple(zip(*rooms))
```

Finally, we can parse the input and pass it to `solve()` to get the answer:

```python
fin      = open(...)
hallway  = (None,) * 7
rooms    = parse_rooms(fin)
min_cost = solve(rooms, hallway)

print('Part 1:', min_cost)
```

### Part 2

Now the total number of objects doubles: we have 16 objects, 4 per kind, and the
rooms can hold 4 objects. The task is unchanged: find the minimum cost to
complete the puzzle and reach a state where each room contains all 4
corresponding objects.

Given the way we have written our code for part 1, adapting it to part 2 is a
walk in the park. We'll make it more general by adding a `room_size` parameter
and passing it around where needed. In reality, the only places where we'll
actually need it is when calculating the cost of moving in or out of a room in
`move_cost()` and when determining if we are finished in `done()`, but we'll
have to get the parameter there propagating it through all the function calls.

Here are the needed modifications (basically just adding the `room_size`
parameter and propagating it everywhere):

```diff
-def move_cost(room, hallway, r, h, to_room=False):
+def move_cost(room, hallway, r, h, room_size, to_room=False):
     ...
-    return 10**obj * (ROOM_DISTANCE[r][h] + (to_room + 2 - len(room)))
+    return 10**obj * (ROOM_DISTANCE[r][h] + (to_room + room_size - len(room)))

-def moves_to_room(rooms, hallway):
+def moves_to_room(rooms, hallway, room_size):
     ...
-        cost = move_cost(room, hallway, obj, h, to_room=True)
+        cost = move_cost(room, hallway, obj, h, room_size, to_room=True)
     ...

-def moves_to_hallway(rooms, hallway):
+def moves_to_hallway(rooms, hallway, room_size):
     ...
-            cost = move_cost(room, hallway, r, h)
+            cost = move_cost(room, hallway, r, h, room_size)

-def possible_moves(rooms, hallway):
+def possible_moves(rooms, hallway, room_size):
     try:
-        yield next(moves_to_room(rooms, hallway))
+        yield next(moves_to_room(rooms, hallway, room_size))
     except StopIteration:
-        yield from moves_to_hallway(rooms, hallway)
+        yield from moves_to_hallway(rooms, hallway, room_size)

-def done(rooms):
+def done(rooms, room_size):
    for r, room in enumerate(rooms):
-        if len(room) != 2 or any(obj != r for obj in room):
+        if len(room) != room_size or any(obj != r for obj in room):
            return False
    return True

@lru_cache(maxsize=None)
-def solve(rooms, hallway):
-    if done(rooms):
+def solve(rooms, hallway, room_size=2):
+    if done(rooms, room_size):
        return 0

    best = INFINITY

-    for cost, next_state in possible_moves(rooms, hallway):
-        cost += solve(*next_state)
+    for cost, next_state in possible_moves(rooms, hallway, room_size):
+        cost += solve(*next_state, room_size)

        if cost < best:
            best = cost
```

The code for part 1 remains unchanged. For part 2 we only need to add the four
new objects given in the problem statement:

```python

newobjs  = [(3, 3), (2, 1), (1, 0), (0, 2)]
newrooms = []

for room, new in zip(rooms, newobjs):
    newrooms.append((room[0], *new, room[-1]))

rooms    = tuple(newrooms)
min_cost = solve(rooms, hallway, len(rooms[0]))

print('Part 2:', min_cost)
```


Day 24 - Arithmetic Logic Unit
------------------------------

[Problem statement][d24-problem] — [Complete solution][d24-solution] — [Back to top][top]

### Part 1

Do you like reverse engineering? Hope you do. Today is reverse engineering day!

We are given an assembly program as input. This program runs on a custom machine
whose CPU has 4 registers named `x`, `y`, `z` and `w`. There are 6 different
opcodes available:

- `inp DST`: takes a number as input and store it in register `DST`.
- `add DST SRC`: store the value of `DST + SRC` into `DST`. In this case `SRC`
  can either be another register name or an immediate integer value (positive or
  negative).
- `mul DST SRC`: same as `add`... `DST := DST * SRC`.
- `div DST SRC`: `DST := DST / SRC` (integer division).
- `mod DST SRC`: `DST := DST % SRC` (integer modulus).
- `eql DST SRC`: `DST := 1` if `DST == SRC`, else `DST := 0`.

Our program has exactly 14 `inp` instructions, and each of them should take a
digit between 1 and 9 (inclusive) as input. The program will then tell us if
the 14-digit number we entered one digit at a time is valid or not, by running
to its end and leaving a result in the `z` register. If `z` is `0` at the end of
the run, the number was valid.

We want to know the highest possible 14-digit number accepted by the machine.

The problem is not trivial: it is not enough to simply implement the CPU as
specified and emulate the execution of the program. There are too many
possibilities to guess, and testing them all would take ages. It's also not
possible to do any kind of binary search, as there could be multiple "local"
solutions in the input range.

There are three main approaches for solving the problem:

1. Manually look at the program code and figure out which constraints are being
   checked on the input. Then, we can either fully solve them by hand, or write
   a program to do so.
2. Do an exhaustive depth-first search of the solution (from highest to lowest),
   [memoizing][wiki-memoization] the intermediate states of the CPU (registers
   and current input digit) at each `inp` instruction. This will run pretty
   slowly, but it's still doable as the set of possible states for the CPU is
   not too large.
3. Implement the CPU instructions and determine the input constraints through
   [symbolic execution][wiki-symbolic-execution]. This can be done through the
   use of a [SMT solver][wiki-smt], and is exactly what I did for my
   [original solution][d24-original] (with some more smart simplifications
   first). Take a look at [this comment of mine][d24-reddit-comment] on today's
   Reddit megathread to know more. This does not require understanding what the
   code does *at all*, and it's most likely the quickest option to implement,
   however it is still pretty slow.

I'm going to proceed with option number 1 in today's waklthrough. It's fun and
also the most optimal solution, however the code we are going to write highly
relies on the input format, so it will only work for AoC inputs, and not for any
possible input programs.

Let's start analyzing the program. Right off the bat, we can notice some
interesting characteristics:

1. All the 14 `inp` instructions store the input digit in register `w`.
2. There are exactly 17 other instructions following an `inp w`. This means we
   can see the whole program as 14 different 18-instruction chunks.
3. Each chunk always consists of the same 18 instructions, except the last
   operand of those instructions changes from chunk to chunk.

Let's examine the first chunk of code, and try to understand what happens to the
various registers. Here's a commented version of the code, where on the right
side I have simplified the result of successive instructions that operate on the
same register:

```none
 #  Instr       Result

 1. inp w       w = current input digit

 2. mul x 0     x = 0
 3. add x z     x = z
 4. mod x 26    x = x % 26
 5. div z 1     z = z
 6. add x 12    x = (z % 26) + 12
 7. eql x w     if x == w (input digit), then x = 1; else x = 0
 8. eql x 0     if x == 0, then x = 1; else x = 0

 9. mul y 0     y = 0
10. add y 25    y = 25
11. mul y x     y = 25 * x        (either 25 or 0)
12. add y 1     y = (25 * x) + 1  (either 26 or 1)
13. mul z y     z = z * y         (either z * 26 or z * 1)

14. mul y 0     y = 0
15. add y w     y = w (input digit)
16. add y 4     y = w + 4
17. mul y x     y = (w + 4) * x   (either w + 4 or 0)
18. add z y     z = z + y         (either z + w + 4 or 0)
```

I have split the chunk into 4 sub-chunks on purpose. We can now observe the
following:

1. Taking a look at the `z` register, we can see that it's being treated like a
   base 26 number: the two fundamental operations performed on it are `z % 26`
   or `z * 26 + something`. Other operations like `div z 1` or `mul z y`
   (when `y = 1`) are useless and don't change its value.
2. Instructions 2 to 8 seem useless: no matter what is the value of `z % 26`
   (which initially will be `0`), if we add `12` to it, it will never compare
   equal to `w`, since `w` holds the input digit and must therefore be between
   `1` and `9`. The result after instruction 8 is simply `x = 1`.
3. The rest of the code does things based on the value of `x`. Since we now know
   that `x` will always be `1` after instruction 8, we can simplify the rest.

Applying the simplification:

```none
 #  Instr       Result

 1. inp w       w = current input digit

 2. mul x 0
 3. add x z
 4. mod x 26
 5. div z 1
 6. add x 12
 7. eql x w
 8. eql x 0     x = 1

 9. mul y 0     y = 0
10. add y 25    y = 25
11. mul y x     y = 25
12. add y 1     y = 26
13. mul z y     z = z * 26

14. mul y 0     y = 0
15. add y w     y = w (input digit)
16. add y 4     y = w + 4
17. mul y x     y = w + 4
18. add z y     z = z + w + 4
```

The above code is basically *"pushing" the input digit plus `4` into `z`* as the
last digit, treating `z` as a base-26 number. The end result of the above code
is `z = 26*z + (w+4)`.

Looking at the next two chunks of code, the behavior seems to be the same: the
second chunk does `z = 26*z + (w+11)`, and the third chunk does
`z = 26*z + (w+7)`. What these first 3 chunks are doing is nothing more than
pushing the first 3 input digits (plus some constants) into z, one after the
other.

Coming to the fourth chunk, the story is different:

```none
 #  Instr       Result
 1. inp w       w = input digit

 2. mul x 0
 3. add x z
 4. mod x 26    x = z % 26
 5. div z 26    z //= 26

 6. add x -14   x -= 14
 7. eql x w
 8. eql x 0     if x != w then x = 1 else x = 0

 9. mul y 0
10. add y 25
11. mul y x     y = 25 * x  (either 25 or 0)
12. add y 1     y += 1      (either 26 or 1)
13. mul z y     z = z * y   (either z * 26 or z)

14. mul y 0
15. add y w
16. add y 2
17. mul y x     y = (w + 2) * x  (either w + 2 or 0)
18. add z y     z += y
```

The main difference between this chunk and the previous ones is that
instructions 2 to 5 are doing something different: the last base-26 digit of `z`
is being extracted into `x` with the `mod` instruction, then removed from `z`
with the integer division. After instruction 5, `x` represents the last value
that was "pushed" into `z`, which in our case was `w+7` i.e. the previous digit
plus `7`. It seems that `z` is being used as a simple *stack* of base 26
numbers.

Instructions 6 to 8 then perform another addition and compare `x` (which is the
value of the previously pushed digit plus some constants) with the current
digit. If they are equal, the final value of `x` becomes `0`. In such case, the
rest of the operations do *nothing:* we have ops 9 to 13 which compute `z *= 1`
and instructions 14 to 18 which compute `z += 0`. Otherwise, if after
instruction 8 we end up with `x = 1` (the two numbers did not match), we have
the rest of the operations which push some other value into `z`.

In the entire program, we have two different kinds of 18-instruction chunks:

1. 7 chunks arf of the first kind we analyzed, they simply push the current
   input digit plus some constant into `z`. This kind of chunk can be seen as:

   ```none
   push (current_digit + A) into z
   ```

2. The other 7 are of the second kind. They pop a previously saved digit (plus
   constant) from `z`, add another constant to it, and then compare it with the
   current digit. If the comparison is successful, `z` just "lost" its least
   significant base-26 digit, otherwise some other value is pushed into it.

   This kind of chunk can be seen as:

   ```none
   pop (other_digit + A) from z

   if (other_digit + A + B) != current_digit:
       push some_value into z
   ```

If we want `z` to have value `0` after all these operations, we need the
comparisons done in the second kind of chunk to succeed. This way, we are
pushing and popping from `z` exactly 7 times and 7 times, resulting in an
"empty" `z` stack with value `0` at the end of execution. Otherwise, if any of
the comparisons doesn't succeed, we'll end up with some non-zero value in `z`.

All we have to do to pass the program check on the input digits is pass all the
7 comparisons, which are comparing pairs of digits together. More specifically,
each of those pairs of digits needs to have a known difference (`D = A + B`)
given by the constants in the program.

How can we get the maximum possible values of two digits of a pair knowing that
they are both between `1` and `9`, and that their difference is `D`? Well, one
of them will of course be `9`. The other one will be `9 - D` if `D` is positive
or `9 + D` if `D` is negative.

Let's get to coding. The first thing we want to do is parse the input program
and parse each chunk of 18 instructions to extract the constants that determine
our input constraints. The first constant gets added to the current input digit
by the 16th instruction (`add x A`) of each first-kind chunk, then pushed into
`z`. The second constant gets added by the 6th instruction (`add x B`) of each
second-kind chunk, after popping. The two kinds of chunks can be distinguished
by the 5th instruction: it's `div z 1` for the first kind and `div z 26` for the
second kind.

Since we really don't care about most of the instructions, we'll skip a lot of
input lines. Let's write a function to skip `n` lines for simplicity:

```python
def skip(file, n):
    for _ in range(n):
        next(file)
```

Now we can extract the constants and return them along with the indexes of the
pair of digits they refer to and return a `list` of constraints to use later to
determine the value we want. For the "stack" we'll use a
[`deque`][py-collections-deque]. Each time we'll determine the kind of chunk:

- For the first kind of chunk we'll push the current digit index and the
  constant to add into the stack.
- For the second kind chunk we'll pop from the stack the other digit index and
  the first constant, add the second constant to the first and then append old
  digit index, current digit index and sum of the constants to the result to
  return.

Doing the above, the result will be a list of tuples of the form `(i, j, diff)`,
each of which indicates the constraint `digits[j] - digits[i] = diff`. Here's
the code:

```python
def get_constraints(fin):
    constraints = []
    stack = deque()

    for i in range(14):
        skip(fin, 4)
        op = next(fin).rstrip()
        assert op.startswith('div z '), 'Invalid input!'

        if op == 'div z 1': # first kind of chunk
            skip(fin, 10)
            op = next(fin)
            assert op.startswith('add y '), 'Invalid input!'

            a = int(op.split()[-1]) # first constant to add
            stack.append((i, a))
            skip(fin, 2)
        else:               # second kind of chunk
            op = next(fin)
            assert op.startswith('add x '), 'Invalid input!'

            b = int(op.split()[-1]) # second constant to add
            j, a = stack.pop()
            constraints.append((i, j, a + b)) # digits[j] - digits[i] must equal a + b
            skip(fin, 12)

    return constraints
```

With the list of constraints, we can now solve each pair of digits. One of them
will always be 9, while the other will be `9 - diff` in case `diff` is positive,
or `9 + diff` in case it's negative.

```python
def find_max(constraints):
    digits = [0] * 14

    for i, j, diff in constraints:
        if diff > 0:
            digits[i], digits[j] = 9, 9 - diff
        else:
            digits[i], digits[j] = 9 + diff, 9

    # Compute the actual number from its digits.
    num = 0
    for d in digits:
        num = num * 10 + d

    return num
```

The last part of the above function where we reconstruct the number from its
digits can be simplified using [`functools.reduce()`][py-functools-reduce]:

```python
from functools import reduce

def find_max(constraints):
    # ...
    return reduce(lambda acc, d: acc * 10 + d, digits)
```

Perfect, now we should have today's first star in our pocket:

```python
fin         = open(...)
constraints = get_constraints(fin)
nmax        = find_max(constraints)

print('Part 1:', nmax)
```

### Part 2

For the second part we are asked to find the minimum possible accepted number
instead.

Well, we already have all we need. Let's modify `find_max()` to calculate both
the maximum and minimum accepted values. Finding minimum is analogous to what we
did to find the maximum: given a pair of digits and their difference, one of the
two will just be the lowest possible (`1`), and the other will be `1 + diff` in
case `diff` is positive, and `1 - diff` otherwise.

```python
def find_max_min(constraints):
    nmax = [0] * 14
    nmin = [0] * 14

    for i, j, diff in constraints:
        if diff > 0:
            nmax[i], nmax[j] = 9, 9 - diff
            nmin[i], nmin[j] = 1 + diff, 1
        else:
            nmax[i], nmax[j] = 9 + diff, 9
            nmin[i], nmin[j] = 1, 1 - diff

    nmax = reduce(lambda acc, d: acc * 10 + d, nmax)
    nmin = reduce(lambda acc, d: acc * 10 + d, nmin)
    return nmax, nmin
```

We can now solve both parts at once using the above function:

```python
fin         = open(...)
constraints = get_constraints(fin)
nmax, nmin  = find_max_min(constraints)

print('Part 1:', nmax)
print('Part 2:', nmin)
```

Nice puzzle today. Not really much about programming, but more about
reverse engineering. Indeed, we could have solved the constraints in the input
by hand in a fraction of the time we spent writing a more general automated
solution!

Day 25 - Sea Cucumber
---------------------

[Problem statement][d25-problem] — [Complete solution][d25-solution] — [Back to top][top]

Not a hard ptoblem for this years' Christmas day. We are givn an ASCII-art grid
where we can have three kind of cells: `>` (a sea cucumber facing right), `v` (a
sea cucumber facing down), `.` (empty). We need to evolve the grid according to
the following rules to be applied every evolution step:

1. First all sea cucumbers facing right (`>`) try moving right simultaneously.
   They succeed only if the cell on their right is empty (`.`), and on the
   rightmost cell, they wrap around to the leftmost if possible.
2. Then, all sea cucumbers facing down (`v`) try moving down simultaneously.
   They succeed only if the cell below them is empty (`.`), and on the very
   bottom cell, they wrap up to the very top if possible.

We want to know how many evolution steps it takes for all the sea cucumber to
stop moving because they all get stuck in front of others.

Looks simple. We could solve this problem either with an actual grid (a 2x2
matrix i.e. `list` of `list`) or with a sparse matrix represented by a `dict`. I
will go with the first approach. I have implemented both options, and for
today's input there is no performance difference between using an actual matrix
or a sparse matrix backed by a `dict`, but in general using a sparse matrix
could perform better if the input is sparse enough (i.e. lots of empty spaces
`.`). You can find my sparse matrix solution implemented
**[here][d25-alternative]**.

Input parsing is simple: read the entire input, split it on whitespace
(newlines), and then transform every single line in a `list` with the help of
[`map()`][py-builtin-map]:

```python
fin  = open(...)
grid = list(map(list, fin.read().split()))
```

For the evolution of our grid, we need to pay attention to the fact that all
right facing sea cucumbers check the next cell simultaneously, *before* any of
them moves. This means that in a situation where some of them are stuck in line
(`>>>..`), only the first one will move (`>>.>.`). To take this into account, we
could either:

1. Clone the entire grid before performing the moves, then use the old copy to
   check if cells are free, and only modify the new copy.
2. Use a single grid, scanning it without modifying it first, remembering all
   the locations of sea cucumbers that will be able to move (e.g. storing them
   in a list). Then, perform all the moves.

The second option seems both faster and more memory efficient, since copying the
grid every single time might be an expensive operation, and would probably also
use more memory than a simple list of coordintes.

To check if the "next" cell is free, and take into account that sea cucumbers
can and will wrap around (`..>>>` becomes `>.>>.`), we can just use the modulo
operator (`%`) when calculating the candidate new coulmn. Here's what a single
sweep and move of all the right-facing cucumbers looks like:

```python
h, w = len(grid), len(grid[0])
advance = []

for r in range(h):
    for c in range(w):
        newc = (c + 1) % w

        # Check if this cell contains a right-facing sea cucumber and if the
        # next one is free. If so, this sea cucumber can advance.
        if mat[r][c] == '>' and mat[r][newc] == '.':
            advance.append((r, c, newc))

# Move all right-facing sea cucumbers that can advance.
for r, c, newc in advance:
    mat[r][c]    = '.'
    mat[r][newc] = '>'
```

After doing the above, we can determine if any sea cucumber advanced
horizontally by checking if `advanced` is empty or not. Python lists are
"truthy" if they aren't empty, so:

```python
horiz_still = not advance # true if no right-facing sea cucumber advanced
```

For the down-facing sea cucumbers... well, it's exactly the same story, only
that we'll need to make movements on rows instead of columns. The code barely
changes. In the end, we can check if `horiz_still==True` and the new `advanced`
list is empty: if so, nothing moved and we can call it a day.

Wrapping things up, here's the full code of the function we'll use to evolve the
grid until everything stops moving. The steps are counted using
[`itertools.count()`][py-itertools-count] as we don't know how many there will
be.

```python
def evolve(grid):
    h, w  = len(grid), len(grid[0])
    steps = 0

    for steps in count(1):
        advance = []

        for r in range(h):
            for c in range(w):
                newc = (c + 1) % w

                if grid[r][c] == '>' and grid[r][newc] == '.':
                    advance.append((r, c, newc))

        for r, c, newc in advance:
            grid[r][c]    = '.'
            grid[r][newc] = '>'

        horiz_still = not advance
        advance = []

        for r in range(h):
            for c in range(w):
                newr = (r + 1) % h

                if grid[r][c] == 'v' and grid[newr][c] == '.':
                    advance.append((r, c, newr))

        if horiz_still and not advance:
            break

        for r, c, newr in advance:
            grid[r][c]    = '.'
            grid[newr][c] = 'v'

    return steps
```

Simple enough. We can now get the last two stars of the year:

```python
ans = evolve(grid)
print('Part 1:', ans)
```

As always, there is no part 2 for day 25. Merry Christmas!

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
[d13]: #day-13---transparent-origami
[d14]: #day-14---extended-polymerization
[d15]: #day-15---chiton
[d16]: #day-16---packet-decoder
[d17]: #day-17---trick-shot
[d18]: #day-18---snailfish
[d19]: #day-19---beacon-scanner
[d20]: #day-20---trench-map
[d21]: #day-21---dirac-dice
[d22]: #day-22---reactor-reboot
[d23]: #day-23---amphipod
[d24]: #day-24---arithmetic-logic-unit
[d25]: #day-25---sea-cucumber

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
[d13-problem]: https://adventofcode.com/2021/day/13
[d14-problem]: https://adventofcode.com/2021/day/14
[d15-problem]: https://adventofcode.com/2021/day/15
[d16-problem]: https://adventofcode.com/2021/day/16
[d17-problem]: https://adventofcode.com/2021/day/17
[d18-problem]: https://adventofcode.com/2021/day/18
[d19-problem]: https://adventofcode.com/2021/day/19
[d20-problem]: https://adventofcode.com/2021/day/20
[d21-problem]: https://adventofcode.com/2021/day/21
[d22-problem]: https://adventofcode.com/2021/day/22
[d23-problem]: https://adventofcode.com/2021/day/23
[d24-problem]: https://adventofcode.com/2021/day/24
[d25-problem]: https://adventofcode.com/2021/day/25

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

[d03-orginal]:             original_solutions/day03.py
[d07-orginal]:             original_solutions/day07.py
[d18-original]:            original_solutions/day18.py
[d21-original]:            original_solutions/day21.py
[d24-original]:            original_solutions/day24.py
[d25-alternative]:         misc/day25/sparse_matrix.py
[d22-alternative]:         misc/day22/coord_compression.py
[d22-alternative-2]:       misc/day22/octree.py
[d06-p2]:                  #part-2-7
[d14-p2]:                  #part-2-13
<!-- TODO: change this when adding d19! -->
[d21-p2]:                  #part-2-19
[2019-d06-p2]:             ../2019/README.md#part-2-5
[2019-d18]:                ../2019/README.md##day-18---many-worlds-interpretation

[d07-reddit-discussion]:   https://www.reddit.com/r/adventofcode/comments/rars4g/
[d07-reddit-megathread]:   https://www.reddit.com/rar7ty
[d07-reddit-paper]:        https://www.reddit.com/r/adventofcode/comments/rawxad
[d07-reddit-paper-author]: https://www.reddit.com/user/throwaway7824365346/
[d17-reddit-megathread]:   https://www.reddit.com/ri9kdq
[d18-reddit-megathread]:   https://www.reddit.com/rizw2c
[d24-reddit-comment]:      https://www.reddit.com/r/adventofcode/comments/rnejv5/2021_day_24_solutions/hps4c3n/

[py-assert]:                  https://docs.python.org/3/reference/simple_stmts.html#grammar-token-python-grammar-assert_stmt
[py-class]:                   https://docs.python.org/3/tutorial/classes.html#a-first-look-at-classes
[py-cond-expr]:               https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-decorator]:               https://wiki.python.org/moin/PythonDecorators#What_is_a_Decorator
[py-dict-comprehension]:      https://www.python.org/dev/peps/pep-0274/
[py-lambda]:                  https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-generator-function]:      https://wiki.python.org/moin/Generators
[py-generator-expr]:          https://www.python.org/dev/peps/pep-0289/
[py-stopiteration]:           https://docs.python.org/3/library/exceptions.html#StopIteration
[py-unpacking]:               https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists
[py-yield-from]:              https://docs.python.org/3.9/whatsnew/3.3.html#pep-380

[py-builtin-abs]:             https://docs.python.org/3/library/functions.html#abs
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-eval]:            https://docs.python.org/3/library/functions.html#eval
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-len]:             https://docs.python.org/3/library/functions.html#len
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-next]:            https://docs.python.org/3/library/functions.html#next
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-bytes]:                   https://docs.python.org/3/library/stdtypes.html#bytes
[py-bytes-fromhex]:           https://docs.python.org/3/library/stdtypes.html#bytes.fromhex
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-counter]:     https://docs.python.org/3/library/collections.html#collections.Counter
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-dict-items]:              https://docs.python.org/3/library/stdtypes.html#dict.items
[py-frozenset]:               https://docs.python.org/3/library/stdtypes.html#frozenset
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-functools-cache]:         https://docs.python.org/3/library/functools.html#functools.cache
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-heapq]:                   https://docs.python.org/3/library/heapq.html
[py-io-readline]:             https://docs.python.org/3/library/io.html#io.IOBase.readline
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-itertools-cycle]:         https://docs.python.org/3/library/itertools.html#itertools.cycle
[py-itertools-filterfalse]:   https://docs.python.org/3/library/itertools.html#itertools.filterfalse
[py-itertools-permutations]:  https://docs.python.org/3/library/itertools.html#itertools.permutations
[py-itertools-product]:       https://docs.python.org/3/library/itertools.html#itertools.product
[py-itertools-repeat]:        https://docs.python.org/3/library/itertools.html#itertools.repeat
[py-itertools-starmap]:       https://docs.python.org/3/library/itertools.html#itertools.starmap
[py-itertools-chain]:         https://docs.python.org/3/library/itertools.html#itertools.chain
[py-list-extend]:             https://docs.python.org/3/library/stdtypes.html#list.extend
[py-list-sort]:               https://docs.python.org/3/library/stdtypes.html#list.sort
[py-math-prod]:               https://docs.python.org/3/library/math.html#math.prod
[py-operator-itemgetter]:     https://docs.python.org/3/library/operator.html#operator.itemgetter
[py-re]:                      https://docs.python.org/3/library/re.html
[py-set-intersection]:        https://docs.python.org/3/library/stdtypes.html#frozenset.intersection
[py-statistics-median-low]:   https://docs.python.org/3/library/statistics.html#statistics.median_low
[py-str-format]:              https://docs.python.org/3/library/stdtypes.html#str.format
[py-str-index]:               https://docs.python.org/3/library/stdtypes.html#str.index
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[algo-bfs]:       https://en.wikipedia.org/wiki/Breadth-first_search
[algo-dijkstra]:  https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-dfs]:       https://en.wikipedia.org/wiki/Depth-first_search
[algo-quicksort]: https://en.wikipedia.org/wiki/Quicksort

[wiki-bingo]:                 https://en.wikipedia.org/wiki/Bingo_(American_version)
[wiki-bounding-box]:          https://en.wikipedia.org/wiki/Minimum_bounding_box
[wiki-cartesian-coords]:      https://en.wikipedia.org/wiki/Cartesian_coordinate_system
[wiki-closed-form-expr]:      https://en.wikipedia.org/wiki/Closed-form_expression
[wiki-cpython]:               https://en.wikipedia.org/wiki/CPython
[wiki-cycle-detection]:       https://en.wikipedia.org/wiki/Cycle_detection
[wiki-dyck-language]:         https://en.wikipedia.org/wiki/Dyck_language
[wiki-dynamic-programming]:   https://en.wikipedia.org/wiki/Dynamic_programming
[wiki-floor-ceil]:            https://en.wikipedia.org/wiki/Floor_and_ceiling_functions
[wiki-fold]:                  https://en.wikipedia.org/wiki/Fold_(higher-order_function)
[wiki-graph-component]:       https://en.wikipedia.org/wiki/Component_(graph_theory)
[wiki-heat-death-universe]:   https://en.wikipedia.org/wiki/Heat_death_of_the_universe
[wiki-image-convolution]:     https://en.wikipedia.org/wiki/Kernel_(image_processing)
[wiki-linear-least-squares]:  https://en.wikipedia.org/wiki/Linear_least_squares
[wiki-linear-time]:           https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-linked-list]:           https://en.wikipedia.org/wiki/Linked_list
[wiki-lru-cache]:             https://en.wikipedia.org/wiki/Cache_replacement_policies#Least_recently_used_(LRU)
[wiki-median]:                https://en.wikipedia.org/wiki/Median
[wiki-memoization]:           https://en.wikipedia.org/wiki/Memoization
[wiki-min-heap]:              https://en.wikipedia.org/wiki/Binary_heap
[wiki-np-complete]:           https://en.wikipedia.org/wiki/NP-completeness
[wiki-numpy]:                 https://en.wikipedia.org/wiki/NumPy
[wiki-octree]:                https://en.wikipedia.org/wiki/Octree
[wiki-priority-queue]:        https://en.wikipedia.org/wiki/Priority_queue
[wiki-projectile-motion]:     https://en.wikipedia.org/wiki/Projectile_motion
[wiki-pushdown-automata]:     https://en.wikipedia.org/wiki/Pushdown_automaton
[wiki-queue]:                 https://en.wikipedia.org/wiki/Queue_(abstract_data_type)
[wiki-reflection]:            https://en.wikipedia.org/wiki/Reflection_(mathematics)
[wiki-scipy]:                 https://en.wikipedia.org/wiki/SciPy
[wiki-segment-tree]:          https://en.wikipedia.org/wiki/Segment_tree
[wiki-seven-segment-display]: https://en.wikipedia.org/wiki/Seven-segment_display
[wiki-smt]:                   https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
[wiki-stack]:                 https://en.wikipedia.org/wiki/Stack_(abstract_data_type)
[wiki-symbolic-execution]:    https://en.wikipedia.org/wiki/Symbolic_execution
[wiki-tower-of-hanoi]:        https://en.wikipedia.org/wiki/Tower_of_Hanoi
[wiki-triangular-number]:     https://en.wikipedia.org/wiki/Triangular_number
[wiki-zocchihedron]:          https://en.wikipedia.org/wiki/Zocchihedron

[misc-aoc-bingo]:               https://www.reddit.com/r/adventofcode/comments/k3q7tr/
[misc-coord-compression-so]:    https://stackoverflow.com/q/29528934/3889449
[misc-coord-compression-quora]: https://www.quora.com/What-is-coordinate-compression-and-what-is-it-used-for
[misc-inverse-triangular]:      https://math.stackexchange.com/a/2041994
[misc-issue-11]:                https://github.com/mebeim/aoc/issues/11
[misc-issue-14]:                https://github.com/mebeim/aoc/issues/14
[misc-cpp-nth-element]:         https://en.cppreference.com/w/cpp/algorithm/nth_element
[misc-cpp-nth-element-so]:      https://stackoverflow.com/q/29145520/3889449
[misc-cpython-median-low]:      https://github.com/python/cpython/blob/ddbab69b6d44085564a9b5022b96b002a52b2f2b/Lib/statistics.py#L549-L568
[misc-median-math-se]:          https://math.stackexchange.com/q/113270
[misc-pypy]:                    https://www.pypy.org/
[misc-regexp]:                  https://www.regular-expressions.info/
[misc-so-recursive-bfs]:        https://stackoverflow.com/q/2549541/3889449
