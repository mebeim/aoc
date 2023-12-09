Advent of Code 2023 walkthrough
===============================

**Note**: in the hope of speeding up the process of writing walkthroughs each
day, this year I am *not* going to give a brief summary of the "part 1" problem
statement at the beginning of each day. Instead, I will jump right at the
solution. The official problem statements are linked throughout the document for
reference.

Table of Contents
-----------------

- [Day 1 - Trebuchet?!][d01]
- [Day 2 - Cube Conundrum][d02]
- [Day 3 - Gear Ratios][d03]
- [Day 4 - Scratchcards][d04]
- [Day 5 - If You Give A Seed A Fertilizer][d05]
- [Day 6 - Wait For It][d06]
- [Day 7 - Camel Cards][d07]
- [Day 8 - Haunted Wasteland][d08]
- [Day 9 - Mirage Maintenance][d09]
<!--
- [Day 10 - ][d10]
- [Day 11 - ][d11]
- [Day 12 - ][d12]
- [Day 13 - ][d13]
- [Day 14 - ][d14]
- [Day 15 - ][d15]
- [Day 16 - ][d16]
- [Day 17 - ][d17]
- [Day 18 - ][d18]
- [Day 19 - ][d19]
- [Day 20 - ][d20]
- [Day 21 - ][d21]
- [Day 22 - ][d22]
- [Day 23 - ][d23]
- [Day 24 - ][d24]
- [Day 25 - ][d25]
-->


Day 1 - Trebuchet?!
-------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution] — [Back to top][top]

### Part 1

Task seems easy enough. How do you find out if a character is a digit? Simply
check [`char.isdigit()`][py-str-isdigit]. We can do this for each character of
each line of input, first iterating forward to find the first, and then
iterating backwards (using `[::-1]`) to find the last. The digits we find will
need to be converted to `int`, and the first one will need to also be multiplied
by `10`.

```python
fin   = open(...)
total = 0

for line in fin:
    for char in line:
        if char.isdigit():
            total += 10 * int(char)
            break

    for char in line[::-1]:
        if char.isdigit():
            total += int(char)
            break
```

We can simplify this with the help of the [`filter()`][py-builtin-filter]
built-in function: just filter out any character that satisfies `str.isdigit()`.
To only extract the first such character from the iterator returned by
`filter()` we can simply use [`next()`][py-builtin-next].

```python
for line in fin:
    digit1 = next(filter(str.isdigit, line))
    digit2 = next(filter(str.isdigit, line[::-1]))
    total += 10 * int(digit1) + int(digit2)

print('Part 1:', total)
```

### Part 2

Things get more complex and this is probably the "hardest" day 1 problem I have
seen so far. We need to also consider English *words* when checking each line of
input. The first and last digits to appear either as a digit or as an english
word need to be found.

There isn't much to do except checking each spelled out English digit for each
line. We can simplify things by building a `dict` to use as a lookup table:

```python
DIGITS = {
    'one'  : 1,
    'two'  : 2,
    'three': 3,
    'four' : 4,
    'five' : 5,
    'six'  : 6,
    'seven': 7,
    'eight': 8,
    'nine' : 9,
}
```

Now the check is a bit more annoying, so let's create a function for it: it will
take a string and will check whether the first character is a digit (and in that
case return it) or whether the string starts with a spelled-out English digit
(and in that case convert and return it). We'll return `0` in case of no match
for simplicity.

```python
def check_digit(string):
    if string[0].isdigit():
        return int(string[0])

    for d in DIGITS:
        if string.startswith(d):
            return DIGITS[d]

    return 0
```

The second loop above can again be simplified with the use of `filter()` +
`next()`, but since this time we are not guaranteed to find an English word in
`string`, we need to pass a second argument to `next()` for the default value to
return in case `filter()` does not match anything.

```python
def check_digit(char, string):
    if string[0].isdigit():
        return int(string[0])

    d = next(filter(string.startswith, DIGITS), None)
    return DIGITS.get(d, 0)
```

We can now integrate the above function in the loop we wrote for part 1, using a
second variable for the total. This time, we'll have to iterate over each
possible substring manually, first forward and then backwards. We can easily use
[`range()`][py-builtin-range] for that.

```python
total1 = total2 = 0

for line in fin:
    # Part 1
    total1 += 10 * int(next(filter(str.isdigit, line)))
    total1 += int(next(filter(str.isdigit, line[::-1])))

    # Part 2
    for i in range(len(line)):
        digit1 = check_digit(char, line[i:])
        if digit1:
            break

    for i in range(len(line) - 1, -1, -1):
        digit2 = check_digit(line[i], line[i:])
        if digit2:
            break

    total2 += 10 * digit1 + digit2

print('Part 1:', total1)
print('Part 2:', total2)
```

There is technically a way to "simplify" this even more, again with the use of
`filter()` + `next()`, but it does not really help anything. However, here it
is, just for the fun of it:

```python
for line in fin:
    total2 += 10 * next(filter(None, map(check_digit, (line[i:] for i in range(len(line))))))
    total2 += next(filter(None, map(check_digit, (line[i:] for i in range(len(line) -1, -1, -1)))))
```

First two stars of the year done. Welcome to Advent of Code 2023!


Day 2 - Cube Conundrum
----------------------

[Problem statement][d02-problem] — [Complete solution][d02-solution] — [Back to top][top]

### Part 1

We are dealing with... a game using colored cubes. Today's input seems a bit
annoying to parse. While we could do this with a couple of regular expressions,
I usually prefer to avoid those. Thankfully we can get around with only a few
[`.split()`][py-str-split] operations.

The lines are in the form:

```none
Game 3: 1 red, 2 green; 3 green, 1 blue, 7 red; 3 green, 5 red, 1 blue
```

The first thing to do is extract the game ID and convert it to integer: we can
do this by simply splitting on the colon (`:`) - or more precisely on colon
followed by a space (`': '`) - and then extract the ID by [slicing][py-slicing].

```python
fin = open(...)

for line in fin:
    gid, game = line.split(': ')
    gid = int(gid[5:])
```

We can then split on `'; '` to separate each "turn" of each game, split again on
`', '` to separate each listed number and color combination in the turn, and
again one last time on whitespace to separate the number from the color,
converting numbers to integer.

```python
for line in fin:
    gid, game = line.split(': ')
    gid = int(gid[5:])

    for turn in game.split('; '):
        for n_and_color in turn.split(', '):
            n, color = n_and_color.split()
            n = int(n)
```

We can simplify the above and split `n` and `color` on the fly using
[`map()`][py-builtin-map] and `str.split()`:

```diff
     for turn in game.split('; '):
+        for n, color in map(str.split, turn.split(', ')):
-        for n_and_color in turn.split(', '):
-            n, color = n_and_color.split()
             n = int(n)
```

Now, since we are tasked with identifying impossible games, for each color we
encounter in a turn, we need to check whether the given number exceeds the
limits we are given: 12 red, 13 green and 14 blue. We can do this pretty easily
with a few `if` statements and a boolean variable.

```python
answer = 0

for line in fin:
    gid, game = line.split(': ')
    gid = int(gid[5:])
    bad = False

    for turn in game.split('; '):
        for n, color in map(str.split, turn.split(', ')):
            n = int(n)

            if color == 'red' and n > 12:
                bad = True
            elif color == 'green' and n > 13:
                bad = True
            elif color == 'blue' and n > 14:
                bad = True

    if bad:
        answer += gid
```

Those `if` statements can be simplified down to a single one by combining the
conditions. Additionally, we can `break` out of the loop as soon as we find an
impossible turn:

```python
    # ... same as above ...
            if n > 14 or (n > 13 and color == 'green') or (n > 12 and color == 'red'):
                bad = True
                break

    if bad:
        answer += gid

print('Part 1:', answer)
```

### Part 2

For part two, for each game we now need to find the minimum number of cubes of
each color that would make the game possible. If we think about it for a moment,
this simply means computing the maximum value we see for each color over all the
turns of a game.

We can adapt the code we just wrote for part 1 and integrate the calculations
for part 2 too. We'll add 3 more variables to keep track of the maximum number
for each color among all the turns using [`max()`][py-builtin-max].

```python
answer1 = answer2 = 0

for line in fin:
    gid, game = line.split(': ')
    gid = int(gid[5:])

    # Maximum number of red, green and blue cubes seen in any turn of this game
    maxr = maxg = maxb = 0

    for turn in game.split('; '):
        for n, color in map(str.split, turn.split(', ')):
            n = int(n)

            if color == 'red':
                maxr = max(n, maxr)
            elif color == 'green':
                maxg = max(n, maxg)
            else:
                maxb = max(n, maxb)
```

For each game, at the end of the `for turn` loop, we now have `maxr`, `maxg`,
and `maxb` containing respectively the maximum number of red, green and blue
cubes that we saw in any turn. We can use these values to simplify the logic for
the impossibility check of part 1, which can now happen outside the loop, as we
cannot `break` earlier as we did before. Since the check is moved outside the
loop, we also don't need the `bad` boolean variable anymore.

```python
for line in fin:
    # ...
    for turn in game.split('; '):
        # ...

    if maxr <= 12 and maxg <= 13 and maxb <= 14:
        answer1 += gid
```

Or, if we want to avoid branching, we can use a simple multiplication, since a
`bool` used in arithmetic expressions evaluates either to `0` or `1`:

```diff
-    if maxr <= 12 and maxg <= 13 and maxb <= 14:
-        answer1 += gid
+   answer1 += gid * (maxr <= 12 and maxg <= 13 and maxb <= 14)
```

Finally, the value we want for part 2 simply consists of the sum of the products
of the 3 maximums over all games:

```python
for line in fin:
    # ...
    for turn in game.split('; '):
        # ...

    answer1 += gid * (maxr <= 12 and maxg <= 13 and maxb <= 14)
    answer2 += maxr * maxg * maxb

print('Part 1:', answer1)
print('Part 2:', answer2)
```

And here we go, 4 stars and counting!


Day 3 - Gear Ratios
-------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution] — [Back to top][top]

### Part 1

First ASCII grid problem of the year, let's get right into it! First of all,
parsing: doesn't get much easier than this, we can just read the entire input in
one go and the use [`.splitlines()`][py-str-splitlines] to have a nice list of
strings that we can index like a grid. For later use, let's also calculate width
and height of the grid right away.

```python
fin = open(...)
grid = fin.read().splitlines()
witdh, height = len(grid), len(grid[0])
```
<!--
Now onto the problem: in order to correctly identify numbers on each line that
are adjacent to symbols, we need a way to iterate over the neighbors of a cell
in the grid, so let's write a [generator function][py-generators] for this.
Given the grid, a row index and a column index, we can iterate over all 8
neighbors yielding both their row/column indices and the value of the cell.

```python
def neighbors(grid, r, c):
    for deltar in (-1, 0, 1):
        for deltac in (-1, 0, 1):
            if deltar and deltac:
                rr, cc = r + deltar, c + deltac

                if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
                    yield rr, cc, grid[rr][cc]
```

This works, but we can optimize it in two ways. First of all we already know all
the possible `deltar, deltac` combinations, so we can use a single loop.
Secondly, we can avoid computing the length every single time for the bounds
check and either take it as argument or calculate it once at the start of the
function: I chose the former.

```python
def neighbors(grid, r, c, h, w):
    for dr, dc in ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)):
        rr, cc = r + dr, c + dc

        if 0 <= rr < h and 0 <= cc < w:
            yield rr, cc, grid[rr][cc]
```
-->

Now onto the real problem: given that the numbers scattered around the grid are
always spelled from left to right (i.e. all the digits are always on the same
row), in order to extract a number we can simply scan linearly until we stop
seeing digits. Let's write a function to extract a number in this way: it will
take the row and the starting column as parameters and return a number converted
to integer. For simplicity, we'll also pass the row length since we have it at
hand. The [`.isdigit()`][py-str-isdigit] method of strings comes in handy
(technically, `.isdigit()` doesn't only accept [ASCII][wiki-ascii] digits, but
we know our entire input is ASCII, so it's fine).

```python
def extract_number(row, start, length):
    end = start + 1
    while end < length and row[end].isdigit():
        end += 1

    return int(row[start:end])
```

Now all we need is a way to determine whether a number is adjacent to any
symbol. There are a multitude of ways to go about this, with small variations
that can make the code look completely different. I chose the one that seemed
more readable and intuitive to me.

Following a similar approach as the one used to extract a number, we can scan
linearly from left to right starting from one column before the number and
stopping one column after the number, checking the row containing the number as
well as the one above and below. If we find any symbol, we can stop checking and
we know that number needs to be accounted for.

Let's write another function to do this:

1. Start from the column before the first digit and keep going until we have
   a digit on the given row.
2. Check the same column in the row above and below the given row: if there's
   a symbols, stop here.
3. Check the column of the given row, if there's a symbol, stop here. Otherwise
   stop unconditionally if there's no digit and we are past the starting column.

Point 3 above is a bit tricky, but is basically what allows us to stop scanning
when we encounter the end of the current number.

We don't exactly know what symbols there might be, but we know that anything
that is not a dot (`.`) or a digit is a symbol, so that's the check we'll
implement.

Here's the function:

```python
def has_adjacent_symbols(grid, r, start_c, height, width):
    # Avoid going out of bounds on the left if start_c is 0
    start_c = max(0, start_c - 1)

    for c in range(start_c, width):
        # Check above
        if r > 0 and grid[r - 1][c] not in '0123456789.':
            return True

        # Check below
        if r < height - 1 and grid[r + 1][c] not in '0123456789.':
            return True

        # Check given row
        if not grid[r][c].isdigit():
            # Symbol
            if grid[r][c] != '.':
                return True

            # No more digits, stop
            if c > start_c:
                break

    return False
```

Since the row we are given (`r`) is always the same, and indexing lists is a
pretty slow operation in Python, we can simplify the above function while also
making it more readable by extracting the three rows (given row, row above and
row below) right away. A [conditional expression][py-cond-expr] comes in handy
for this purpose.

```python
def has_adjacent_symbols(grid, r, start_c, h, w):
    row   = grid[r]
    # Take row above if possible, else an empty list
    above = grid[r - 1] if r > 0 else []
    # Take row below if possible, else an empty list
    below = grid[r + 1] if r < height - 1 else []

    for c in range(max(0, start_c - 1), width):
        if above and above[c] not in '0123456789.':
            return True

        if below and below[c] not in '0123456789.':
            return True

        if not row[c].isdigit():
            if row[c] != '.':
                return True

            # No more digits, stop
            if c > start_c:
                break

    return False
```

The multiple `not in ...` checks may seem a bit redundant, but there aren't many
alternatives that are shorter or simpler to read.

We now have all we need to solve the problem. All that's left to do is iterate
over the grid one row at a time, and scan characters in the row until we find a
digit. Once we do, check for adjacent symbols and extract the number if any
symbol is found.

The [`enumerate()`][py-builtin-enumerate] built-in is nice to have to iterate
both on rows and their row index at once.

```python
answer = 0

for r, row in enumerate(grid):
    c = 0

    while c < width:
        # Skip all non-digits
        while c < width and not row[c].isdigit():
            c += 1

        # Stop if we are past the end of the row
        if c >= width:
            break

        # We have a digit, check for adjacent symbols and extract it
        if has_adjacent_symbols(grid, r, c, height, width):
            answer += extract_number(row, c, width)

        # Skip remaining digits
        while c < width and row[c].isdigit():
            c += 1

print('Part 1:', answer)
```

### Part 2

The task now becomes a bit more complex: we need to identify "gears", that is:
all the asterisk (`*`) symbols that have exactly two adjacent numbers. For each
such pair of numbers, we then need to calculate the product, and sum all the
products up.

It may seem like a lot of work, but the way we wrote the
`has_adjacent_symbols()` function for part one makes it easy to modify it to
identify gears instead of just stopping at the first symbol and returning a
boolean. We can transform the function to return a boolean plus a list of
coordinates for asterisk symbols found. We can then use those coordinates (row
and column index) as an unique identifier of a given asterisk: each time we
encounter the same coordinates it means we found the same one.

Let's turn `has_adjacent_symbols()` into `adjacent_symbols()`:

```python
def adjacent_symbols(grid, r, start_c, height, width):
    row   = grid[r]
    # Take row above if possible, else an empty list
    above = grid[r - 1] if r > 0 else []
    # Take row below if possible, else an empty list
    below = grid[r + 1] if r < height - 1 else []

    # List of coordinates of adjacent '*' symbols found
    gears = []
    # True if any adjacent symbol is found
    adj_to_symbol = False

    for c in range(max(0, start_c - 1), width):
        if above and above[c] not in '0123456789.':
            adj_to_symbol = True

            if above[c] == '*':
                gears.append((r - 1, c))

        if below and below[c] not in '0123456789.':
            adj_to_symbol = True

            if below[c] == '*':
                gears.append((r + 1, c))

        if not row[c].isdigit():
            adj_to_symbol |= row[c] != '.'

            if row[c] == '*':
                gears.append((r, c))

            # No more digits, stop
            if c > start_c:
                break

    return adj_to_symbol, gears
```

Now a call to `adjacent_symbols()` returns a boolean indicating whether any
symbols were found adjacent to the number starting at `start_c` in the row at
index `r`, as well as the coordinates of all the `*` symbols encountered. We can
keep track of the numbers adjacent to a given `*` symbol with a dictionary of
lists. Using a [`defaultdict(list)`][py-collections-defaultdict] makes it even
easier as we can just [`.append()`][py-list-append] without worrying if a given
symbol was already added to the dictionary or not.

```python
from collections import defaultdict

# For each '*' symbol, keep a list holding its adjacent numbers
gears = defaultdict(list)
```

The main loop needs minimal modifications:

```python
answer1 = 0

for r, row in enumerate(grid):
    c = 0

    while c < width:
        # Skip all non-digits
        while c < width and not row[c].isdigit():
            c += 1

        # Stop if we are past the end of the row
        if c >= width:
            break

        adj_to_symbol, adj_gears = list(adjacent_symbols(grid, r, c, height, width))

        if adj_to_symbol:
            number = extract_number(row, c, width)
            answer1 += number

            # For each '*' symbol, add the current number to the list of numbers
            # adjacent to the symbol
            for coords in adj_gears:
                gears[coords].append(number)

        # Skip remaining digits
        while c < width and row[c].isdigit():
            c += 1

print('Part 1:', answer1)
```

We now have a complete `gears` dictionary of the form `{(r, c): [num, ...]}`,
for example:

```python
{
    (1, 2): [123, 456],
    (3, 4): [999],
    # ...
}
```

We already have the part 1 answer. For part 2 we are asked to consider `*`
symbols that have exactly *two* adjacent numbers, so we can simply iterate over
`gears` and check which lists have a length of `2`. Simple enough!

```python
answer2 = 0

for numbers in gears.values():
    if len(numbers) == 2:
        answer2 += numbers[0] * numbers[1]
```

We can also use [`math.prod()`][py-math-prod] to calculate the product:

```python
from math import prod

for numbers in adj_numbers.values():
    if len(numbers) == 2:
        answer2 += prod(numbers)
```

Since all we are doing is summing up, we can simplify even more with the help of
a few builtins:

- [`filter()`][py-builtin-filter] each list with a [`lambda`][py-lambda]
  function that checks the length, to only extract the ones with length `2`.
- [`map()`][py-builtin-map] each list to the product of its numbers with
  `prod()`.
- [`sum()`][py-builtin-sum] up all the products.

```python
len_2_lists = filter(lambda x: len(x) == 2, gears.values())
products    = map(prod, len_2_lists)
answer2     = sum(products)
```

Or more concisely:

```python
answer2 = sum(map(prod, filter(lambda x: len(x) == 2, gears.values()))))
print('Part 2:', answer2)
```

Although I like the conciseness of the above expression, one may prefer the more
verbose loop since it is undoubtedly easier to understand if you are not an
hardcore Python dev. Well, a bit of golfing is always fun anyway, so I'll keep
it as is. Six stars out of fifty!


Day 4 - Scratchcards
--------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution] — [Back to top][top]

### Part 1

For each line of input we have two easy to parse lists of integers, and we want
to know how many integers of the first list are also in the second one. We can
do this with a simple loop while parsing the input.

To extract the lists we can start by discarding anythig before the first `:`,
whose index can be found with [`.find()`][py-str-find]. Then,
[`.split()`][py-str-split] the line on `|` (the delimiter of the two lists),
split again each list on whitespace, and finally [`map()`][py-builtin-map]
everything to `int`.

```python
fin = open(...)

for line in fin:
    winners, numbers = line[line.find(':') + 1:].split('|')
    winners = list(map(int, winners.split()))
    numbers = list(map(int, numbers.split()))
```

Now we have two lists for each input line that are easy to work with: to check
how many elements of `winners` are in `numbers` the first thing that comes to
mind is simply iterating over the former and checking if elements are in the
latter using the `in` operator:

```python
    matches = 0
    for w in winners:
        if w in numbers:
            matches += 1
```

This isn't really optimal though, as the `in` operator has to scan `numbers`
every single time. It would be better if `numbers` was a `set`, so that
membership could be tested instantly. In fact... if both `winners` and `numbers`
are `set`s, we can use the `&` (binary AND) operator to calculate the
[intersection][py-set-intersection] of the two sets. The length of the
intersection will then be equal to the number of elements that are in both sets,
which is what we want.

```python
for line in fin:
    winners, numbers = line[line.find(':') + 1:].split('|')
    winners = set(map(int, winners.split()))
    numbers = set(map(int, numbers.split()))
    matches = len(numbers & winners)
```

Now, as the rules of the game suggest, for each card, each matching number
doubles the score of the card, which starts at `1` on the first match. This is
basically just a power of two, so we can calculate it with one expression
without the need of loops. Doing `2**(matches - 1)` seems enough, but in case of
zero matches we will get `2**-1 == 0.5` while we would want to have `0` instead.
We can transform the result to `int` to work around this.

```python
score = 0

for line in fin:
    winners, numbers = line[line.find(':') + 1:].split('|')
    winners = set(map(int, winners.split()))
    numbers = set(map(int, numbers.split()))
    matches = len(numbers & winners)
    score += int(2**(matches - 1))

print('Part 1:', score)
```

### Part 2

We don't need to calculate a score anymore, but instead for each card we need to
*duplicate* the N cards past the current one, where N is the number of matches
of the current card. So for example, if card 1 has 3 matches, we'll need to
duplicate card 2, 3 and 4. After doing this for all cards, we want to know how
many cards we end up with in total (originals and copies).

The peculiar thing is that we need to account for the copies as well, so each
time we process a card, *every single copy* of that card will generate a new
copy of the next N cards. Therefore, in general, the number of matches must be
multiplied by the number of copies of the card we have.

Let's keep track of the number of matches calculated in part 1 with a `list`:

```diff
+matches = []
+
 for line in fin:
     winners, numbers = line[line.find(':') + 1:].split('|')
     winners = set(map(int, winners.split()))
     numbers = set(map(int, numbers.split()))
-    matches = len(numbers & winners)
-    score += int(2**(matches - 1))
+    matches.append(len(numbers & winners))
```

The total score for part 1 could still be calculated inside the loop, or outside
the loop with a [`sum()`][py-builtin-sum] and a
[generator expression][py-gen-expr]:

```python
score = sum(int(2**(n - 1)) for n in matches)
print('Part 1:', score)
```

To keep track of the number of copies of each card, we can either use a `dict`
or a `list`. Since we already know that we have exactly `len(matches)` cards, we
can just use a `list`. Initially, we have `1` copy of each card:


```python
copies = [1] * len(matches)
```

For each card `i` we process, we need to add one copy of the next `matches[i]`
cards. Since the card itself could have already been copied, instead of adding
only one copy of the next cards, we'll add `copies[i]` instead. We can
[`enumerate()`][py-builtin-enumerate] the matches to have both the current
card's index and its number of matches ready. Other than that, it's just a
matter of a couple of `for` loops:

```python
for i, n in enumerate(matches):
    for j in range(i + 1, i + n + 1):
        copies[j] += copies[i]
```

The answer we are after is the total number of cards (copies included), so we
can just `sum()` up the number of copies:

```python
total = sum(copies)
print('Part 2:', total)
```


Day 5 - If You Give A Seed A Fertilizer
---------------------------------------

[Problem statement][d05-problem] — [Complete solution][d05-solution] — [Back to top][top]

### Part 1

Interesting problem today! And unfortunately also some kind of annoying input
parsing... so let's get it out of the way quickly.

Our input is split in "sections" that are delimited by empty lines. The first
section is simply a list of seeds (integers), while the other sections represent
"mappings". Each mapping has a header (first line) followed by a list of entries
that are 3-tuples of integers, one per line. With enough splitting and mapping,
we should be able to do it:

1. [`.split()`][py-str-split] the whole input in sections: simple enough, just
   need to split on two consecutive newlines (`'\n\n'`).
2. Parse the seeds, simply discarding the initial `'seeds:'`, `.split()` on
   whitespace and [`map()`][py-builtin-map] the numbers to `int`.
3. Parse the mappings one at a time: for each one, discard the header and then
   build a list of 3-tuples, again splitting on whitespace and converting to
   `int`.

This time I decided to write a function for input parsing, here it is:

```python
def parse_input(fin):
    sections = fin.read().split('\n\n')
    seeds    = sections[0]
    seeds    = list(map(int, seeds[6:].split()))
    mappings = []

    for section in sections[1:]:
        mapping = []
        mappings.append(mapping)

        for line in section.splitlines()[1:]:
            entry = tuple(map(int, line.split()))
            mapping.append(entry)

    return seeds, mappings
```

The entries in each mapping are given in the form `dst src length` meaning that
numbers in the source range `[src, src + length)` should map to the destination
range `[dst, dst + length)`. This simply means that if a number is in the source
range, a delta needs to be applied to bring it to the destination range: that
delta is simply `dst - src`. Since it's easier to work with source range and
delta, let's just convert each entry in the mapping accordingly right at the
moment of parsing:

```diff
 def parse_input(fin):
     # ... unchanged ...
         for line in section.splitlines()[1:]:
-             entry = tuple(map(int, line.split()))
-             mapping.append(entry)
+             dst, src, length = map(int, line.split())
+             mapping.append((src, src + length, dst - src))
     # ... unchanged ...
```

The input can now be easily parsed:

```python
fin = open(...)
seeds, mappings = parse_input(fin)
```

We now need to apply all the mappings (in order) to each of the `seeds` we have,
and find the smallest final value (after all mappings are applied). We can do
this quite easily:

- For each seed value `v`, iterate over all mappings one by one.
- For each entry `start, end, delta` in the mapping: if `v` is in the range
  `[start, end)`, then `v + delta` is the new value and we can stop scanning the
  entries of this mapping and proceed to the next one. Otherwise, `v` remains
  unchanged.

We can use `float('inf')` for an initial "infinite" positive value as minimum.
Putting the above into code we already have a complete solution:

```python
minimum = float('inf')

for v in seeds:
    for step in steps:
        for start, end, delta in step:
            if start <= v < end:
                v += delta
                break

    minimum = min(minimum, v)

print('Part 1:', minimum)
```

### Part 2

The `seed` numbers we were initially given now need to be interpreted
differently: they are pairs of the form `start_seed n`. Each pair represents the
seeds in the range `[start_value, start_value + n)`. The request is unchanged,
but now we have *a whole lot* more seeds to work with.

If we take a look at our input, we can see numbers that are easily in the
hundreds of millions. Needless to say, a bruteforce approach (simply checking
all seeds in each range), is going to be way too slow. We could maybe get away
with it a compiled programming language like C/C++/Go/Rust, but (1) we are stuck
with Python 3 and (2) that's just lame, we want to find the *real* solution!

The way to go about this is to write a new algorithm that is able to work with
*segments* instead of single values. If we think about it, for every input
segment `[A, B)`, for every source range `[C, D)` of a given mapping, we can
only have four different possibilities of overlap:

```none
(1) Complete           (2) Partial inner

        AxxxB              A----xxx----B
    C----xxx----D              CxxxD

(3) Partial right      (4) Partial left

    A----xxxB                  Axxx----B
        Cxxx----D          C----xxxD
```

While processing a segment, for each segment (source range) in the mapping, if
we have overlap, we can "extract" the overlapping and non-overlapping parts: the
overlapping part can be converted to the destination range by applying `delta`
on both its ends, while the non-overlapping parts can be kept to check if it
overlaps with other segments.

The first thing to do now is to convert the initial list of `seeds` into a list
of segments. We can do this easily if we iterate its elements pairwise:

```python
segments = []

for i in range(0, len(seeds), 2):
    start_value, n = seeds[i:i + 2]
    segments.append((start_value, start_value + n))
```

An alternative way to do this is through the use of [`zip()`][py-builtin-zip]:

```python
segments = []

for start_value, n in zip(seeds[::2], seeds[1::2]):
    segments.append((start_value, start_value + n))
```

The "trick" here is that `seeds[::2]` returns a list of the elements with *even*
indices, and `seeds[1::2]` returns a list of the elements with *odd* indices.
Using a [generator expression][py-gen-expr] we can also get rid of the loop:

```python
segments = [(v, v + n) for v, n in zip(seeds[::2], seeds[1::2])]
```

The algorithm to implement is now as follows:

- Start with a list of segments to convert.
- For each mapping:
  - Create an empty list of processed segments (to be converted by the next
    mapping).
  - For each segment we need to convert:
    - Check for overlaps with each segment of the mapping:
      - In case of overlap, extract the overlapping part, shift it by `delta`
        and move it to the list of processed segments. Then extract the
        non-overlapping part(s) and add them back to the list of segments to
        convert (they may overlap with other segments in this mapping).
      - In case of no overlap with any segment of the mapping, move the segment
        as is to the list of processed segments.
   - Take the list of processed segments as the new list of segments to convert.

Let's write a function to implement the above. In order to perform fast removal
and insertion from the beginning, we can use a [`deque`][py-collections-deque]
for both the list of segments to convert and the list of processed segments.

```python
from collections import deque

def solve(segments, mappings):
    for mapping in mappings:
        processed = deque()

        while segments:
            a, b = segments.popleft()

            for c, d, delta in mapping:
                partial_left  = c <= a < d
                partial_right = c < b <= d

                if partial_left and partial_right:
                    # Complete overlap:
                    #     a---b
                    # c-----------d
                    # Entire [a, b) segment is converted
                    processed.append((a + delta, b + delta))
                    break

                if partial_left:
                    # Partial left overlap:
                    #     a------b
                    # c------d
                    # [a, d) is converted
                    processed.append((a + delta, d + delta))
                    # [d, b) may overlap with other segments, keep it
                    segments.append((d, b))
                    break

                if partial_right:
                    # Partial right overlap:
                    # a------b
                    #     c------d
                    # [a, d) is converted
                    processed.append((c + delta, b + delta))
                    # [a, c) may overlap with other segments, keep it
                    segments.append((a, c))
                    break

                if a < c and b > d:
                    # Partial inner overlap:
                    # a-----------b
                    #     c---d
                    # [c, d) is converted
                    processed.append((c + delta, d + delta))
                    # [a, c) may overlap with other segments, keep it
                    segments.append((a, c))
                    # [d, b) may overlap with other segments, keep it
                    segments.append((d, b))
                    break
            else:
                # No overlap with any segment in this mapping, keep as is
                processed.append((a, b))

        segments = processed

    # We are done, the minimum possible final value will be the minimum start
    # of the final segments after conversion
    return min(s[0] for s in segments)
```

A careful reader may have noticed the `for: ... else:` construct above: the
`else:` branch is only entered if no `break` happens inside the `for`. Since we
break on any overlap, the `else:` is only entered when there is no overlap with
any segment of the mapping.

Quite nice! All that's left to do is call the above function and print the
result!

```python
segments = deque(segments)
minimum = solve(segments, mappings)
print('Part 2:', minimum)
```

If we really want, we could even use the function we just wrote to solve part 1:
after all, single numbers can be seen as segments of length `1`:

```python
segments = deque((s, s + 1) for s in seeds)
minimum = solve(segments, mappings)
print('Part 1:', minimum)
```

As an interesting plus, my solution for today's part 2 is `84206669`, which
contains the numbers 420, 666 and 69, LOL. 10 stars and counting!


Day 6 - Wait For It
-------------------

[Problem statement][d06-problem] — [Complete solution][d06-solution] — [Back to top][top]

### Part 1

Simple and fast problem today!

First of all, input parsing: we just have two lists of integers, so a simple
[`.split()`][py-str-split] plus [`map()`][py-builtin-map] will do after
splitting the input in lines and discarding the words at the start of each line.

```python
fin   = open(...)
lines = fin.readlines()
times = map(int, lines[0][9:].split())
dists = map(int, lines[1][9:].split())
```

We don't really need to make `times` and `dists` into lists or tuples as we will
iterate over them just once.

Now, without thinking too much about it, it seems simple enough to just run a
couple loops to solve the problem. For each pair of time `t` and distance `d`,
we can simply try and hold for any possible time between `1` and `t`, and see if
that wins the race. The remaining time we have to run will be `t` minus the time
we hold. Adding up all the times this happens gives us the number of different
ways to win the race, which we can accumulate as a product as requested.

To iterate over pairs of `times` and `dists` we can use
[`zip()`][py-builtin-zip].

```python
result = 1

for t, d in zip(times, dists):
    wins = 0

    for hold in range(1, t):
        if hold * (t - hold) > d:
            wins += 1

    result *= wins

print('Part 1:', result)
```

That was... easy! Wasn't it?

### Part 2

Now we are told that we need to discard all whitespace between input times and
distances, and only consider the single resulting big value for time and
distance. Needless to say, these values are pretty huge. Our part 1 solution is
still feasible, but would definitely benefit from some optimization.

If you think about it, the problem is quite simple, and we can express it with a
single mathematical formula. We have *t* time to win the race, and to win we
need to travel at least *d* distance. The time we have to run is equal to the
total time of the race (*t*) minus the time *x* we hold at the start. Therefore
we win if:

*x(t - x) ≥ d*

Where *x* is the hold time and *t - x* is the remaining time we have for
running. Simplifying the equation we get:

*-x<sup>2</sup> + tx ≥ d* ​​⇒ *-x<sup>2</sup> + tx - d ≥ 0*

Given the quadratic equation *-x<sup>2</sup> + tx - d = 0*, we can use the
[quadratic formula][wiki-quadratic-formula] to find the two solutions for *x*:

- *x<sub>min</sub> = (-t + √(t<sup>2</sup> - 4d)) / (-2) = (t - √(t<sup>2</sup> - 4d)) / 2*
- *x<sub>max</sub> = (-t - √(t<sup>2</sup> - 4d)) / (-2) = (t + √(t<sup>2</sup> - 4d)) / 2*

Since we want a non-negative result we then know that any value of *x* between
the minimum solution *x<sub>min</sub>* and the maximum solution
*x<sub>max</sub>* is valid.

Let's write a function to calculate the solution and directly give us the
answer. Since we are dealing with powers and square roots, the numbers we'll
calculate will be `float`, but we can use [`math.floor()`][py-math-floor] and
[`math.ceil()`][py-math-ceil] as needed to get integral values. Ideally we'd
want to calculate *x<sub>max</sub>* - *x<sub>min</sub>*, but to get the correct
value we will need to round down *x<sub>max</sub>*, round up *x<sub>min</sub>*
and subtract 1 from the result.

```python
from math import ceil, floor

def solve(t, d):
    delta = (t**2 - 4*d)**0.5
    xmin, xmax = (t - delta) / 2, (t + delta) / 2
    return ceil(xmin) - floor(xmax) - 1
```

We can now simplify the loop we wrote in part 1:

```python
answer = 1

for t, d in zip(times, dists):
    wins = solve(t, d)
    answer *= wins
```

And since all we are doing is calculating a product, we can use
[`math.prod()`][py-math-prod] with a [generator expression][py-gen-expr] to get
rid of the loop entirely:

```python
from math import prod

answer = prod(solve(t, d) for t, d in zip(times, dists))
```

We can also use `map()` and get rid of the generator expression (it will unpack
pairs of values from `times` and `dists` and pass them as two arguments for us):

```python
answer = prod(map(solve, times, dists))
print('Part 1:', answer)
```

Sweet! For part 2, all we need to do is remove whitespace between the input
numbers using [`.replace()`][py-str-replace] and do a single calculation:

```python
time = int(lines[0][9:].replace(' ', ''))
dist = int(lines[1][9:].replace(' ', ''))
answer = solve(time, dist)
print('Part 2:', answer)
```

Don't you love it when a single closed formula can solve the entire problem? I
definitely do.


Day 7 - Camel Cards
-------------------

[Problem statement][d07-problem] — [Complete solution][d07-solution] — [Back to top][top]

### Part 1

Input parsing seems quite easy today: we have a list of pairs where the first
one is a string and the second an integer. We can simply
[`.split()`][py-str-split] each input line, convert to `int` the second element
and be done with it. We are asked to somehow sort the hands in ascending order
according to their strength, so we need a way to remember the bet associated
with each hand: we can do this with a `dict` of the form `{hand: bet_value}`.
Let's build it:

```python
fin = open(...)

bets = {}
for line in fin:
    hand, bet = line.split()
    bets[hand] = int(bet)
```

Now, the strength of a hand can be calculated according to a few simple rules,
which basically only boil down to counting the number of occurrences of each
card in the hand to establish the type of the hand. For hands of the same type,
the stronger hand is the one with the highest card from left to right. For
example, given `AAAKK` and `AKAKA` (both full houses of aces over kings), the
first one is stronger since the second card is `A`, while the second card of the
second hand is `K`, which is lower than `A`.

The cards we are given may be digits between `2` and `9` as well as any of the
letters `TJQKA`. Given two hands that have the same counts of cards (i.e. none
is immediately higher than the other), it would be nice to split ties by simply
comparing the two hands as strings (e.g. `hand_a < hand_b`).

This would work very well for [ASCII][wiki-ascii] digits since `'0' < '1'`,
`'1' < '2'` and so on until `'8' < '9'`, but it does not work as for the letters
we have since e.g. `'A' < 'K'`, while we would want `A` to have a higher value.
To overcome this limitation and have easy comparisons, we can simply choose
other characters for cards higher than `9`. Instead of `TJQKA`, we can use
`ABCDE`, since `'A' > '9'`, `'B' > 'A'` and so on.

Let's translate all the letters in the hands we have from `TJQKA` to `ABCDE`: we
can do this easily with [`str.translate()`][py-str-translate] after building a
translation table with [`str.maketrans()`][py-str-maketrans].

```python
tbl = str.maketrans('TJQKA', 'ABCDE')
bets = {}

for line in fin:
    hand, bet = line.split()
    bets[hand.translate(tbl)] = int(bet)
```

The above loop be simplified with the help of [`map()`][py-builtin-map]:

```python
for hand, bet in map(str.split, fin):
    bets[hand.translate(tbl)] = int(bet)
```

And since all we are doing is creating a dictionary we could also use a
[dict comprehension][py-dict-comprehension].

```python
bets = {hand.translate(tbl): int(bet) for hand, bet in map(str.split, fin)}
```

*Okay... that might be a bit hard to read for the average Python programmer, but
it does look pretty cool.* I'll keep it in my solution's code.

Nice! Now the keys of the `bets` are strings representing hands, and have been
translated to be easily comparable. In case of hands of the same type (e.g. two
double pairs), we can use a normal Python string comparison to pick the highest.

How can we determine the kind of a hand? Well, by counting the number of equal
cards, of course. The [`Counter`][py-collections-counter] class from the
[`collections`][py-collections] module can do this for us easily. Once we know
the counts, it is pretty simple to establish the hand type. Let's see what
happens for each type:

| Type            | `hand`    | `Counter(hand)`                            | Sorted frequencies |
|-----------------|-----------|--------------------------------------------|--------------------|
| Five of a kind  | `'AAAAA'` | `{'A': 5}`                                 | `[5]`              |
| Four of a kind  | `'AAAAB'` | `{'A': 4, 'B': 1}`                         | `[4, 1]`           |
| Full house      | `'AAABB'` | `{'A': 3, 'B': 2}`                         | `[3, 2]`           |
| Three of a kind | `'AAABC'` | `{'A': 3, 'B': 1, 'C': 1}`                 | `[3, 1, 1]`        |
| Double pair     | `'AABBC'` | `{'A': 2, 'B': 2, 'C': 1}`                 | `[2, 2, 1]`        |
| One pair        | `'AABBC'` | `{'A': 2, 'B': 1, 'C': 1, 'D': 1}`         | `[2, 1, 1, 1]`     |
| High card       | `'ABCDE'` | `{'A': 1, 'B': 1, 'C': 1, 'D': 1, 'E': 1}` | `[1, 1, 1, 1, 1]`  |

From the above table, it should seem quite obvious that the only information we
need to establish the strength of a hand based on its type is the frequencies of
its cards. Given two cards, to know which one has the stronger type, we can
simply compare the counter frequencies in descending order! The first hand with
a has a higher frequency wins. In fact, we have `[5] > [4, 1]`,
`[4, 1] > [3, 2]`, `[3, 2] > [3, 2, 1]` and so on.

Let's write a function to calculate the strength of a given hand so that we can
later pass it as a `key=` function to [`sorted()`][py-builtin-sorted]. We can
first determine the strength of the hand type using the card frequencies
returned by `Counter(hand)`, then, in case of tie (same type), we can look at
the cards in the hand itself.

All we need to be able to sort a collection of hands is a tuple of the form
`(descending_frequencies, hand)`, where `descending_frequencies` is a tuple or
list of `int`, and `hand` is the string representing the hand itself. The
`sorted()` function will then first compare the frequencies and in case of tie
compare the hands. Given that both compare exactly the way we want with simple
Python comparison operators, this is all that's needed!

```python
from collections import Counter

def strength(hand):
    counter = Counter(hand).values()
    frequencies = sorted(counter, reverse=True)
    return (frequencies, hand)
```

We can now sort the keys of our `bets` dictionary using the above function as
`key=` and calculate the total as defined by the problem statement: sum the
products between the rank of each hand and its bid value. This can be easily
done with the help of [`enumerate()`][py-builtin-enumerate] providing `start=1`.

```python
ordered_hands = sorted(bets, key=strength)
total = 0

for rank, hand in enumerate(ordered_hands, 1):
    total += rank * bets[hand]
```

To simplify things, we can [`map()`][py-builtin-map] the hands to their bet
through `bet.get()`, and then use [`sum()`][py-builtin-sum] plus a
[generator expression][py-gen-expr] to compute the total:

```python
ordered_hands = sorted(bets, key=strength)
ordered_bets  = map(bets.get, ordered_hands)
total         = sum(rank * bet for rank, bet in enumerate(ordered_bets, 1))
```

We can also calculate the `total` with `map()` and
[`math.prod()`][py-math-prod]. In any case, we already have our answer!

```python
total = sum(map(prod, enumerate(ordered_bets, 1)))
print('Part 1:', total)
```

### Part 2

We are now supposed to treat the `J` cards as "jokers". A Joker can assume the
value of any other card, and when used in a hand, it will assume the value of
the card that maximizes the hand's strength. When breaking ties though, a `J`
should be considered weaker than a `2` (in other words, by itself, it is the
weakest card).

Since the Joker should be considered the weakest card when breaking ties, we
cannot use the previous translation of `TJQKA` to `ABCDE` anymore, but we can
use `A0CDE` instead, since `'0' < '2'`. Let's first translate the cards again.
We simply need to turn any `B` into a `0`:

```python
new_bets = {}
for hand, bet in bets.items():
    new_bets[hand.replace('B', '0')] = bet
```

The above can also be simplified using a dict comprehension:

```python
new_bets = {hand.replace('B', '0'): bet for hand, bet in bets.items()}
```

The initial request is the same: sort the hands in ascending order based on
their strength, then calculate the total winnings. However, calculating the
strength of a given hand became a bit harder, as we need to account for jokers
too.

Let's see what happens in case we have jokers in different scenarios:

- *Five of a kind*: `JJJJJ`, a five of a kind of jokers is simply the weakest
  five of a kind.

- *Four of a kind*: we can either have `XXXXJ` or `JJJJX`. In both cases,
  converting the jokers to the other card will give us a five of a kind.
  **Converting any of the jokers to any other card will just weaken the hand.**

- *Full house*: we can either have `XXXJJ` or `JJJXX`. In both cases, converting
  the jokers to the other card will give us a five of a kind. Again, converting
  any of the jokers to any other card will just weaken the hand.

- *Three of a kind*: we can either have `XXXYJ` or `JJJXY`. The best we can get
  is a four of a kind: convert `J` to `X` in the first case or to `Y` in the
  second case.

- *Double pair*: we can either have `XXYYJ` or `JJXXY`. The best we can get is a
  full house converting `J` to `X`.

- *One pair*: we can either have `XXYZJ` or `JJXYZ`. The best we can get is a
  three of a kind converting `J` to `X` in the first case or to any of the other
  cards in the second case.

- *High card*: `XYZWJ`... we can simply get a pair converting `J` to any of the
  other cards.

It should be clear enough from the above examples: whenever we have one or more
jokers available, the best thing to do is to make them all count as the card
with the highest frequency. **Doing anything else can only turn the hand into a
weaker type**, or at best keep it of the same type.

Following this logic, let's write another function to deal with hands that may
contain jokers (remember that we previously translated jokers to `0` to easily
compare hands of the same type).

```python
def strength_with_joker(hand):
    # Calculate frequencies for each card
    counter = Counter(hand)
    # Rremove jokers
    jokers = counter.pop('0', 0)
    # Sort frequencies in descending order
    freqs = sorted(counts.values(), reverse=True)
    # Convert all jokers to the card with the highest frequency
    freqs[0] += jokers

    return freqs, hand
```

The only edge case to consider is a five of a kind of jokers: in that case after
`counter.pop('0', 0)` we'll be left with nothing, so `frequs[0]` will fail. We
can simply detect this at the start:

```python
def strength_with_joker(hand):
    if hand == '00000':
        return [5], hand

    counter = Counter(hand)
    jokers  = counter.pop('0', 0)
    freqs   = sorted(counts.values(), reverse=True)
    freqs[0] += jokers

    return freqs, hand
```

The final result can be calculated in exactly the same as we did for part 1:

```python
ordered = map(new_bets.get, sorted(bets, key=strength_with_joker))
total   = sum(map(prod, enumerate(ordered, 1)))
print('Part 2:', total)
```

I really enjoyed this one! 14/50 stars.


Day 8 - Haunted Wasteland
-------------------------

[Problem statement][d08-problem] — [Complete solution][d08-solution] — [Back to top][top]

### Part 1

First problem of the year on a graph??? Hmm, almost.

Parsing the input is rather straightforward. First, let's extract the first line
of input representing the directions to follow, removing the final newline with
[`.rstrip()`][py-str-rstrip]:

```python
fin = open(...)
directions = fin.readline().rstrip()
```

To make it easier to work with, let's also convert the list of directions in
the directions to integers: `0` for `L` and `1` for `R`. We'll see why this is useful
in a moment.

```python
new_directions = []
for direction in directions:
    if direction == 'R':
        new_directions.append(1)
    else:
        new_directions.append(0)

directions = new_directions
```

The above can also be simplified by converting the boolean comparison result to
an integer since `int(True) == 1` and `int(False) == 0`:

```python
new_directions = []
for direction in directions:
    new_directions.append(int(direction == 'R'))

directions = new_directions
```

Let's just go one step further and convert the above to a
[generator expression][py-gen-expr]:

```python
directions = tuple(int(d == 'R') for d in directions)
```

Next, let's extract the network nodes from each of the following input lines
with simple [slicing][py-slicing] operations, since every line has exactly the
same format and node names are all 3 characters long. To represent the graph of
nodes we'll use a `dict` of the form `{source: (left, right)}`.

```python
# Skip empty line
fin.readline()

g = {}
for line in fin:
    # Lines are of the form: 'AAA = (BBB, CCC)\n'
    src, left, right = line[:3], line[7:10], line[12:15]
    g[src] = (left, right)
```

That could also be simplified to a single generator expression, or more
precisely a [dict comprehension][py-dict-comprehension] (*ok, I might be getting
too comfortable with these, but whatever*):

```python
fin.readline()
g = {l[:3]: (l[7:10], l[12:15]) for l in fin}
```

Now we have all we need to solve the problem. Counting the steps from `AAA` to
`ZZZ` is merely a matter of following the directions through our graph `g`.
Given the way we built `g`, going from one node to the next can be done with
`next_node = g[node][direction]`. All we need to do is follow the `directions`,
and since we may need to repeat them multiple times, we can use
[`itertools.cycle()`][py-itertools-cycle] to make our life easier:

```python
from itertools import cycle

node = 'AAA'
steps = 0

for d in cycle(directions):
    node = g[node][d]
    steps += 1
    if node == 'ZZZ':
        break
```

We can also use [`enumerate()`][py-builtin-enumerate] starting from `1` to count
the steps. Either way, we're done for part 1.

```python
node = 'AAA'

for d in enumerate(cycle(directions), 1):
    node = g[node][d]
    if node == 'ZZZ':
        break

print('Part 1:', steps)
```

### Part 2

Now things get significantly more complex, and to be fair probably a tad too
much for my liking. We are told to start from all nodes ending with `A` and
simultaneously follow the directions like we did for part 1 until all the nodes
we are on end with `Z`.

This may seem like a simple problem at first sight, but as it turns out it's all
except simple. Attempting the naïve solution (literally advancing N nodes in
parallel) will take us nowhere since the number of steps required is way too
large (for my input, it was in the order of 10<sup>13</sup>).

Why exactly am I saying that this is hard? Well, because **the key to
simplifying this problem is detecting cycles of nodes**, but:

1. It's hard to determine when a cycle is encountered.
2. We can encounter "temporary" cycles that only loop a few times before never
   being seen again.
3. Once in a cycle, we could encounter more than one Z-ending node per loop.

Firstly, we cannot simply tell that we are in a cycle if we reach the same node
twice. Simple directions and graphs can give us false cycles where we encounter
the same node multiple times before wandering off. For example, take the
following input (I use shorter node names for simplicity):

```
LLLLRRLLRRRLL

A = (Z, A)
Z = (A, A)
```

Starting from `A`, the nodes we'd visit would be: A, Z, A, Z, A, A, A, Z, A, A,
A, A, Z. We clearly encountered `Z` multiple times: after 2 steps, after 4
steps, after 8 and after 13. It's only after this that we'll keep visiting the
same pattern again, so we have a cycle of length 13 where a node ending with `Z`
is encountered four times per cycle at offsets 2, 4, 8 and 13.

This is clearer if we use pairs of the form `(node, i)` where `i` is the index
in the list of directions to follow. We have: (A 0), (Z 1), (A 2), (Z 3), (A 4),
(A 5), (A 6), (Z 7), (A 8), (A 9), (A 10), (A 11), (Z 12). After this, we have
exhausted the list of directions (of length 13), so we go back to: (A 0), (Z 1),
(A 2), and so on.

In other words, **a real loop is one where we encounter the same at the same
step in the given list of directions**. Therefore, a real loop must have a
length that is a multiple of the length of the given directions
(`len(directions)`).

Moreover, a situation like the following would also be completely valid:

```
L

A = (B, X)
B = (C, X)
C = (D, X)
D = (Z, X)
Z = (D, X)
```

Here the nodes we'd visit would be A, B, C, D, Z, D, Z, D, Z [...]. In this
case, we initially have a "useless" chain (A, B, C) leading us into the real
cycle (D, Z), so we also have an "initial offset" to account for.

This leads us into a situation similar (albeit more complex) to the one of
[2020 day 13 part 2][2020-d13-p2-crt], where the problem was solvable in a
purely mathematical way using the [Chinese Remainder Theorem][wiki-crt].

The problem statement does not help much, because the generic description we are
given does not exclude the above possibilities. In other words, we aren't
directly given any hint about special properties of the input that would
simplify things for us. However, as it turns out, **there definitely are special
properties that hold for all inputs of today's problem** and that reduce the
complexity by an order of magnitude.

This isn't really the first time this has happened, and it's common for AoC
puzzles. Nonetheless it left a lot of people (including me) wondering why their
very simple solution, which was making a lot of assumptions about the input,
would work. [Here's a thread][d08-reddit-thread] on the AoC subreddit where a
lot of people people shared their ideas.

Given the above (and most importantly given the fact that I really don't have
the time nor the willpower to solve the general problem), I will focus on
explaining the properties of the input that make this problem simpler to solve
and then verify them in my solution.

Let's use "A-nodes" to refer to the nodes ending with `A`, and "Z-nodes" to
refer to nodes ending with `Z`. A simpler version of the problem would include
the following constraints:

1. Following the given directions, each A-node only reaches one Z-node;
2. Continuing to follow the directions from such Z-node, it is guaranteed that
   we will loop back to it without encountering any other Z-node;
4. The length of the loop is equal to the number of steps required to reach the
   Z-node from the A-node.

If the above assumptions hold, this means that for each A-node we have exactly
one reachable Z-node, and we will encounter such Z-node once every N steps,
where N is equal to the length of the loop and also equal to the number of
initial steps from the A-node to the Z-node.

As we already saw, "looping back" does not simply mean encountering the same
node twice, but encountering it twice exactly after a number of steps that is a
multiple of the length of the given directions.

Let's write a function that given a starting A-node node finds and returns the
length of the loop to the first Z-node.

```python
def steps(g, node, directions):
    directions_iter = enumerate(cycle(directions), 1)

    for n1, d in directions_iter:
        node = g[node][d]
        if node[-1] == 'Z':
            # Z-node encountered for the first time, stop here
            break

    # Remember this Z-node
    znode = node

    # Continue following the path until we find another Z-node
    for loop_len, (n2, d) in enumerate(directions_iter, 1):
        node = g[node][d]
        if node[-1] == 'Z':
            # Second Z-node found (should be the same as the first)
            break

    # Check assumptions:
    #
    # 1) Each A-node should only reach one Z-node;
    # 2) Continuing from such node, we should loop back to it without
    #    encountering any other Z-nodes;
    # 3) The length of the loop is equal to the number of steps required to
    #    reach the Z-node from the A-node.
    #
    assert node == znode
    assert n1 % len(directions) == n2 % len(directions)
    assert n1 == loop_len

    return loop_len
```

Since we are assuming that the loop length is equal to the number of steps
needed to reach the Z-node in the first place, we can also use this function to
solve part 1. In fact, we are guaranteed to be able to reach `ZZZ` from `AAA` by
the problem statement, and since we are also verifying that only one Z-node is
reachable from any A-node, the `ZZZ` node is also guaranteed to be the only node
reachable from `AAA`.

Let's find the loop length for each A-node. First we need to find the A-nodes:
this can be done with a simple scan of the keys of our `g` graph dictionary
using [`filter()`][py-builtin-filter] plus a [`lambda`][py-lambda] or a
filtering generator expression:

```python
a_nodes = filter(lambda node: node[-1] == 'A', g)
# Or, equivalent:
a_nodes = (node for node in g if node[-1] == 'A')
```

For each starting A-node, we can calculate the loop length using the function we
just wrote. For part 1 we can simply pass `'AAA'`.

```python
steps_part1 = steps(g, 'AAA', directions)
print('Part 1:', steps_part1)
```

For any other A-node we can use `map()` or a generator expression:

```python
cycle_lengths = map(lambda a: steps(g, a, directions), a_nodes)
```

We are now essentially dealing with N cycles of different lengths: how can we
determine the number of steps needed for them to sync up? Pretty easy: just
calculate the [least common multiple][wiki-lcm] (LCM) of the lengths using the
[`math.lcm()`][py-math-lcm] function (available since Python 3.9). Since this
function takes an arbitrary number of arguments (but not an iterable), we can
[unpack][py-unpacking] the iterable when passing it as argument.

```python
steps_part2 = lcm(*cycle_lengths)
print('Part 2:', steps_part2)
```

Quite the conundrum today, can't say I enjoyed jumping through hoops and
verifying questionable input assumptions, but hey, that's what we get I guess!


Day 9 - Mirage Maintenance
--------------------------

[Problem statement][d09-problem] — [Complete solution][d09-solution] — [Back to top][top]

### Part 1

We are dealing with lists of integers. Parsing the input couldn't be easier. For
each line, we can simply [`.split()`][py-str-split] and
[`map()`][py-builtin-map] to `int`, a patter we should be familiar with by now.

```python
fin = open(...)

for line in fin:
    numbers = list(map(int, line.split()))
    # ...
```

We are told to keep calculating pairwise differences, so let's write a generator
function that does exactly this. There are different ways to do it, I will use
[`iter()`][py-builtin-iter] to turn the list into an iterator, then extract the
first number, and iterate over the next ones, yelding the differences one at a
time.

```python
def deltas(nums):
    it = iter(nums)
    prev = next(it)

    for n in it:
        yield n - prev
        prev = n
```

Sweet. Now, according to the rules, we can simply keep calling `deltas(nums)`
until all the deltas we calculate are `0`. For example:

```
0   3   6   9  12  15
  3   3   3   3   3
    0   0   0   0
```

Now we are told to append one more `0` to the last list (of all zeroes), and,
going backwards, find the next element of the original list. So, for example:

```
0   3   6   9  12  15   A  -->  0   3   6   9  12  15  [18]
  3   3   3   3   3   B    -->    3   3   3   3   3  [3]
    0   0   0   0  [0]     -->      0   0   0   0  [0]
```

The number *A* above is what we are looking for. Since we added a `0` at the end
of the last list, we know that *B - 3 = 0*, and therefore that *B = 0 + 3 = 3*.
Similarly, *A - 15 = B*, therefore *A = B + 15 = 0 + 3 + 15 = 18*.

It's easy to see how *A* is nothing more than the sum of the last elements of
each of the list we have.

Let's write a function that calculates it for us. We'll keep computing
differences until we have all zeroes, and accumulate the sum of the last
(rightmost) element each time. To check if all the elements of a list are `0`,
we can either write a good ol' loop, or we can use the [`all()`][py-builtin-all]
builtin: `all(x == 0 for x in nums)` will tell us if there is any number that is
not `0` in the list.

```python
def solve(nums):
    tot = 0

    while 1:
        tot += nums[-1]
        nums = list(deltas(nums))

        if all(x == 0 for x in nums):
            break

    return tot
```

Alternatively, we can invert the check using [`any()`][py-builtin-any] to verify
that our lis contains any non-zero value, and use it as the loop condition:

```diff
 def solve(nums):
     tot = 0

-    while 1:
+    while any(nums):
         tot += nums[-1]
         nums = list(deltas(nums))
-
-        if all(x == 0 for x in nums):
-            break

     return tot
```

For each input list, we now need to calculate the next number according to the
rules using the above function, then sum all of themse numbers up.

```python
total = 0

for line in fin:
    numbers = list(map(int, line.split()))
    total += solve(numbers)

print('Part 1:', numbers)
```

### Part 2

We now need to do a similar thing to find the *previous* number of each list.
Such number is found by first prepending a `0` to the last list (of all zeroes)
and working backwards.

For example:

```
A  10  13  16  21  30  45  -->  [5] 10  13  16  21  30  45
  B   3   3   5   9  15    -->    [5]  3   3   5   9  15
    C   0   2   4   6      -->     [-2]  0   2   4   6
      D   2   2   2        -->        [2]  2   2   2
       [0]  0   0          -->          [0]  0   0
```

This time, we know that:

- *2 - D = 0*
- *0 - C = D*
- *3 - B = C*
- *10 - A = B*

Therefore we have:

- *A = -B + 10*
- *= -(-C + 3) + 10*
- *= -(-(-D + 0) + 3) + 10*
- *= -(-(-(-0 + 2) + 0) + 3) + 10*
- *= -(-0 + 2) + 0 - 3 + 10*
- *= 0 - 2 + 0 - 3 + 10*
- *= 5*

It's a little bit harder to see this time, but what we are doing now is simply
calculating the sum of the leftmost numbers of each list, inverting the sign of
the ones in odd positions. Indeed, reordering the second to last steop above, we
have `10 - 3 + 0 - 2 + 0`.

We can therefore calculate this number as easily as how we did for part 1:
simply keep adding the first number of each list, multiplied by either `1` or
`-1` depending on the iteration.

```python
def solve(nums):
    tot_right = tot_left = 0
    sign = 1

    while any(nums):
        tot_right += nums[-1]
        tot_left += sign * nums[0]
        sign = -sign
        nums = list(deltas(nums))

    return tot_right, tot_left
```

As simple as that, we now have a function that returns both the previous number
and the next number of the original list, so we can calculate the answers for
both part 1 and 2 at the same time:

```python
total1 = total2 = 0

for line in fin:
    nums = list(map(int, line.split()))
    r, l = solve(nums)
    total1 += l
    total2 += r

print('Part 1:', total1)
print('Part 2:', total2)
```

---


*Copyright &copy; 2023 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2023-walkthrough
[d01]: #day-1---trebuchet
[d02]: #day-2---cube-conundrum
[d03]: #day-3---gear-ratios
[d04]: #day-4---scratchcards
[d05]: #day-5---if-you-give-a-seed-a-fertilizer
[d06]: #day-6---wait-for-it
[d07]: #day-7---camel-cards
[d08]: #day-8---haunted-wasteland
[d09]: #day-9---mirage-maintenance
[d10]: #day-10---
[d11]: #day-11---
[d12]: #day-12---
[d13]: #day-13---
[d14]: #day-14---
[d15]: #day-15---
[d16]: #day-16---
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
[d18-solution]: solutions/day18.py
[d19-solution]: solutions/day19.py
[d20-solution]: solutions/day20.py
[d21-solution]: solutions/day21.py
[d22-solution]: solutions/day22.py
[d24-solution]: solutions/day24.py
[d25-solution]: solutions/day25.py

[d08-reddit-thread]: https://www.reddit.com/r/adventofcode/comments/18dfpub
[2020-d13-p2-crt]:   https://github.com/mebeim/aoc/blob/master/2020/README.md#part-2---purely-mathematical-approach

[py-assert]:             https://docs.python.org/3/reference/simple_stmts.html#the-assert-statement
[py-cond-expr]:          https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-dict-comprehension]: https://peps.python.org/pep-0274/
[py-gen-expr]:           https://docs.python.org/3/reference/expressions.html#generator-expressions
[py-lambda]:             https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-generators]:         https://docs.python.org/3/howto/functional.html#generators
[py-slicing]:            https://docs.python.org/3/library/stdtypes.html#common-sequence-operations
[py-unpacking]:          https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-iter]:            https://docs.python.org/3/library/functions.html#iter
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-next]:            https://docs.python.org/3/library/functions.html#next
[py-builtin-range]:           https://docs.python.org/3/library/functions.html#range
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections]:             https://docs.python.org/3/library/collections.html#collections
[py-collections-counter]:     https://docs.python.org/3/library/collections.html#collections.deque
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-itertools-cycle]:         https://docs.python.org/3/library/itertools.html#itertools.cycle
[py-math-ceil]:               https://docs.python.org/3/library/math.html#math.ceil
[py-math-floor]:              https://docs.python.org/3/library/math.html#math.floor
[py-math-lcm]:                https://docs.python.org/3/library/math.html#math.ceil
[py-math-prod]:               https://docs.python.org/3/library/math.html#math.prod
[py-dict-values]:             https://docs.python.org/3/library/stdtypes.html#dict.values
[py-list-append]:             https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-set-intersection]:        https://docs.python.org/3/library/stdtypes.html#frozenset.intersection
[py-str-find]:                https://docs.python.org/3/library/stdtypes.html#str.find
[py-str-isdigit]:             https://docs.python.org/3/library/stdtypes.html#str.isdigic
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-replace]:             https://docs.python.org/3/library/stdtypes.html#str.replace
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[wiki-ascii]:             https://en.wikipedia.org/wiki/ASCII
[wiki-crt]:               https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Statement
[wiki-lcm]:               https://en.wikipedia.org/wiki/Least_common_multiple
[wiki-quadratic-formula]: https://en.wikipedia.org/wiki/Quadratic_formula
