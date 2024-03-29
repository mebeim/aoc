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
- *Day 10 - TODO*
- [Day 11 - Cosmic Expansion][d11]
- [Day 12 - Hot Springs][d12]
- [Day 13 - Point of Incidence][d13]
- [Day 14 - Parabolic Reflector Dish][d14]
- [Day 15 - Lens Library][d15]
- [Day 16 - The Floor Will Be Lava][d16]
- [Day 17 - Clumsy Crucible][d17]
- [Day 18 - Lavaduct Lagoon][d18]
- [Day 19 - Aplenty][d19]
- [Day 20 - Pulse Propagation][d20]
<!--
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

$x(t - x) \ge d$

Where $x$ is the hold time and $t - x$ is the remaining time we have for
running. Expanding the equation we get:

$-x^2 + tx \ge d \implies -x^2 + tx - d \ge 0$

Given the quadratic equation $-x^2 + tx - d = 0$, we can use the
[quadratic formula][wiki-quadratic-formula] to find the two solutions for $x$:

- $x_\text{min} = \frac{-t + \sqrt{t^2 - 4d}}{-2} = \frac{t - \sqrt{t^2 - 4d}}{2}$
- $x_\text{max} = \frac{-t - \sqrt{t^2 - 4d}}{-2} = \frac{t + \sqrt{t^2 - 4d}}{2}$

Since we want a non-negative result we then know that any value of $x$ between
the minimum solution $x_\text{min}$ and the maximum solution $x_\text{max}$ is
valid.

Let's write a function to calculate the solution and directly give us the
answer. Since we are dealing with powers and square roots, the numbers we'll
calculate will be `float`, but we can use [`math.floor()`][py-math-floor] and
[`math.ceil()`][py-math-ceil] as needed to get integral values. Ideally we'd
want to calculate $x_\text{max} - x_\text{min}$, but to get the correct value we
will need to round down $x_\text{max}$, round up $x_\text{min}$ and subtract 1
from the result.

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
simply compare the counter frequencies in descending order! The first hand that
has a higher frequency wins. In fact, we have `[5] > [4, 1]`, `[4, 1] > [3, 2]`,
`[3, 2] > [3, 1, 1]` and so on.

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


Day 11 - Cosmic Expansion
-------------------------

[Problem statement][d11-problem] — [Complete solution][d11-solution] — [Back to top][top]

### Part 1

We are going off on grid problems this year it seems. This time the grid is
relatively simple, and we won't even need it for much else than extracting some
coordinates. In fact, the only thing we care about is the position of each
galaxy (`#`) in the grid. As we need to find rows or columns that are empty
(composed only of empty space `.` and no galaxy `#`).

Let's take a top-down approach this time and leave the input parsing for later.

The problem statements asks us to alculate the [taxicab distance][wiki-taxicab]
between all possible pairs of galaxies in the grid. The taxicab distance between
two points $A$ and $B$ with coordinates $(r_A, c_A)$ and $(r_B, c_B)$ can be
calculated as $|r_A - r_B| + |c_A - c_B|$. It's not hard to notice that such
distance can be computed separately first on one axis (vertical) and then on the
other axis (horizontal), as the two components of the sum, namely the vertical
distance and the horizontal distance, are independent. The 2D problem we are
dealing with is therefore just two instances of the same 1D problem.

Here's an example 1D input (consisting of a single row):

```none
.##.#..#.#
```

Now, given that we are told that each space (`.`) expands to two spaces, and
therefore each empty column in reality corresponds to *two* empty columns, we
cannot simply calculate the distance right away with a handful of subtractions.
We first need to figure out the *real* coordinates of each galaxy after the
expansion. This can be done by scanning the only row we have from left to right
and keeping track of the real column index: each time a space (`.`) is crossed,
increment the index by two, while each time a galaxy (`#`) is encountered,
remember its index and then increment by one.

Let's write a [generator function][py-generators] for this:

```python
def expand(row):
    column = 0

    for char in row:
        if char == '#':
            yield column
            column += 1
        else:
            # Empty space expands: each '.' becomes two '.'
            column += 2
```

Simple enough. However, we are dealing with a *grid* of galaxies, so while it is
true that the above works for the simple 1D case, in the more general 2D case
there can be more than one galaxy on each column, for example:

```none
.##.#..#.#
##...#.##.
```

In order to account for this, we can build a list of counts for each column.
Let's do this with our actual input. The parsing couldn't be easier, just
`.read()` everyting and use [`str.splitlines()`][py-str-splitlines] to get a
list of strings. Then, scan it and keep track of the count of galaxies on each
column. While we are at it, we can also do the same for rows, since the
situation is analogous. As usual with grids, the
[`enumerate()`][py-builtin-enumerate] will help iterating over both the
row/column indices and the characters at the same time.

```python
with open(...) as fin:
    grid = fin.read().splitlines()

row_counts = [0] * len(grid)
col_counts = [0] * len(grid[0])

for r, row in enumerate(grid):
    for c, char in enumerate(row):
        if char == '#':
            row_counts[r] += 1
            col_counts[c] += 1
```

Now that we have our counts we can easily identify empty rows/columns: those
will be the ones where the count is zero. Let's modify the `expand()` function
we wrote earlier to take the counts into account. It's simple enough, for each
zero count we have a space, and for each non-zero count we will just need to
`yield` the same index as many times as the count.

```python
def expand(counts):
    real_index = 0

    for count in counts:
        if count > 0:
            # One or more galaxies, yield all of them
            for _ in range(count):
                yield real_index

            real_index += 1
        else:
            # Empty space expands: each '.' becomes two '.'
            real_index += 2
```

Now that we are able to calculate the expanded indices for both rows and
columns, we need to calculate the sum of all pairwise distances. How can we do
this? The simplest solution would be to iterate over all possible pairs of
indices using two nested loops, but we can do better.

Let's take for example the following case:

```
.##.#
##...
12101 <-- counts per column
```

As we can see, the above gives us the column counts `[1, 2, 1, 0, 1]`, which
translate to the expanded column indices `[0, 1, 1, 2, 5]` (the double `1` is
because of the two galaxies on the same column).

How do we calculate the sum of all the pairwise distances (which in this case
is nothing else than the sum of pairwise differences)? Simply iterate over
all possible pairs. In order to avoid counting pairs twice, we can write one
loop iterating from the firt to the last, and a second inner loop iterating from
the first to the current position of the outer loop:

```python
indices = [0, 1, 1, 2, 5]
total   = 0

for i in range(len(indices)):
    for j in range(0, i):
        total += indices[i] - indices[j]
```

What we just calculated is:

- $(1 - 0)$
- $+ (1 - 1) + (1 - 0)$
- $+ (2 - 1) + (2 - 1) + (2 - 0)$
- $+ (5 - 2) + (5 - 1) + (5 - 1) + (5 - 0)$

If we take a closer look, we can see that the above simplifies to:

- $1 - 0$
- $+ 2\cdot1 - (1 + 0)$
- $+ 3\cdot2 - (1 + 1 + 0)$
- $+ 4\cdot5 - (2 + 1 + 1 + 0)$

In general, for a given element $x_i$, the sum of the differences between $x_i$
and its predecessors will be:

$(x_i - x_{i-1}) + (x_i - x_{i-2}) + ... + (x_i - x_1) + (x_i - x_0)$

Which is equal to:

$i \cdot x_i - (x_{i-1} + x_{i-2} + ... + x_1 + x_0) = ix_i - \sum\limits_{j=0}^{i-1}x_j$

The first term is the `i`-th element multiplied by the number of elements
preceding it, and the second term is the sum of all the elements preceding it.

The above formula allows us to calculate the sum of pairwise differences in a
single linear sweep of the values from lowest to highest. All we have to do is
keep track of the index, and a partial sum of preceding values. Let's implement
it!

```python
def sum_pairwise_distances(values):
    total = partial_sum = 0

    for i, x in enumerate(values):
        total += i * x - partial_sum
        partial_sum += x

    return total
```

As simple as that. Now, all we need to do to solve the problem is first
`expand()` the row and column coordinates given the row and column counts, then
calculate the sum of pairwise distances for the rows and for the columns. Let's
write a functio to do it:

```python
def solve(row_counts, col_counts):
    return sum_pairwise_distances(expand(row_counts)) + \
           sum_pairwise_distances(expand(col_counts))
```

And the solution is one function call away!

```python
total = solve(row_counts, col_counts)
print('Part 1:', total)
```

### Part 2

The problem remains the same, but this time the expansion factor is 1000000,
meaning that each space `.` turns into 1000000 spaces. Thankfully, we already
have everything we need to solve the problem. We are already accounting for
expansion in the `expand()` function, we can simply add an additional
`multiplier` to make it more generic:

```diff
-def expand(counts):
+def expand(counts, multiplier):
     real_index = 0

     for count in counts:
         if count > 0:
             for _ in range(count):
                 yield real_index

             real_index += 1
         else:
-            real_index += 2
+            real_index += multiplier
```

The `solve()` function can be modified to take a `multiplier` parameter as well,
and pass it down:

```python
def solve(row_counts, col_counts, multiplier=2):
    return sum_pairwise_distances(expand(row_counts, multiplier)) + \
           sum_pairwise_distances(expand(col_counts, multiplier))
```

And we can now solve part 2:

```python
total2 = solve(row_counts, col_counts, 1000000)
print('Part 2:', total2)
```

### Optimized solution

The algorithm we wrote is already fast as is for a moderate number of galaxies
like the one we are dealing with, but it can technically be made faster by
getting rid of the `expand()` function and incorporating the calculations into
the `sum_pairwise_distances()`. This is what I did for my final solution.

The key takeaway is that instead of yielding the same $x_i$ value $n_i$ times
(where $n_i$ is the count), we can incorporate $n_i$ into the calculations. This
allows to solve the problem with a single linear scan of the counts, keeping
track of:

- The current real value $x_i$ taking into account the expansion multiplier (the
  same way as `expand()` does);
- The partial sum of the previous values, which can be expressed as the sum of
  each previous value multiplied by its count: $S_i = \sum\limits_{j=0}^{i-1} n_j x_j$;
- The number of previous values, which can be expressed as a partial sum of the
  counts: $N_i = \sum\limits_{j=0}^{i-1} n_j$.

The total then grows of $n_i(N_i x_i - S_i)$ each iteration. In
[my solution][d11-solution], `space` corresponds to $x_i$, `previous`
corresponds to $N_i$, and `partial_sum` corresponds to $S_i$.

Doing this, we get the following simplified function that computes the result
in significantly less iterations:

```python
def sum_distances(counts, multiplier):
    total = partial_sum = previous = space = 0

    for n in counts:
        if n:
            total       += n * (previous * space - partial_sum)
            partial_sum += n * space
            previous    += n
            space       += 1
        else:
            space += multiplier

    return total
```


Day 12 - Hot Springs
--------------------

[Problem statement][d12-problem] — [Complete solution][d12-solution] — [Back to top][top]

### Part 1

To parse the input data, we can simply [`.split()`][py-str-split] each line,
keep the first string as is, then split the second string on commas (`,`) and
[`map()`][py-builtin-map] every number to `int`.

```python
fin = open(...)

for line in fin:
    record, groups = line.split()
    groups = tuple(map(int, groups.split(',')))
```

It's clear that we are dealing with repeated occurrences of the same basic
problem, given one per line. There is a possibility to brute force each one,
which incidentally is what I did for part 1 in my
[original solution][d12-original] in a pretty inconvenient way, but that seems
like a pretty slow solution... let's think about it.

As it turns out, brute force might not be the answer, but it sure does get very
close to it. In fact, let's start implementing a brute-force approach, and see
what can be done to improve it.

For each `record`, the goal is to try and build the groups of `#` in all
possible ways that match the requested lengths (`groups`). Given an input record
and the list of group lengths we are looking for, we can iteratively build the
groups one at a time, scanning the record while keeping track of the remaining
characters to check, the remaining groups we still have to complete, and the
length of the current group we are building.

The logic for each step can then be implemented as follows:

1. If we encounter a `#` we can simply add `1` to the current group length.
2. If we encounter a `.` we can be in two situations:
   1. We were already building a group, so the current group length is positive.
      In such case, we can check the first of the remaining group lengths to
      build and verify that we correctly reached exactly that length. If so, we
      can continue, otherwise we made a mistake and can throw away this attempt.
   2. We were not building a group, so the current group length is zero. In such
      case, we can just keep going forward to find the next `#` or `?` where we
      can start building the next group.
3. If we encounter a `?` we can choose to turn it either in a `#` or a `.`, so
   we simply try both, applying the logic of *both* the above steps.

When do we stop? Well, of course when we get to the end of the record. Once we
do, there are two possibilities: either we built all groups correctly (so we
can count this arrangement in the total) or we did not (so we don't count this
arrangement).

If we built all groups correctly, we can be in one of two scenarios (either one
is good):

- No groups left to build and we are currently not building one (current group
  length is zero).
- Exactly one group left to build and we just completed it (the current group
  length is the same as the requested one).

Now that we have all the logic, we can implement it as a recursive function:

```python
def solve(record: str, groups: tuple[int], curlen=0) -> int:
    # Did we reach the end of the record?
    if not record:
        if len(groups) == 0 and curlen == 0:
            # We have no groups left to build and we aren't currently building
            # one (we did not encounter any '#' after building the last group)
            return 1
        if len(groups) == 1 and curlen == groups[0]:
            # We only have one group left to build and the current group we are
            # building has exactly the requested length
            return 1

        # We either have more than one group left to build or we are building
        # more groups than needed
        return 0

    char = record[0]
    total = 0

    if char == '#':
        # (1.) Current group gets one more '#'
        total += solve(record[1:], groups, curlen + 1)
    elif char == '.':
        if curlen == 0:
            # (2.1) Not currently building a group and cannot start here, keep going
            total += solve(record[1:], groups, 0)
        elif len(groups) > 0 and curlen == groups[0]:
            # (2.2) We completed this group correctly, advance to the next one
            total += solve(record[1:], groups[1:], 0)
    elif char == '?':
        # (1.) Try turning this into a '#'
        # Current group gets one more '#'
        total += solve(record[1:], groups, curlen + 1)

        # (2.) Try turning this into a '.'
        if curlen == 0:
            # (2.1) Not currently building a group and cannot start here, keep going
            total += solve(record[1:], groups, 0)
        elif len(groups) > 0 and curlen == groups[0]:
            # (2.2) We completed this group correctly, advance to the next one
            total += solve(record[1:], groups[1:], 0)

    return total
```

The advancement to the next record character is done by simply popping one from
the front of the string (`record[1:]`), and the same goes for the group lengths
(`groups[1:]`).

The above function should already solve the problem, but before using it we can
simplify it a little bit. Notice how in the case of `?` we are repeating the
logic we use for `#` and `.` (makes sense since we can turn `?` into any of `#`
or `.`). We can simply move the check for `?` in the two `if` statements above
and get rid of the duplicated logic:

```diff
 def solve(record: str, groups: tuple[int], curlen=0) -> int:
     # ... unchanged ...

-    if char == '#':
+    if char == '#' or char == '?':
         # (1.) Current group gets one more '#'
         total += solve(record[1:], groups, curlen + 1)
-    elif char == '.':
+    if char == '.' or char == '?':
         if curlen == 0:
             # (2.1) Not currently building a group and cannot start here, keep going
             total += solve(record[1:], groups, 0)
         elif len(groups) > 0 and curlen == groups[0]:
             # (2.2) We completed this group correctly, advance to the next one
             total += solve(record[1:], groups[1:], 0)
-    elif char == '?':
-        # (1.) Try turning this into a '#'
-        # Current group gets one more '#'
-        total += solve(record[1:], groups, curlen + 1)
-
-        # (2.) Try turning this into a '.'
-        if curlen == 0:
-            # (2.1) Not currently building a group and cannot start here, keep going
-            total += solve(record[1:], groups, 0)
-        elif len(groups) > 0 and curlen == groups[0]:
-            # (2.2) We completed this group correctly, advance to the next one
-            total += solve(record[1:], groups[1:], 0)

     return total
```

The solution we just built looks like brute force, but has a couple of smart
checks that make it avoid bad arrangements early on. For example, when
encountering a `.`, we only advance if we aren't building a group
(`curlen == 0`) of if we matched the current requested group length. Going
forward unconditionally would just mean reaching a bad final arrangement. This
already cuts down the search space a little bit.

We can implement one additional check to make it a little bit smarter: if we
ever find ourselves in a situation where the current group length is higher than
the next requested group length, or if we finish building the requested groups
but encounter any `#`, we can simply stop. This will prune away even more bad
arrangements early on:

```python
def solve(record: str, groups: tuple[int], curlen=0) -> int:
    # ... unchanged ...

    if len(groups) > 0 and curlen > groups[0]:
        # Building a group that is too long
        return 0

    if len(groups) == 0 and curlen > 0:
        # Building a group when we shouldn't be building any more
        return 0

    char = record[0]
    total = 0

    # ... unchanged ...
```

We can now run the `solve()` function for each line of input and accumulate the
total to get the answer we are looking for:

```python
total = 0

for line in fin:
    records, groups = line.split()
    groups = tuple(map(int, groups.split(',')))
    total += solve(records, groups)

print('Part 1:')
```

### Part 2

The problem remains the same, but each record now needs to be *quintupled* in
length: the string representing the record is repeated five times and four `?`
are added in between. The group lengths also need to be extended by simply
copying them five times.

Okay, we already have a solution, let's run it. We can use simple multiplication
to repeat the `groups`, while for the records we can use
[`str.join()`][py-str-join] to add `?` characters between five copies of the
original string.

```python
total1 = total2 = 0

for line in fin:
    records, groups = line.split()
    groups = tuple(map(int, groups.split(',')))

    total1 += solve(records, groups)

    records = '?'.join([record] * 5)
    groups  = groups * 5
    total2 += solve(records, groups)

print('Part 1:', total1)
print('Part 2:', total2)
```

Well, that couldn't have been easier! Shortest part two of the year??? Well no,
not really. We could stare at the terminal for ages, but the above script will
not terminate anytime soon. Indeed, while our "smart" brute force solution works
fine for small inputs, the problem complexity grows exponentially with the input
length, and there now are simply too many possible arrangements to test
extensively!

As it turns out though, we are very close to the solution. In fact, we are so
close that all we need to add is *two* lines of code... but let's see why first.

To drastically improve the current solution we need to realize one thing: if we
ever encounter the same situation more than once, we are doing unneeded work, as
we already previously computed the answer.

As an example, let's check the following input:

```
record: ??...??...### | groups: 1,1,3 | curlen: 0
```

We have two ways to compose the first group:

```
#....??...###
.#...??...###
```

In both cases, we continue advancing and reach the same scenario:

```
record: ..??...### | groups: 1,3 | curlen: 0
record: ..??...### | groups: 1,3 | curlen: 0

...??...### 1,3
```

This now means that we will try to solve the same problem twice. Needless to
say, solving the same subproblem multiple times is clearly not optimal. If we
can figure out a way to remember partial solutions we can check each time if a
solution already exists and avoid any further (useless) computation.

As it turns out, this can be easily achieved using a dictionary as a cache! The
dictionary keys will be tuples of the form `(record, groups, curlen)` and the
dictionary values will be the solution for that specific input. At the start,
before doing any calculation, we can check the dictionary to see if we already
have a solution, and if so return it right away. At the end of any calculation,
before returning the solution we'll store the calculated `total` in the
dictionary so that it can be used later.

The changes to our `solve()` function are minimal:

```python
CACHE = {}

def solve(record: str, groups: tuple[int], curlen=0):
    key = (record, groups, curlen)
    if key in CACHE:
        # Result was already calculated
        return CACHE[key]

    # ... actual computation here ...

    # Save result to reuse it later
    CACHE[key] = total
    return total
```

Congrats, we just solved a problem using [dynamic programming][wiki-dp]! Nothing
fancy, we just needed to add some [memoization][wiki-memoization].

What I just wrote above can be achieved with a single line of code (in case all
the function arguments are hashable, which is our case) using the
[`functools.cache`][py-functools-cache] (since Python 3.9) or
[`functools.lru_cache`][py-functools-lru_cache] decorators.

```python
from functools import cache

@cache
def solve(record, groups, curlen=0):
    # ... unchanged ...
```

The loop we wrote earlier now simply works *as is* without any change. However,
both the `@cache` and `@lru_cache` decorators provide a way to clear the cache
of the function, which can be done through `func.cache_clear()`. We don't
necessarily need to do it, but since technically each line of input is a
different problem, we can clear the cache each time to avoid wasting memory
caching unneeded solutions from previous problems.

```python
total1 = total2 = 0

for line in fin:
    records, groups = line.split()
    groups = tuple(map(int, groups.split(',')))
    total1 += solve(records, groups)

    records = '?'.join([record] * 5)
    groups  = groups * 5
    total2 += solve(records, groups)

print('Part 1:', total1)
print('Part 2:', total2)
```

24/50 stars and counting!


Day 13 - Point of Incidence
---------------------------

[Problem statement][d13-problem] — [Complete solution][d13-solution] — [Back to top][top]

### Part 1

Seems like we are dealing with *reflections* today. The input is a series of
rectangular character grids separated by empty lines. It should be simple to
parse it and transform each grid into a list of strings (rows): just a couple of
split operations will do, and [`str.splitlines()`][py-str-splitlines] comes in
handy.

```python
fin = open(...)
raw_grids = fin.read().split('\n\n')

for raw_grid in raw_grids
    grid = raw_grid.splitlines()
```

Since all we are doing is calling `.splitlines()` for each grid, we can use
[`map()`][py-builtin-map] instead:

```python
for grid in map(str.splitlines, raw_grids):
    # ... solution code here ...
```

OK... now, what do we do with those? Well, we find reflections of course! The
problem statement seemed a bit hard to understand today, but in short, all we
need to do for each grid is find the horizontal line at which we get a
reflection of all the rows either from the bottom or the top (whichever is
closer), and the same goes for vertical lines.

As an example, take the following grids:

```
 #....#..#                                ###.##.#.#
 ..##..###     .#.....     ##..###.#.    v.#..##.###v
v#####.##.v    ####..#     .#....#.#.    ^.#..##.###^
^#####.##.^   v# # ##.v    .#.#.##..#     ###.##.#.#
 ..##..###    ^# # ##.^   v# ## #.##.v    ...###.#.#
 #....#..#     ####..#    ^# ## #.##.^    #.#.#.#.#.
```

The horizontal reflection lines for these grids are in between the rows marked
with `v` and `^`. Not all the rows must be reflected, in fact, it is enough for
only one set of rows from either the top or the bottom to be fully reflected,
and the others can be ignored. In fact, the only "perfect" reflection happening
above is in the first grid. The same reasoning applies to vertical reflections.

For all the grids we have we need to find reflections and count the rows above
(for horizontal reflections) or to the left (for vertical reflections). How can
we do this? The grids are small enough that there is no need to come up with
insanely optimized solutions: a simple scan through the grid choosing all
possible sizes for the reflection will do just fine.

Let's write a function to solve this for horizontal reflections, since it's
easier to work with rows (they are simple strings) than columns. The maximum
size of a horizontal reflection (expressed in number of rows) is `h // 2`, where
`h` is the height of the grid. For each possible reflection size from `1` to
`h // 2`, we can either have a reflection at the top or at the bottom of the
grid. It will be enough to make a couple of slice operations and comparisons to
detect it.

Once we have two chunks of rows obtained through slicing (e.g. `grid[a:b]` and
`grid[c:d]`), to check whether they are a reflection of each other we can simply
reverse one of the two (`[::-1]`) and compare it with the other. Since comparing
two lists means comparing their contents, we'll get a match only if both lists
have the same length and contain equal strings.

```python
def find_reflections(grid):
    height = len(grid)

    for size in range(1, height // 2 + 1):
        # Check for reflection of the top size rows
        top = grid[:size]
        bottom = grid[size:2 * size]

        if top == bottom[::-1]:
            return size

        # Check for reflection of the bottom size rows
        top = grid[height - 2 * size:height - size]
        bottom = grid[height - size:]

        if top == bottom[::-1]:
            return height - size

    # No horizontal reflection found
    return 0
```

Technically, doing `bottom = grid[size:2 * size]` and then `bottom[::-1]`
immediately after performs a copy twice. We could simplify this to a single
slice doing `grid[2 * size - 1:size - 1:-1]`, though it's a bit hard to read.
The same goes for the second bottom slice operation which can be expressed as
`grid[height - 1:height - size - 1:-1]`. I always found 3-argument slices pretty
weird and counter-intuitive. In any case, uNfortunately we are always performing
a copy when slicing... that's a shortcoming of the language that does not allow
to perform non-copying slices, but again since grids are small this is no big
deal.

What about vertical reflections? Columns seem much more annoying to deal with. A
clever way to get around the problem is [transposing][wiki-transpose] the grid
and checking for horizontal reflections again. This isn't in general the best
solution, but for small lists like the ones we are dealing with it's no big
deal. Let's write a function to transpose a grid (list of strings):

```python
def transpose(grid):
    newgrid = []

    for c in range(len(grid[0])):
        row = []
        for r in range(len(grid)):
            row.append(grid[r][c])

        newgrid.append(''.join(row))

    return newgrid
```

The above can be simplified quite a lot, first by replacing the inner loop with
a [generator expression][py-gen-expr], since all we are doing is building a
list:

```python
def transpose(grid):
    newgrid = []

    for c in range(len(grid[0])):
        row = [grid[r][c] for r in range(len(grid))]
        newgrid.append(''.join(row))

    return newgrid
```

We are now iterating over all the rows of the grid at the same time, each
iteration extracting the `c`-th element of each of them. This is exactly what
the [`zip()`][py-builtin-zip] already does...

```python
def transpose(grid):
    newgrid = []

    for row in zip(*grid):
        newgrid.append(''.join(row))

    return newgrid
```

And finally, we can do away with the loop by using [`map()`][py-builtin-map] to
join the rows into strings:

```python
def transpose(grid):
    return list(map(''.join, zip(*grid)))
```

Okay, it took more time to write a simple grid transposition than solving the
actual problem :') but we are done. Now it's only a matter of applying the same
function to all the grids in our input. Continuing from the initial input
parsing code we wrote, we now have:

```python
total = 0

for grid in map(str.splitlines, raw_grids):
    total += 100 * find_reflections(grid)
    total += find_reflections(transpose(grid))

print('Part 1:', total)
```

Onto part 2!

### Part 2

We are now told that in addition to the reflections we just found, there also
are additional reflections happening, where *all cells except one* match. This
means that looking for reflections, we will not get a match by simply comparing
the two sides like we are doing now. For example:

```
v###.#.##.v
^#####.##.^
```

The minimal grid shown above has a horizontal reflection where all cells match
except one (the first `.` on the first row). If we turn that `.` into a `#` we
get a real reflection.

We could try all possible combinations by flipping each cell once and checking
for reflections, but that'd be awfully slow (and also awful in general). What we
can do instead is count the number of differences after extracting the two sides
of the reflection. If there are zero different cells we have a reflection that
is good for part 1, otherwise if there is exactly one we have a reflection that
is good for part 2.

Let's write a function to count the number of differences given two lists of
strings. We will assume that the second list has already been flipped over so
that we can easily iterate over both lists using [`zip()`][py-builtin-zip]:

```python
def count_differences(a, b):
    diff = 0
    for linea, lineb in zip(a, b):
        for chara, charb in zip(linea, lineb):
            if chara != charb:
                diff += 1

    return diff
```

We could theoretically stop counting whenever we reach a `diff` higher than `1`
since we won't consider that a reflection in any case. Furthermore, the inner
loop can be simplified with a [`sum()`][py-builtin-sum] plus a generator
expression:

```python
def count_differences(a, b):
    diff = 0
    for linea, lineb in zip(a, b):
        diff += sum(chara != charb for chara, charb in zip(linea, lineb))
        if diff > 1:
            break

    return diff
```

Good. We can now modify the `find_reflections()` function that we wrote for part
1 to use `count_differences()` and return both lines of reflections.

```python
def find_reflections(grid):
    height = len(grid)
    perfect = imperfect = 0

    for size in range(1, height // 2 + 1):
        # Check for reflection of the top size rows
        top = grid[:size]
        bottom = grid[size:2 * size]
        diff = count_differences(top, bottom[::-1])

        if diff == 0:
            perfect = size
        elif diff == 1:
            imperfect = size

        # Check for reflection of the bottom size rows
        top = grid[height - 2 * size:height - size]
        bottom = grid[height - size:]
        diff = count_differences(top, bottom[::-1])

        if diff == 0:
            perfect = height - size
        elif diff == 1:
            imperfect = height - size

    return perfect, imperfect
```

We can also stop as soon as we find both the perfect and the imperfect
reflection:

```diff
 def find_reflections(grid):
     height = len(grid)
     perfect = imperfect = 0

     for size in range(1, height // 2 + 1):
         # Check for reflection of the top size rows
         top = grid[:size]
         bottom = grid[size:2 * size]
         diff = count_differences(top, bottom[::-1])

         if diff == 0:
             perfect = size
         elif diff == 1:
             imperfect = size
+
+        if perfect and imperfect:
+            break

         # Check for reflection of the bottom size rows
         top = grid[height - 2 * size:height - size]
         bottom = grid[height - size:]
         diff = count_differences(top, bottom[::-1])

         if diff == 0:
             perfect = height - size
         elif diff == 1:
             imperfect = height - size
+
+        if perfect and imperfect:
+            break

     return perfect, imperfect
```

And finally, we can integrate both part 1 and part 2 calculations in the same
main loop:

```python
total1 = total2 = 0

for grid in map(str.splitlines, grids):
    perfect, imperfect = find_reflections(grid)
    total1 += 100 * perfect
    total2 += 100 * imperfect

    perfect, imperfect = find_reflections(transpose(grid))
    total1 += perfect
    total2 += imperfect

print('Part 1:', total1)
print('Part 2:', total2)
```


Day 14 - Parabolic Reflector Dish
---------------------------------

[Problem statement][d14-problem] — [Complete solution][d14-solution] — [Back to top][top]

### Part 1

Another day dealing with rectangular character grids. This time we need to
transform the grid we are given though, so that's going to be fun.

Parsing the input is a walk in the park, just read everything and split the
lines into a list, and while we are at it also calculate the grid height and
width for later:

```python
with open(...) as fin:
    grid = fin.read().splitlines()
    height, width = len(grid), len(grid[0])
```

We have two main kinds of cells in our grid: cubic rocks `#`, which stay fixed
in place, and spherical rocks `O`, which we need to move around. It seems easier
to represent things using [sparse matrices][wiki-sparse-matrix] instead of a
single conventional matrix (the `grid` we just created above).

Let's create two sparse matrices, one for fixed rocks and one for movable rocks.
We'll use sets of coordinates as sparse matrices since we don't really need to
associate coordinates with any kind of value. As usual,
[`enumerate()`][py-builtin-enumerate] comes in handy to easily iterate over both
cells and grid coordinates.

```python
fixed   = set()
movable = set()

for r, row in enumerate(grid):
    for c, char in enumerate(row):
        if char == '#':
            fixed.add((r, c))
        elif char == 'O':
            movable.add((r, c))
```

We now need to move all the movable rocks (`O`) up, sort of like swiping UP in
the game [2048][wiki-2048]. We can do this by creating a new sparse matrix and
iterating over the coordinates in `movable` in ascending order (since the rocks
that need to be moved first are the ones at the top). We can use the
[`sorted()`][py-builtin-sorted] built-in to do this.

For each movable rock we have, starting from its original position, move one
cell up at a time, and stop when the top is reached (`r < 0`) or at the first
rock encountered, then add the new coordinates to the new movable matrix. We can
either encounter rocks that are fixed or that are in the new matrix.

```python
def move(fixed, movable):
    new_movable = set()

    for r, c in sorted(movable):
        # Go up one cell at a time until we encounter another (fixed or movable) rock
        r -= 1
        while r >= 0 and (r, c) not in fixed and (r, c) not in new_movable:
            r -= 1

        # Given that the above condition is checked only after decrementing r,
        # we will always be one step further up than needed, so use r + 1 here
        new_movable.add((r + 1, c))

    return new_movable
```

Since we only care about the ordering of the `r` coordinate, we can use a `key=`
function to extract only that coordinate and speed the sorting up a little bit.
The [`operator.itemgetter()`][py-operator-itemgetter] function seems a bit
cleaner than writing a [`lambda`][py-lambda] function in this case:

```diff
-    for r, c in sorted(movable):
+    for r, c in sorted(movable, key=itemgetter(0)):
```

Secondly, we are doing two membership checks at a time: `in fixed` and
`in new_movable`. We can simplify things by starting with
`new_movable = fixed.copy()` and checking only for `in new_movable`. At the end
of the function we can then remove all the fixed coordinates at once with a
[set difference][py-set-difference]. This may seem slower, but in this case the
operations of copying a set and computing a set difference, which are
implemented in *native* code ([here][misc-cpython-set-difference] for the
curious), are way faster than all the double membership checks we are doing in
Python code.

```diff
 def move(fixed, movable):
-    new_movable = set()
+    new_movable = fixed.copy()

     for r, c in sorted(movable, key=itemgetter(0)):
         r -= 1
-        while r >= 0 and (r, c) not in fixed and (r, c) not in new_movable:
+        while r >= 0 and (r, c) not in new_movable:
             r -= 1

         new_movable.add((r + 1, c))

-    return new_movable
+    return new_movable - fixed
```

We almost have all we need. After applying the `move()` function above to our
set of movable rocks, we then need to compute the sum of their distance from the
bottom of the grid:

```python
new_movable = move(fixed, movable)
total = 0

for r, _ in new_movable:
    total += height - r
```

Since all we are doing is summing things up, we can simplify the above using the
classic [`map()`][py-builtin-map] + [`sum()`][py-builtin-sum] combo with a
`lambda`:

```python
new_grid = move(fixed, movable)
total = sum(map(lambda rc: height - rc[0], new_grid))
print('Part 1:', total)
```

### Part 2

We now need to move the movable rocks in all four directions: first up, then
left, then down, and finally right. These 4 consecutive move operations are
called a "spin", and we need to perform 1000000000 (*one billion!*) spins before
calculating the final sum.

First of all: we know how to move rocks up, as we just wrote a function to do
it, but what about down, left, and right? Well, we don't necessarily need to
complicate things by writing a new function or changing the current one.
Instead, we can simply *rotate our coordinates* and apply the same `move()`
function each time.

Rotating the grid 90 degrees clockwise and moving everything up is equivalent to
moving everything left, the only difference is that we then need to rotate it
back 90 degrees counter-clockwise after the movement. However, since for each
"spin" we need to move things 4 times (once per direction), we can simply rotate
90 degrees clockwise each time, and end up in the same direction as we started.

Writing a rotation function is straightforward: row indices become column
indices, and column indices become row indices (but from the bottom, not the
top, so we need to invert them). Let's write a function to rotate our sparse
matrices:

```python
def rotate_90(coords, height):
    rotated = set()
    for r, c in coords:
        rotated.add((c, height - r - 1))
    return rotated
```

We can also simplify the above down to a single
[generator expression][py-gen-expr]:

```python
def rotate_90(coords, height):
    return set((c, height - r - 1) for r, c in coords)
```

Okay, now to the real problem: needless to say, we won't get anywhere with a
literal implementation that spins *one billion times*. That's the equivalent of
4 billion rotations and 4 billion movements. It's going to take ages. We could
*maybe* get away with it in a compiled language such as C/C++/Rust/Go, but
nonetheless, there must be a smarter solution!

What if, after some arbitrary number of spins, we find ourselves in the same
configuration as the start? That would mean that the possible configurations are
only a finite amount, and that we can only cycle through them. Once a cycle is
found, a bit of math is all that's needed to determine the final result.

Let's write a function that keeps applying spins until a cycle is identified. In
order to check if we already saw a configuration, and at which iteration, we can
use a dictionary of the form `{seen_set: iteration_number}`. As we are working
with sets, and sets are not hashable (as they are mutable), we will need to turn
any set into an immutable [`frozenset`][py-frozenset] first before adding it as
key in a dictionary.

```python
def spin(fixed, movable, height, width):
    seen = {frozenset(movable): 0}

    for i in range(1, 1000000000 + 1):
        # Move up, rotate
        movable = rotate_90(move(fixed, movable), height)
        fixed   = rotate_90(fixed, height)
        # Move left, rotate
        movable = rotate_90(move(fixed, movable), width)
        fixed   = rotate_90(fixed, width)
        # Move down, rotate
        movable = rotate_90(move(fixed, movable), height)
        fixed   = rotate_90(fixed, height)
        # Move right, rotate
        movable = rotate_90(move(fixed, movable), width)
        fixed   = rotate_90(fixed, width)

        # Freeze the set and check if we already saw it
        key = frozenset(movable)
        if key in seen:
            break

        # Didn't see this set yet, take note of the current iteration
        seen[key] = i

    # ...
```

The above function can be simplified a bit, but we first need to figure out how
to compute the final result once we identify a cycle. We can sketch the
situation up with some ASCII-art:

```
    Iteration  0     1     2     3     4     5
Configuration  A --> B --> C --> D --> E --> F
                           ^                 |
                           |                 |
                           +-----------------+
```

In the above example, at iteration 6 we find ourselves with the same
configuration (`C`) as iteration 2. At this point, we are back at the start of
the cycle, and if we keep going we'll see `D`, `E`... and so on.

To find the iteration at which the cycle starts, we can simply check the values
in `seen`. The cycle length is then simply the current iteration minus the start
iteration (in the above example it's 4). The number of iterations remaining is
one billion minus the cycle start iteration. Once we have these values, we can
calculate the final step (inside the cycle) with a modulo operation.

Let's complete the function with this in mind. We'll return the final solution
right away.

```python
def spin(fixed, movable, height, width):
    seen = {frozenset(movable): 0}

    for i in range(1, 1000000000 + 1):
        for h in (height, width, height, width):
            movable = rotate_90(move(fixed, movable), h)
            fixed   = rotate_90(fixed, h)

        key = frozenset(movable)
        if key in seen:
            break

        seen[key] = i

    cycle_start = seen[key]
    cycle_len   = i - cycle_start
    remaining   = iterations - cycle_start
    final       = remaining % cycle_len + cycle_start

    # Find the configuration corresponding to the final iteration
    for key, i in seen.items():
        if i == final:
            break

    # Calculate final result as we did for part 1
    return sum(map(lambda rc: height - rc[0], key))
```

There are a couple of optimizations to apply here:

1. As fixed rocks don't move, we will only ever have 4 different `fixed`
   configurations possible (one per 90-degree rotation), therefore we can
   pre-calculate them.
2. Instead of iterating over `seen` to find the configuration corresponding to
   the `final` iteration, we can [ab]use it to also store the inverse mapping
   `{i: key}`. After all, there is no risk of confusing things as one is an
   integer and the other is a `frozenset`, and storing a reference is a
   lightweight operation that does not perform a copy.

```diff
 def spin(fixed, movable, height, width):
     seen = {frozenset(movable): 0}
+
+    cache = [(fixed, height)]
+    for _ in range(3):
+        fixed = rotate_90(fixed, height)
+        cache.append((fixed, width))
+        height, width = width, height

     for i in range(1, 1000000000 + 1):
-        for h in (height, width, height, width):
-            movable = rotate_90(move(fixed, movable), h)
-            fixed   = rotate_90(fixed, h)
+        for fixed, height in cache:
+            movable = rotate_90(move(fixed, movable), height)

         key = frozenset(movable)
         if key in seen:
             break

         seen[key] = i
+        seen[i]   = key

     cycle_start = seen[key]
     cycle_len   = i - cycle_start
     remaining   = iterations - cycle_start
     final       = remaining % cycle_len + cycle_start

-    # Find the configuration corresponding to the final iteration
-    for key, i in seen.items():
-        if i == final:
-            break
+    key = seen[final]

     # Calculate final result as we did for part 1
     return sum(map(lambda rc: height - rc[0], key))
```

We can now take our shiny `spin()` function *for a spin* and solve part 2:

```python
total = spin(fixed, movable, height, width)
print('Part 2:', total)
```


Day 15 - Lens Library
---------------------

[Problem statement][d15-problem] — [Complete solution][d15-solution] — [Back to top][top]

### Part 1

Today we need to implement a (rather simple) custom
[hash function][wiki-hash-func]. The problem asks us to work with ASCII values
of the input strings, so it seems appropriate to read the input in binary mode
(`'b'`) and work with `bytes` instead of `str`, since iterating over `bytes`
objects yields integers corresponding to the byte values, and in case of ASCII
characters those are exactly the ASCII values we want.

To parse the input we only need to [`.strip()`][py-bytes-strip] away unwanted
newlines and [`.split()`][py-bytes-split] on commas to obtain a list of `bytes`
objects:

```python
with open(..., 'rb') as fin:
    strings = fin.read().strip().split(b',')
```

Now we can write a function to calculate the hash of an input string. The rules
are very simple, so it's only a few lines of code:

```python
def aoc_hash(s):
	h = 0
	for c in s:
		h = ((h + c) * 17) % 256
	return h
```

And finally, [`map()`][py-builtin-map] each string to its hash and
[`sum()`][py-builtin-sum] up all the hashes:

```python
total = sum(map(aoc_hash, strings))
print('Part 1:', total)
```

That was fast!

### Part 2

We now need to implement a hashmap with some... weird (to say the least) rules.
Each string in the input can be in one of two forms:

- `key-` meaning "remove `key`".
- `key=v` meaning "set the value associated with `key` to `v`".

The hashmap has 256 slots numbered from `0` to `255` that are lists. Each slot
contains entries of the form `(key, value)`. The hashmap behaves as follows:

- When a key is removed from the, the corresponding `(key, value)` entry is
  removed from the slot corresponding to the key hash (obtained using the
  hashing function we just wrote for part 1).
- When a key is added, it is inserted at the end of the slot corresponding to
  the key hash. However, in case the key was already present in such slot, the
  position of its corresponding entry remains unchanged, but the value is
  replaced with the new one, so an entry `(key, oldval)` becomes
  `(key, newval)`.

Without much thinking, we can quite literally implement the above instructions
as is. Let's create a `HashMap` class just for the sake of it. We will use a
[`defaultdict`][py-collections-defaultdict] as the backing store of slots, just
to avoid having to deal with the insertion of empty lists when a given slot is
accessed the first time.

```python
from collections import defaultdict

class HashMap:
    def __init__(self):
        self.backing_store = defaultdict(list)
```

In both the removal and the insertion case, the old entry needs to be removed
from the slot. The only difference is that in the insertion case, a new entry
is also inserted in the slot at the same index as the existing one (if any).
Let's implement an internal method to find the entry associated with a key in a
given slot and [`.pop()`][py-list-pop] it away. We'll return the index in case
the entry was found and popped, or `-1` in case no entry was found.

It'd be nice to simply call [`slot.index(key)`][py-list-index], but the slots
contain entries of the form `(key, v)`, so we cannot simply look for a `key`, so
we'll need to iterate them manually. The [`enumerate()`][py-builtin-enumerate]
built-in is always helpful:

```python
class HashMap:
    # ... continued from above ...

    def _find_and_pop(self, slot, key):
        for i, (k, _) in enumerate(slot):
            if k == key:
                slot.pop(i)
                return i

        return -1
```

Awesome, now we need a `.remove(key)` method and an `.insert(key, value)`
method. In case of removal we just need to find the slot and use
`self._find_and_pop()`, while in case of insertion we also need to `.insert()`
the new `(key, value)` entry either at the same index the old entry was popped
or at the end of the slot.

Here's the code:

```python
class HashMap:
    # ... continued from above ...

    def remove(self, key):
        h    = aoc_hash(key)
        slot = self.backing_store[h]
        self._find_and_pop(slot, key)

    def insert(self, key, value):
        h    = aoc_hash(key)
        slot = self.backing_store[h]
        i    = self._find_and_pop(slot, key)

        if i != -1:
            slot.insert(i, (key, value))
        else:
            slot.append((key, value))
```

It's worth noting that in general using a list/array for things such as
insertion and removal of elements right in the middle is not a good idea as the
operation generally needs to rearrange the whole list after inserting/removing
the element. Since we are doing a linear scan, a [linked list][wiki-linked-list]
would be perfect for this. However, we are dealing with very small lists and
implementing a linked list in Python would be far *slower* in such case, so
let's stick to a normal `list`.

Since the first two operations of `.remove()` and `.insert()` are the same, we
could also move them into `._find_and_pop()`, making it return both the slot and
the index:

```diff
 class HashMap:
     # ...

     def _find_and_pop(self, key):
+        slot = self.backing_store[aoc_hash(key)]
+
         for i, (k, _) in enumerate(slot):
             if k == key:
                 slot.pop(i)
-                return i
+                return slot, i

-        return -1
+        return slot, -1

     def remove(self, key):
-        h    = aoc_hash(key)
-        slot = self.backing_store[h]
-        self._find_and_pop(slot, key)
+        self._find_and_pop(key)

     def insert(self, key, value):
-        h    = aoc_hash(key)
-        slot = self.backing_store[h]
-        i    = self._find_and_pop(slot, key)
+        slot, i = self._find_and_pop(key)

         if i != -1:
             slot.insert(i, (key, value))
         else:
             slot.append((key, value))
```

That's about it. Now we can instantiate our `HashMap` class and insert/remove keys as
requested by iterating over the input strings:

```python
hashmap = HashMap()

for s in strings:
    if b'-' in s:
        key = s[:-1]
        hashmap.remove(key)
    elif b'=' in s:
        key, value = s.split(b'=')
        hashmap.insert(key, int(value))
```

The final value to calculatea "power" that corresponds to a weird sum over all
entries present in the hashmap. For each entry, we need its value multiplied by
its index in the slot (strating at 1) multiplied again by its slot number
(starting at 1). Let's write a method to do this:

```python
class HashMap:
    # ... continued from above ...

    def power(self):
        total = 0

        for slot_number, lst in self.backing_store.items():
            for entry_index, (_, value) in enumerate(lst, 1):
                total += (slot_number + 1) * entry_index * value

        return total
```

The answer is now just one method call away:

```python
total = hashmap.power()
print('Part 2:', total)
```


Day 16 - The Floor Will Be Lava
-------------------------------

[Problem statement][d16-problem] — [Complete solution][d16-solution] — [Back to top][top]

### Part 1

We're on the roll with these ASCII grid problems it seems... well, we should
know the drill by now, parsing the input is literally one line of code:

```python
grid = open(...).read().splitlines()
```

As we already did for previous days, we can express coordinates as pairs `(r, c)`
of row index and column index, and directions as pairs of deltas `(dr, dc)`. The
four directions we can go are up, down, left, right, and they correspond to the
deltas `(-1, 0)`, `(1, 0)`, `(0, -1)`, `(0, 1)`. Moving in any given direction
is a simple vector sum with the new coordinates being `(r + dr, c + dc)`.

What about mirrors (`\` and `/`) though? How do they change the current
direction of travel? To extract a general rule we can simply test all
directions:

- Encountering `\`:
  - If we are going up `(-1, 0)` we end up going left `(0, -1)`;
  - If we are going down `(1, 0)` we end up going right `(0, 1)`;
  - If we are going left `(0, -1)` we end up going up `(-1, 0)`;
  - If we are going right `(0, 1)` we end up going down `(1, 0)`.
- Encountering `/`:
  - If we are going up `(-1, 0)` we end up going right `(0, 1)`;
  - If we are going down `(1, 0)` we end up going left `(0, -1)`;
  - If we are going left `(0, -1)` we end up going down `(1, 0)`;
  - If we are going right `(0, 1)` we end up going up `(-1, 0)`.

It looks like the `\` mirror simply swaps the two deltas of the current
direction from `(dr, dc)` to `(dc, dr)`. The `/` mirror does a similar
transformation, but the signs of the deltas are inverted: it transforms
`(dr, dc)` in `(-dc, -dr)`.

What about the splitters `-` and `|`? Well, these complicate things a little
bit, since they create additional paths to follow at the same time (at least
theoretically). Let's "ignore" them for now and write a function to explore the
grid following *a single path*, starting from the top left and going right. We
will consider any `-` that is perpendicular to our direction as "go right" and
any `|` perpendicular to our direction as "go down".

To count the number of cells we visit we can use a set of coordinates: we'll add
the current coordinates to the set each step, and check its length when we are
done.

How do we stop? well, the beam we are emulating can either escape the grid or
end up in an infinite loop. The first case is easy to detect with a bounds
check, and for the second one we can keep a set of already visited states: if we
ever find ourselves on the same cell and going in a direction that we already
traveled on that cell, we will know we entered a loop.

This is enough to implement an initial `travel()` function:

```python
def travel(grid):
    height     = len(grid)
    width      = len(grid[0])
    r, c       = 0, 0 # top left corner
    dr, dc     = 0, 1 # going right
    seen_cells = set()
    seen       = set()

    while 1:
        # Are we out of bounds?
        if not (0 <= r < height and 0 <= c < width):
            # Can't possibly continue!
            break

        # Dif we already get here while also going in the same direction?
        if (r, c, dr, dc) in seen:
            # This is a loop!
            break

        seen.add((r, c, dr, dc))
        seen_cells.add((r, c))
        cell = grid[r][c]

        if cell == '/':
            dr, dc = -dc, -dr
        elif cell == '\\':
            dr, dc = dc, dr
        elif cell == '-':
            # If we are moving either up or down, just turn right
            if dr != 0:
                dr, dc = 0, 1
        elif cell == '|':
            # If we are moving either left or right, just turn down
            if dc != 0:
                dr, dc = 1, 0

        r += dr
        c += dc

    return len(seen_cells)
```

The two checks right at the start of the `while` loop can be moved to the loop
condition, which becomes:

```python
    while 0 <= r < height and 0 <= c < width and (r, c, dr, dc) not in seen:
        # ...
```

Okay, but what about following multiple paths? It's not that complicated: we can
remember the paths that we still have to visit in a queue. Then, each time we
encounter a `-` or `|` split that is perpendicular to our direction of travel,
we keep advancing in one of the two directions and put the second (unexplored)
direction in the queue for later. Once we are done exploring, we can pop from
the queue and continue from there. This approach corresponds to a
[depth-first][wiki-dfs] exploration of all the paths.

Let's use a [`deque`][py-collections-deque] for our queue. We only need to add
one more `while` loop:

```python
def travel(grid):
    queue      = deque([(0, 0, 0, 1)]) # r, c, dr, dc
    height     = len(grid)
    width      = len(grid[0])
    seen_cells = set()
    seen       = set()

    # While there are still paths to explore (i.e. queue is not empty)
    while queue:
        r, c, dr, dc = queue.pop()

        while 0 <= r < height and 0 <= c < width and (r, c, dr, dc) not in seen:
            seen.add((r, c, dr, dc))
            seen_cells.add((r, c))
            cell = grid[r][c]

            if cell == '/':
                dr, dc = -dc, -dr
            elif cell == '\\':
                dr, dc = dc, dr
            elif cell == '-':
                # If we are we moving either up or down, just go right
                if dr != 0:
                    dr, dc = 0, 1
                    # We will explore the path that goes left later
                    queue.append((r, c - 1, 0, -1))
            elif cell == '|':
                # If we are we moving either left or right, just go down
                if dc != 0:
                    dr, dc = 1, 0
                    # We will explore the path that goes up later
                    queue.append((r - 1, c, -1, 0))

            r += dr
            c += dc

    return len(seen_cells)
```

Awesome, we can now call our function and solve the problem:

```python
n_energized = travel(grid)
print('Part 1:', n_energized)
```

### Part 2

We now need to try and start exploring from any possible cell on the grid's
perimeter and calculate the maximum possible number of encountered cells. We
always start going towards the inside, so if we start on the left wall the
initial direction is right, if we start on the bottom wall it's up, and so on.
For corner cells, we need to test both possible start directions (e.g., for the
top left cell we can either start going right or down).

Well... we already have the code, let's just move the start coordinates and
direction to the parameters of our `travel()` function:

```diff
-def travel(grid):
-    queue      = deque([(0, 0, 0, 1)])
+def travel(grid, startr, startc, dr, dc):
+    queue      = deque([(startr, startc, dr, dc)])
     # ...
```

For simplicity, let's also pass the width and height of the grid to the
function, so that we don't have to call `len()` a thousand times:

```diff
-def travel(grid, startr, startc, dr, dc):
+def travel(grid, height, width, startr, startc, dr, dc):
     queue      = deque([(startr, startc, dr, dc)])
-    height     = len(grid)
-    width      = len(grid[0])
     # ...
```

The function call for part 1 can now be adjusted as follows:

```python
height, width = len(grid), len(grid[0])
n_energized = travel(grid, height, width, 0, 0, 0, 1)
print('Part 1:', n_energized)
```

For part 2, we can call the function for every cell on the perimeter of the grid
and calculate the maximum value returned:

```python
best = 0

# Vertical walls
for r in range(len(grid)):
    # Leftmost, start going right
    best = max(best, travel(grid, height, width, r, 0, 0, 1))
    # Rightmost, start going left
    best = max(best, travel(grid, height, width, r, width - 1, 0, -1))

# Horizontal walls
for c in range(len(grid[0])):
    # Top, start going down
    best = max(best, travel(grid, height, width, 0, c, 1, 0))
    # Bottom, start going left
    best = max(best, travel(grid, height, width, height - 1, c, -1, 0))

print('Part 2:', best)
```

32 stars! I like powers of two.


Day 17 - Clumsy Crucible
------------------------

[Problem statement][d17-problem] — [Complete solution][d17-solution] — [Back to top][top]

### Part 1

The long awaited shortest path finding problem of the year! But of course, this
is not just plain boring shortest path finding, there's a twist to make things
interesting.

Let's get input parsing out of the way. Once again we have a grid of
ccharacters: the code to parse it is basically just muscle memory at this
point...

```python
grid = open(...).read().splitlines()
```

Since incidentally these characters are also digits, and we'll need them in
integer form, let's also convert everything to `int` with the help of
[`map()`][py-builtin-map] plus a [generator expression][py-gen-expr], and while
we are at it, let's also compute the height and width of the grid, which will be
useful later as usual.

```python
grid   = [list(map(int, row)) for row in grid]
height = len(grid)
width  = len(grid[0])
```

The raw information given in the form of a grid can be used to build a weighted
[directed graph][wiki-directed-graph]. The only three things we need to
understand are:

1. How to represent a node.
2. How to identify the neighbors of a node (i.e. how to identify the arcs that
   exit a given node).
3. How to assign weights to such arcs.

When it comes to cells in a grid, the instinctive way to represent nodes is as
simple pairs of coordinates `(r, c)`. However, this time it won't be enough.
Given the movement rules in the problem statement, our movement on a given cell
may be restricted to a cetain set of ditections: for example, if we reached a
cell after 3 consecutive right, the only directions we can go from there are up
or down.

Ideally, the only thing that should determine the possible paths to follow from
a given node is the node itself, and *not* how the node was reached. If we reach
the same coordinates twice without knowing where we came from, we cannot
possibly know whether we should stop because we already explored all possible
paths from the node, or continue because this time new paths are reachable.

Given that we can reach nodes in differnt ways, and that this will directly
influence which nodes will be reachable from them, we need more information than
just the cell coordinates to represent a node. The bare minimum needed in this
case is the coordinates plus the directions we are allowed to explore from the
node. We can represent a node using a tuple of the form
`(coords, possible_directions)` (where `coords` is a pair `(r, c)`).

How can we identify the neighbors of a node then? The problem statement tells us
that, from any given cell, we can travel between 1 and 3 consecutive steps in
the same direction until we need to turn. Therefore, given a node, one way to
find its neighbors is to identify all the possible coordinates that are
reachable within 3 steps in a straight line in any of the allowed directions.

Take this small grid as an example:

```none
  012345
  ------
0|X23522
1|411111
2|211111
```

We start on the cell marked as `X` with coordinates `(0, 0)`, and we can travel
right or down. The coordinates reachable from this cell therefore are:

- Traveling right: `(0, 1)` with distance 2, `(0, 2)` with distance 5 (2 + 3),
  and `(0, 3)` with distance 10 (2 + 3 + 5).
- Traveling down: `(1, 0)` with distance 4, and `(2, 0)` with distance 6
  (4 + 2).

What about the coordinates reachable from `(0, 1)` then? Technically, we can
travel right from `(0, 1)` to `(0, 2)` with distance 2, for a total distance of
4 from the start, but given how we explored the grid, we already know that we
can reach `(0, 2)` with distance 4 from `(0, 0)`, so that would be a pointless
intermediate step to reach the same goal.

Similarly, we could go from `(1, 0)` down to `(2, 0)` with distance 2, for a
total distance of 4 from the start, but we already know that `(2, 0)` is
reachable with distance 4 from the start!

The above reasoning gives a pretty neat way to identify neighbors: given a node
identified by a pair of coordintates and possible directions of travel, travel
on a straight line in any of the possible directions up to 3 steps. The
neighbors of the node will then be any of the reached coordinates, and each of
them will be only allowed to turn 90 degrees to continue traveling.

As another example:

```none
  012345
  ------
0|111111
1|3X2751
2|111111
```

The neighbors of the node `((1, 2), [left, right])` (the `X` cell above) are:

- `((1, 0), [up, down])` at distance 3, with neighbors `((0, 0), [left, right])`
  and `((2, 0), [left, right])`;
- `((1, 3), [up, down])` at distance 2, with neighbors `((0, 3), [left, right])`
  and `((2, 3), [left, right])`;
- `((1, 4), [up, down])` at distance 9, with neighbors `((0, 4), [left, right])`
  and `((2, 4), [left, right])`;
- `((1, 5), [up, down])` at distance 14, with neighbors
  `((0, 5), [left, right])` and `((2, 5), [left, right])`.

As you may have noticed, using this kind of representation, we only ever switch
from allowed directions `[left, right]` to allowed directions `[up, down]`. We
can therefore simplify things and say that the allowed directions are either
vertical or horizontal, which can be represented with a single `bool` variable
tells us whether we can travel vertically or not vertically (i.e. horizontally).

Finally, arcs: an arc will simply be a tuple of the form
`(neighbor_node, weight)`, and the weight of the arc, as is probably already
obvious from the above examples, is simply the sum of the numbers encountered on
the grid (including the destination cell, but not the starting cell).

<!--
Let's start by writing a [generator function][py-generators] that, given a node,
will `yield` all its neighbors. As we already said, a node is a tuple of the
form `((r, c), can_travel_vertically)`. We have two main cases: either go
vertically and yield as neighbors the (up to) 3 cells above and (up to) 3 cells
below, or go horizontally and yield as neighbors the (up to) 3 cells left and
(up to) 3 cells right.

For now, let's assume that we will be using the global variables `grid`,
`height` and `width` to avoid an insane amount of parameters, we'll see later
how to "fix" this. The only parameter we need is the node.

```python
def neighbors(node):
    # Just to be explicit, not really needed
    global grid, height, width

    (r, c), can_travel_vertically = node

    if can_travel_vertically:
        # Go up to 3 cells up
        for delta in range(1, 3 + 1):
            if r - delta >= 0:
                break
            yield ((r - delta, c), False)

        # Go up to 3 cells down
        for delta in range(1, 3 + 1):
            if r + delta < height:
                break
            yield ((r + delta, c), False)
    else:
        # Go up to 3 cells left
        for delta in range(1, 3 + 1):
            if c - delta >= 0:
                break
            yield ((r, c - delta), False)

        # Go up to 3 cells right
        for delta in range(1, 3 + 1):
            if c + delta < width:
                break
            yield ((r, c + delta), False)
```

Okay, seems good to identify the neighbors... but we also want to know what's
their distance (i.e. the weight of the arc from the original `node` to each of
them). Let's add that calculation to the function:

```diff
 def neighbors(node):
     # Just to be explicit, not really needed
     global grid, height, width

     (r, c), can_travel_vertically = node

     if can_travel_vertically:
         # Go up to 3 cells up
+        weight = 0
         for delta in range(1, 3 + 1):
             if r - delta >= 0:
                 break
+            weight += grid[r][c]
-            yield ((r - delta, c), False)
+            yield ((r - delta, c), False), weight

         # Go up to 3 cells down
+        weight = 0
         for delta in range(1, 3 + 1):
             if r + delta < height:
                 break
+            weight += grid[r][c]
-            yield ((r + delta, c), False)
+            yield ((r + delta, c), False), weight
     else:
         # Go up to 3 cells left
+        weight = 0
+        for delta in range(1, 3 + 1):
             if c - delta >= 0:
                 break
+            weight += grid[r][c]
-            yield ((r, c - delta), True)
+            yield ((r, c - delta), True), weight

         # Go up to 3 cells right
+        weight = 0
         for delta in range(1, 3 + 1):
             if c + delta < width:
                 break
+            weight += grid[r][c]
-            yield ((r, c + delta), True)
+            yield ((r, c + delta), True), weight
```
-->

Let's write a [generator function][py-generators] that, given a pair of starting
coordinates and a direction, calculates and yields all the coordinates and the
weights moving in a straight line up to 3 steps. It seems simple enough: just
keep going for at most 3 steps in the given direction as long as you are inside
the grid, add up all the weights encountered, and `yield` a tuple
`(coords, weight)` each time.

```python
def straight_line(grid, height, width, r, c, deltar, deltar):
    weight = 0

    for _ in range(1, 3 + 1):
        r += deltar
        c += deltac

        if not (0 <= r < height and 0 <= c < width):
            break

        weight += grid[r][c]
        yield ((r, c), weight)
```

With the help of the above code, we can now easily write another generator
function that, given a node, will `yield` all its neighbors. As we already said,
a node is a tuple of the form `((r, c), can_travel_vertically)`. We have two
main cases: if we can go vertically, travel in a straight line up and down up to
3 steps, and if we can not go vertically then travel in a straight line left and
right up to 3 steps. This transltes to 4 calls to the above function.

```python
def neighbors(grid, height, width, node):
    (r, c), can_travel_vertically = node

    if can_travel_vertically:
        # Up
        for coords, weight in straight_line(grid, height, width, r, c, -1, 0):
            yield ((coords, False), weight)
        # Down
        for coords, weight in straight_line(grid, height, width, r, c, 1, 0):
            yield ((coords, False), weight)
    else:
        # Left
        for coords, weight in straight_line(grid, height, width, r, c, 1, -1):
            yield ((coords, True), weight)
        # Right
        for coords, weight in straight_line(grid, height, width, r, c, 1, 1):
            yield ((coords, True), weight)
```

The above function is definitely still siplifiable, but to avoid wasting ages
I'll leave that as an exercise to the reader (or you can just check out my
complete solution linked above).

Awesome! We now have:

- The definition of a node.
- The definition of an arc and its weight.
- A way to list the outgoing arcs from a node (i.e. to determine all the
  neighbors of a given node).

This is all we need to implement a pathfinding algorithm. In particular, since
we are interested in finding the shrotest path from one node to another, we can
use the famous [Dijkstra's algorithm][wiki-dijkstra].

Copying almost verbatim from my 2019 walkthrough: as we already did in previous
years ([2019 d6 p2][2019-d06-p2], [2021 d15 p1][2021-d15-p1]), w ewill implement
Dijkstra's algorithm using a [min-heap][wiki-min-heap] as a [priority
queue][wiki-priority-queue] to hold the nodes to visit and always pop the one
with the shortest distance from the source. The [`heapq`][py-heapq] module is
exactly what we need. A [`defaultdict`][py-collections-defaultdict] that returns
`float('inf')` (also provided by `math.inf`) as the default value is also useful
to treat not-yet-seen nodes as being infinitely distant (positive floating point
infinity compares greater than any integer).

The algorithm is well-known and also well-explained in the Wikipedia page I just
linked above, so I'm not going into much detail about it, I'll just add some
comments to the code.

```python
import heapq
from collections import defaultdict
from math import inf as INFINITY

def dijkstra(grid, height, width, src_coords, dst_coords):
    # Set of visited nodes to avoid visiting the same node twice
    visited = set()

    # List of (distance, node) used as heap to choose the next node to visit
    queue = []
    # We'll start from the coordinates src_coords. This is the only special case
    # where we can go bot horizontally and vertically, so we'll add two nodes to
    # the initial queue.
    queue.append((0, (src_coords, False)))
    queue.append((0, (src_coords, True)))

    # Dictionary of the form {node: total_distance} keeping track of the minimum
    # distance from any given node to the start
    distance = defaultdict(lambda: INFINITY)

    # While we have nodes to visit
    while queue:
        # Pop the node with lowest distance from the priority queue
        dist, node = heapq.heappop(queue)

        # If we got to the destination, we found what we were looking for
        if node[0] == dst_coords:
            return dist

        # If we already visited this node, skip it, proceed to the next one
        if node in visited:
            continue

        # Mark the node as visited
        visited.add(node)

        # For each neighbor of this node...
        for neighbor, weight in neighbors(grid, height, width, node):
            # Calculate the total distance from the source to this neighbor
            # passing through this node
            new_dist = dist + weight

            # If the new distance is lower than the minimum distance we know to
            # reach this neighbor, then update its minimum distance and add it
            # to the queue, as we found a "better" path to it
            if new_dist < distance[neighbor]:
                distance[neighbor] = new_dist
                heapq.heappush(queue, (new_dist, neighbor))

    # If we ever empty the queue without entering the node[0] == dst_coords
    # check in the above loop, there is no path from source to destination
    return INFINITY
```

Assuming we wrote everything correctly, all that's left to do is call the
function to get our answer:

```python
src_coords = (0, 0)
dst_coords = (height - 1, width - 1)

min_dist = dijkstra(grid, height, width, src_coords, dst_coords)
print('Part 1:', min_dist)
```

### Part 2

For part 2, we still need to find the shortest path to victory, but this time
the movement rules change: whenever we move, we always have to take *at least* 4
steps in the same direction. Then, we can keep going for
*up to 6 additional steps* in the same direction before we necessarily have to
turn.

Well, thankfully, given the way we coded things for part 1, the changes to make
are not that many. The only function to change is `straight_line()`, which
should now take into account the minimum distance of 4 and maximum of 4+6 = 10.
To make it generic enough, let's take these numbers as parameters:

```diff
-def straight_line(grid, height, width, r, c, deltar, deltar):
+def straight_line(grid, height, width, r, c, deltar, deltar, start, stop):
     weight = 0

-    for _ in range(1, 3 + 1):
+    for i in range(1, stop + 1):
         r += deltar
         c += deltac

         if not (0 <= r < height and 0 <= c < width):
             break

         weight += grid[r][c]
-        yield ((r, c), weight)
+        if i >= start:
+            yield ((r, c), weight)
```

The only other changes to make are simplying a matter of passing around the
`start` and `stop` values:

```diff
-def neighbors(grid, height, width, node):
+def neighbors(grid, height, width, node, start, stop):
     (r, c), can_travel_vertically = node

     if can_travel_vertically:
-        for coords, weight in straight_line(grid, height, width, r, c, -1, 0):
+        for coords, weight in straight_line(grid, height, width, r, c, -1, 0, start, stop):
             yield ((coords, False), weight)
-        for coords, weight in straight_line(grid, height, width, r, c, 1, 0):
+        for coords, weight in straight_line(grid, height, width, r, c, 1, 0, start, stop):
             yield ((coords, False), weight)
     else:
-        for coords, weight in straight_line(grid, height, width, r, c, 1, -1):
+        for coords, weight in straight_line(grid, height, width, r, c, 1, -1, start, stop):
             yield ((coords, True), weight)
-        for coords, weight in straight_line(grid, height, width, r, c, 1, 1):
+        for coords, weight in straight_line(grid, height, width, r, c, 1, 1, start, stop):
             yield ((coords, True), weight)
```

And in the main `dijkstra()` function:

```diff
-def dijkstra(grid, height, width, src_coords, dst_coords)
+def dijkstra(grid, height, width, src_coords, dst_coords, start, stop):
     # ....
-        for neighbor, weight in neighbors(grid, height, width, node):
+        for neighbor, weight in neighbors(grid, height, width, node, start, stop):
     # ...
```

We can now calculate the answer for both parts with two function calls:

```python
min_dist1 = dijkstra(grid, height, width, src_coords, dst_coords, 1, 3)
print('Part 1:', min_dist1)

min_dist2 = dijkstra(grid, height, width, src_coords, dst_coords, 4, 10)
print('Part 2:', min_dist2)
```


Day 18 - Lavaduct Lagoon
------------------------

[Problem statement][d18-problem] — [Complete solution][d18-solution] — [Back to top][top]

### Part 1

No way, grids again? Ok, no, not really. This time we are not dealing directly
with a gid, but rather only following directions to draw something on it.

Given that the input instructions to draw edges only contain directions to go
up/down/left/right, what we will end up drawing a polygon that only has right
angles and vertical or horizontal edges. Our task is to calculate its total area
expressed in terms of points with integral coordinates that reside either inside
or on the edges of the polygon.

How can this be done? There are multiple ways: the naïve approach would be to
draw the entire perimeter of the polygon following the directions liteally and
then determine use [breadth-first search][wiki-bfs] starting from any cell on
its inside to count how many cells there are (including the perimeter). That
would work, but would definitely not be optimal.

In fact, closed formulas exist that can solve this problem. A quick internet
search for *"area of a polygon given its vertices"* brings up the
[shoelace formula][wiki-shoelace], also known as "Gauss' area formula". The
formula is more general and also works for edges that are not horizontal and
vertical, so in our case it can also be simplified a bit. There are different
variations of the formula, but the one that I think fits the scenario best is
the trapezoid formula.

The core concept is easy to undestand with the help of an example. Consider the
following polygon:

```none
^ Y
|    1        8
|     ########
|     #      #          6
|     #      ###########
|     #     7|         #
|     #      |     3   #
|     #############    #
|    2|      |    #    #
|     |      |    ######
|     |      |   4|    |5
|     |      |    |    |
O-----x------x----x----x-----> X
```

Ignoring the vertical segments (they have zero area below them), if we denote
the area below a segment from *a* to *b* with $A_{a,b}$, then the area of the
above polygon can be calculated as: $A_{1,8} + A_{7,6} - A_{2,3} - A_{4,5}$. In
fact, if we take a look at it we can se that $A_{1,8}$ includes a piece of
$A_{2,3}$ below it, $A_{7,6}$ includes the remaining piece of $A_{2,3}$ and also
$A_{4,5}$.

The Shoelace formula in fact calculates the area exactly like this: as the
summation of the *signed areas* below the edges of the polygon considered in
counter-clockwise order. The area $A_{a,b}$ can be calculated as
$(b_x - a_x)(a_y + b_y)/2$ for the generic case where the shape is a trapezoid.
In our case it's just $(b_x - a_x)a_y$, since horizontal segments will have the
same *y* ($a_y + b_y = 2a_y$), and vertical segments will have the same *x*
($b_x - a_x = 0)$.

If we iterate over the vertices of the above example pairwise, we get:
$A_{2,1} + A_{3,2} + A_{5,4} + ... + A_{1,8}$. The areas $A_{3,2}$ and $A_{5,4}$
are negative since we are considering the edges in their opposite direction.

The only additional thing to consider is that we also want to include the cells
on the perimeter of the polygon itself in our area, but the formula we just
wrote will only include part of it. To overcome this, we can apply
[Pick's theorem][wiki-pick-theorem], which states that $A = I+\frac{P}{2}-1$,
that is: the area is equal to the number of internal points, minus one half of
the points laying on the perimeter, plus 1.

Jonathan Paulson made a good and straight-to-the-point video explanation of this
approach in [his youtube video here][d18-jonathan-video].

Okay, we have our mind set on the goal, now onto the coding part. We want the
coordinates of all the vertices and the number of points on the perimeter. We
can calculate all of this in one go by parsing the input line by line.

We will [`.split()`][py-str-split] each line extracting the direction and the
number of steps that follows (ignoring the last hexadecimal part for now as the
problem statement says). We will express coordinates as `(r, c)` as usual (using
`x` and `y` would be equivalent, but I find `r` and `c` more intuitive).
Starting from an arbitrary point, for example `(0, 0)`, we will then move each
time in the given direction for the given number of steps, and add the new
coordinates to a list of vertices. The direction, which can be one of `UDLR`,
can be easily converted into deltas to apply to `r` and `c` with the help of a
dictionary.

```python
fin = open(...)

dirmap = {'R': (0, 1), 'D': (1, 0), 'L': (0, -1), 'U': (-1, 0)}

vertices = []
perimeter = 0
r = c = 0

for line in fin:
    direction, steps, _ = line.split()
    steps = int(steps)

    dr, dc = dirmap[direction]
    r += steps * dr
    c += steps * dc

    vertices.append((r, c))
    perimeter += steps
```

Since we will iterate over vertices pairwise, and we also want include in our
calculations the edge that goes from the last vertex to the first, we will add
`(0, 0)` at the end of the list.

```python
vertices.append((0, 0))
```

We now have a list of vertices and the perimeter of the polygon. Let's write a
function to calculate the inner area using the shoelace formula. To iterate over
pairs of vertices we can use [`itertools.pairwise()`][py-itertools-pairwise], or
alternatively re-implement it ourselves using
[`itertools.tee()`][py-itertools-tee] as the example in the Pytho ndocumentation
shows, since `pairwise()` is only available from Python 3.10.

Since we want to iterate over vertices in counter-clockwise order, but we don't
know if they are ordered clockwise or counter-clockwise, there is a chance that
the resulting area will be negative. That's no issue, we can calculate its
absolute value with [`abs()`][py-builtin-abs].

```python
from itertools import pairwise

def shoelace(vertices):
    area = 0
    for (r1, c1), (_, c2) in pairwise(vertices):
        area += (c2 - c1) * r1

    return abs(area)
```

We can now calculate the inner area and then apply Pick's theorem to get the
total area we want. We want an integer result, and the perimeter we calculate
will always be an even number (given that the path we take from the initial
vertex always brings us back to the origin), so we can use itneger division
(`//`).

```python
area = shoelace(vertices) + perimeter // 2 + 1
print('Part 1:', area)
```

### Part 2

For part 2 we are told that the hexadecimal values we ignored in part 1 actually
represent the real edges: the lowest hex digit represents the direction, which
can be `0123` for `RDLU`, and the other digits represent the number of steps to
take (the length of the edge).

We already have all we need to solve the problem, we only need to feed our
function new values. We can either rewind the input and parse it again or do
everything in a single loop and keep two lists of vertices and two perimeters.
To convert hexadecimal numbers into decimal we can pass `16` (the base to
convert from) as second argument to [`int()`][py-builtin-int]. In any case, we
can add `0123` to our `dirmap` to convert those digits to the appropriate
deltas.

```python
dirmap = {
	'R': (0, 1), 'D': (1, 0), 'L': (0, -1), 'U': (-1, 0),
	'0': (0, 1), '1': (1, 0), '2': (0, -1), '3': (-1, 0),
}

vertices1 = []
vertices2 = []
perimeter1 = 0
perimeter2 = 0
r1 = c1 = r2 = c2 = 0

for line in fin:
    direction, steps1, hexval = line.split()
    steps1 = int(steps1)

    dr, dc = dirmap[direction]
    r1 += steps1 * dr
    c1 += steps1 * dc

    direction = hexval[-2]
    steps2 = int(hexval[2:-2], 16)
    dr, dc = dirmap[direction]
    r2 += steps2 * dr
    c2 += steps2 * dc

    vertices1.append((r1, c1))
    vertices2.append((r2, c2))
    perimeter1 += steps1
    perimeter2 += steps2

vertices1.append((0, 0))
vertices2.append((0, 0))
```

Yeah, not the prettiest code I've seen... but why complicate things? The
solutions for both parts are both one function call away:

```python
area1 = shoelace(vertices1) + perimeter1 // 2 + 1
print('Part 1:', area1)

area2 = shoelace(vertices2) + perimeter2 // 2 + 1
print('Part 2:', area2)
```


Day 19 - Aplenty
----------------

[Problem statement][d19-problem] — [Complete solution][d19-solution] — [Back to top][top]

### Part 1

Interesting problem today, I'd say the most interesting so far this year. We
need to emulate a set of "workflows" composed of rules that are linked to each
other.

To the input parsing! We have two section of input separated by an empty line,
so we can just read everything, [`.split()`][py-str-split] on `\n\n` to get the
two sections, and then use [`.splitlines()`][py-str-splitlines] on each section.

```python
with open(...) as fin:
    raw_workflows, raw_variables = fin.read().split('\n\n')

raw_workflows = raw_workflows.splitlines()
raw_variables = raw_variables.splitlines()
```

Since parsing is a bit tedious, let's write two functions: one to parse the
workflows and another one to parse the variable assignments.

Each line in `raw_workflows` represents a single workflow of the following
form:

```none
zzz{a>3102:vrv,a<2800:cqj,a<2999:A,bvc}
```

The name (`zzz`) can be easily extracted by locating the first `{` character
through [`.find()`][py-str-find] and then slicing. The rules start right after
`{` and end at the second-to-last character, so they can again be extracted by
slicing. They can then be `.split()` on commas (`,`) and parsed.

Each rule has the form `expression:next_workflow_name`, except the last rule
which only represent the workflow name to go to if none of the previous rules
are satisfied. Each rule can therefore be `.split()` on the colon (`:`) through
a simple generator expression to obtain a list of pairs
`[expression, next_workflow_name]`.

Each expression has the form `v>num` or `v<num` where `v` is a
variable name and `num` is an integer. We can extract these three components
with slicing, and once again use a generator expression to transform each
`[expression, next_workflow_name]` pair into
`(var_name, op, value, next_workflow_name)`.

Where do we store parsed workflows? Well, since each workflow include rules that
identify other workflows by name, a dictionary of the form
`{name: (rules, last_name)}` seems ideal ot easy find workflows by name. That
`last_name` is simply the name in the final rule, which does not have an
expression.

Here's a function that parses workflows from raw input lines to a dictionary as
described above:

```python
def parse_workflows(lines):
    workflows = {}

    for line in lines:
        name = line[:line.find('{')]
        rules = line[line.find('{') + 1:-1].split(',')
        # Separate the last rule (name only) from the rest
        rules, last = rules[:-1], rules[-1]
        # ['expr1:name1', ...] -> [[expr1, name1], ...]
        rules = (r.split(':') for r in rules)
        # [[expr1, name1], ...] -> [(var_name, op, value, next_workflow_name), ...]
        rules = [(exp[0], exp[1], int(exp[2:]), nxt) for exp, nxt in rules]
        workflows[name] = (rules, last)

    return workflows
```

Parsing variable assignments is simpler: remove the leading `{` and trailing
`}`, split each assignment on `=` to have pairs of the form `[var_name, value]`,
and finally convert each value to integer.

Again, the most convenient container to use is a dictionary of the form
`{var_name: value}`. This is because workflow rules will refer to the variable
by name, so we need an easy way to get their value given their name. This
dictionary can be consicely built using
[dict comprehension][py-dict-comprehension].

Since these assignments only need to be iterated over once, we can write a
[generator function][py-generators] that yields one dictionary at a time.

```python
def parse_variables(lines):
    for line in lines:
        # '{a=123,b=456}' -> ['a=123', 'b=456']
        assignments = line[1:-1].split(',')
        # ['a=123', 'b=456'] -> [('a', '123'), ('b', '456')]
        assignments = map(lambda a: a.split('='), assignments)
        # [('a', '123'), ('b', '456')] -> {'a': 123, 'b': 456}
        yield {a[0]: int(a[1]) for a in assignments}
```

Now we can parse the two input sections we have using the functions we just
wrote:

```python
workflows = parse_workflows(raw_workflows)
variables = parse_variables(raw_variables)
```

Our task is to try running the workflows (starting from the one named `in`) with
all the given variable assignments, and for workflows that succeed (i.e. end up
referencing the dummy `A` workflow) sum the variable values.

Let's write a function to run the workflows we have given one dictionary of
variable assignments. The algorithm seems straightforward:

1. Start with the workflow `in`;
2. For each rule in the workflow, test the referenced variable against the
   given value, depending on the given operation (`<` or `>`);
3. If the check passes, proceed to the next workflow identified by the rule,
   otherwise proceed to the next rule;
4. If all the rules of the current workflow are processed without any match
   (i.e. none of the tested expressions were saisfied), proceed to the `last`
   workflow (corresponding to the final rule that has no expression);
5. Continue until a workflow named `'A'` or `'R'` is encountered;
6. In case `'A'` is encountered, return the sum of the variable values, or zero
   otherwise.

Here's the implementation:

```python
def run(workflows, variables):
    cur = 'in'

    while cur != 'A' and cur != 'R':
        rules, last = workflows[cur]

        for varname, op, value, nxt in rules:
            var = variables[varname]
            if op == '<' and var < value:
                cur = nxt
                break
            if op == '>' and var > value:
                cur = nxt
                break
        else:
            # No break statement encountered (i.e., none of the rules matched)
            cur = last

    if cur == 'A':
        return sum(variables.values())
    return 0
```

Using the above function, we can now calculate the value for all the variable
assignments we have, and [`sum()`][py-builtin-sum] everything up.

```python
total = sum(run(workflows, v) for v in variables)
```

We can also use [`map()`][py-builtin-map] instead of a generator expression if
we first bind the first argument of `run` to be always `workflows` using
[`functoos.partial()`][py-functools-partial]:

```python
total = sum(map(partial(run, workflows), variables))
print('Part 1:', total)
```

### Part 2

Now we are told to ignore the given variable assignments. We know that each of
the four variables we have (`x`, `m`, `a`, `s`) can have a value ranging from 1
to 4000 (ends included), and want to calculate how many among all the possible
value assignments are accepted by the workflows.

We clearly cannot test all the possible assignments in a reasonable time, since
we have 4 ranges of 4000 values, so a total of 4000<sup>4</sup> =
256000000000000 (256 trillion) unique possible assignments. We need to architect
a smarter strategy.

It may already be obvious, but the workflows we are given represent a
[directed graph][wiki-directed-graph]: each workflow represents a node, and is
connected to other workflows through some ordered expressions (arcs). We can
advance from one node to the other testing the expressions in the given order
and taking the arc corresponding to the first satisfied expression (or the final
arc with no expression).

Additionally, there are no loops (otherwise part 1 would have been impossible),
so the graph is also a [tree][wiki-tree], where the root is the workflow named
`'in'`, and the only two leaves are the two workflows named `'A'` and `'R'`.

We can solve the problem in a single exploration of the tree from the root down
to the leaves, either using [BFS][wiki-bfs] or [DFS][wiki-dfs]. The latter is
simpler to implement as a recursive function. To do this, along the way we'll
keep track of *ranges of possible values* instead of single values.

Starting from the root workflow (`'in'`) with [1, 4000] as the possible range
for all the variables, the strategy to implement is as follows:

1. If we reach the `'A'` workflow, return the product of all the range sizes,
   which corresponds to the number of possible combinations;
2. Otherwise, if we reach the `'R'` workflow, return `0`;
3. Otherwise, we need to go through the rules of the current workflow. For each
   rule:
   1. Check the value *v* to test and the current range *[lo, hi]* of possible
      values for the tested variable. In case the expression is *var < v*, we
      need to discard all the values above *v*, so the new accepted range will
      be *[lo, v - 1]*. In case the operation is *var > v*, we need to discard
      all the values below *v*, so the new accepted range will be *[v + 1, hi]*.
   2. Make a recursive call to know the amount of accepted values for the new
      ranges. Add the result of the recursive call to the total number of
      accepted rules.
   3. Update the current range for the tested variable with the opposite of the
      accepted range (we advance to the next rule only if the current did not
      match). In case of *var < v* we advance with *[v, hi]*, while in case od
      *var > v* we advance with *[lo, value]*.
4. Finally, after processing all the rules, make a last recursive call to also
   explore the workflow corresponding to the final rule that has no associated
   expression using the updated ranges. Add the result of the recursive call
   to the total and return it.

The above algorithm essentially splits the search space in half each time a rule
is evaluated: one half is accepted and continues to the next workflow, while the
other half is rejected and passed on to the next rule of the current workflow.

This can be nicely visualized using a [Sankey diagram][wiki-sankey], which is
what was done [here in this Reddit post][d19-reddit-sankey] in the AoC
subreddit. Pretty neat!

We'll implement the above as a recursive function taking 3 arguments: the
workflows, the initial ranges and the current workflow name. The variable ranges
will be represented with a dictionary of the form `{var_name: (lo, hi)}`,
starting with `lo=1` and `hi=4000` for all variables.

To update the dictionary of ranges and pass it on recursively, we can use the
bitwise OR operator (`|`), which has the effect of creating a new dictionary
with the values taken from the right side of the operator overriding the
originals, as documented [here][py-dict]. So, for example:
`{'x': 1, 'y': 2} | {'x': 3}` will produce `{'x': 3, 'y': 2}`.

Here's the implementation of the above:

```python
def count_accepted(workflows, ranges, cur='in'):
    if cur == 'A':
        # The ranges we have are accepted, return the number of possible
        # combinations, which corresponds to the product of the range sizes
        product = 1
        for lo, hi in ranges.values()
            product *= hi - lo + 1

        return product

    if cur == 'R':
        # The ranges we have were rejected
        return 0

    rules, last = workflows[cur]
    total = 0

    for var, op, value, nxt in rules:
        lo, hi = ranges[var]

        if op == '<':
            # Check if this rule can match any of the values in [lo, hi]
            if lo < value:
                # Crate a new ranges dictionary updating the range of this
                # variable from [lo, hi] to [lo, value - 1], then explore the
                # next workflow with a recursive call
                ranges | {var: (lo, value - 1)}
                total += count_accepted(workflows, , nxt)

            # If possible, update the current range with the opposite of the
            # match (since we also want to explore the possibility of no match),
            # so from [lo, hi] to [value, hi], and continue to the next rule
            if hi >= value:
                ranges[var] = (value, hi)
        else:
            # Pretty much the same reasoning as above...
            if hi > value:
                total += count_accepted(workflows, ranges | {var: (value + 1, hi)}, nxt)

            if lo <= value:
                ranges[var] = (lo, value)

    # Also try processing the next workflow, which should be explored only if no
    # rules match (we already updated all the ranges as needed)
    total += count_accepted(workflows, ranges, last)
    return total
```

The calculation of the product in case we encounter the `'A'` workflow can be
simplified using [`math.prod()`][py-math-prod] plus a
[generator expression][py-gen-expr]:

```diff
+from math import product
+
 def count_accepted(workflows, ranges, cur='in'):
     if cur == 'A':
         # The ranges we have are accepted, return the number of possible
         # combinations, which corresponds to the product of the range sizes
-        product = 1
-        for lo, hi in ranges.values()
-            product *= hi - lo + 1
-
-        return product
+        return prod(hi - lo + 1 for lo, hi in ranges.values())

     # ... unchanged ...
```

We are once again one function call away from the solutoin, so let's get our
38th star:

```python
accepted = count_accepted(workflows, {v: (1, 4000) for v in 'xmas'})
print('Part 2:', accepted)
```


Day 20 - Pulse Propagation
--------------------------

[Problem statement][d20-problem] — [Complete solution][d20-solution] — [Back to top][top]

### Part 1

Today's problem is a fun one (well, at least for part 1). We are working with
singals and want to propagate them through what is essentially a
[directed graph][wiki-directed-graph] of "modules".

The input we are given consists of lines of the form `src -> dst1, dst2, dst3`.
Te easiest way to represent the graph is a dictionary of the form
`{node: list_of_neighbors}`, and the input provides us the key-value pairs to
fill it with.

We can represent "pulses" as booleans with `True` meaning high and `False`
meaning low. In order to distinguish between different kind of modules, we can
use two additional dictionaries: one for "flip-flop" modules, where the values
will be the current state of each flip-flop, and one for "conjunction" modules,
where the values will be dictionaries used to remember the last state of the
inputs for each conjunction. Modules that are neighte flip-flops nor
conjunctions don't need to remember any state them.

Let's get to parsing then: separate sources from destinations by
[`.split()`][py-str-split]-ing each line on the arrow (`'->'`), then
[`.strip()`][py-str-strip] useless whitespace from both parts and `.split()`
again the destinations on commas (`', '`) to get a list.

To determine the module type we simply check the first character: for flip-flops
we initialize their state to `False` (low), while for conjunctions we'll create
a new empty dictionary (to fill later). Finally, we'll add everything to the
graph dictionary.

```python
flops = {}
conjs = {}
graph = {}

with open(...) as fin:
    for line in fin:
        source, dests = line.split('->')
        source = source.strip()
        dests = dests.strip().split(', ')

        if source[0] == '%':
            source = source[1:]
            flops[source] = False
        elif source[0] == '&':
            source = source[1:]
            conjs[source] = {}

        graph[source] = dests
```

Now that we have built the graph and recognized each flip-flop and conjunction,
we need to initialize the state of each conjunction module: for each
conjunction, we will add any module that has such conjunction in its destination
list to the conjunction's dictionary. This can be done with a simple `for` loop
over the [`.items()`][py-dict-items] of the `conjs` dictionary we just built.

```python
for source, dests in graph.items():
    for dest in dests:
        if dest in conjs:
            cnjs[dest][source] = False
```

Now the fun begins. Following the rules, we need to propagate an initial pulse
starting from the `'broadcaster'` module. This module gets a los (`False`) pulse
from an initial button press, and such pulse will propagate according to the
rules in the problem statement.

We can implement a [breadth-first][wiki-bfs] exploration of the graph using a
[`deque`][py-collections-deque] as [FIFO][wiki-fifo] queue. The elemenents to
enqueue will be tuples of the form `(sender, receiver, pulse)` where `sender` is
the module that sent the pulse, `receiver` is the module currently receiving it,
and `pulse` is `True`/`False` for high/low.

We'll keep going until there are elements in the queue, popping one at a time
from the front and processing it, which may result in appending new elements to
process to the tail of the queue. We'll also keep track of the number of low and
high pulses encountered, as this is what we are asked.

Let's write a function for this: the implementation will simply follows the
rules given by the problem statement.

```python
from collections import deque

def run(graph, flops, conjs):
    q   = deque([('button', 'broadcaster', False)])
    nhi = 0 # number of high pulses encountered
    nlo = 0 # number of low pulses encountered

    while q:
        sender, receiver, pulse = q.popleft()

        if pulse:
            nhi += 1
        else:
            nlo += 1

        if receiver in flops:
            # Flip flops only react to low pulses
            if pulse:
                return
            # When a low pulse is received, the state of the flip-flop switches
            # to its opposite and a concording pulse is propagated
            next_pulse = flops[receiver] = not flops[receiver]
        elif receiver in conjs:
            # When a pulse is received by a conjunction, the last known state of
            # the sender is updated for this conjunction
            conjs[receiver][sender] = pulse
            # If all the last pulse seen from all the inputs of this conjunction
            # was high, then a low pulse is propagated, otherwise a high pulse
            next_pulse = not all(conjs[receiver].values())
        elif receiver in graph:
            # Neither a flip-flop nor a conjunction, propagate the pulse as is
            next_pulse = pulse
        else:
            # This module is not connected to any other module, cannot propagate
            return

        # Now propagate the new pulse to all the modules connected to this one
        for new_receiver in graph[receiver]:
            q.append((receiver, new_receiver, next_pulse))

    return nhi, nlo
```

To get our 39th star, we can now call the function 1000 times and calculate the
product of the total number of low and high pulses observer:

```python
tothi = totlo = 0
for _ in range(1000):
    nhi, nlo = run(graph, flops, conjs)
    tothi += nhi
    totlo += nlo

answer = tothi * totlo
print('Part 1:', answer)
```

### Part 2

Things take an interesting turn: we need to reset all flip-flops and
conjunctions to their initial state, and then find out when will the `'rx'`
module ever receive the first low pulse, in terms of number of button presses.

Theoretically, we already have the code to do this: in part 1 we had to emulate
1000 button presses, why not simply add a check inside the `run()` function and
call it indefinitely until the check is hit? Well, of course, in classic Advent
of Code spirit, this brute force approach won't work. Or well, it would work, if
it weren't for the fact that the number we are looking for is insanely high, so
the solution would take a little bit too much time to run.

We need to take a look at our input to realize what's going on. A couple of
visualizations posted today on AoC's subreddit are also helpful for this:
[one][d20-reddit-viz1], [two][d20-reddit-viz2]. In any case, a few interesting
aspects stand out:

1. There's only one `rx` module;
2. There's only one input to the `rx` module, and it's a conjunction module;
3. All the inputs to this conjunction module are also conjunction modules.

Let's stop and think for a second. Unfortunately we will have to make a few
assumptions without which our life would be much, much harder. The good news is
that these assumptions seem to hold, the bad news is that making assumptions
theoretically makes the solution less general. As I take it though, this always
happens for at least one or two AoC problems each year, so I'm relatively fine
with it.

Consider the following:

1. Assume that the three above conditions always hold (at least, they dit for my
   input and I assume everyone else's input);
2. Let's call $A$ the conjunction mentioned in point 2 above, which is the only
   input module to `rx`. Then, let's call $B_1, B_2, ..., B_N$ the *N*
   conjunctions mentioned in point 3 above, which are the only input modules to
   $A$.
3. Given the behavior of conjunctions, $A$ will send a low pulse to `in` as soon
   as all the remembered pulses from its inputs ($B_i$) are high.
4. Each $B_i$ will send a high pulse to $A$ every time it receives a low pulse
   (no matter the state, a low pulse received by a conjunction will always
   propagate another low pulse).
5. Assume that each $B_i$ **somehow** periodically receives a low pulse every
   $P_i$ button presses (i.e., each $P_i$ runs of the `run()` function we
   wrote).
6. Assume that the period of each $B_i$ module starts at the first button press
   and ends at the first low pulse delivered to the module.

We now have *N* modules ($B_1, ..., B_n$), which according to the assumption in
point 5 above are periodically sending high pulses with different period lengths
($P_1, ..., P_n$). According to the assumption in point 6, all these periods
also start at the same time (the first button press).

The *N* modules we have send high pulses in periods of different lengths
starting at the same instant, and we want to know when they will synchronize.
This will happen every [$\text{lcm}(P_1,...,P_n)$][wiki-lcm] iterations. The
situation is similar to the one of [day 8 part 2][d08-p2].

The logic to use to propagate pulses is unchanged, so whatever code we write
will be very similar to the code for part 1. Let's therefore extract the pulse
propagation logic of the `run()` function into an helper
[generator function][py-generators] that we can then use for both part 1 and
part 2. This function will take the current `sender`, `receiver` and `pulse`,
process the pulse according to the rules, and `yield` all the next elements to
explore (i.e., to add the queue). It's as simple as cut and paste:

```python
def propagate_pulse(graph, flops, conjs, sender, receiver, pulse):
    if receiver in flops:
        if pulse:
            return
        next_pulse = flops[receiver] = not flops[receiver]
    elif receiver in conjs:
        conjs[receiver][sender] = pulse
        next_pulse = not all(conjs[receiver].values())
    elif receiver in graph:
        next_pulse = pulse
    else:
        return

    for new_receiver in graph[receiver]:
        yield receiver, new_receiver, next_pulse
```

The `run()` function from part 1 can then be rewritten as follows:

```python
def run(graph, flops, conjs):
    q = deque([('button', 'broadcaster', False)])
    nhi = nlo = 0

    while q:
        sender, receiver, pulse = q.popleft()

        if pulse:
            nhi += 1
        else:
            nlo += 1

        q.extend(propagate_pulse(graph, flops, conjs, sender, receiver, pulse))

    return nhi, nlo
```

We can now write a function to find out the $P_i$ periods. First, we'll have to
identify $A$: the only conjunction module that is an input to `rx`. Then, we
have to identify each $B_i$: the only conjunction modules that are inputs to
$A$. Both these operations can be done by iterating over the `.items()` of the
`graph` we have. Since we are making assumptions, where possible, it's best to
make sure that they hold with [`assert`][py-assert].

```python
def find_periods(graph, flops, conjs):
    periodic = set() # These are B1, B2, ... BN

    for rx_source, dests in graph.items():
        if dests == ['rx']:
            # rx_source is A
            assert rx_source in conjs
            break

    for source, dests in graph.items():
        if rx_source in dests:
            assert source in conj
            periodic.add(source)

    # TODO: find periods...
```

Cool. Now, to find the periods, we can simply [`count()`][py-itertools-count]
the iterations starting from `1` and each time do a full run. Whenever we
encounter a low pulse, if the receiver is one of the $B_i$ modules we are
interested in, we will yield the current iteration count and
[`.discard()`][py-set-discard] it from our `periodic` set. We will be done when
the set is empty.

```python
from itertools import count

def find_periods(graph, flops, conjs):
    # ... same as above ...

    for iteration in count(1):
        q = deque([('button', 'broadcaster', False)])

        while q:
            sender, receiver, pulse = q.popleft()

            if not pulse:
                if receiver in periodic:
                    yield iteration

                    periodic.discard(receiver)
                    if not periodic:
                        return

            q.extend(propagate_pulse(graph, flops, conjs, sender, receiver, pulse))
```

Now we can simply call the above function and calculate the [LCM][wiki-lcm] of
all the numbers it returns using [`math.lcm()`][py-math-lcm]. First thouh, we
have to reset the state of all the flip-flops and the conjunctions. That's not
a problem it only takes a couple of `for` loops.

```python
from math import lcm

# Reset flip-flops
for f in flops:
    flops[f] = False

# Reset conjunctions
for inputs in conjs.values():
    for i in inputs:
        inputs[i] = False

answer = lcm(*find_periods(graph, flops, conjs))
print('Part 2:', answer)
```

40 stars collected, 10 more to go!

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
[d11]: #day-11---cosmic-expansion
[d12]: #day-12---hot-springs
[d13]: #day-13---point-of-incidence
[d14]: #day-14---parabolic-reflector-dish
[d15]: #day-15---lens-library
[d16]: #day-16---the-floor-will-be-lava
[d17]: #day-17---clumsy-crucible
[d18]: #day-18---lavaduct-lagoon
[d19]: #day-19---aplenty
[d20]: #day-20---pulse-propagation
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

[d08-reddit-thread]:  https://www.reddit.com/r/adventofcode/comments/18dfpub
[d08-p2]:             #part-2-7
[d12-original]:       original_solutions/day12.py
[d18-jonathan-video]: https://www.youtube.com/watch?v=UNimgm_ogrw
[d19-reddit-sankey]:  https://old.reddit.com/r/adventofcode/comments/18lyvuv
[d20-reddit-viz1]:    https://www.reddit.com/r/adventofcode/comments/18mypla
[d20-reddit-viz2]:    https://www.reddit.com/r/adventofcode/comments/18mqnrl
[2019-d06-p2]:        ../2019/README.md#part-2-5
[2021-d15-p1]:        ../2021/README.md#day-15---chiton
[2020-d13-p2-crt]:    https://github.com/mebeim/aoc/blob/master/2020/README.md#part-2---purely-mathematical-approach


[py-assert]:             https://docs.python.org/3/reference/simple_stmts.html#the-assert-statement
[py-cond-expr]:          https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-dict]:               https://docs.python.org/3/library/stdtypes.html#typesmapping
[py-dict-comprehension]: https://peps.python.org/pep-0274/
[py-gen-expr]:           https://docs.python.org/3/reference/expressions.html#generator-expressions
[py-lambda]:             https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-generators]:         https://docs.python.org/3/howto/functional.html#generators
[py-slicing]:            https://docs.python.org/3/library/stdtypes.html#common-sequence-operations
[py-unpacking]:          https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[py-builtin-abs]:             https://docs.python.org/3/library/functions.html#abs
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-iter]:            https://docs.python.org/3/library/functions.html#iter
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-next]:            https://docs.python.org/3/library/functions.html#next
[py-builtin-range]:           https://docs.python.org/3/library/functions.html#range
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-bytes-split]:             https://docs.python.org/3/library/stdtypes.html#bytes.split
[py-bytes-strip]:             https://docs.python.org/3/library/stdtypes.html#bytes.strip
[py-collections]:             https://docs.python.org/3/library/collections.html#collections
[py-collections-counter]:     https://docs.python.org/3/library/collections.html#collections.deque
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-dict-items]:              https://docs.python.org/3/library/stdtypes.html#dict.items
[py-dict-values]:             https://docs.python.org/3/library/stdtypes.html#dict.values
[py-frozenset]:               https://docs.python.org/3/library/stdtypes.html#frozenset
[py-functools-cache]:         https://docs.python.org/3/library/functools.html#functools.cache
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-heapq]:                   https://docs.python.org/3/library/heapq.html
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-itertools-cycle]:         https://docs.python.org/3/library/itertools.html#itertools.cycle
[py-itertools-pairwise]:      https://docs.python.org/3/library/itertools.html#itertools.pairwise
[py-itertools-tee]:           https://docs.python.org/3/library/itertools.html#itertools.tee
[py-list-append]:             https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-index]:              https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-pop]:                https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-math-ceil]:               https://docs.python.org/3/library/math.html#math.ceil
[py-math-floor]:              https://docs.python.org/3/library/math.html#math.floor
[py-math-lcm]:                https://docs.python.org/3/library/math.html#math.ceil
[py-math-prod]:               https://docs.python.org/3/library/math.html#math.prod
[py-operator-itemgetter]:     https://docs.python.org/3/library/operator.html#operator.itemgetter
[py-set-intersection]:        https://docs.python.org/3/library/stdtypes.html#frozenset.intersection
[py-set-difference]:          https://docs.python.org/3/library/stdtypes.html#frozenset.difference
[py-set-discard]:             https://docs.python.org/3/library/stdtypes.html#frozenset.discard
[py-str-find]:                https://docs.python.org/3/library/stdtypes.html#str.find
[py-str-isdigit]:             https://docs.python.org/3/library/stdtypes.html#str.isdigit
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-replace]:             https://docs.python.org/3/library/stdtypes.html#str.replace
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-strip]:               https://docs.python.org/3/library/stdtypes.html#str.strip
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[wiki-2048]:              https://en.wikipedia.org/wiki/2048_(video_game)
[wiki-ascii]:             https://en.wikipedia.org/wiki/ASCII
[wiki-bfs]:               https://en.wikipedia.org/wiki/Breadth-first_search
[wiki-crt]:               https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Statement
[wiki-dp]:                https://en.wikipedia.org/wiki/Dynamic_programming
[wiki-dfs]:               https://en.wikipedia.org/wiki/Depth-first_search
[wiki-dijkstra]:          https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[wiki-directed-graph]:    https://en.wikipedia.org/wiki/Directed_graph
[wiki-fifo]:              https://it.wikipedia.org/wiki/FIFO
[wiki-hash-func]:         https://en.wikipedia.org/wiki/Hash_function
[wiki-lcm]:               https://en.wikipedia.org/wiki/Least_common_multiple
[wiki-linked-list]:       https://en.wikipedia.org/wiki/Linked_list
[wiki-memoization]:       https://en.wikipedia.org/wiki/Memoization
[wiki-min-heap]:          https://en.wikipedia.org/wiki/Binary_heap
[wiki-pick-theorem]:      https://en.wikipedia.org/wiki/Pick%27s_theorem
[wiki-priority-queue]:    https://en.wikipedia.org/wiki/Priority_queue
[wiki-quadratic-formula]: https://en.wikipedia.org/wiki/Quadratic_formula
[wiki-sankey]:            https://en.wikipedia.org/wiki/Sankey_diagram
[wiki-shoelace]:          https://en.wikipedia.org/wiki/Shoelace_formula
[wiki-sparse-matrix]:     https://en.wikipedia.org/wiki/Sparse_matrix#Dictionary_of_keys_(DOK)
[wiki-taxicab]:           https://en.wikipedia.org/wiki/Taxicab_geometry
[wiki-transpose]:         https://en.wikipedia.org/wiki/Transpose
[wiki-tree]:              https://en.wikipedia.org/wiki/Tree_(graph_theory)

[misc-cpython-set-difference]: https://github.com/python/cpython/blob/e24eccbc1cf5f22743cd5cda733cd04891155d54/Objects/setobject.c#L1500
