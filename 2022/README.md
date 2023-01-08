Advent of Code 2022 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Calorie Counting][d01]
- [Day 2 - Rock Paper Scissors][d02]
- [Day 3 - Rucksack Reorganization][d03]
- [Day 4 - Camp Cleanup][d04]
- [Day 5 - Supply Stacks][d05]
- [Day 6 - Tuning Trouble][d06]
- [Day 7 - No Space Left On Device][d07]
- [Day 8 - Treetop Tree House][d08]
- [Day 9 - Rope Bridge][d09]
- [Day 10 - Cathode-Ray Tube][d10]
- [Day 11 - Monkey in the Middle][d11]
- [Day 12 - Hill Climbing Algorithm][d12]
- [Day 13 - Distress Signal][d13]
- [Day 14 - Regolith Reservoir][d14]
- [Day 15 - Beacon Exclusion Zone][d15]
- [Day 16 - Proboscidea Volcanium][d16]
- Day 17 - Pyroclastic Flow: *TODO*
- [Day 18 - Boiling Boulders][d18]
- [Day 19 - Not Enough Minerals][d19]
- [Day 20 - Grove Positioning System][d20]
- [Day 21 - Monkey Math][d21]
- Day 22 - Monkey Map: *TODO*
- Day 23 - Unstable Diffusion: *TODO*
- [Day 24 - Blizzard Basin][d24]
- [Day 25 - Full of Hot Air][d25]


Day 1 - Calorie Counting
------------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution] — [Back to top][top]

### Part 1

Welcome to AoC 2022! First day, easiest problem: we are given a list of integers
divided in chunks by empty lines, and we need to find the chunk whose integers
have the greatest sum.

There are a couple of easy ways of parsing today's input, I took advantage of a
[list comprehension][py-list-comprehension] coupled with the
[`map()`][py-builtin-map] to do this in two lines.

First, we read the entire input and [`.split()`][py-str-split] its content on
empty lines (i.e. two consecutive newline characters `\n\n`):

```python
fin = open(...)
chunks = fin.read().split('\n\n')
# ['1000\n2000\n3000', '4000', '5000\n6000']
```

To transform a single chunk from a single string into a list of integers we can
`.split()` it again and then use `tuple(map(int, chunk))` to turn it into a
[`tuple`][py-tuple] of `int` (we could also transform it into a
[`list`][py-list], but for things that should be immutable it's good practice to
use a `tuple`). To do the same for *all* chunks we can either use
[`map()`][py-builtin-map] again or a *list comprehension*. In this case, the
latter is easier to write:

```python
chunks = [tuple(map(int, chunk.split())) for chunk in chunks]
# [(1000, 2000, 3000), (4000,), (5000, 6000)]
```

We end up with a list of tuples, and now we can search for the one whose sum is
the greatest. We can now `map()` each of those tuples into the `sum()` of its
elements and then use [`max()`][py-builtin-max] to find the greatest.

```python
best = max(map(sum, chunks))
print('Part 1:', best)
```

### Part 2

For the second part, we need to find the top 3 chunks with the greatest sums and
then sum their sums.

While in general there are algorithms such as [quickselect][algo-quickselect]
that are able to find the Nth largest elements of an unsorted sequence in
[linear time][wiki-linear-time] (i.e. *O(n)*), Python sadly does not provide any
such function in its standard library. However we're still very far from needing
such a level of optimization, and the list we are dealing with is pretty small.
The "naive" solution of [`.sort()`][py-list-sort]ing the chunks (*O(nlogn)*) and
then extracting the top 3 works just fine.

We pass `reverse=True` to sort in descending order, and `key=sum` to sort the
chunks according to the sum of their elements (the `key=` function is applied to
each chunk before comparing it with others).

```python
chunks.sort(key=sum, reverse=True)
best3 = sum(map(sum, chunks[:3]))

print('Part 2:', best3)
```


Day 2 - Rock Paper Scissors
---------------------------

[Problem statement][d02-problem] — [Complete solution][d02-solution] — [Back to top][top]

### Part 1

As you may have guessed from the title, today we're playing probably one of the
oldest games in the world. We are given a list of rounds of rock-paper-scissors
composed of two letters, one for the first player and one for the second one
(us), indicating for each round who made which choice. We have to score each
round and compute the total score for us. Each round, a win is worth 6 points, a
draw 3 and a loss 0. Additionally, we get 1 point if we played rock, 2 if we
played paper and 3 if we played scissors.

The rules seem pretty simple. The only annoying thing is that rock, paper and
scissors are identified by `ABC` for the first player and `XYZ` for the second.
For any given round there are a total of 9 possible combinations of moves: `AX`,
`AY`, `AZ`, `BX`, ..., `CZ`. Given the rules, the easiest solution is to
pre-compute all possible scores for the second player:

```python
SCORES = (
    1 + 3, # A (rock)     vs X (rock)     -> draw
    2 + 6, # A (rock)     vs Y (paper)    -> win
    3 + 0, # A (rock)     vs Z (scissors) -> loss
    1 + 0, # B (paper)    vs X (rock)     -> loss
    2 + 3, # B (paper)    vs Y (paper)    -> draw
    3 + 6, # B (paper)    vs Z (scissors) -> win
    1 + 6, # C (scissors) vs X (rock)     -> win
    2 + 0, # C (scissors) vs Y (paper)    -> loss
    3 + 3, # C (scissors) vs Z (scissors) -> draw
)
```

Now if we want to know the score for the round `A Z` we can simply access
`SCORES[2]`, for `C Y` `SCORES[7]` and so on. The index to use can be calculated
by simply transforming the 3 possible moves into integers: `ABC` -> `036` and
`XYZ` -> `012` and summing them up. To make the operation easier we can
translate the entire input at once using [`str.maketrans()`][py-str-maketrans]
and [`str.translate()`][py-str-translate].

```python
table = str.maketrans('ABCXYZ', '036123')

with open(...):
    data = fin.read().translate(table)
```

The [`with`][py-with] statement used above is useful to auto-close the file once
done using it. We can also avoid decoding the input by opening it with
`open(..., 'rb')` since we already know we'll only be reading simple ASCII
characters, but in that case we'd also need to use `bytes.maketrans()` and
`bytes.translate()` instead.

Now that we read and translated the input moves into integer values, we can
iterate on each line of input, split it, parse the two integers, and use them to
index `SCORES`. As usual, [`map()`][py-builtin-map] comes in handy.

```python
score = 0

for line in data.splitlines():
    a, b = map(int, line.split())
    score += SCORES[a + b]

print('Part 1:', score)
```

### Part 2

Now we are told that the second letter does not actually represent the move of
the second player, but rather an instruction: `X` means we should play a move
that makes us lose, `Y` means we should draw, and `Z` means we should win.

This doesn't change our algorithm one bit. The only thing that changes is the
move we need to play. For example, for `A Y` the first player played "rock"
(`A`), and since we should draw (`Y`) we need to play rock too, thus the score
for the round would be `3 + 1` (draw + rock). All we need to do is declare a
second `SCORES` tuple for the second part with different precomputed scores. We
can then use the same loop we already wrote to compute the scores for both parts
together.

```python
SCORES1 = ... # SCORES from part 1, unchanged

SCORES2 = (
    0 + 3, # A (rock)     and X (lose) -> play scissors
    3 + 1, # A (rock)     and Y (draw) -> play rock
    6 + 2, # A (rock)     and Z (win)  -> play paper
    0 + 1, # B (paper)    and X (lose) -> play rock
    3 + 2, # B (paper)    and Y (draw) -> play paper
    6 + 3, # B (paper)    and Z (win)  -> play scissors
    0 + 2, # C (scissors) and X (lose) -> play paper
    3 + 3, # C (scissors) and Y (draw) -> play scissors
    6 + 1, # C (scissors) and Z (win)  -> play rock
)

score1 = score2 = 0

for line in data.splitlines():
    a, b = map(int, line.split())
    score1 += SCORES1[a + b]
    score2 += SCORES2[a + b]

print('Part 1:', score1)
print('Part 2:', score2)
```

An alternative solution to using a lookup table for pre-calculated scores would
be to "exploit" the nature of the scores themselves. It's easy to notice in the
above lookup tables that we are always repeating the same numbers over and over,
and in particular we are cycling among them depending on the move of the first
player. Thus, given any two moves (appropriately converted to integers) we can
calculate the score for the round using a simple closed-form mathematical
formula using the modulo operator. I implemented a simplified version of this
approach in my [alternative solution][d02-alternative].


Day 3 - Rucksack Reorganization
-------------------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution] — [Back to top][top]

### Part 1

For today's problem, we are dealing with strings. We are given a list of strings
of even length, one per line of input, composed of seemingly random uppercase
and lowercase letters. For each input string, there is exactly one common letter
that appears in both of its halves. Once found, we need to calculate its
"priority" using a simple rule given in the problem statement. The answer we are
looking for is the sum of all the priorities for such common letters.

First of all, let's write a short function to calculate the "priority" value of
a letter given the instructions in the problem statement. It's basically equal
to the letter's position in the English alphabet, plus 26 in case it's
uppercase. Knowing this, and given that we are dealing with [ASCII][wiki-ascii]
characters, the [`ord()`][py-builtin-ord] builtin comes in handy, as we can use
`ord(x) - ord('a')` to calculate the position of the letter in the variable `x`
in the English alphabet. Note that for this to work we must have `len(x) == 1`.

```python
def prio(x):
    if 'a' <= x <= 'z':
        return ord(x) - ord('a') + 1
    return ord(x) - ord('A') + 27
```

We can optimize the function a bit by pre-computing everything that is constant,
like for example `ord('A') + 27`. Furthermore, since we are guaranteed to only
have to deal with lowercase and uppercase ASCII letters, the check for lowercase
can be simplified to `x >= 'a'`, as lowercase letters come after uppercase ones.

```python
def prio(x):
    if x >= 'a':
        return ord(x) - 96
    return ord(x) - 38
```

We can also make use of a [ternary operator][py-cond-expr] if we wish to
simplify things even further:

```python
def prio(x):
    return ord(x) - (96 if x >= 'a' else 38)
```

Now we are ready to solve the actual problem. We'll iterate over the input one
line at a time and split each line in half. We can do this through
[slicing][py-slicing].

```python
fin = open(...)

for line in fin:
    mid = len(line) // 2
    a, b = line[:mid], line[mid:]
```

A careful reader is going to notice one small thing in the above code: we are
iterating with `for line in fin` to get lines of input, however, these lines
will still contain the trailing newline character (`\n`), which will therefore
end up in `b`. We are actually splitting the string in half correctly, since the
length is odd and doing `odd // 2` is the same as doing `(odd - 1) // 2`.
Nonetheless, we can strip the final newline from each line if we wish, using
[`map()`][py-builtin-map] and [`str.rstrip()`][py-str-rstrip]:

```python
for line in map(str.rstrip, fin):
    # ...
```

Now that we have the two halves we can simply iterate over the first one and
check which letter is present in the second one. When we find such a sletter, we
calculate its priority and stop the search, moving on to the next line of input.

```python
total = 0

for line in fin:
    mid = len(line) // 2
    a, b = line[:mid], line[mid:]

    for letter in a:
        if letter in b:
            total += prio(letter)
            break

print('Part 1:', total)
```

### Part 2

We still need to search for common letters, but this time among groups of 3
lines of input, and compute the same sum of priorities that we did before. For
example, given the following input:

```none
asdfgXjkl
qwXertyui
zxcvbnXab
lksjhagAa
Awuytiqwe
mmvxbbzAz
```

The first 3 lines of input all contain `'X'`, while the following 3 all contain
`'A'`, so the total would be `prio('X') + prio('A')`.

We can keep using the same input loop we wrote for part 1, accumulating lines
into a small temporary list (the current group). When the group list reaches a
length of `3` we will find the common letter among the lines in the group and
update the total priority for part 2.

```python
group = []
total = group_total = 0

for line in fin:
    # .. same code as part 1 ...

    group.append(line)

    if len(group) == 3:
        a, b, c = group
        group = []

        for item in a:
            if item in b and item in c:
                group_total += prio(item)
                break

print('Part 1:', total)
print('Part 2:', group_total)
```

Easy peasy! Daily puzzle solved once again.


Day 4 - Camp Cleanup
--------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution] — [Back to top][top]

### Part 1

Our job today is rather straightforward. We are given a list of pairs of integer
ranges (in the form `<start>-<end>,<start>-<end>`), and we want to count the
pairs for which one of the two ranges is fully contained within the other. A
range is fully contained within another even if they share one or both their
ends. For example, `2-3` is fully contained within `0-3`.

Let's start by parsing the input. Quite simple: [`.split()`][py-str-split] each
input line on the comma (`,`), split each of the two parts on the dash (`-`),
and turn the numbers into `int`s. We can do the integer conversion on the fly
using [`map`][py-builtin-map].

```python
fin = open(...)

for line in fin:
    a, b   = line.strip().split(',')
    a1, a2 = map(int, a.split('-'))
    b1, b2 = map(int, b.split('-'))
```

Now for each line of input we know the start and end of the two ranges. There
are a few different ways in which we could check if one range is within another,
for example computing their overlap:

```text
    a1|------------|a2
b1|---------|b2
    o1|-----|o2
      overlap
```

If the length of the overlap is equal to the length of one of the two
ranges, then that range is fully contained within the other. Or, to put it in
other words, the extremes of the overlap (`o1` and `o2`) coincide with the
extremes of the inner range.

```text
    a1|--------------|a2
         b1|-----|b2
         o1|-----|o2
           overlap
```

We can compute the extremes of the overlap by simply calculating the maximum
between the two range start values and the minimum between the two range end
values. For this purpose, we have the [`max()`][py-builtin-max] and
[`min()`][py-builtin-min] builtins.

```python
full_overlap = 0

for line in fin:
    a, b   = line.strip().split(',')
    a1, a2 = map(int, a.split('-'))
    b1, b2 = map(int, b.split('-'))

    o1 = max(a1, b1)
    o2 = min(a2, b2)

    if o1 == a1 and o2 == a2 or o1 == b1 and o2 == b2:
        full_overlap += 1

print('Part 1:', full_overlap)
```

And as easy as that, we have our solution!

Another way full overlap could have been checked is through simple logic
formulas:

```python
for line in fin:
    # ...

    #        b inside a               a inside b
    if a1 <= b1 and a2 >= b2 or b1 <= a1 and b2 >= a2:
        full_overlap += 1
```

However, as we'll shortly see, computing the overlap also helps us solve part 2
effortlessly.

### Part 2

Now we want to count the number of range pairs that overlap in any way, either
*partially* or fully (part 1).

We know that all the cases counted in part 1 will also count for part two, since
if one range is fully contained within another, there is a full overlap. To also
take into account *partial* overlaps, we can simply check the two extremes of
the overlap we just calculated.

```text
    a1|------------|a2     |            a1|--------|a2
b1|---------|b2            |   b1|--|b2
    o1|-----|o2            |        |o2 o1|
      overlap (o2 >= o1)   |       no overlap (o2 < o1)
```

As can be seen in the above example, if the end of the overlap (`o2`) is after
the start (`o1`) then we have a valid range and an overlap (partial or full)
must exist.

All of this simply means adding one check to our part 1 code, and since we know
that a full overlap is a special case of a partial overlap, we can move the part
1 check inside the part 2 one.

```python
overlap = full_overlap = 0

for line in fin:
    # ... same as part 1 ...

    if o2 >= o1:
        overlap += 1
        if o1 == a1 and o2 == a2 or o1 == b1 and o2 == b2:
            full_overlap += 1

print('Part 1:', full_overlap)
print('Part 2:', overlap)
```

Et voilà! 8 out of 50 stars.


Day 5 - Supply Stacks
---------------------

[Problem statement][d05-problem] — [Complete solution][d05-solution] — [Back to top][top]

### Part 1

Do you like simulations? Today we're gonna need to simulate a crane moving
crates stacked on top of each other. We start with a few stacks of crates, given
as input in the following form:

```none
    [D]
[N] [C]
[Z] [M] [P]
 1   2   3
```

This represents the initial configuration of N stacks of crates (in the above
example we have N = 3, but in the real input N = 9). Following the initial
configuration is an empty line followed by a list of instructions, one per line,
of the form `move <n> from <i> to <j>`, meaning "move the top `n` crates from
stack `i` to stack `j`, one at a time.

After executing all instructions, we need to answer with a string of letters
representing the topmost crate of each stack in order. For example, if the above
configuration was the final one, we would answer `NDP`.

Today's input is particularly annoying to parse: we are given stacks in fancy
ASCII art columns, and we need to somehow turn each one into a string or list in
order to work with it. The easiest way to approach this is probably to just read
the entirety of the first few lines of input, stopping at the first empty line,
and then *transpose* them to obtain a list of columns. In other words, do
something like this:

```none
 +----------> ' [[ '
 |+---------> ' NZ1'
 ||+--------> ' ]] '
 |||+-------> '    '
 ||||+------> '[[[ '
 |||||+-----> 'DCM2'
 ||||||+----> ...
 |||||||
'    [D]    '
'[N] [C]    '
'[Z] [M] [P]'
' 1   2   3 '
```

After reading the initial ASCII art and stopping at the first empty line:

```python
fin = open(...)
raw = []

for line in fin:
    if line == '\n':
        break
    raw.append(line)

# raw = ['    [D]    \n',
#        '[N] [C]    \n',
#        '[Z] [M] [P]\n',
#        ' 1   2   3 \n']
```

We can transpose the `raw` list with the help of [`zip()`][py-builtin-zip] plus
an [unpacking operator][py-unpacking]:

```python
columns = list(zip(*raw))
# [(' ', '[', '[', ' ', '\n'),
#  (' ', 'N', 'Z', '1', '\n'),
#   ...                      ]
```

This seemingly esoteric single-line transposition works because `zip()` yields
tuples consisting of the i-th element of each line in `raw`, i.e. it effectively
yields columns.

We went from strings to tuples, but that's no problem for now. The next thing to
do is skip all the useless columns (those consisting of only spaces and square
brackets) and keep the rest, turning good columns into strings through
[`str.join()`][py-str-join] and discarding leading whitespace with
[`str.lstrip()`][py-str-lstrip].

Fortunately, all we need to identify good columns is
[`enumerate()`][py-builtin-enumerate], skip the first column and then only keep
one every 4, which can be achieved using the modulo (`%`) operator.

```python
# Indexes in the instructions are 1-based, fill stacks[0] with some useless
# value so that later we can do stacks[i] instead of stacks[i - 1].
stacks = [None]

for i, column in enumerate(zip(*raw)):
    if i % 4 == 1:
        # column = (' ', 'N', 'Z', '1', '\n')
        column = ''.join(column[:-1]) # -> ' NZ'
        column = column.lstrip()      # -> 'NZ'
        stacks.append(column)

# Make a copy to use for part 2
original = stacks[:]
```

Now that we *finally* have the initial stacks parsed, let's also parse the
instructions. This is quite simple: iterate over input lines, split them and
extract the three numbers at positions `1`, `3` and `5`:

```python
moves = []

for line in fin:
    line = line.split()
    moves.append((int(line[1]), int(line[3]), int(line[5])))
```

We have the instructions parsed, now let's simply follow them:

```python
for n, i, j in moves:
    for _ in range(n):
        crate = stacks[i][0]          # Extract top of stacks[i]
        stacks[i] = stacks[1:]        # Remove it from stacks[i]
        stacks[j] = crate + stacks[j] # Add it to top of stacks[j]
```

We can optimize the above operation by extracting all `n` crates at once and
reversing their order with `crates[::-1]`, a common Python trick to reverse an
indexable iterable through [slicing][py-slicing]:

```python
for n, i, j in moves:
    crates = stacks[i][:n][::-1]
    stacks[i] = stacks[i][n:]
    stacks[j] = crates + stacks[j]
```

Finally, we can extract the topmost element of each stack using a simple
[generator expression][py-generator-expr] and `.join()` the result into a
string:

```python
top = ''.join(s[0] for s in stacks[1:]) # Skip stacks[0], which is None
print('Part 1:', top)
```

### Part 2

For part two, we need to follow the same list of instructions as part 1, but
this time moving *all* of the topmost `n` crates from a given stack to another
at once, meaning that their final order on top of the second stack will *not* be
reversed.

Well, given the code we already wrote, this is really child's play. We can use
the same code as part 1, removing the reversing operation (`[::-1]`):

```python
# Restore initial state from the copy we made earlier
stacks = original

for n, i, j in moves:
    crates = stacks[i][:n] # <- removed [::-1] from here
    stacks[i] = stacks[i][n:]
    stacks[j] = crates + stacks[j]

top = ''.join(s[0] for s in stacks[1:])
print('Part 2:', top)
```


Day 6 - Tuning Trouble
----------------------

[Problem statement][d06-problem] — [Complete solution][d06-solution] — [Back to top][top]

### Part 1

Today's problem feels like it could have been a day 1 problem. In fact, I
believe it was even easiest than this year's day 1. We are given a long string
of seemingly random characters as input, and we need to find the first group of
4 consecutive characters that are all different, called the "start-of-packet".
Once found, our answer will be the 1-based index of the character immediately
following the start-of-packet.

After reading the whole file as a string:

```python
with open(...) as fin:
    data = fin.read()
```

We can extract groups of 4 consecutive characters starting at index `i` just
doing `data[i:i + 4]`. To check whether they are all different, a quick and easy
way is to simply put them all inside a `set` and calculate the size of the set:
if the size is 4, it means all 4 were different.

```python
for i in range(len(data) - 4):
    if len(set(data[i:i + 4])) == 4:
        sop = i + 4
        break

print('Part 1:', sop)
```

You technically do not need to build the entire set in order to perform this
check: you can add the characters to the set one by one and stop at the first
one that is already present. However, since we are talking about merely 4
characters, such an optimization would just be pointless.

### Part 2

We need to... do the same thing as before, only that we are looking for a
"start-of-message" consisting of *14* different consecutive characters now.

Well, the code is the same as part 1, so let's just move it into a function. We
also know for a fact that our "start-of-message" cannot appear before the
"start-of-packet" (we do not have 4 consecutive different characters before the
start-of-packet, let alone 14), so let's also give our function the ability to
skip the start of the data for performance.

```python
def find_start(data, header_len, start=0):
    for i in range(start, len(data) - header_len):
        if len(set(data[i:i + header_len])) == header_len:
            return i + header_len
```

Here we go, we can now get both part 1 and part 2 answers using this function:

```python
sop = find_start(data, 4)
som = find_start(data, 14, sop)
print('Part 1:', sop)
print('Part 2:', som)
```


Day 7 - No Space Left On Device
-------------------------------

[Problem statement][d07-problem] — [Complete solution][d07-solution] — [Back to top][top]

### Part 1

First challenging problem of the year today! We are dealing with a filesystem,
and we are given the output of a shell session where the only two commands used
are `cd` to change directory and `ls` to list the current directory's contents.
Each line of input that starts with `$` indicates a command, and the following
lines that don't start with `$` are the command's output.

Simply enough, only the `ls` command generates output. Each directory can
contain other directories or files, and the `ls` command prints out a list where
each directory name is preceded by the string `dir` and each file name is
preceded by its size.

The total size of a directory is the sum of the sizes of the files it contains,
either directly or inside other subdirectories. We are asked to find all
directories with total size up to 100000 and sum all their sizes.

First of all, let's see an example input to help us understand what we're
talking about:

```none
$ cd /
$ ls
dir a
1000 b.txt
699 c.dat
$ cd a
$ ls
100 d
200 e
```

Given the above shell session, we can infer the contents of `/` and `/a`, and we
know that the filesystem looks like this:

```none
/
├── a
│   ├── d, size 100
│   └── e, size 200
├── b.txt, size 1000
└── c.dat, size 699
```

The total size of the directory `/a` is `100 + 200 = 300`, and the total size of
`/` is `300 + 1000 + 699 = 1999`.

Since the size of a directory will need to be calculated recursively entering
all its descendant directories and finding all the files contained within them,
it's pretty obvious that we'll need to somehow reconstruct the structure of the
filesystem to fulfill our request. We can represent the filesystem as a
[tree][wiki-tree] structure, where the root is `/`.

Parsing the input line by line, one option would be to store the size of each
file and the contents of each directory in a dictionary, for example like this:

```python
fs = {
    '/': ['a', 'b.txt', 'c.dat'],
    'a': ['d', 'e'],
    'd': 100,
    'e': 200,
    'b.txt': 1000,
    'c.dat': 699,
}
```

However, this is not enough, because directory and file names are not unique.
There could be for example multiple directories, each containing a file with the
same name. Even worse, there could be one directory containing a file, and
another one containing a directory with the same name as the file! Indeed, we
should already know, the thing that uniquely identifies a file or directory in a
filesystem is not its name, but its *path*. The path to the file `d` in the
above example would be `/a/d`.

Given the input, and starting with an empty path, we should be able to keep
track of the current path by simply looking at the `cd` commands that are
performed. For simplicity, we'll use a `tuple` to represent a path instead of a
string of path components separated by slashes, meaning that the path `/a/d`
will be represented by the tuple `('/', 'a', 'd')`. This will make it easier to
add and remove path components as needed.

The output we want is a dictionary of the form `{path: list_of_contents}`. Since
we do not care about file names at all, instead of storing their names we'll
simply store their size as an integer. Later, when iterating over the list of
contents of a given path, we'll know that anything that is an integer is the
size of a file. Furthermore, we also do not care about directories that we do
not explicitly enter through the `cd` command. If some `ls` command lists 100
directories, but we only enter one of them, that's the only one we care about.
We can therefore skip all the lines of `ls` output that start with `dir`. Our
input seems to be "well-formed", and seems to suggest that we actually enter
with `cd` every single directory that is listed by a `ls` command, but still.

We'll parse the input one line at a time, like so:

- Each time we encounter a `cd` command, we'll add a component to the current
  path. If we encounter the special component `..` we'll remove the last
  component from the current path instead.
- Each time we encounter a `ls` command, we'll start reading the following lines
  until the next command. Each line can either be `dir <dirname>` or
  `<size> <filename>`. We will completely skip lines starting with `dir`, and
  for the others we'll only parse the file size as an integer, adding it to the
  list of the contents of the current directory.

As already said, we'll use a dictionary to keep track of the contents of each
path we encounter. More precisely, to make things easier, a
[`defaultdict`][py-collections-defaultdict] of `list` comes in handy, so that we
can just do `fs[path].append(...)` without worrying about `path` not being
already present in `fs`. A [`deque`][py-collections-deque] (double-ended queue)
is also useful to process the input line by line while being able to peek at the
next line without consuming it, since we want to stop parsing the output of the
`ls` command whenever we encounter a line starting with `$`. We can peek the
first element of a `deque` with `d[0]`, and consume it by popping it with
`d.popleft()`. The same could be done with a normal list through `l.pop(0)`, but
the operation is much more expensive as it internally requires to move all
elements of the list back one position after removing the first one.

Here's a function that implements the above logic taking advantage of
`defaultdict` and `deque`:

```python
from collections import deque, defaultdict

def parse_filesystem(fin):
    lines = deque(fin)
    fs    = defaultdict(list)
    path  = ()

    while lines:
        line    = lines.popleft().split() # ['$', 'cd', 'foo']
        command = line[1]
        args    = line[2:] # ['foo'] or [] in case the command is `ls`

        if command == 'ls':
            # The `ls` command outputs a list of directory contents, keep going
            # until we either run out of lines or the next line is a command
            while lines and not lines[0].startswith('$'):
                # Get the size of the file
                size = lines.popleft().split()[0]

                # Skip if not a file
                if size == 'dir':
                    continue

                # Add the size of the file to the contents of the current path
                fs[path].append(int(size))
        else:
            # The `cd` command has no output, but changes the current path
            if args[0] == '..':
                # Discard last path component (go up one directory)
                path = path[:-1]
            else:
                # Calculate path of the directory we are moving into
                new_path = path + (args[0],)
                # Add its path to the contents of the current directory
                fs[path].append(new_path)
                # Move into the new directory
                path = new_path

    return fs
```

The result of calling `parse_filesystem()` using the example input we saw
earlier should be something like this:

```python
with open(...) as fin:
    fs = parse_filesystem(fin)

# fs = {
#     ()        : [('/',)],
#     ('/',)    : [('/', 'a'), 1000, 699],
#     ('/', 'a'): [100, 200]
# }
```

The extra empty tuple `()` is an artifact of the fact that we start with an
empty path (`path = ()`), and the first command is `cd /`, so effectively our
actual root is `()`, but it only contains `('/',)` so there isn't much
difference. If we wanted to avoid this, we could have started with
`path = ('/',)` skipping the first command.

Technicalities aside, now we have a dictionary that represents the tree of our
filesystem. In order to calculate the size of a single directory we need to
traverse the tree starting at its path, and sum up any file sizes we find along
the way. The simplest way to do this is through a
[depth-first search][algo-dfs], which, given the data structure we have, can be
implemented as a recursive function in just a few lines of code. All we have to
do given a path is iterate over `fs[path]` and check whether the current item is
an `int` (size of a file) or another path representing a subdirectory. In the
first case, we'll just add the size to the total, while in the second case we'll
make a recursive call to determine the size of the subdirectory. The
[`isinstance`][py-builtin-isinstance] built-in function can be used to check for
`int`s, as well as the [`type`][py-builtin-type] built-in, it's more or less a
matter of taste.

```python
def directory_size(fs, path):
    size = 0

    for subdir_or_size in fs[path]:
        if isinstance(subdir_or_size, int):
            # File, add size to total
            size += subdir_or_size
        else:
            # Directory, recursively calculate size
            size += directory_size(fs, subdir_or_size)

    return size
```

Now we have all we need to solve the problem. We'll iterate over all the keys of
`fs` (representing all the paths of the directories we know) and call
`directory_size()` for each one of them, summing up the sizes that are less than
100000.

There is a small performance issue though: calling the `directory_size()`
function we just wrote for every single path is not optimal. It's a recursive
function that will traverse the whole tree starting from `path` every time it's
called, however we only need a single traversal (starting at the root `('/',)`)
to kno the size of any directory. We can save this information into a dictionary
before returning from the function.

```python
def directory_size(fs, path, output):
    size = 0

    for subdir_or_size in fs[path]:
        if isinstance(subdir_or_size, int):
            size += subdir_or_size
        else:
            size += directory_size(subdir_or_size)

    output[path] = size
    return size
```

This only traverses the entire `fs` tree once and saves the size of each
directory into a dictionary of the form `{path: size}`. After a single call
starting from the root, we'll know the size of any directory:

```python
sizes = {}
directory_size(fs, ('/',), sizes)

small_dir_total = 0
for sz in sizes.values():
    if sz <= 100000:
        small_dir_total += sz
```

Alternativelt, we could also use [memoization][wiki-memoization] to cache the
results of `directory_size()` calls, and keep calling the function regardless.
This is an easy to implement solution since Python 3 already provides us with a
decorator to implement memoization out of the box:
[`functools.lru_cache`][py-functools-lru_cache]. For those who are interested, I
explained memoization and the use of `lru_cache` in more detail towards the end
of [2019 day 18 part 1][2019-d18-p1].

```python
@lru_cache(maxsize=None)
def directory_size(path):
    size = 0

    for subdir_or_size in fs[path]:
        if isinstance(subdir_or_size, int):
            size += subdir_or_size
        else:
            size += directory_size(subdir_or_size)

    return size
```

Now no matter how many times we call `directory_size()`, the calculation is only
performed *once* for any given `path` on the first call and cached automatically
by `lru_cache` to be reused for subsequent calls. This however

In any case, we finally have our solution:

```python
small_dir_total = 0

for path in fs:
    sz = directory_size(path)
    if sz <= 100000:
        small_dir_total += sz

print('Part 1:', small_dir_total)
```

As a bonus, this can also be rewritten as a one-liner with the help of
[`filter`][py-builtin-filter], [`map`][py-builtin-map] and a
[`lambda`][py-lambda]:

```python
small_dir_total  = sum(filter(lambda s: s <= 100000, map(directory_size, fs)))
print('Part 1:', small_dir_total)
```

Though I would honestly avoid it for readability.

### Part 2

The bulk of the work is done, now we want to find a single directory to delete
to free some space on the disk. The total available space is 70000000, and we
need at least 30000000 of it free. We need to find the size of the smallest
directory that can be deleted in order to end up with a free space of at least
30000000.

Well, we already have the code to do everything, all we need to do is add a
couple of variables and another `if` inside the final `for` loop used to
calculate the answer for part 1:

```python
used = directory_size(('/',))
free = 70000000 - used
need = 30000000 - free

small_dir_total  = 0
min_size_to_free = used

for path in fs:
    sz = directory_size(path)

    if sz <= 100000:
        small_dir_total += sz

    if sz >= need and sz < min_size_to_free:
        min_size_to_free = sz

print('Part 1:', small_dir_total)
print('Part 2:', min_size_to_free)
```

Ta-dah! Thankfully an easier part 2 than part 1, and nothing too weird.


Day 8 - Treetop Tree House
--------------------------

[Problem statement][d08-problem] — [Complete solution][d08-solution] — [Back to top][top]

### Part 1

The long-awaited grid of characters strikes back. This time we are dealing with
trees. We are given a grid of tree heights, each represented by a single digit
between `0` and `9`, and we need to count how many trees are visible from
outside the grid. A tree is considered visible from outside the grid if it is
taller than any other tree in at least one of the four cardinal directions
(looking north, south, east or west).

Obviously, all trees on the perimeter of the grid are visible from the outside,
but what about the inner ones?

Let's start by parsing the input data. Transforming each digit of each line into
an `int` seems natural, but it's unneeded. We are, as usual, dealing with plain
[ASCII][wiki-ascii] characters, and the byte values of the digits `0` through
`9` in ASCII are ascending (from `0x30` to `0x39`). If we open the input file in
binary mode, we can simply use [`.splitlines()`][py-bytes-splitlines] and we'll
have a list of `bytes` objects (one per line), and iterating over `bytes`
already yields integers. We could do the same by opening the file in text mode
(the default), since `'1' > '0'` still holds for strings too, but decoding is
unneeded.

```python
with open(..., 'rb') as fin:
    grid = fin.read().splitlines()
```

As already said, all the trees on the perimeter of the grid are visible, and we
can pre-calculate this number to save time: it's simply `H * 2 + W * 2 - 4` (the
`- 4` is needed to avoid counting vertices twice). While we are at it, let's
also calculate a couple of useful values for later.

```python
height, width = len(grid), len(grid[0])
maxr, maxc = height - 1, width - 1
visible = height * 2 + width * 2 - 4
```

We'll use two nested `for` loops to iterate over the entire grid. Since we
already pre-computed the visibility of the perimeter of the grid, we can skip
it, which means starting our iterations from `1` and stopping right before
`maxr` and `maxc` (calculated above). We'll also keep the current row in a
variable, to avoid double-indexing the grid where possible.

```python
for r in range(1, maxr):
    row = grid[r]

    for c in range(1, maxc):
        tree = row[c]

        ...
```

To know whether a tree is visible from outside the grid on the east side we can
iterate the current `row` starting from `c + 1` up to its end, and check if our
`tree` is higher than all of them. If not, there is no visibility from east.

```python
        # ... continues from above

        visible_from_east = True
        for t in row[c + 1:]:
            if tree <= t:
                visible_from_east = False
```

Let me take a second to make a small digression. It should be noted that in
general doing something like `row[c + 1:]` is not that good of an idea, since in
Python slicing lists, tuples, strings, bytes or similar collections *performs a
copy* of the sliced values. Clearly a copy is unneeded if we don't need to
modify the data and only slows things down, more so if the operation is
performed on large collections or repeated a lot of times. This is a pretty
unfortunate design flaw of the language that we can get around in a couple
different ways, including using external libraries such as [NumPy][misc-numpy],
since [by default slices of NumPy arrays return *views*][misc-numpy-views]
instead of performing copies. In our case, the input grid is 99 by 99, which is
a pretty small size, so we can get away with all this unnecessary copying to
keep the code more concise and easier to read, but be warned that in general
this isn't the case.

Back to the problem. The kind of loop we just wrote is exactly what the
[`all()`][py-builtin-all] built-in function was invented for: using `all()`
together with a [generator expression][py-generator-expr] gives us a one-liner
equivalent to the above loop that is also easily readable:

```python
visible_from_east = all(tree > t for t in row[c + 1:])
```

Analogously, we can do the same thing for west, south and north. The only hiccup
is that for south and north we don't have a nice `column` variable to iterate
over, and we'll have to iterate over the `grid` with an index instead of using
[`range()`][py-builtin-range].

```python
visible_from_east  = all(tree > t for t in row[c + 1:])
visible_from_west  = all(tree > t for t in row[:c])
visible_from_south = all(tree > grid[i][c] for i in range(r + 1, len(grid)))
visible_from_north = all(tree > grid[i][c] for i in range(r - 1, -1, -1))
```

Now, in theory, a tree is visible from outside the grid if *any* of the above
variables is `True`, so we are doing unneeded work. For example, if
`visible_from_east` is `True`, we don't need to calculate the rest, and the same
goes for the others. Since we are in a loop, we could use `continue` to skip
right to the next iteration when any of the four is satisfied:

```python
for r in range(1, maxr):
    row = grid[r]

    for c in range(1, maxc):
        tree = row[c]

        if all(tree > t for t in row[c + 1:]): # east
            visible += 1
            continue

        if all(tree > t for t in row[:c]): # west
            visible += 1
            continue

        # Same for south and north...
```

However, if we save the generators in a variable instead of feeding them to
`all()` immediately we can also do this without duplicating much code with a
single `if` statement, retaining the lazyness of the operation with a simple
`or`, which only evaluates its right operand if the left one is `False`.

```python
for r in range(1, maxr):
    row = grid[r]

    for c in range(1, maxc):
        tree = row[c]

        east  = (tree > t for t in row[c + 1:])
        west  = (tree > t for t in row[:c])
        south = (tree > grid[i][c] for i in range(r + 1, len(grid)))
        north = (tree > grid[i][c] for i in range(r - 1, -1, -1))

        if all(east) or all(west) or all(south) or all(north):
            visible += 1

print('Part 1:', visible)
```

### Part 2

For the second part we need to do a similar job, but this time we want to find
out *how far can we see from the top of a given tree* in the four cardinal
directions. Being on top of a tree, we can only see in a certain direction up
until our view is blocked by a taller tree. For each tree, we need to calculate
a *score* equal to the product of the viewing distances in the four directions.
Out of all these scores, we must then find the highest.

As an example, given the following small grid:

```
8303730
9255124
3677320
```

The tree with height `5` in the middle of the grid can see `1` unit north, `3`
units east, `1` unit south and `1` unit west (blocked by the other `5`). Its
score would then be `1 * 3 * 1 * 1 = 2`.

Calculating the view distance in each direction is pretty similar to what we
just did for part 1, except that we need to *count* how many grid cells we pass
before stopping because of a higher tree. Well, if we use plain and simple (but
also boring) `for` loops instead of writing fancy generator expressions, we can
do this pretty easily.

For example, for east:

```python
for r in range(1, maxr):
    row = grid[r]
    for c in range(1, maxc):
        tree = row[c]

        for i in range(c + 1, width):
            if row[i] >= tree:
                break

        view_east = i - c
```

Doing the same for all directions, and adding the formula to calculate the
score, we have the solution for part 2:

```python
for r in range(1, maxr):
    row = grid[r]

    for c in range(1, maxc):
        tree = row[c]

        for east in range(c + 1, width):
            if row[east] >= tree:
                break

        for west in range(c - 1, -1, -1):
            if row[west] >= tree:
                break

        for south in range(r + 1, height):
            if grid[south][c] >= tree:
                break

        for north in range(r - 1, -1, -1):
            if grid[north][c] >= tree:
                break

        score = (east - c) * (c - west) * (south - r) * (r - north)

        if score > best:
            best = score

print('Part 2:', best)
```

Technically, the code for both parts could be easily joined together into the
same extended loop we just wrote for part 2, but I liked the concise part 1 code
using `all()` with generator expressions, so I kept it in my final solution.

### Reflections

The algorithms I implemented for today's part 1 and part 2 scan the grid in four
direction for every single grid cell. This means that in the worst case scenario
we are potentially scanning the entire grid 4 times per single tree. For a
square grid of side *n* there are *n<sup>2</sup>* trees, thus the computational
complexity of these algorithm is at worst
*O(4n<sup>2</sup>n<sup>2</sup>) = O(n<sup>4</sup>)* operations.

That honestly doesn't sound very good. Indeed, there is a smarter solution, at
least for part 1, which achieves the same result in *O(n<sup>2</sup>)*
operations only:

- Scan the entire matrix once per direction.
- For each row/column, keep track of the tallest tree while scanning.
- Mark all the trees taller than the tallest as visible from outside the grid.
- As a bonus: stop scanning the current row/column when the tallest tree
  encountered is a `9`.

I implemented this approach in [my alternative solution][d08-alternative] for
those that are curious.

For part 2, a similar logic can be used, keeping track of the last time a tree
of *each possible height* was seen, and using such information to instantly
compute the view distance from any encountered tree in the current scanning
direction. This requires a bit more effort though, and I did not have time to
re-implement my part 2 solution using this approach.


Day 9 - Rope Bridge
-------------------

[Problem statement][d09-problem] — [Complete solution][d09-solution] — [Back to top][top]

### Part 1

2D grids again, huh? Today we're not really taking a grid as input, but moving
through one instead. Given a list of moves of the form `<direction> <N>` (e.g.
`R 5`) we need to simulate the movements of a small piece of rope by tracking
the position of its head and tail in a grid. The rope moves head first one step
at a time in any of the four cardinal directions, and the tail will always stay
"attached" to the head, meaning in one of the 8 neighboring cells. Whenever the
head makes a movement that separates it from the tail, the tail also moves
toward the head in the nearest cell that is directly above, below, left or right
of the head. We need to count the number of different positions the tail will
occupy while simulating all the moves in our input.

An example makes it easier to understand what is going on. Let's analyze the
movement of the head and tail, given that they start in the same spot and the
moves to perform are `R 2` followed by `U 2`:

```none
...      ...      ...      ...      ..H
...  ->  ...  ->  ...  ->  ..H  ->  ..T
H..      TH.      .TH      .T.      ...
```

As can be seen above, when the head (`H`) moves up one cell, the tail (`T`) is
still "attached" to it. However, the second movement of the head would cause the
tail to disconnect, thus it moves *towards the head*.

If we zoom in and break a single transition in two steps, the movement of the
tail will be clearer:

```none
.   .   .      .   .   .      .   .   .

.   .   .  =>  .   .   .  =>  .   .   .

T   H   .      T-------H      .   T   H
```

In the simple case where the head moves, but stays on the same horizontal or
vertical line as the tail, the movement of the tail is straightforward: it wants
to move towards the head following the segment depicted above, and so it simply
needs to move one unit in the right direction.

The second, not-so-obvious case is when the head moves while not on the same
horizontal/vertical line as the tail:

```none
.   .   .      .   .   H      .   .   H
                      /
.   .   H  =>  .   . / .  =>  .   .   T
                    /
.   T   .      .   T   .      .   .   .
```

Again, the instant after the head moves up, the tail becomes disconnected, and
thus must move towards the head. The tail wants to follow the straight segment
plotted above, thus it moves up one unit and right one unit, ending up right
below the head.

To generalize: whenever the tail becomes disconnected, it will move in the
direction "suggested" by the imaginary segment connecting it straight to the
head. Thus, if this segment is parallel to the grid axes, the movement is a
simple step (up, down, left or right), otherwise the movement will be a larger
*diagonal* step in the same direction as the segment.

Oookay. Now that we (hopefully) understood how this dance of head and tail rope
movements works, let's start coding. First of all, since for each input move
we'll have to simulate all the steps, let's make things easier with a dictionary
of deltas to apply to make a single step given a direction:

```python
# {direction: (deltax, deltay)}
DELTA = {'U': (0, 1), 'D': (0, -1), 'L': (-1, 0), 'R': (1, 0)}
```

In order to keep track of head and tail positions we'll use 4 variables as two
2D coordinates. Parsing the input is only a matter of [`.split()`][py-str-split]
and conversion to `int`, and the movement of the head can be done with an
addition after looking up the right delta on both axes using the dictionary we
just defined.

```python
hx, hy = 0, 0
tx, ty = 0, 0

with open(...) as fin:
    for line in fin:
        direction, steps = line.split()
        steps = int(steps)

        for _ in range(steps):
            deltax, deltay = DELTA[direction]
            hx += deltax
            hy += deltay

            # Move the tail somehow...
```

Okay, now we are simulating the movement of the head, but we also need the tail
to follow along. We can represent the segment that the tail wants to follow as
2D vector, meaning another couple of variables: `dx` and `dy`, which can be
easily calculated:

```python
dx = hx - tx
dy = hy - ty
```

Now, how do we know if the head moved too far from the tail? We can use
[Euclidean distance][wiki-euclidean-distance] for that. The 8 possible cells
surrounding the head will always be at an Euclidean distance of at most *√(2)*
(square root of 2) units. That is, the four cells above, below, left and right
will have a distance of *1* unit, while the other four cells will have a
distance of *√(1<sup>2</sup>+1<sup>2</sup>) = √(2)* units. Thus, the tail needs
to move and follow the head *IFF √(dx<sup>2</sup>+dy<sup>2</sup>) > √(2)*. If we
get rid of the square root by squaring both sides, we are left with the
condition *dx<sup>2</sup>+dy<sup>2</sup> > 2*.

How does the tail need to move? Well, following `dx` and `dy`. If `dx` is
positive, it moves one unit to the right, while if it's negative it moves one
unit to the left. If `dx` is zero it means that either the tail is right on top
of the head, or that it's on its same horizontal line: either way, it does not
need to move along the *x* axis (left or right). The same reasoning applies to
`dy`.

Following these conclusions, and using a [`set`][py-set] to keep track of all
the different coordinates visited by the tail, we have the complete solution:

```python
hx, hy = 0, 0
tx, ty = 0, 0
seen = {(0, 0)}

with open(...) as fin:
    for line in fin:
        direction, steps = line.split()
        steps = int(steps)

        for _ in range(steps):
            deltax, deltay = DELTA[direction]
            hx += deltax
            hy += deltay
            dx = hx - tx
            dy = hy - ty

            if dx**2 + dy**2 > 2:
                if dx != 0:
                    tx += 1 if dx > 0 else -1
                if dy != 0:
                    ty += 1 if dy > 0 else -1

                seen.add((tx, ty))
```

The use of the [conditional expression][py-cond-expr] `1 if dx > 0 else -1`
could be simplified. After all, what we are doing is merely taking the *sign* of
`dx`. As it turns out though, Python does not have a built-in for the sign of a
number, apparently because [the authors of the language could not
agree][misc-py-sign] on what such a function would return in special cases (e.g.
`0` or `NaN`). We can however write our own `sign()` function to take care of
this, and make it return `0` in case the given value is `0`.

```python
# Intuitive implementation, the first one you'd probably think of
def sign(x):
    if x == 0:
        return 0
    return 1 if x > 0 else -1

# More clever, branchless implementation:
def sign(x):
    return (x > 0) - (x < 0)
```

And now we have:

```python
            # ...
            if dx**2 + dy**2 > 2:
                tx += sign(dx)
                ty += sign(dy)
            # ...
```

In any case, after the main loop is done, we have all the different coordinates
visited by the tail in our `seen` set, and the solution is one `len()` away:

```python
different_tail_positions = len(seen)
print('Part 1:', different_tail_positions)
```

### Part 2

Now our rope becomes longer. It's composed of 10 pieces in total (including the
head). The rules to follow are the same as before, but now every piece follows
the one in front of it. The tail is the last piece, and we still need to
count the number of different positions occupied by it.

We can re-write our solution to keep track of a `list` of 2D coordinates instead
of just four variables. Furthermore, we can solve both parts together, since
part 1 fundamentally asks us to keep track of the second piece of the rope, and
part 2 asks us to keep track of the tenth:

```python
rope  = [(0, 0)] * 10
seen1 = {(0, 0)}
seen9 = {(0, 0)}
```

The only thing that actually changes is that the logic used to move the tail for
part 1 now needs to be applied 9 times (once per piece following the head).
Each time, any given piece follows the one in front of it. Instead of going
through each step again, I'll just let the code speak for itself with the help
of a few comments:

```python
with open(...) as fin:
    for line in fin:
        direction, steps = line.split()
        steps = int(steps)

        for _ in range(steps):
            hx, hy = rope[0]
            dx, dy = DELTA[direction]

            # Move the head
            rope[0] = hx + dx, hy + dy

            for i in range(9):
                # Consider this piece as the "head"
                hx, hy = rope[i]
                # And the one after it as the "tail"
                tx, ty = rope[i + 1]

                # Do the exact same thing we did for part 1
                dx, dy = hx - tx, hy - ty
                if dx**2 + dy**2 > 2:
                    tx += sign(dx)
                    ty += sign(dy)
                    rope[i + 1] = (tx, ty)

            # Keep track of both the second and the last pieces
            seen1.add(tuple(rope[1]))
            seen9.add(tuple(rope[9]))

answer1 = len(seen1)
answer2 = len(seen9)
print('Part 1:', answer1)
print('Part 2:', answer2)
```


Day 10 - Cathode-Ray Tube
------------------------

[Problem statement][d10-problem] — [Complete solution][d10-solution] — [Back to top][top]

### Part 1

It wouldn't be Advent of Code without some kind of virtual machine to implement!
Today's puzzle requires us to implement a VM that only has one register `X` and
knows two instructions: `noop` and `addx n`. The first one has a duration of
1 cycle and does nothing, while the second one has a duration of 2 cycles and
adds the immediate value `n` to `X` *after* the two cycles have passed.

We start at the first cycle, and need to emulate a list of instructions. Then,
starting from cycle 20 and every 40 cycles after that (60, 100, 140, ...) we
need to calculate the product of the current value of `X` and the current cycle
number. Summing up all these products together will give us the answer for part
1.

Seems quite simple. The only pitfall is that the `addx` instruction takes ***2
cycles*** instead of 1, and one of those could be the one we are interested in
(where we need to compute the product). Not a real problem: whenever we
encounter an `addx` we'll just need to repeat the cycle increment twice and
check its value in between these two increments.

We don't need to do much input parsing, let's just get everything into a list
with [`.readlines()`][py-file-readlines]. We could also wrap our main loop
inside a `with` statement as we did [yesterday][d09] and read the file one line
at a time if we want.

```python
with open(...) as fin:
    program = fin.readlines()
```

Now we'll start a simple loop `for instr in program`, incrementing a cycles
counter at the start of each iteration. We'll skip the `noop` instructions
completely as they do nothing else, while for `addx` we'll need to increment the
counter a second time and perform the addition on the `X` register.

```python
total = 0
cycle = 1
x     = 1

for instr in program:
    cycle += 1

    if instr.startswith('addx'):
        # Check cycle and calculate product

        # Increment again and perform the operation
        cycle += 1
        x += int(instr[5:])

    # Check cycle and calculate product
```

In between each increment of the cycle counter, we need to check whether it is
one of the wanted values and perform the multiplication. The values we have are
all of the form *40n + 20* with *n ≥ 0*, so a simple modulus operation will
suffice:

```python
for instr in program:
    cycle += 1

    if instr.startswith('addx'):
        if cycle % 40 == 20:
            total += cycle * x

        cycle += 1
        x     += int(instr[5:])

    if cycle % 40 == 20:
        total += cycle * x

print('Part 1:', total)
```

### Part 2

We are now told that this weird VM has a [CRT monitor][wiki-crt], and that each
cycle a pixel is drawn. Each line on the monitor consists of 40 pixels, so a new
line of pixels begins every 40 pixels drawn. This means that the second line of
the monitor starts at the 41st pixel, the third line at the 81st, and so on.

Whether the pixel drawn each cycle is lit or not depends on the value of the `X`
register, which indicates the position of the left side of a 3-pixel wide,
1-pixel tall sprite. Whenever the pixel currently being drawn falls within this
sprite, the pixel is lit.

After emulating the display, a 40-by-6 image should appear, representing 8
capital letters: our part 2 answer. This seems fun, as we actually need to
"draw" these pixels in our terminal to see the answer.

We'll implement part 2 within the same loop used for part 1. The only two
additional things we need to do *each cycle* are:

1. Check whether we need to advance to the next line. This again can be easily
   done with a modulo operation since the beginning of each line will be at
   *40n + 1* cycles (with *n ≥ 0*).
2. Check whether we need to draw a lit pixel or not. This means checking whether
   the column of the current pixel to draw falls within the "sprite". A row is
   40 pixels wide, so the column within the current row is simply the cycle
   counter *modulo 40*, and the sprite position within the current row is
   represented by the `X` register. This means that a lit pixel is drawn any
   time the cycle counter *modulo 40* is within `X` and `X + 2` (extremes
   included).

It really takes 10 times the amount of lines to explain it than to write it. To
emulate the CRT monitor we'll use a simple string, where each character is a
pixel. We'll use `'#'` to represent lit pixels, `' '` (a space) for dark
pixels and we'll add a newline (`'\n'`) each time a new row is needed.

Here's the code to add to the main loop we already wrote:

```diff
+crt = ''

 for instr in program:
+    if x <= cycle % 40 <= x + 2:
+        crt += '#'
+    else:
+        crt += ' '
+
     cycle += 1

     if instr.startswith('addx'):
         if cycle % 40 == 20:
             total += cycle * x
+        elif cycle % 40 == 1:
+            crt += '\n'
+
+        if x <= cycle % 40 <= x + 2:
+            crt += '#'
+        else:
+            crt += ' '

         cycle += 1
         x += int(instr[5:])

     if cycle % 40 == 20:
         total += cycle * x
+    elif cycle % 40 == 1:
+        crt += '\n'
```

The [3-way comparison][py-3-way-comparison] `x <= y <= z` is equivalent to
`x <= y and y <= z`, but only evaluates `y` once, and only evaluates `z` if
`x <= y` is not satisfied. This is a nice little feature that makes bound
checking in Python much cooler than in other languages.

The addition of new pixels to the `crt` variable can also be done using a
[tristate operator][py-cond-expr]:

```python
crt += '#' if x <= cycle % 40 <= x + 2 else ' '
```

Now all that's left to do is print the solution. We'll tell
[`print()`][py-builtin-print] to add an extra newline between the prompt and the
answer using `sep='\n'` so that the contents of `crt` are printed nicely:

```python
print('Part 2:', crt, sep='\n')
```

The output will look something like this:

```none
Part 2:
###   ##   ##  #### #  # #    #  # ####
#  # #  # #  # #    # #  #    #  # #
###  #  # #    ###  ##   #    #### ###
#  # #### #    #    # #  #    #  # #
#  # #  # #  # #    # #  #    #  # #
###  #  #  ##  #### #  # #### #  # #
```

And here we go, 20/50 stars!


Day 11 - Monkey in the Middle
-----------------------------

[Problem statement][d11-problem] — [Complete solution][d11-solution] — [Back to top][top]

### Part 1

Today's problem is more of a reading comprehension challenge than a real
problem, at least for part 1. We need to simulate some sort of game happening
between a number of monkeys. Each monkey has some specific attributes that are
listed in our input:

- A *list of items* (positive integers) it currently holds.
- An *operation* to perform when inspecting an item: this is either an addition
  or a multiplication, of which the first operand is always the item value.
- The *second operand* of the operation: either a fixed integer or the item
  value again.
- A *divisor* to check the item value against after inspecting it and performing
  the operation on it: if the calculated value is divisible by this number, the
  item is passed to a given monkey, otherwise to another.
- Two *indices* of the monkeys to pass items to, as explained in the previous
  point.

The game to simulate happens in rounds, and each round every monkey plays one
turn, consisting of the following operations:

1. Inspect the first item in the list of items, applying the operation to its
   value.
2. Divide the result by 3.
3. Check whether the obtained value is divisible by the divisor.

   - If so, pass the item (with the new value) to a given monkey (the index of
     the monkey to pass to is a property of the monkey itself).
   - Otherwise, pass it to another given monkey.

After simulating 20 rounds, we need to find the two monkeys who inspected the
most items and calculate the product of the total number of inspections they
performed.

Since we are dealing with complex objects with different properties to remember,
let's write a class to represent a single monkey. This class will hold all the
properties defined above. We don't really need to pass a code review, so we'll
assign all attributes after creating the class. For now, let's just define its
attributes with a [`__slots__`][py-class-slots] class variable. This allows for
faster attribute lookup and less memory usage, but the class will only be able
to hold the properties defined in `__slots__` (which is fine by us).

```python
class Monkey:
    __slots__ = (
        'items', 'op', 'op_value', 'divisor',
        'pass_if_true', 'pass_if_false', 'inspections'
    )
```

Now, for the input parsing... this is going to be painful. Here's the
description of a single monkey in our input:

```none
Monkey 0:
  Starting items: 98, 97, 98, 55, 56, 72
  Operation: new = old * 13
  Test: divisible by 11
    If true: throw to monkey 4
    If false: throw to monkey 7
```

All monkey descriptions are divided by an empty line, so we can initially
[`.read()`][py-file-read] the whole input file and [`.split()`][py-str-split]
the resulting string on empty lines to obtain a list of "raw" monkey
description strings:

```python
with open(...) as fin:
    raw_monkeys = fin.read().split('\n\n')
```

Now we can iterate over the strings in `raw_monkeys`, split them into single
lines through [`.splitlines()`][py-str-splitlines], and parse the properties on
each line. Since every line contains different text, a
[regular expression][misc-regexp] to extract integers on each line is probably
the simplest way to go. We can create one with the `re` module, and then use its
[`.findall()`][py-re-pattern-findall] method to extract a list of matches from a
string.

```python
import re
regexp = re.compile(r'\d+') # r is for "raw string"

>>> regexp.findall("Hello 123 World 456, today is December 11th, 2022")
['123', '456', '11', '2022']
```

The item list contains one or more integers, so we can keep the matches as a
list and transform them to `int` with [`map()`][py-builtin-map]. Since we will
be removing/adding items to/from this list a lot, a
[`deque`][py-collections-deque] from the [`collections`][py-collections] module
is a better choice than `list`, as it provides fast insertion and deletion from
either of its ends (while `list` does not).

Other lines contain only one integer, so we can simply do `[0]` on the obtained
list of matches. The operation to perform (e.g. `new = old * 13`) can be either
an addition or a multiplication. We can import those two as functions from the
[`operator`][py-operator] module: `operator.add()` and `operator.mul()`.

The only "annoying" line is the third, which can either contain an integer (e.g.
`Operation: new = old * 13`) or not (e.g. `Operation: new = old + old`): for
this, we'll have to first check if we have any match, and if not, it means the
operation uses `old` as operand on both sides.

```python
from collections import deque
from operator import add, mul

monkeys = []

for raw_monkey in raw_monkeys:
    lines   = raw_monkey.splitlines()
    matches = regexp.findall(lines[2])

    m = Monkey()
    m.items         = deque(map(int, regexp.findall(lines[1])))
    m.op            = add if '+' in lines[2] else mul
    m.op_value      = int(matches[0]) if matches else None
    m.divisor       = int(regexp.findall(lines[3])[0])
    m.pass_if_true  = int(regexp.findall(lines[4])[0])
    m.pass_if_false = int(regexp.findall(lines[5])[0])
    m.inspections   = 0
    monkeys.append(m)
```

As promised, we initialized all attributes of each instance of `Monkey` from
outside the class. You would normally do this by passing all the values to the
class constructor (i.e. its [`__init__()`][py-object-init] method), but there
are a lot of them and I did not want to write a function taking so many
parameters.

Now that we have a list of objects to work with, let's actually simulate the
game. To make things simpler, let's implement the basic "inspection" operation
that a monkey performs as a method of the `Monkey` class:

```python
class Monkey:
    # ... unchanged ...

    def inspect(self):
        # Remove the first item from the items we have (we'll pass it on to
        # another monkey anyway)
        item = self.items.popleft()

        if self.op_value is None:
            # Operation to perform is `old + old` or `old * old`
            return self.op(item, item)

        # Operation to perform is `old + VALUE` or `old * VALUE`
        return self.op(item, self.op_value)
```

The rules of each round, as explained in the numbered list a few paragraphs
above, are pretty straightforward. Let's write a function to play a given number
of rounds in a row and return the answer we want.

After simulating all the requested rounds, we can extract the `.inspections`
attribute of each monkey class using `map()` plus a [`lambda`][py-lambda], or
better `map()` plus [`attrgetter()`][py-operator-attrgetter]. Then, the top two
values can be extracted after sorting in descending order with
[`sorted()`][py-builtin-sorted] (not a good idea in general if we only need the
top two, but we have a very small list, so it's fine).

```python
from operator import attrgetter

def simulate(monkeys, n_rounds):
    for _ in range(n_rounds):
        for m in monkeys:
            # This monkey will inspect all of its items in this round
            m.inspections += len(m.items)

            while m.items:
                # Pop the first item and apply the needed operation to it, then
                # divide by 3
                item = m.inspect() // 3

                # Check if the new value is divisible by m.divisor and pass it
                # on to the correct monkey by appending it to its items
                if item % m.divisor == 0:
                    monkeys[m.pass_if_true].items.append(item)
                else:
                    monkeys[m.pass_if_false].items.append(item)

    # Get the two highest total number of inspected items
    a, b = sorted(map(attrgetter('inspections'), monkeys), reverse=True)[:2]
    return a * b
```

All that's left to do is call the function we just wrote:

```python
answer = simulate(monkeys, 20)
print('Part 1:', answer)
```

### Part 2

We need to do the same thing we did for part 1, but the rules change slightly:
we no longer need to perform the division by 3 after a monkey "inspects" an
item, and we need to simulate 10000 (ten thousand) rounds. This is interesting.

The first requirement is not a problem, we can just remove the `// 3` from the
code of our `simulate()` function. The second requirement is a bit of a pain
though. We are dealing with additions and multiplications, this means that the
value of an item can only ever increase, and doing *10000* rounds means doing *a
lot* of additions and multiplications... we will never be able to work with such
large numbers, at least not in a reasonably fast way.

Apart from the multiplication and addition done by each monkey when "inspecting"
an item, the only other operation we perform is a divisibility check (`item %
m.divisor == 0`). In other words, at the end of the day, the only thing that
matters about a given item value, is whether it can be divided by the divisor of
any given monkey. This is what "drives" the game in different directions since
it's used to choose the next monkey to pass an item to. We need a way to keep a
value small enough to be able to work with it, while still being able to check
whether it is divisible by a given set of integers (the divisors of each
monkey).

How do we do this? With a bit of modular arithmetic:

- Clearly, if there only was *one* monkey, instead of `item` we could keep the
  much smaller `item % m.divisor` around. After all, we don't care about the
  real value, only about its divisibility by `m.divisor`. The divisibility would
  then be preserved since [*congruence*][wiki-congruence] to a fixed modulus is
  preserved by addition and multiplication, which are the only two operations we
  perform. In other words, `(x + a) % d == ((x % d) + (a % d)) % d`, or in
  mathematical terms *a + b ≡ (a mod d) + (b mod d)  (mod d)*.

- In the case of *two* monkeys with divisors `d` and `q`, in order to preserve
  the divisibility by both, we only need to keep `item % (d * q)` around. This
  is somewhat intuitive since a number divisible by `d * q` will also always be
  divisible by both `d` and `q` separately. We have `(x % (d*q)) % d == x % d`
  for any value of `q`, or in mathematical terms:
  *x mod dq ≡ a (mod d) ⇔ x ≡ a (mod d)* for any positve integer *q*.

- In the general case of multiple different divisors, we only need to keep item
  values *modulo the product of all the divisors*. This product is small enough
  and is also pre-computable and fixed through the entire simulation (since
  divisors are fixed). To be precise, we actually only need the
  [least common multiple][wiki-lcm] of the divisors.

Knowing all of the above, we can get our part 2 solution almost for free with
only a couple of modifications to our `simulate()` function:

```diff
-def simulate(monkeys, n_rounds):
+def simulate(monkeys, n_rounds, part2=False):
+    if part2:
+        modulus = lcm(*map(attrgetter('divisor'), monkeys))
+
     for _ in range(n_rounds):
         for m in monkeys:
             m.inspections += len(m.items)

             while m.items:
-                item = m.inspect() // 3
+                if part2:
+                    item = m.inspect() % modulus
+                else:
+                    item = m.inspect() // 3

                 if item % m.divisor == 0:
                     monkeys[m.pass_if_true].items.append(item)
                 else:
                     monkeys[m.pass_if_false].items.append(item)

     a, b = sorted(map(attrgetter('inspections'), monkeys), reverse=True)[:2]
     return a * b
```

The [`lcm()`][py-math-lcm] function (used above to compute the least common
multiple of all the `.divisor`s) is available in the `math` module from Python 3.9
onwards. If we are on a lower Python version, we can implement it ourselves
using [`gcd()`][py-math-gcd], available in the `math` module from Python 3.5
onwards.

```python
# Python >= 3.5: from math import gcd
def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

# Python >= 3.9: from math import lcm
def lcm(*integers):
    it  = iter(integers)
    res = next(it)

    for x in it:
        res = res * x // gcd(res, x)
    return res
```

One last thing before computing the answer: since we are modifying the `.items`
of each monkey while simulating, we need to keep a copy of the original values
in order to perform the simulation again. We can do this with
[`copy.deepcopy()`][py-copy-deepcopy].

We finally have a complete solution:

```python
from copy import deepcopy

original = deepcopy(monkeys)

answer1 = simulate(monkeys, 20)
print('Part 1:', answer1)

answer2 = simulate(original, 10000, True)
print('Part 2:', answer2)
```

Smooth!


Day 12 - Hill Climbing Algorithm
--------------------------------

[Problem statement][d12-problem] — [Complete solution][d12-solution] — [Back to top][top]

### Part 1

Pathfinding on a grid! I was missing that on my [AoC bingo][misc-aoc-bingo] card
this year :'). We are given a grid of letters ranging from `a` to `z`. The grid
represents a [topographic map][wiki-topographic-map], and each letter is a
different level of elevation: `a` is lower than `b`, which is lower than `c`,
and so on until `z`. This grid also contains two uppercase letters, `S` and `E`,
which are respectively the start cell and the destination to reach. The start is
at elevation `a`, and the destination is at elevation `z`.

We need to find the minimum number of steps in the four cardinal directions that
are needed to reach the destination from the start, with the constraint that we
can only move to cells that have an elevation not higher than the current
elevation plus one.

If you've ever done any problem similar to this, you already know that the
answer to "what's the minimum distance from A to B on a grid" is always
[breadth-first search][algo-bfs] (BFS) as the steps to perform are unitary. All
we need to do is parse the input grid and create and perform an adequate BFS on
the grid, taking into account the rules to move from one cell to another.

Let's start with the BFS implementation right off the bat. We'll be working with
coordinates of the form `(row, column)`. Given a cell's coordinates, we need to
explore all the reachable cells using BFS, avoiding neighboring cells that are
too high in elevation, and stopping whenever we reach the coordinates of the
destination. Here's a commented function that implements BFS, using a
[`deque`][py-collections-deque] as queue and [`math.inf`][py-math-inf] to
indicate that no solution is found:

```python
from collections import deque
from math import inf as INFINITY

def bfs(grid, src, dst):
    h, w    = len(grid), len(grid[0]) # pre-calculate height and width for simplicity
    queue   = deque([(0, src)])       # queue of tuples (distance_from_src, coords)
    visited = set()

    # While there are coordinates to visit
    while queue:
        # Get the first one in the queue
        distance, rc = queue.popleft()
        # If we reached the desination, return the distance traveled so far
        if rc == dst:
            return distance

        # Skip already vsited coordinates
        if rc not in visited:
            visited.add(rc)

            # For each neighboring cell that wasn't already visited
            for n in get_neighbors(grid, r, c, h, w):
                if n in visited:
                    continue

                # Add it to the back of the queue with a distance equal to the
                # current one plus 1
                queue.append((distance + 1, n))

    return INFINITY
```

So far, this is just plain and simple BFS. The `get_neighbors()` used above will
contain the actual logic to solve the problem, let's write it as a
[generator][py-generators] function that will `yield` all the coordinates of
reachable neighboring cells according to the elevation rules. We will assume to
be working with a `grid` where each cell contains integers representing
elevation values. Given a position `(r, c)`, the maximum elevation reachable
will therefore `grid[r][c] + 1`, and the neighboring cells in the 4 cardinal
directions will be at `(r+1, c)`, `(r-1, c)`, `(r, c+1)` and `(r, c-1)`.

```python
def get_neighbors(grid, r, c, h, w): # get h, w as parameters for simplicity
    max_el = grid[r][c] + 1

    for nr, nc in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)):
        if 0 <= nr < h and 0 <= nc < w: # ensure we are within the grid
            if grid[nr][nc] <= max_el:  # ensure this neighbor is reachable
                yield nr, nc
```

We are almost done. Let's parse the input now: since we are working with ASCII
characters, we can do what we did for [day 8 part 1][d08-p1] and open the input
file in binary mode (`'rb'`) to get a free conversion from characters to
elevation values. The lines can be extracted as `bytes` with
[`.splitlines()`][py-bytes-splitlines] after reading the whole file, and we can
then transform each line into a list of `int` with [`map()`][py-builtin-map]
(pretty easy since iterating over `bytes` already yields `int`s).

```python
with open(..., 'rb') as fin:
    lines = fin.read().splitlines()
    grid = list(map(list, lines))
```

A couple of constants to represent the source, the destination and the
highest/lowest elevations will help us make the code more human readable:

```python
# These will all be ints since iterating bytes yields ints
START, END, LOWEST, HIGHEST = b'SEaz'
```

Now we need to find the source and destination coordinates. A simple scan of the
grid with a double `for` loop gets the job done, and I will also throw a couple
of [`enumerate()`][py-builtin-enumerate] in there for ease. Since our
`get_neighbors()` function looks at grid cells assuming they all represent
elevation values, after finding the source and the destination, we will edit the
grid replacing their value with the actual elevation.

```python
src = dst = None

for r, row in enumerate(grid):
    for c, cell in enumerate(row):
        if cell == START:
            src = r, c
            grid[r][c] = LOWEST
        elif cell == END:
            dst = r, c
            grid[r][c] = HIGHEST

    if src and dst:
        break
```

Perfect, we've got all we need. The answer is one `bfs()` call away:

```python
min_dist = bfs(grid, src, dst)
print('Part 1:', min_dist)
```

### Part 2

For part 2, we are told that all cells at elevation `a` are valid starting
points: we need to find the minimum possible distance to travel to get to the
destination (`E`) starting from any `a`.

The instinctive thing to do here is to just call `bfs()` in a loop passing the
grid coordinates of any `a` cell as source, and keep the minimum returned value.
We can do better though. Since we are using BFS on a graph where arcs have all
the same weight (i.e. all steps we make are one unit of distance), we know for a
fact that whenever we visit a given cell for the first time, we have also
traveled the shortest possible distance to do so. This means that if we perform
BFS backward from the destination, we can simply stop at the first cell with
elevation `a` that we encounter, and we'll have found the minimum distance from
any `a` to the destination.

There's a catch though. If we want to move backward from the destination (`E`),
we also need to write a different `get_neighbors()` function, since now the
check to perform on the elevation is the opposite: we can only move to
neighboring cells that have an elevation *higher than or equal to* the current
cell's elevation plus one.

We still need the original `get_neighbors()` function. Let's split it into three
different functions: a generic `neighbors4()` function that only returns the
coordinates of any valid neighboring cell, a second one that checks elevation
constraints assuming we are moving forward, and a third one that checks elevation constraints
assuming we are moving backward.

```python
def neighbors4(grid, r, c, h, w):
    for nr, nc in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)):
        if 0 <= nr < h and 0 <= nc < w:
            yield nr, nc

def neighbors_forward(grid, r, c, h, w):
    max_el = grid[r][c] + 1

    for nr, nc in neighbors4(grid, r, c, h, w):
        if grid[nr][nc] <= max_el:
            yield nr, nc

def neighbors_backward(grid, r, c, h, w):
    min_el = grid[r][c] - 1

    for nr, nc in neighbors4(grid, r, c, h, w):
        if grid[nr][nc] >= min_el:
            yield nr, nc
```

We can further simplify the last two functions using a *filtering*
[generator expression][py-generator-expr] of the form
`x for x in iterable if <condition on x>`, which will only yield items that
satisfy a certain condition. Here it is:

```python
def neighbors_forward(grid, r, c, h, w):
    max_el = grid[r][c] + 1
    neigh = neighbors4(grid, r, c, h, w)
    yield from ((nr, nc) for nr, nc in neigh if grid[nr][nc] <= max_el)

def neighbors_backward(grid, r, c, h, w):
    min_el = grid[r][c] - 1
    neigh = neighbors4(grid, r, c, h, w)
    yield from ((nr, nc) for nr, nc in neigh if grid[nr][nc] >= min_el)
```

The BFS code we wrote for part 1 only needs a couple of modifications to also
work for part 2:

- Since we want to use two different functions to get cell neighbors, we can
  accept a function as an additional parameter.
- Since for part 2 we also want to stop whenever we visit a cell containing a
  given value, we can alter the condition used to `return` to also check whether
  `grid[r][c] == dst`, and then pass the destination coordinates as `src`, and
  the value `LOWEST` as `dst`. This won't break part 1 since `grid[r][c] == dst`
  will never match when `dst` is a tuple of coordinates.

```diff
-def bfs(grid, src, dst):
+def bfs(grid, src, dst, get_neighbors):
     h, w    = len(grid), len(grid[0])
     queue   = deque([(0, src)])
     visited = set()

     while queue:
         distance, rc = queue.popleft()
-         if rc == dst:
+         r, c = rc
+         if rc == dst or grid[r][c] == dst:
             return distance

         if rc not in visited:
             visited.add(rc)

             for n in get_neighbors(grid, r, c, h, w):
                 if n in visited:
                     continue

                 queue.append((distance + 1, n))

     return INFINITY
```

And here we go, we now have the solution for both parts:

```python
min_dist = bfs(grid, src, dst, neighbors_forward)
print('Part 1:', min_dist)

min_dist_from_any_a = bfs(grid, dst, LOWEST, neighbors_backward)
print('Part 2:', min_dist_from_any_a)
```


Day 13 - Distress Signal
------------------------

[Problem statement][d13-problem] — [Complete solution][d13-solution] — [Back to top][top]

### Part 1

Today we're dealing with nested lists of integers, called "packets" in the
problem statement. We are given a list of packet *pairs*, and we need to compare
the two packets in each pair to determine if they are in the correct order or
not. In other words, we need to establish an order for all the given pairs.

The order of a pair of packets is based on some arbitrarily given rules that
need to be applied recursively:

1. If both values are integers, the lower integer should come first. If they are
   equal, we don't know which one should come first.

2. If both values are lists, check the order between each pair of items in the
   lists. The first pair of items for which the order can be determined also
   determines the order of the two lists. Whichever list runs out of items
   before a decision can be made should come first. If instead no order can be
   determined for any of the pairs, and both lists have the same length, we
   don't know which list should come first.

3. If one of the values is a list and the other is an integer, transform the
   integer into a 1-item list (containing only said integer), and re-perform the
   check.

We need to find the sum of the (1-based) indices of the pairs of packets that
are in the right order.

Let's start with an example to understand the rules. Let's say we have the
following pair of packets:

```python
[[1],[2,3,4],9]
[[1],4,0]
```

These are the checks that would be performed, and their outcome, according to
the above rules:

- Compare `[[1],[2,3,4],9]` with `[[1],4,0]`. Both are lists, so compare their
  items pairwise:
  - Compare `[1]` with `[1]`:
    - Compare `1` with `1`:
      - They are equal, order is unknown.
  - Compare `[2,3,4]` with `4`. One is a list and one is an integer. Transform
    `4` into `[4]` and retry:
    - Compare `[2,3,4]` with `[4]`:
      - Compare `2` with `4`:
        - `2` is less than `4` so `2` should come first, and indeed it does.
          This means that the original packets were in the right order. Stop.

As can be seen from the above example, Whenever we are able to make a decision
about the order of two items, at any nesting level, we should stop and
"propagate" that decision back to the original packets. It does not matter
what's in the rest of the packets. In fact, the two packets above also contained
a `9` and a `0`, which were never compared because we could determine the order
before getting to them.

As yesterday, we'll use a bottom-up approach. Let's implement a recursive
function to compare two packets. We'll assume to have two parameters `a` and
`b`, both of which can either be `list` or `int`, and apply the rules to
determine which one should come first. For simplicity, we'll make the function
return an integer: negative if `a` should come before `b`, positive if `b`
should come before `a`, and zero otherwise. This is also known as a "cmp"
function (which [actually was a built-in function][misc-py2-cmp] in Python 2).

- In case both parameters are `int`, we can simply return `b - a`. In fact,
  `a - b` will be negative if `a < b`, positive if `a > b` and zero if `a == b`.

- In case only one is an `int`, we'll wrap it into a list and make a recursive
  call to re-perform the comparison.

- In case both parameters are `list`, to compare their items pairwise we can
  iterate over the lists with [`zip(a, b)`][py-builtin-zip] and make a recursive
  call for each pair of items. If any of the recursive calls we make is
  conclusive (i.e. the result is not `0`), we are done. Otherwise, we'll keep
  going.

  If we run out of items to compare, we'll need to check the length of the two
  lists instead: the shorter one should come first (same logic as the one for
  two integers), so we can just return `len(a) - len(b)`.

To check whether a variable is an `int`, we can either use
[`type(x)`][py-builtin-type] or [`isinstance(x, int)`][py-builtin-isinstance]).
I'll go with the former.

```python
def compare(a, b):
    a_is_int = type(a) is int
    b_is_int = type(b) is int

    # Both integers.
    if a_is_int and b_is_int:
        return a - b

    # One is an integer, wrap it into a list and re-check.
    if a_is_int != b_is_int:
        if a_is_int:
            return compare([a], b)
        else:
            return compare(a, [b])

    # Both lists, check their items pairwise, stop at the first conclusive result.
    for x, y in zip(a, b):
        res = compare(x, y)
        if res != 0:
            return res

    # We ran out of items before coming to a conclusion. Now what matters is
    # which list was longer (according to rule number 2).
    return len(a) - len(b)
```

Okay, now to the input parsing. The first thing to do is read each packet in the
input as a string. We can skip empty lines delimiting packet pairs either
iterating over the input line by line or reading it all at once and using
[`.replace()`][py-str-replace]. Then, [`.splitlines()`][py-str-splitlines] will
give us a list of raw packets (strings) to later parse.

```python
with open(...) as fin:
    lines = fin.read().replace('\n\n', '\n').splitlines()
```

We chose to read all packets at once into a list in order to easily parse them
all at once with a single call to [`map()`][py-builtin-map], given a function
able to parse one packet.

As you probably already noticed, the packets are valid Python lists, meaning
that if we pasted them into a Python interpreter they would evaluate to actual
lists. There's a function that can do exactly this: [`eval()`][py-builtin-eval].
It must be noted however that using `eval()` for input parsing is in general a
*really bad idea*, as it can evaluate arbitrary Python code and therefore do
unexpected things. If the input comes from an untrusted source, we should never
`eval()` it before making sure it's safe to do so, and we should avoid `eval()`
in general.

```python
# Example of "unexpected things"
eval('__import__("os").system("arbitrary shell commands here")')
```

As it turns out though, our packets are also valid [JSON][wiki-json] objects,
and we have [`json.loads()`][py-json-loads] that parses a string representing a
JSON object into a Python object. JSON arrays (`[...]`) are turned into `list`
and integers into `int`, so this function is all we need to parse a packet
without worrying about evaluating random Python code. We could write an actual
parsing function ourselves without the use of `eval()` or `json.loads()`, but...
I am honestly too lazy for that, at least today. Also, why do it in 10 lines of
code when you can do it in one (said no sane programmer ever)?

Anyway... here goes nothing:

```python
from json import loads
packets = list(map(loads, lines))
```

Now we can group our packets in pairs:

```python
pairs = []
for i in range(0, len(packets), 2):
    pairs.append(packets[i:i + 2])
```

Which can be simplified to a single [generator expression][py-generator-expr]:

```python
pairs = (packets[i:i + 2] for i in range(0, len(packets), 2))
```

Note that the above does not actually create a list or tuple, but rather a
generator that will `yield` pairs on the fly, and which is thus only iterable
*once*, which is enough for us.

Now we can finally iterate over the pairs and `compare()` them. Since we need to
provide the sum of 1-based indices of correctly ordered pairs as the answer,
we'll also use [`enumearte()`][py-builtin-enumerate].

```python
answer = 0
for i, (a, b) in enumerate(packets, 1):
    if compare(a, b) < 0: # a should come before b
        answer += i

print('Part 1:', answer)
```

All the above loop is doing is calculating a sum, so we can also re-write the
entire thing using [`sum()`][py-builtin-sum] plus a filtereg generator
expression (`x for x in ... if <condition>`):

```python
answer = sum(i for i, (a, b) in enumerate(pairs, 1) if compare(a, b) > 0)
print('Part 1:', answer)
```

### Part 2

Now that we have a "primitive" to establish the order between two packets, why
not use it to *sort* all the packets? That's exactly what we are asked to do,
after adding to our packets two "divider" packets: `[[2]]` and `[[6]]`. Once
sorted, we need to find the product of the two 1-based indices of the divider
packets.

Well. This is easy. We already have a comparison function, and we have
[`list.sort()`][py-list-sort]. The only hiccup is that `list.sort()` does not
take a comparison function... it used to in Python 2 with the `cmp=` argument,
but in Python 3 that was replaced with `key=`, which only takes a single value
and is expected to somehow transform it.

Transforming a `cmp` function into a `key` function and vice-versa is not really
straightforward. Thankfully, Python developers thought about this for us:
[`functools.cmp_to_key()`][py-functools-cmp_to_key] is a function that takes a
`cmp`-style function (taking two arguments and returning an integer) and
magically transforms it into a `key`-style function (taking one argument and
returning an arbitrary object). The way the conversion is performed is actually
quite interesting and clever, you can read about it [in this Stack Overflow
post][misc-so-cmp_to_key] if curious.

Okay, let's do this:

```python
packets.extend(([[2]], [[6]]))
packets.sort(key=cmp_to_key(compare))
```

Now we can use [`.index()`][py-list-index] to find the indices of the dividers
and multiply them together. We also know that the second divider (`[[6]]`) must
come *after* the first as per the ordering rules, so we can pass a second
argument to `.index()` (the index to start from) to skip already checked items.

```python
answer = packets.index([[2]]) + 1
answer *= packets.index([[6]], answer) + 1
print('Part 2:', answer)
```

Like a walk in the park!


Day 14 - Regolith Reservoir
---------------------------

[Problem statement][d14-problem] — [Complete solution][d14-solution] — [Back to top][top]

### Part 1

Today we are dealing with a cave that fills with sand. As the problem statement
remings us, a similar (although more intricate) concept was explored in
[2018 day 17][2018-d17-problem] (of which unfortunately I did not write a
walkthrough for... *yet*).

The cave we are in is a 2D grid, and our input is a list of segments in the form
`ax,ay -> bx,by -> ...`, which represent sequances of vertical and horizontal
segments of cave cells occupied by rocks. Units of sand, each occupying one grid
cell, start pouring into the cave *one at a time* from `x=500,y=0` (`y=0` is the
top) and fall down the cave obeying four simple rules:

1. If the cell immediately below is free, the unit of sand falls one step
   straight down.
2. If instead that cell is occupied, it falls one step diagonally, one cell down
   and one to the left.
3. If instead that cell is occupied, it falls one step diagonally, one cell down
   and one to the right.
4. Otherwise (the three cells under the unit of sand are all occupied), it stops
   falling and settles down where it is.

Our cave is infinitely deep (`y` does not have an upper bound), but there is a
limited number of cells occupied by rocks (our input) forming platforms that
sand can rest on. At some point though, sand will inevitably fill all the
platforms it is able to reach, at which point the next unit that is poured will
start falling down indefinitely into the void. We want to know *how many units
of sand will fall and settle down* before this happens.

To make the above rules a little bit clearer, here's a simple diagram:

```none
...s...
..213..
```

A unit of sand (`s` above) first tries to fall to the cell labeled `1`; if
that's occupied it tries `2`; if that's also occupied it tries `3`. If all of them
are occupied, it settles down where it is. In other words, a unit of sand can
only settle down above the middle of a 3-cell platform (whether it is sand,
rock, or a mix of the two). More examples that can help better understand the
problem are provided in the [problem statement][d14-problem], so I won't go
deeper with the explanation and dive directly into the solution.

It's tempting to create a matrix as a `list` of `list` to represent our 2D cave.
However, we don't know its size before parsing the entire input, and even then,
it could potentially need expansion due to the sand being poured in the cave
(spoiler, we'll be dealing with a lot more sand in part 2). Instead, we'll use a
`set` of points (i.e. tuples of the form `(x, y)`), which is a lot simpler to
manage: if a point is in the set, that cave cell will be considered occupied.

```python
cave = set() # Any point (x, y) in this set is occupied (by either a rock or a sand unit)
```

Let's parse the input. Each line consists of a list of 2D coordinates separated
by `' -> '`, and each point has its x and y components separated by a comma.
Parsing a single line is therefore only a matter of a couple of
[`.split()`][py-str-split] operations:

```python
fin = open(...)

for line in fin:
    points = []

    for p in line.split(' -> '):
        x, y = p.split(',')
        points.append(int(x), int(y))
```

The internal loop above can be further simplified with the use of
[`map()`][py-builtin-map] and a couple [`lambda`][py-lambda] functions:

```python
for line in fin:
    points = line.split(' -> ')
    points = map(lambda p: p.split(','), points)
    points = map(lambda p: (int(p[0]), int(p[1])), points)
```

Note that we did not actually need to create a `list` of points for each parsed
line, we can keep the generator returned by `map()` as we don't need to iterate
on the points more than once.

Each pair `ax,ay -> bx,by` in the lists of points we get on each line indicates
a segment of cells occupied by rocks. These segments are always either vertical
or horizontal, never diagonal. In the first case all the cells with `x == ax`
(`== bx`) and `y` from `ay` to `by` are occupied by rocks, while in the second
case all the cells with `y == ay` (`== by`) and `x` from `ax` to `bx` are
occupied with rocks. Therefore, to add rocks to our cave, we need to do
something like this for each pair of points on each line:

```python
if ax == bx: # vertical segment
    for x in range(ax, bx + 1):
        cave.add((x, ay))
else: # horizontal segment
    for y in range(ay, by + 1):
        cave.add((ax, y))
```

There's a problem though: we have no guarantee on the order of the coordinates,
so we don't know if `ax < bx` or `ay < by`. We need to distinguish between the
two cases and iterate over a different [`range()`][py-builtin-range]
accordingly. Let's write a function to do that:

```python
def autorange(start, end):
    if start > end:
        return range(start, end - 1, -1)
    return range(start, end + 1)

# Or, alternatively (this range always does steps of +1)
def autorange(start, end):
    return range(min(start, end), max(start, end) + 1)
```

For simplicity, we can now also create a `range2d()`
[generator function][py-generators] that takes two *points* and uses
`autorange()` to `yield` all the points of the horizontal or vertical segment
connecting them:

```python
def range2d(a, b):
    ax, ay = a
    bx, by = b

    if ax == bx:
        # yield all points in the vertical segment
        for y in autorange(ay, by):
            yield ax, y
    else:
        # yield all points in the horizontal segment
        for x in autorange(ax, bx):
            yield x, ay
```

Now we can add rocks to our cave. To iterate on points pairwise we'll just have
two variables `prev` and `cur`, and initialize `prev` with the first point
yielded returned by the `map()` generator using [`next()`][py-builtin-next].
The [`.update()`][py-set-update] method of `set` can take any iterable and add
all its elements to the set, which means we can avoid explicitly looping over
the points yielded by `range2d(prev, cur)`.

```python
for line in fin:
    points = line.split(' -> ')
    points = map(lambda p: p.split(','), points)
    points = map(lambda p: (int(p[0]), int(p[1])), points)
    prev   = next(points)

    for cur in points:
        cave.update(range2d(cur, prev))
        prev = cur
```

In Python >= 3.10, we have [`itertools.pairwise()`][py-itertools-pairwise] that
can be used to achieve the same thing:

```python
for line in fin:
    # ...
    for prev, cur in pairwise(points):
        cave.update(range2d(cur, prev))
```

Or, even more concisely, with the help of
[`itertools.starmap()`][py-itertools-starmap] to unpack the pairs:

```python
for line in fin:
    # ...
    cave.update(*starmap(range2d, pairwise(points)))
```

Before we can simulate the sand pouring into the cave, we know that at some
point sand will fill all the rock platforms in the cave and start falling down
to oblivion, we need to detect this in order to avoid ending up in an infinite
loop. We can do this by pre-calculating the `y` coordinate of the deepest rock
in the cave and making sure to never exceed it. This means iterating over all
the points initially in the `cave` set and finding the max `y`, which we can do
in one line with a simple [`max()`][py-builtin-max] plus `map()` + `lambda`,
or better `map()` + [`itemgetter()`][py-operator-itemgetter].

```python
from operator import itemgetter
maxy = max(map(itemgetter(1), cave))
```

Good, now let's start pouring some sand into this cave. The rules are quite
simple, it's only a matter of following them. Let's write a function to pour a
single unit of sand down the cave from the source (`(500, 0)`), adding the final
coordinates to our `cave` set if the unit settles down. Since we'll need to call
this function multiple times in a loop, let's also make it return `True` if the
sand unit settles and `False` otherwise, so we'll know when to stop pouring.

```python
def pour_sand(cave, maxy):
    x, y = 500, 0

    while y < maxy:
        # Can this unit of sand fall directly down?
        if (x, y + 1) not in cave:
            y = y + 1
            continue

        # Can it fall one unit down and one to the left (diagonally)?
        if (x - 1, y + 1) not in cave:
            x, y = x - 1, y + 1
            continue

        # Can it fall one unit down and one to the right (diagonally)?
        if (x + 1, y + 1) not in cave:
            x, y = x + 1, y + 1
            continue

        # This unit of sand cannot fall anymore, so it settles.
        cave.add((x, y))
        return True

    # This unit will keep falling down the infinitely deep cave without settling
    return False
```

We are doing quite a number of repeated calculations with those `x` and `y`
coordinates. Since we are performing the same fundamental operation
(`if ... in cave`) 3 times each iteration of the `while` loop, we can simplify
things with a `for`:

```python
def pour_sand(cave, maxy):
    x, y = 500, 0

    while y < maxy:
        newy = y + 1

        for newx in (x, x - 1, x + 1):
            if (newx, newy) not in cave:
                x, y = newx, newy
                break
        else:
            cave.add((x, y))
            return True

    return False
```

Yep, in Python [`for ... else`][py-loop-else] is a thing. The `else` block is
only entered if no `break` is performed during the loop, meaning that our sand
unit could not continue falling down. All we need to do now is call
`pour_sand()` repeatedly until it returns `False`, counting the number of sand
units poured.

```python
sand = 0
while pour_sand(cave, maxy):
    sand += 1

print('Part 1:', sand)
```

### Part 2

Now we also need to account for sand that overflows the rock platforms (after
filling them all). The cave does actually have a bottom: exactly two units under
the lowest piece of rock lies a flat horizontal and infinitely wide surface. Any
sand unit that previously overflowed will now settle and pile up because of this
horizontal floor. At some point, the pile of sand will become so high that it
will obstruct the source (at `500,0`). We want to know exactly how many units of
sand will it take for this to happen.

There are a few ways to solve this second part:

1. The simplest: keep doing what we did for part 1 and pour a single unit of
   sand, this time accounting for the cave floor, until some unit settles right
   at `500,0`.

2. Using [breadth-first search][algo-bfs]. We can in fact find the solution in
   a much faster way using BFS without having to simulate every single sand
   unit. If we stop and think about it for a moment, the problem we are facing
   now is merely *identifying all grid cells that can be reached by sand units
   starting from the source*. A simple BFS on the entire cave, starting from the
   source and exploring for each cell the three cells below it, will effectively
   explore all the cells reachable by sand.

3. Using [depth-first search][algo-dfs]. Analogously, DFS is just another way of
   exploring all the cells reachable by sand in the cave. However, while BFS is
   only useful to solve part 2 due to the order in which cave cells would be
   explored, DFS could also be used to solve part 1. This is because DFS allows
   us to more closely emulate the behavior of the falling sand units, with the
   opportunity to stop and [backtrack][wiki-backtracking] whenever a unit
   overflows and falls under the lowest rock (`maxy` we calculated in part 1).

   In fact, the `pour_sand()` function we wrote for part 1 is exploring a single
   path to an unique final grid cell in a depth-first manner every time it is
   called. If the path until a certain sand unit settles is 100 steps long,
   calling the function a second time means re-traveling along 99 of those
   steps! To avoid this, each time a unit of sand settles, we should in theory
   be able to backtrack going back to all the previous positios in the path and
   find the first one where we can either settle another unit of sand or from
   which we can start exploring a different sub-path.

Admittedly, I was tired enough this morning (AoC happens at 6 AM in Italy) to
just choose option 1 above and call it a day. However, as it turns out,
[posting your solution to Reddit][d14-italyinformatica] saying you know there's
some optimization to make but you are lazy to implement it, actually attracts
other smart and helpful programmers that at the end of the day convince you to
optimize your solution. I'm going to go with option number 3 above, scrapping
the `pour_sand()` function we wrote for part 1 in favor of a simpler, concise
recursive DFS implementation.

Now that we are familiar with the problem, the logic should be quite clear in
our mind. DFS is very easy to implement recursively, and the Wikipedia page
linked above has an example implementation that looks a lot like Python code.

There is however a small difference between the "standard" DFS algorithm and the
one we need to write now: normally a "node" would be marked as visited as soon
as it is reached (i.e. as the first operation in the function), before visiting
its neighbors. In our case though, "visiting" a given cell does **not**
necessarily mean settling a unit of sand there! Whether or not that's the case
can only be decided after making sure that the three cells under it are
occupied. This means that marking a unit of sand as settled (adding its
coordinates to our `grid`) is in fact the *last* thing we'll do before returning
from the function, *after* first recursively exploring the 3 cells immediately
below.

Let's first implement the function with only part 1 in mind. If the above
paragraph is clear, there isn't much more to say. Our new `pour_sand()` function
still directly adds coordinates to `cave`, returning `True` when a unit settles
at the given coordinates, and `False` otherwise.

```python
def pour_sand(cave, maxy, x=500, y=0):
    # We are overflowing to the bottom of the cave!
    # This unit of sand will not settle anywhere, stop.
    if y == maxy:
        return False

    newy = y + 1

    # Check the 3 cells below this one: straight down, down & left, down & right
    for newx in (x, x - 1, x + 1):
        # If this cell (newx, newy) is not already occupied...
        if (newx, newy) not in cave:
            # ... will another unit of sand settle here?
            if not pour_sand(cave, maxy, newx, newy):
                # If not, the current unit cannot settle at (x, y).
                return False

    # All three cells below this unit of sand are occupied (otherwise we would
    # have already returned False), so it can settle here.
    cave.add((x, y))
    return True
```

Now we can modify the function to also take into account the bottom of the cave
for part 2. We know the cave floor is a horizontal line at depth `maxy + 2`,
which means that sand will only ever settle *at most* at `maxy + 1`. The
addition of a boolean `floor` parameter indicating whether the cave floor is
present or not is enough to adapt our function to solve both parts:

- In case `floor=False` (part 1), we need to give up if `y == maxy`, which is
  exactly the check we are making at the beginning of the function above.
- In case `floor=True` (part 2), we can actually exceed `maxy`, so we can skip
  the initial check. Additionally, since we know that every single cell at
  depth `maxy + 2` will be occupied, if we find ourselves at some `y > maxy`, we
  already know that the current unit will settle here (the only value of `y`
  higher than `maxy` that we can get is `maxy + 1`, as we'll mark settled any
  unit that gets there.

Here's the new version of the function:

```python
def pour_sand(cave, maxy, floor=False, x=500, y=0):
    # For part 2 (floor=True), this check is not needed
    if not floor and y == maxy:
        return False

    # For part 1 (floor=False) we always need to do a recursive check of the
    # three cells below us. However, for part 2 (floor=True) we only need to do
    # this when y <= maxy. At y = maxy + 1 we can skip the check.
    if not floor or y <= maxy:
        newy = y + 1

        for newx in (x, x - 1, x + 1):
            if (newx, newy) not in cave:
                if not pour_sand(cave, maxy, floor, newx, newy):
                    return False

    cave.add((x, y))
    return True
```

Now we can solve both parts with single call to `pour_sand()`. To know the
number of settled sand units we can simply calculate the size of the `cave` set
before pouring the sand (when it only includes rocks) and after.

```python
rocks = len(cave)

pour_sand(cave, maxy)
sand = len(cave) - rocks
print('Part 1:', sand)

pour_sand(cave, maxy, True)
sand = len(cave) - rocks
print('Part 2:', sand)
```

This was a fun one! Let's continue our journey...


Day 15 - Beacon Exclusion Zone
------------------------------

[Problem statement][d15-problem] — [Complete solution][d15-solution] — [Back to top][top]

### Part 1

Hmm bacon, yummy! Err, nope, sorry, it's *beacons* we have to deal with today.
We are in 2D space, dealing with integer coordinates only, and measuring
distances using [Manhattan geometry][wiki-manhattan]. We are given a list of
sensors as input: each sensor sits at a given `x,y` point in space, and knows
the position of its *closest* beacon, which is also given.

For each sensor in our input, there cannot be any other beacons at a Manhattan
distance lower than the distance of the closest one, however, there could very
well be beacons farther away. Using this observation, we need to determine how
many integer coordinates with `y=2000000` are *invalid* beacon positions.

Let's start by parsing the input. Each line is a rather long string from which
we should only extract four integers. Similarly to what we did for
[day 11][d11], to make parsing simple, we can use the [`re`][py-re] module and a
[regular expression][misc-regexp] that matches digits optionally preceded by a
minus sign, transforming each match into an integer with
[`map()`][py-builtin-map].

We do not really care about the actual position of any beacon, but rather about
the distance from the sensor that detected them, so we'll just calculate the
Manhattan distance right away and save it for later.

```python
import re

def manhattan(ax, ay, bx, by):
    return abs(ax - bx) + abs(ay - by)

exp = re.compile(r'-?\d+')
sensors = []

with open(...) as fin:
    for line in fin:
        sx, sy, bx, by = map(int, exp.findall(line))
        sensors.append((sx, sy, manhattan(sx, sy, bx, by)))
```

The Manhattan distance we just calculated for each of the sensor we are dealing
is effectively their *detection radius*. Since we know the coordinates of each
sensor and the ones of its closest beacon, we also know that *there must be no
other beacon at a distance lower than this detection radius*. Since we are
working with Manhattan geometry, the area of detection will not be shaped like a
circle, but rather like a *diamond* (or well, a square rotated 45 degrees). For
example, a sensor at `3,0` that can see the closest beacon at `4,2` will have a
detection radius of `3`:

```none
  3     #
  2    ##B
  1   #####
Y 0  ###S###
 -1   #####
 -2    ###
 -3     #
     0123456
        X
```

In the above example, apart from the point marked as `B`, we can be sure there
is no other beacon within the detection radius of the sensor, meaning no beacon
can be in any of the points marked as `#`.

We are only interested in a single line at `y=2000000` though, and we want to
know how many spots are impossible positions for beacons. We can visualize this
as follows:

```none
                        .                           .
                       ...                         ...
                      .....                       .....
                     .......     .          .      ...
              .     .........   ...        ...      .
             ...     .......   .....      .....
            .....     .....   .......    .......
y=200000:  #######     ###     #####    #########
            .....       .       ...    ...........
             ...             .   .      .........
              .             ...          .......
                           .....          .....
                            ...            ...
                             .              .
```

Out of all the diamonds "projected" by each sensor, some of them will intersect
with the `y=200000` line, and some will not. For those that do, we can easily
calculate the `x` coordinate of the start and end of the intersection. If the
`y` coordinate of the sensor is exactly `200000`, the length is exactly double
the intersection radius: from `sx - r` to `sx + r`. Otherwise, it will decrease
linearly with the distance from the `y=200000` line on both sides, and we'll
have a segment from `sx - r + dist` to `sx + r - dist`.

Let's write a function to detect whether the diamond projected by a given sensor
intersects with `y=200000` and if so, also calculate its extremes:

```python
def diamond_segment(sx, sy, r):
    dist = abs(2000000 - sy)

    if dist <= r:
        return (sx - r + dist, sx + r - dist)
    return None
```

We can now call the above function for all sensors, and collect the results that
are not `None`. This will give us a "raw" list of segments of the form
`(start, end)` where we know no beacon can be present. We can use
[`itertools.starmap()`][py-itertools-starmap] to unpack the arguments correctly
(as we parsed the sensors into tuples of 3 elements). Then, we can filter those
that are `None` using the [`filter()`][py-builtin-filter] built-in.

```python
from itertools import starmap

segments = list(filter(None, starmap(diamond_segment, sensors)))
```

Cool. All that's left to do is sum up all the segment lengths, right? Wrong!
There's a small problem. We could be dealing with overlapping segments. Consider
for example the following scenario:

```none
                   .
                  ...
                 .....
              . .......
             ...........
            ...........
y=200000:  ######X####
            ..... ...
             ...   .
              .
```

In the above example, simply summing up the length of each segment, we would be
over-counting the point marked as `X` because the segments from two diamonds
overlap there.

To avoid such a situation, we can detect and merge overlapping and contiguous
segments into larger ones. We can do this by sorting the segments by their start
and then iterating over them, "accumulating" them into a larger segment until we
find a segment that is detached (i.e., it has start after the end of the current
merged segment).

Sorting is just a matter of calling the [`sorted()`][py-builtin-sorted]
built-in. Then we can get an iterator over the sorted sequence with
[`iter()`][py-builtin-iter], use [`next()`][py-builtin-next] to extract the
first segment, and finally iterate over the rest to join them. Each time a new
"detached" segment is encountered, we can add the length of the current merged
segment to the total, update the current start and end, and keep going. Let's
write a function to do all of this.

```python
def invalid_spots(sensors):
    segments = iter(sorted(filter(None, starmap(diamond_segment, sensors))))
    start, end = next(segments) # Current "merged" segment
    total = 0

    for s, e in segments:
        if s > end + 1:
            # This segment is detached from the current one: add current length
            # to the total and use this as new initial segment to merge into.
            total += end - start + 1
            start, end = s, e
        else:
            # This segment overlaps with the current one: keep its end and keep going.
            end = max(end, e)

    # Account for the last segment
    total += end - start + 1

    return total
```

All that's left to do is call the above function!

```python
answer = invalid_spots(sensors)
print('Part 1:', answer)
```

**But wait**, what? The returned value seems wrong! Indeed, there is still one
thing we did not consider. If there *already is* any beacon detected on the
`y=200000` line, we should not count its spot as invalid. We could simply
subtract the number of beacons with `y=200000` from the total, but this won't
work, as multiple sensors could be detecting the same beacon, and we would be
over-counting them. Instead, we can use a [`set`][py-set] of `x` coordinates to
exclude for all the beacons that are on the target line.

Let's modify the initial input-parsing code to also create this `set`:

```diff
 exp = re.compile(r'-?\d+')
 sensors = []
+beacons_on_target = set()

 with advent.get_input() as fin:
     for line in fin:
         sx, sy, bx, by = map(int, exp.findall(line))
         sensors.append((sx, sy, manhattan(sx, sy, bx, by)))
+
+        if by == 2000000:
+            beacons_on_target.add(bx)
```

And we can finally calculate the correct answer:

```python
answer = invalid_spots(sensors) - len(beacons_on_target)
print('Part 1:', answer)
```

### Part 2

For part 2 our task becomes harder: we are told there is exactly *one* valid
spot for a beacon with *X* and *Y* coordinates between *0* and *4000000*, and we
need to find it. Our answer will then be `4000000 * x + y`.

Technically, we could implement a very simple soluion by modifying the
`diamond_segment()` function we wrote for part 1 and search from `y=0` to
`y=4000000` until we find a line where we have exactly `4000000` invalid points.
However, that's going to be just a little bit slow... so we better think of
another approach.

Given what we discussed above for part 1, it should be clear enough that
wherever the magical spot we are looking for might be, it must be *outside* the
detection diamonds of all our sensors. There are however a few additional
observations we can make:

- Since there is only *one* such spot, this also means that it will be
  surrounded by invalid spots belonging to some detection diamonds.
- Therefore, we can deduce that the spot we are looking for must be "touching"
  the border of one or more detection diamonds.
- Therefore, such a spot must be located at a distance of `radius + 1` from more
  than one diamond.

Given the above observations, we can use the following strategy:

- For each detection diamond, find the linear equation of the four lines that
  are just outside its perimeter, at `radius + 1` (exactly one more unit away
  than the real radius). These will be 4: one per side.
- For every possible pair of diamonds, try intersecting those lines. If there is
  any intersection, that point is a candidate for the magic spot we are looking
  for.
- Test any such candidate to check whether it is within the *[0, 4000000]* range
  for both *X* and *Y*: the first one that does is the one we want.

The reason I am talking about [*linear equation*][wiki-linear-equation] above is
that those are what is usually needed to find an intersection between two lines
in space. For a given "diamond", the linear equations for its four sides can be
easily calculated with the help of some pen and paper. Assuming that the center
(i.e. the sensor) is at `0,0` and the radius is `r`, we have 4 lines that form a
45-degree angle with both axes, with pretty simple equations.

Here's an ASCII-art to illustrate this, with sides labeled `A`, `B`, `C`, `D` in
clockwise order for reference:

```none
y = x + r + 1       A/\B    y = -x + r + 1
                    /  \
                    \  /
y = -x - (r + 1)    D\/C    y = x - (r + 1)
```

For a sensor at an arbitrary `sx,sy` position, we only need to apply a
[linear translation][wiki-euclidean-translation].

```none
y - sy = x - sx + r + 1         A/\B    y - sy = -(x - sx) + r + 1
                                /  \
                                \  /
y - sy = -(x - sx) - (r + 1)    D\/C    y - sy = x - sx - (r + 1)
```

Now, how do we plan on "storing" these equations? Let's look at them more
closely:

- Side A: *y =  x - s<sub>x</sub> + s<sub>y</sub> + r + 1*
- Side B: *y = -x + s<sub>x</sub> + s<sub>y</sub> + r + 1*
- Side C: *y =  x - s<sub>x</sub> + s<sub>y</sub> - r - 1*
- Side D: *y = -x + s<sub>x</sub> + s<sub>y</sub> - r - 1*

The parts we care about are those following the *x* variable in the above
equations. They are constants that depend on the sensor position (`sx,sy`) and
its detection radius. We can easily calculate them for every sensor. Let's write
a [generator function][py-generators] to do this:

```python
def sides(sx, sy, r):
    r += 1
    yield -sx + sy + r # a/\b  a: y =  x - sx + sy + r + 1
    yield  sx + sy + r # /  \  b: y = -x + sx + sy + r + 1
    yield -sx + sy - r # \  /  c: y =  x - sx + sy - r - 1
    yield  sx + sy - r # d\/c  d: y = -x + sx + sy - r - 1
```

Now let's say we want to intersect the `A` side of a diamond with the `B` side
of a second one, we will have the following equations (where the constants
*a<sub>1</sub>* and b<sub>2</sub> have already been calculated using the above
function):

- Side A of diamond 1: *y = x + a<sub>1</sub>*
- Side B of diamond 2: *y = -x + b<sub>2</sub>*

The intersection can be calculated as follows:

  - *x + a<sub>1</sub> = -x + b<sub>2</sub></sub>*
  - *2x = b<sub>2</sub> - a<sub>1</sub>*
  - *x = (b<sub>2</sub> - a<sub>1</sub>) / 2*
  - *y = x + a<sub>1</sub>*

We can now write a function to calculate the intersection given the two linear
equation constants:

```python
def intersect(a, b):
    x = (b - a) // 2
    return x, x + a
```

Using the above function, given any pair of diamonds, we can now calculate all
the possible intersections between pairs of their sides (or well, actually the
sides at `radius + 1`). We saw side `A` intersected with side `B` above. The
situation is analogous if we want to intersect side `A` and `D`, side `C` and
`B`, or side `C` and `D`: the only thing that changes is the order of the
operands in the subtraction. Additionally, it does not make sense to intersect
sides that are parallel to each other (e.g., `A` and `C`) because such an
intersection will either give infinite solutions (the two lines coincide) or no
solutions at all.

Let's write another generator function for this. It will take two sensors,
extract the linear equation constants for the sides of their detection diamonds,
and calculate all possible candidate points as intersections of perpendicular
sides:

```python
def candidates(s1, s2):
    a1, b1, c1, d1 = sides(*s1)
    a2, b2, c2, d2 = sides(*s2)
    yield intersect(a1, b2)
    yield intersect(a1, d2)
    yield intersect(c1, b2)
    yield intersect(c1, d2)
    yield intersect(a2, b1)
    yield intersect(a2, d1)
    yield intersect(c2, b1)
    yield intersect(c2, d1)
```

We have almost all we need to solve the problem. The final function we'll write
will find the magic spot for the missing (undetected) beacon by computing all
possible candidate points as intersections between parallel sides of any pair of
diamonds and checking their validity. To check the validity of a candidate
point, we need to ensure its coordinates are within `0` and `4000000`, and that
it is outside of all the detection diamonds of our sensors.

We'll use [`itertools.combinations()`][py-itertools-combinations] to iterate
over unique pairs of sensors. If a candidate point has coordinate within range,
we'll check that the manhattan distance between the point and any sensor is
greater than its detection radius, which can be done with
[`all()`][py-builtin-all] plus a [generator expression][py-generator-expr]. The
first candidate satisfying these conditions is the magic beacon spot we are
looking for.

```python
from itertools import combinations

def missing_beacon(sensors):
    # For all unique pairs of different sensors
    for s1, s2 in combinations(sensors, 2):
        # Intersect the perpendicular sides of their detection diamonds (at radius + 1)
        for x, y in candidates(s1, s2):
            # Ensure the solution is within range
            if x < 0 or x > 4000000 or y < 0 or y > 4000000:
                continue

            # Ensure the solution is outside the detection diamond of all sensors
            if all(manhattan(sx, sy, x, y) > r for sx, sy, r in sensors):
                return x, y
```

Finally, we can calculate the answer:

```python
x, y = missing_beacon(sensors)
answer = x * 4000000 + y
print('Part 2:', answer)
```


Day 16 - Proboscidea Volcanium
------------------------------

[Problem statement][d16-problem] — [Complete solution][d16-solution] — [Back to top][top]

### Part 1

We are inside a volcano that is about to erupt, and we want to stop it. We can
control the internal pressure of the volcano by means of a series of [pressure
relief valves][wiki-relief-valve] connected together in a network of pipes. All
valves start closed, and each one will release a given amount of pressure per
minute if opened. Opening a valve takes 1 minute, and traveling from a valve to
another that is connected to it also takes 1 minute. We initially start at the
valve with identifier `AA` and have 30 minutes until the volcano erupts, and we
want to maximize the total amount of pressure to relieve during this time.

It's clear from the problem statement that what we are dealing with is an
undirected [graph][wiki-graph], where the nodes are valves and the edges are the
pipes connecting them. What we essentially want to do is find the best "path" of
actions that take at most 30 mintues and give the best total pressure release
possible.

Let's parse the input into a graph structure then. I will use a dictionary of
lists for this purpose. A [`defaultdict`][py-collections-defaultdict] comes in
handy as usual in these cases, so that we don't have to check whether a key is
already present or not. The lines of input are a bit annoying to parse, but if
we simply [`.split()`][py-str-split] each one on whitespace one we'll notice
that the second field contains the name of a valve, and the fifth contains its
"pressure released per minute". Fields from the 10th onwards contain other
valves connected to the first one: we can use [`map()`][py-builtin-map] with a
[`lambda`][py-lambda] to easily extract those by [`.strip()`][py-str-strip]ping
away commas where needed.

```python
rates = {}
graph = defaultdict(list)

with open(...) as fin:
    for fields in map(str.split, fin):
        src  = fields[1]                                      # name of this valve
        dsts = list(map(lambda x: x.rstrip(','), fields[9:])) # valves connected to it
        rate = int(fields[4][5:-1])                           # pressure release rate (per minute)

        rates[src] = rate

        for dst in dsts:
            graph[src].append(dst)
```

The `graph` dictionary we just created is of the form `{valve: [<connected
valves>...]}`, so doing `graph['AA']` will give us the list of graph nodes
adjacent to the valve named `'AA'`. Additionally, the `rates` dictionary, kept
separate from `graph` for simplicity, will tell us what's the pressure release
rate of any valve.

There are several ways to solve the problem: most notably, this problem is a
good candidate for a [dynamic programming][wiki-dp]. This is the solution I
initially had in mind (but miserably failed to implement for whatever reason)
and also the one that a lot of other people used. The first instinctive thought
however when reading such a problem would be: can we brute-force the solution?
Well, as it turns out, *yes*, almost, if we are smart about it.

The first thing to usually do to brute-force something is understand what's the
space of the solutions we are looking to brute-force. We can represent a
solution as a dictionary of the form `{valve_id: time_of_release}`, which
contains all the valves we decided to open and the time at which they were
opened. Better yet, `{valve_id: time_remaining}` where `time_remaining` is the
amount of minutes remaining before the volcano erupts: this is much nicer since
the total pressure release of a valve can then simply be computed as
`rates[valve_id] * time_remaining`. Summing this up for all the valves in a
given solution will yield the total pressure release of the solution (i.e. the
value whose maximum we are looking for).

Let's implement a function to calculate the score of a solution:

```python
def score(rates, chosen_valves):
    tot = 0
    for valve, time_left in chosen_valves.items():
        tot += rates[valve] * time_left
    return tot
```

How can we enumerate all the possible solutions (i.e. choices of valves to open
and when)? In order to choose a set of valves, we need to also make sure we do
not exceed the 30 minutes time limit, and therefore the path taken to choose a
given set of valves to open is very important. Clearly, it doesn't make sense to
loop around and waste time, so ideally we would want to follow the shortest
possible path between any pair of valves.

Say we want to choose valves `AA` and `XX`, but they are *not* directly
connected to each other: we'd need to find the shortest path from `AA` to `XX`.
In order to enumerate all valid solutions we will need to perform this action an
awful lot of times! Thankfully, there's an algorithm that can help us. The
[Floyd-Warshall][algo-floyd-warshall] algorithm does exactly what we need: it
calculates the minimum distance between any possible pair of nodes of a given
graph. In our case, since all the arcs of the graph have the same weight, this
would be equivalent to performing a [BFS][algo-bfs] scan starting from every
single node and saving all the distances found, so that could also be
implemented instead.

I'll be using standard Floyd-Warshall, implemented as a function returning a
dictionary of dictionaries of the form `{a: {b: dist, ...}, ...}`. I'm not going
to copy-paste my implementation here as it's nothing special (check it out in
[the full solution][d16-solution] if you need), let's just say that we have a
`floyd_warshall()` function that returns what we need.

```python
distance = floyd_warshall(graph)
# distance['AA']['BB'] -> minimum distance from valve AA to BB
```

The minimum distance from one valve to another represents the time it takes to
travel between the two. Now that we have all the distances between any pair of
valves, it's easy to know how much it'd cost to choose an arbitrary valve at any
point in time.

Now we can start enumerating all the possible solutions as choices of valves
that respect the timing constraint. One simple way to do it is through
[depth-first search][algo-dfs], starting from valve `AA`.

1. Start at `AA` with `30` minutes remaining and no valves chosen.
2. For each of the valves we did not already choose: try choosing it. Choosing
   a valve means spending some time traveling to it (which we already calculated
   for all pairs of valves), plus 1 minute to open it.
3. Make a recursive call with the updated remaining time, valves to choose from
   and valves chosen. Save the returned choices to return them later.

As already said, we'll keep track of the valves chosen to be released through a
dictionary `{valve: time_of_release}`, and return value of our function will be
a list of dictionaries representing the currently chosen valves along with all
the other possibilities of chosen valves explored by deeper recursive calls.

Here's the commented code to do this:

```python
def solutions(distance, rates, valves, time=30, cur='AA', chosen={}):
    res = [chosen]

    # We can't reach any other valve in less than 2m, as it would take minimum
    # 1m to reach it plus 1m to open it, and therefore it'd be stay open for 0m.
    if time < 2:
        return res

    # For all the valves we can currently choose
    for nxt in valves:
        # Choosing this valve will take distance[cur][nxt] to reach it, plus 1m to open it
        new_time   = time - (distance[cur][nxt] + 1)
        # Choose this valve, it will stay open exactly for new_time (i.e. the time
        # we have now minus the time it takes to reach and open it).
        new_chosen = chosen | {nxt: new_time}
        # The new valves to choose from will not include this one
        new_valves = valves - {nxt}
        # Collect all possible choices having taken this valve
        res += solutions(distance, rates, new_valves, new_time, nxt, new_chosen)

    return res
```

Now the above `solutions()` function will return *all possible combinations* of
valves that we can open in under 30 minutes, along with the amount of time each
one will stay open. There are a couple of optimizations to be made though.

First of all, let's convert it into a [generator][py-generators]. Lists are
slow to work with, especially when you have a lot of them. This is very simple,
all we need to do is `yield` each possible choice as soon as we get ahold of it
instead of accumulating them in a list:

```python
def solutions(distance, rates, valves, time=30, cur='AA', chosen={}):
    yield chosen

    if time < 2:
        return

    for nxt in valves:
        new_time   = time - (distance[cur][nxt] + 1)
        new_chosen = chosen | {nxt: new_time}
        new_valves = valves - {nxt}
        yield from solutions(distance, rates, new_valves, new_time, nxt, new_chosen)
```


```python
valves = set(graph.keys())

for choice in solutions(distance, rates, valves):
    pass # calculate max score
```

Now, the above works fine, however it's very slow. The function does not even
seem to terminate soon. Indeed, even for the small example input we have, it
generates over *9 million* possible solutions. We can reduce this number by a
lot if we notice one very important thing: **there seem to be a lot of valves
with a pressure release rate of *zero* in our input**. It is pointless to open
any of them, since they will contribute nothing and only make us waste time to
reach them. We can therefore avoid them. If we pass a `valves` set that excludes
them, the number of possible choices for each recursive call (`for nxt in
valves`) will be greatly reduced, which will in turn exponentially decrease the
total number of solutions returned.

We can use [`filter`][py-builtin-filter] and the rates in the `rates` dictionary
to exclude useless valves, and re-perform the call:

```python
good = set(filter(rates.get, graph.keys()))

for choice in solutions(distance, rates, good):
    pass # calculate max score
```

And finally, another important optimization to make is avoiding unnecessary
recursive calls when we already know the remaining time we are passing is not
enough to open any other valve. This means moving the `time < 2` check inside
the loop:

```diff
 def solutions(distance, rates, valves, time=30, cur='AA', chosen={}):
-    yield chosen
-
-    if time < 2:
-        return
-
     for nxt in valves:
         new_time   = time - (distance[cur][nxt] + 1)
+        if new_time < 2:
+            continue
+
         new_chosen = chosen | {nxt: new_time}
         new_valves = valves - {nxt}
         yield from solutions(distance, rates, new_valves, new_time, nxt, new_chosen)
+
+    yield chosen
```

We have all we need to get the answer now:

```python
best = 0
for choice in solutions(distance, rates, valves):
    cur = score(rates, choice)
    if cur > best:
        best = cur
```

And since all we are doing is calculating a maximum, we can use `max()` plus a
generator expression for it:

```python
best = max(score(rates, s) for s in solutions(distance, rates, good))
print('Part 1:', best)
```

### Part 2

For the second part of today's problem, we are told that now we work in *two* at
the same problem. Both "players" move together, and the total time is now 26
minutes instead of 30. The answer we need to find is the same.

Okay... clearly the fact that we have two players means that they are going to
open different valves, since a valve cannot be opened twice. Therefore, at least
in theory, all we would need to do is try every possible combination of two
solutions that do not have valves in common, more or less like this:

```python
sols = list(solutions(distance, rates, good, 26))
best = 0

for s1 in sols:
    for s2 in sols:
        if ...: # s1 and s2 do not have valves in common
            cur = score(rates, s1) + score(rates, s2)
            if cur > best:
                best = cur
```

However... `len(sols)` for our input is `18676`, and a double nested `for` loop
means 18676<sup>2</sup> = ~350 million solutions to test (half of that in
theory, since we do not care about the order of `s1` and `s2`, but still). That
is... a bit too much. We need to somehow find another simplification.

There are a lot of solutions, but we know that only *some* among them will
achieve the maximum score. What about among *all the solutions that involve the
same valves?* Well, given a set of valves to open, there will be a lot of
different possible orders in which to open them... however, analogously, only
*some* among them will yield the maximum score, therefore only a single maximum
score *per subset of chosen valves* is possible.

We can iterate over the solutions for a single player once and pre-calculate the
maximum score possible for any given set of valves to open (regardless of the
order in which they are opened). Let's do this using a dictionary, more
precisely a `defaultdict` of `int` for commodity. The "key" to remember will be
the set of valves in a given solution. We cannot use a `set` as key since it is
mutable, but we can use a `frezenset` (the immutable variant of a `set`).

```python
maxscore = defaultdict(int)

for solution in solutions(distance, rates, good, 26):
    k = frozenset(choice)
    s = score(rates, choice)

    if s > maxscore[k]:
        maxscore[k] = s
```

Now `maxscore[set_of_valves]` will hold the maximum possible score attainable by
opening `set_of_valves`, irrespective of the order they are opened. The size of
this dictionary is a lot smaller than the number of different solutions returned
by `solutions()`:

```python
print(len(list(solutions(distance, rates, good, 26)))) # 18676
print(len(maxscore)) # 2342
```

Iterating over all possible pairs of solutions, we can then discard those that
have common keys (since as we already said both players cannot open the same
valve), and calculate the maximum of the scores of the remaining ones:

```python
best = 0

for s1, score1 in maxscore.items():
    for s2, score2 in maxscore.items():
        if len(s1 & s2) == 0: # a & b == intersection of the sets a and b
            continue

        cur = score1 + score2
        if cur > best:
            best = cur
```

We are doing a bit too many iterations as we don't care about the order of `a`
and `b`. We can use [`itertools.combinations()`][py-itertools-combinations] to
iterate over all possible pairs without taking the order into account:

```python
from itertools import combinations

best = 0

for (s1, score1), (s2, score2) in combinations(maxscore.items(), 2):
    if len(s1 & s2) == 0:
        continue

    cur = score1 + score2
    if cur > best:
        best = cur

print('Part 2:', best)
```


Day 18 - Boiling Boulders
-------------------------

[Problem statement][d18-problem] — [Complete solution][d18-solution] — [Back to top][top]

### Part 1

Today we are dealing with 3D space and cubes. We are given a list of `x,y,z`
coordinates, each one representing a unit cube (1x1x1) in space, and we want to
find out how many faces in total do not touch other cubes.

Let's start by quickly parsing the input. We have lines of integers separated by
commas, so just [`.split()`][py-str-split] them and [`map()`][py-builtin-map]
them to `int`. We want to keep a count of cube faces, so let's add the
coordinates of each cube we scan to a dictionary of the form
`{coords: free_faces}`, initially filled with all `6`.

```python
cubes = {}

with open(...) as fin:
    for line in fin:
        coords = tuple(map(int, line.split(',')))
        cubes[coords] = 6
```

A unit cube at `x,y,z` can be in contact with any of its immediate neighbors, at
`x±1,y,z`, `x,y±1,z` and `x,y,z±1`. Let's write a
[generator function][py-generators] to calculate and `yield` the coordinates of
the neighbors of a cube. We only need to go forward one step in any of the 6
possible directions:

```python
def neighbors(x, y, z):
    yield (x + 1, y    , z    )
    yield (x - 1, y    , z    )
    yield (x    , y + 1, z    )
    yield (x    , y - 1, z    )
    yield (x    , y    , z + 1)
    yield (x    , y    , z - 1)
```

For any given unit cube, we can know how many faces touch other cubes by simply
checking how many of the 6 neighbors were present in our input. For each
present neighbor, we will have exactly one face touching it, and therefore we
can decrement our initial count of `6` free faces. Since the function we
just wrote takes 3 arguments, we can use [unpack][py-unpacking] (`*`) each
cube's coordinates when calling it.

```python
for c in cubes:
    for n in neighbors(*c):
        if n in cubes:
            cubes[c] -= 1
```

The internal `for` is only performing a sum over a condition, so we can turn it
into a call to [`sum()`][py-builtin-sum] plus a
[generator expression][py-generator-expr]:

```python
for c in cubes:
    cubes[c] -= sum(n in cubes for n in neighbors(*c))
```

Finally, summing up all the values in `cubes` will yield the total number of
"free" faces that are not in contact with other cubes:

```python
surface = sum(cubes.values())
print('Part 1:', surface)
```

### Part 2

What we were actually trying to compute in part 1 was the total external surface
area of the cubes we have, counting connected cubes together as a single 3D
shape. However, the naïve approach of counting how many faces are "free" (not
touching other cubes) is not enough, as we can have a structure of cubes that
completely surrounds an empty portion of space, and the free faces in the inside
should not be counted. This is what we need to do for part 2: figure out how
many faces we over-counted and calculate the real external surface area.

This is intimidating at first, but things will get much clearer with a few
examples. For simplicity, we can reason in 2D, and then apply the same concepts
to 3D. Take for example the following structures where `#` means we have a
*square* there and `.` means empty space:

```none
  A       B       C       D
..#..   .###.   #####   #####
.#.#.   #..#.   #...#   #.#.#
..#..   #.#..   .##.#   ###.#
        .#...   .....   ..###
```

We have:

- Structure A above composed of 4 squares, of which none of them touch each
  other on any side, so we have a total of 16 free sides. However, these 4
  squares completely surround an empty square, and therefore we can distinguish
  between 4 *internal* sides and 12 *external* sides. The external perimeter
  is 12.

- Similarly, for B, we have a "hole" of 3 contiguous squares. The total number
  of free sides is 23, but the external perimeter is 16.

- Structure C does not have an internal perimeter, as it does not completely
  surround any region of 2D space.

- Structure D has two "holes" and traps two different regions of space on its
  inside. It has an internal perimeter of 10 and an external perimeter of 18.

Now it should be clear what we are dealing with. The same concepts apply in 3D
space where we have surface areas instead of perimeters, it's just harder to
visualize. Given a solid structure of unit cubes, some regions of spaces could
be trapped inside it, and therefore not contribute to the external surface area.

How can we detect these pockets of empty space? The simplest solution is to
check every single unit of space in the 3D [bounding box][wiki-bounding-box]
that includes all the unit cubes in our input. The 3D bounding box (you could
actually call it a "bounding cube") we are looking for will have coordinates
spanning from the minimum to the maximum coordinates we have one on each axis.
These can be calculated easily:

```python
minx = miny = minz = float('inf')
maxx = maxy = maxz = 0

for x, y, z in cubes:
    minx, maxx = min(x, minx), max(x, maxx)
    miny, maxy = min(y, miny), max(y, maxy)
    minz, maxz = min(z, minz), max(z, maxz)
```

To simplify any bound checks to perform later, we can create a
[`range`][py-builtin-range] object for each axis, and then use `x in rangex`
instead of `minx <= x <= maxx` (which is exactly the check made when doing
`x in rangex`):

```python
rangex = range(minx, maxx + 1)
rangey = range(miny, maxy + 1)
rangez = range(minz, maxz + 1)
```

For each unit cube of *free space* inside the bounding box, we can try
"escaping" the bounding box by visiting any other *free* unit cubes of space
that we can reach (i.e. coordinates that are not in our input). This can be done
through either [BFS][algo-bfs] or [DFS][algo-dfs]. If we manage to escape the
bounding box, it means that we were not inside an internal "pocket" of space. On
the other hand, if we cannot escape, it means we found such a pocket, and we are
surrounded by non-empty unit cubes. To count the number of "internal" faces we
can perform our exploration and increment a counter whenever we are prevented
from moving in any of the 6 directions by a non-empty unit cube.

Let's implement an `escape()` function that does exactly this, using iterative
DFS with a [`deque`][py-collections-deque] as queue. We'll keep track of the
number of "touched" internal faces with a counter, and return `0` if we manage
to escape, otherwise the counter.

```python
def escape(cubes, src, rangex, rangey, rangez):
    seen = set()
    queue = deque([src])
    faces_touched = 0

    while queue:
        p = queue.pop()
        if p in seen:
            continue

        seen.add(p)
        x, y, z, = p

        # Did we escape the bounding box?
        if x not in rangex or y not in rangey or z not in rangez:
            # If so, we are not trapped in an internal pocket
            return 0, seen

        # Try exploring all 6 directions
        for n in neighbors(x, y, z):
            # If we are blocked in this direction, it means we touched an internal face
            if n in cubes:
                faces_touched += 1
            else:
                # Otherwise, keep going
                if n not in seen:
                    queue.append(n)

    # We ran out of free space to visit, which means we are trapped in an internal pocket
    return faces_touched, seen
```

You may have noticed that the above function also returns a `seen` set of
visited coordinates. This is because we *need* to keep track of all the visited
coordinates of free space: if an exploration finds an internal pocket starting
from a given point in space, we do not need to perform a second redundant
exploration for any of the points we have visited during the first. Most
importantly, doing so would also make us double-count the number of internal
faces we touch, and we don't want that!

Now that we have a function able to identify and count internal faces, we can
call it for every *empty* unit cube inside our bounding box, and accumulate the
results. We need three nested `for` loops to iterate over all possible `x,y,z`
coordinates, so we can use [`itertools.product()`][py-itertools-product] to
make our life easier.

Let's get our part 2 answer:

```python
allseen = set()

for c in product(rangex, rangey, rangez):
    if c not in cubes: # this is an empty unit cube of space
        if c not in allseen: # this is not in an internal pocket we already found
            touched, seen = escape(cubes, c, rangex, rangey, rangez)
            surface -= touched
            allseen |= seen

print('Part 2:', surface)
```


Day 19 - Not Enough Minerals
----------------------------

[Problem statement][d19-problem] — [Complete solution][d19-solution] — [Back to top][top]

### Part 1

For today's problem we are building robots to mine some minerals... interesting.
There are 4 mineral types: ore, clay, obsidian and geodes. Additionally, there
are also 4 robot types, each of which can mine the corresponding mineral. We are
given a list of blueprints: each blueprint tells us which minerals (and how many
units) are needed to build a robot of a given type. We start with only one
ore-mining robot, and we have 24 minutes of time. Each robot we have can mine
one unit of its mineral per minute, and building a new robot takes 1 minute. We
need to figure out the maximum number of geodes we can mine with each of the
given blueprints, and calculate the best score among the blueprints we have,
which is given by the blueprint id multiplied by the maximum number of geodes
achievable with it.

Let's get input parsing out of the way. Each line of input is a quite long
sentence containing some positive integer quantities. We know all sentences are
formatted in the same way, so we can just extract all the integers on each line
with a regular expression using [`.findall()`][py-re-pattern-findall], and
accumulate these numbers in a list:

```python
import re

exp = re.compile(r'\d+')
blueprints = []

with open(...) as fin:
    for line in fin:
        blueprints.append(tuple(map(int, exp.findall(line))))
```

We are dealing with a [search problem][wiki-search-problem]. Given four things,
we can *theoretically* solve any search problem:

1. A consistent definition of a "state".
2. A start state.
3. A way to find successors of a given state (i.e. transition from one state to
   any other possible state).
4. A way to check if a state is a goal.

Let's see what we have for our problem:

- First, we need to define what exactly is a state. In our case, a state could
  be represented by the current time left, the amount of resources we have of
  each type, and the number of robots we have of each type. If at any given time
  two different sequences of choices bring us to the same state, we know both
  those choice sequences are equivalent, and the reachable states from now on
  are the same.

- Given the above, for our start state we have `24` minutes left, `0` of each
  material and `0` of each robot type, except for `1` ore-mining robot.

- A transition from one state to another can be of two different kinds:

  - Wait one minute without building any robot, and let the current robots we
    have mine resources.
  - Build one robot of some type (assuming we have resources to do so), while
    also having pre-existing ones mine resources. There are 4 different
    transitions of this kind (one per robot type).

- A goal state is any state where the time left is `0`, and its "score" is the
  number of geodes we have in such a state.

States can be seen as *nodes* in a graph, actions that change state can be seen
as *edges* of the graph, and goal states can be seen as nodes with no outgoing
edges. A search problem can therefore be solved using different graph
exploration techniques like [BFS][algo-bfs], [DFS][algo-dfs],
[A-star][algo-a-star], and so on.

Let's go with iterative DFS, which is pretty simple to implement. We'll write a
`search()` function that takes the parameters of a blueprint as input and
explores the state space finding the best goal states it comes across. As with
normal DFS, it's pointless to visit the same state multiple times, so we'll keep
a set of `visited` states to avoid this. As usual, we'll use a
[`deque`][py-collections-deque] for the queue of states to visit.

As said above, each state will be a `tuple` of the following form:

```python
(time_left, ore, clay, obsidian, geodes, robots_ore, robots_clay, robots_obsidian, robots_geode)
```

```python
def search(blueprint):
    (rore_cost,      # Cost in ore to build an ore-mining robot.
     rclay_cost,     # Cost in ore to build a clay-mining robot.
     robs_cost_ore,  # Cost in ore to build an obsidian-mining robot.
     robs_cost_clay, # Cost in clay to build an obsidian-mining robot.
     rgeo_cost_ore,  # Cost in ore to build a geode-mining robot.
     rgeo_cost_obs   # Cost in obsidian to build a geode-mining robot.
    ) = blueprint

    time    = 24
    best    = 0     # Best number of geodes we are able to collect.
    visited = set() # Visited states.

    # The "frontier" of our search, containing states to explore next.
    # In the initial state we only have 1 ore-mining robot.
    q = deque([(time, 0, 0, 0, 0, 1, 0, 0, 0)])

    while q:
        time, ore, clay, obs, geo, rore, rclay, robs, rgeo = state = q.pop()
        if state in visited:
            continue

        visited.add(state)

        # Each robot we have mines 1 resource of its type, taking 1 minute.
        newore  = ore  + rore
        newclay = clay + rclay
        newobs  = obs  + robs
        newgeo  = geo  + rgeo
        time -= 1

        # If we run out of time, we reached a "goal" state. Update the best
        # number of geodes we were able to mine.
        if time == 0:
            best = max(best, newgeo)
            continue

        # Following are the possible actions (transitions) to take...

        # We can always just spend one minute only mining without building any robot.
        q.append((time, newore, newclay, newobs, newgeo, rore, rclay, robs, rgeo))

        # If we have enough materials for a geode-mining robot, we could also build that.
        if obs >= rgeo_cost_obs and ore >= rgeo_cost_ore:
            q.append((
                time,
                newore - rgeo_cost_ore,
                newclay,
                newobs - rgeo_cost_obs,
                newgeo,
                rore, rclay, robs, rgeo + 1
            ))

        # If we have enough materials for an obsidian-mining robot, we could also build that.
        if clay >= robs_cost_clay and ore >= robs_cost_ore:
            q.append((
                time,
                newore - robs_cost_ore,
                newclay - robs_cost_clay,
                newobs,
                newgeo,
                rore, rclay, robs + 1, rgeo
            ))

        # If we have enough materials for a clay-mining robot, we could also build that.
        if ore >= rclay_cost:
            q.append((
                time,
                newore - rclay_cost,
                newclay,
                newobs,
                newgeo,
                rore, rclay + 1, robs, rgeo
            ))

        # If we have enough materials for an ore-mining robot, we could also build that.
        if ore >= rore_cost:
            q.append((
                time,
                newore - rore_cost,
                newclay,
                newobs,
                newgeo,
                rore + 1, rclay, robs, rgeo
            ))

    return best
```

The above DFS search is theoretically correct... however, if we try to run it,
we'll notice that it does take a while to finish. A relatively long while. This
is because the search space that we are trying to explore is currently very
large. Taking a look above, for *every single state we branch out 5 times*. We
need to somehow reduce the search space. This is one of the most important
aspects of a search problem. It's rather straightforward to code a DFS search on
any given search problem once you have identified states and transitions, the
real work is optimizing it, finding a way to *prune* away paths that lead to
sub-optimal goals as much as possible and as early as possible.

A lot of smart people have listed different assumptions and optimizations that
can be applied while searching in today's
[Reddit solution megathread][d19-reddit], some of which are rather
straightforward. I'm going to apply some here, until we reach a state where our
program is efficient enough.

The first thing to notice is that we can set an upper limit to the number of
robots to build. If the maximum amount of ore we need to build a robot is *N*,
then we'll never need more than *N* ore-mining robots. Having *N* is enough to
build the most expensive robot (ore-wise) every single minute. The same can be
applied to other minerals: we don't need more clay robots than the amount of
clay needed for obsidian robots, and we don't need more obsidian robots than the
amount of obsidian needed for geode robots.

We can calculate these maximum needed amounts of minerals at the start of our
function:

```python
def search(blueprint):
    # ...
    max_ore_needed  = max(rore_cost, rclay_cost, robs_cost_ore, rgeo_cost_ore)
    max_clay_needed = robs_cost_clay
    max_obs_needed  = rgeo_cost_obs
    # ...
```

Before trying to build a robot of any kind, let's stop and ask ourselves: do
we really need to? If not, we can avoid it and prune the branch. This simple
optimization cuts down the search space by a considerable amount. In terms of
code, it means adding a condition to the `if` for each branch. The only branch
that does not need this is the one for building geode-mining robots, as we
always want the most we can.

```python
def search(blueprint):
        # ... unchanged ...

        if clay >= robs_cost_clay and ore >= robs_cost_ore:
            # Avoid building more obsidian robots than the max obsidian per minute needed.
            if obs < max_obs_needed:
                q.append((...)) # unchanged

        if ore >= rclay_cost:
            # Avoid building more clay robots than the max clay per minute needed.
            if rclay < max_clay_needed:
                q.append((...)) # unchanged

        if ore >= rore_cost:
            # Avoid building more ore robots than the max ore per minute needed.
            if rore < max_ore_needed:
                q.append((...)) # unchanged

    return best
```

Of course, those `if` conditions can be merged for simplicity:

```python
def search(blueprint):
        # ... unchanged ...

        if obs < max_obs_needed and clay >= robs_cost_clay and ore >= robs_cost_ore:
            q.append((...))

        if rclay < max_clay_needed and ore >= rclay_cost:
            q.append((...))

        if rore < max_ore_needed and ore >= rore_cost:
            q.append((...))

    return best
```

This already cuts the execution time in half (at least on the example input),
but we can keep improving.

Let's now ask ourselves: when does it make sense to wait for some minerals to
be mined? Currently, our code *always* tries to explore a new state with a
transition that just waits one minute of time to only mine. Exactly here:

```python
        # We can always just spend one minute only mining without building any robot.
        q.append((time, newore, newclay, newobs, newgeo, rore, rclay, robs, rgeo))
```

This can sometimes be a waste of time. Similarly to what we discussed for the
previous optimization above, there is a certain maximum amount of any given
mineral type above which we'll never need to go. That is the maximum amount
needed to build one robot per minute using that mineral. It only makes sense to
wait for some mineral if we have less than the maximum needed *and* if we also
have at least one robot to mine it.

We already calculated these maximum needed amounts. Let's also use them to
perform this check and avoid spending one turn only mining if needed. The above
line becomes:

```python
        # Does it make sense to wait for a resource? I.E. do I have less than
        # the max needed and do I also have robots to produce it?
        if (robs and obs < max_obs_needed) or (rclay and clay < max_clay_needed) or ore < max_ore_needed:
            # If so, we can also try just spending one minute only mining without building any robot.
            q.append((time, newore, newclay, newobs, newgeo, rore, rclay, robs, rgeo))
```

A little faster, nice, let's keep going!

The third thing to notice is that we can *estimate* how good of a state we are
in, and prune away any paths passing through sub-optimal states. In the
best-case scenario (assuming we have robots and resources), we can build exactly
1 geode-mining robot per minute, and keep all the other geode-mining robots
mining. For example, if we find ourselves at `time=3` minutes left, and we have
`0` geodes and `3` geode-mining robots, in the best-case scenario (building one
more geode-mining robot per minute) we can mine another `3 + 2 + 1 = 6` geodes.
**The same reasoning can be applied to all minerals.**

In general, if we find ourselves with *t* time left, *n* minerals of a given
type already mined, and *r* mining robots for that mineral, in the best-case
scenario we can get a maximum of *n + r + (r + 1) + (r + 2) + ... + (r + t)*
minerals, which can also be written (grouping *r*) as *n + (t + 1)r + 1 + 2 +
3 + ... + t*. That last part consisting of the sum of the first *t* natural
numbers is exactly the *t-th* (lol) [triangular number][wiki-triangular-number],
so the formula can be further simplified to *n + (t + 1)r + t(t + 1)/2*.

Let's write a small helper function to calculate the maximum number of minerals
of a given type achievable in the best-case scenario:

```python
def best_case_scenario(initial_amount, robots, t):
    return initial_amount + robots * (t + 1) + t * (t + 1) // 2
```

We can now use it to perform three optimizations of the same kind any time we
visit a new state:

1. If the amount of geodes achievable in the best-case scenario number is lower
   than the current `best` we have, we can discard the state and any of its
   successors.
2. If the amount of obsidian achievable in the best-case scenario is lower than
   the amount needed to build a geode robot, we know we'll never be able to
   build geode robots anymore, so we can calculate the final score as
   `newgeodes + rgeo * time` and avoid exploring any further.
3. Likewise, this also applies to "ore", as geode robots need both ore and
   obsidian to be built.

```python
def search(blueprint):
    # ... unchanged ...

    while q:
        # ... unchanged ...

        if time == 0:
            best = max(best, newgeo)
            continue

        # If we can't mine more geodes in the best-case scenario, bail out.
        if best_case_scenario(newgeo, rgeo, time) < best:
            continue

        # If we can't mine enough obsidian to build new geode robots even in the
        # best-case scenario, we already know how many geodes we'll be able to get.
        if best_case_scenario(newobs, robs, time) < rgeo_cost_obs:
            best = max(best, newgeo + rgeo * time)
            continue

        # Likewise for ore.
        if best_case_scenario(newore, rore, time) < rgeo_cost_ore:
            best = max(best, newgeo + rgeo * time)
            continue

        # ... unchanged ...
```

We are getting there. There is only one last optimization I will make, which is
also the one that improves our solution the most. Credit goes to
[u/Coffee_Doggo][d19-reddit-user] for figuring this out and
[commenting about it][d19-reddit-comment].

Fourth and final thing to notice: if we ever find ourselves with the ability to
build a robot of a given type, *and* the previous minute we also had the chance
to build it, *but* decided to not build anything instead... doing it now doesn't
make much sense. We should have done it earlier! We can throw away this option.

The above will require us to keep track of which robots we were able to build at
any given state and pass that information to the next state. We can do it by
adding a simple list to our queue, containing numeric IDs:

```python
ORE, CLAY, OBS, GEO = range(4)
```

Here are the modifications that we need to apply:

```python
def search(blueprint):
    # ...

    # Add another element here, the list of robots we could have built in the
    # previous step, but decided not to build instead.
    q = deque([(time, 0, 0, 0, 0, 1, 0, 0, 0, [])])

    while q:
        tmp = q.pop()

        # This last list we added is not part of the state.
        state = tmp[:-1]
        if state in visited:
            continue

        visited.add(state)

        time, ore, clay, obs, geo, rore, rclay, robs, rgeo, did_not_build = tmp

        # ... unchanged ...

        can_build = []

        if obs >= rgeo_cost_obs and ore >= rgeo_cost_ore:
            # Did we have the chance to build this robot type in the previous iteration
            # but decided to not build anything instead? If so, we just wasted precious
            # time, it's pointless to do it now that we are late, the result is inevitably
            # going to be worse.
            if GEO not in did_not_build:
                # Remember that we could have built a geode robot.
                can_build.append(GEO)
                # Pass along an empyy list, we built a robot so we don't have a list
                # of robots that we "could have built" but didn't.
                q.append((..., []))

        if robs < max_obs_needed and clay >= robs_cost_clay and ore >= robs_cost_ore:
            # Likewise.
            if OBS not in did_not_build:
                can_build.append(OBS)
                q.append((..., []))

        if rclay < max_clay_needed and ore >= rclay_cost:
            # Likewise.
            if CLAY not in did_not_build:
                can_build.append(CLAY)
                q.append((..., []))

        if rore < max_ore_needed and ore >= rore_cost:
            # Likewise.
            if ORE not in did_not_build:
                can_build.append(ORE)
                q.append((..., []))

        # If we can also "wait" without building, pass along the list of robots
        # we couldhave built, but decided to not build instead.
        if (robs and obs < max_obs_needed) or (rclay and clay < max_clay_needed) or ore < max_ore_needed:
            q.append((..., can_build))

    return best
```

NOTE: in my complete solution I use a bitmask instead of a list to remember the
robots that could have been built. I simply represent "none" as 0, and any other
robot kind as a power of 2 (1, 2, 4, 8). Then I can *bitwise or* robot kinds
together. A value of `0b1111` for example means all robot kinds could have been
built.

We can *finally* run the above function for each blueprint and collect the
results:

```python
total = 0
for bid, *blueprint in blueprints:
    total += bid * search(blueprint)
```

Pardon me, but I cannot resist turning that loop into a
[`sum()`][py-builtin-sum] + [generator expression][py-generator-expr]:

```python
total = sum(bid * search(b) for bid, *b in blueprints)
print('Part 1:', total)
```

### Part 2

We are now told to only consider the *first 3* blueprints, calculate the maximum
amount of geodes achievable with them in *32* minutes, and then calculate the
product of these three numbers.

Thankfully, all those optimizations we made in part one were worth it! We have
a reasonably fast function, and we can simply move our `time` variable in the
function signature to be passed as a parameter:

```diff
-def search(blueprint):
+def search(blueprint, time=24):
     rore_cost, rclay_cost, robs_cost_ore, robs_cost_clay, rgeo_cost_ore, rgeo_cost_obs = blueprint
     max_ore_needed  = max(rore_cost, rclay_cost, robs_cost_ore, rgeo_cost_ore)
     max_clay_needed = robs_cost_clay
     max_obs_needed  = rgeo_cost_obs

-    time = 24
     best = 0
     ...
```

All that's left to do is get our second star:

```python
total = 1
for bid, *blueprint in blueprints[:3]:
    total *= search(blueprint, 32)
```

Again, the above is simplifiable into a call to [`math.prod()`][py-math-prod]
plus a generator expression:

```python
total = prod(search(b, 32) for _, *b in blueprints[:3])
print('Part 2:', total)
```

Woah. Tough day, but definitely an entertaining one!


Day 20 - Grove Positioning System
---------------------------------

[Problem statement][d20-problem] — [Complete solution][d20-solution] — [Back to top][top]

### Part 1

Simple problem today. We are given a list of integers, and we need to "shuffle"
them moving each one around according to the same rule. Each number, *in the
order they are originally given*, needs to be moved in the list a number of
steps forward or backward equal to its value (negatives numbers move backward).
The input list is cyclic, so moving forward past its end will mean wrapping back
to the first spot. After performing this operation on every single number, we
need to locate the number `0` and find the sum of the 1000th, 2000th and 3000th
number after it (remembering that the list is cyclic).

We mostly have to follow the rules here. The only problem with the algorithm we
need to apply is that the mixing operation must be done for each number in the
original order we are given, but the operation itself moves numbers around: we
need to somehow keep track of them. It would be easy to do if all the numbers
were different, but we have duplicates in our input, and we need to track
duplicates separately. This can be done in different ways, but the simplest one
is to "wrap" each number up in an object that stores additional information to
help us unequivocally identify it.

The wrapper object could be anything, for example, a tuple of the form
`(original_index, number)` would suffice, as the original index will be unique
for each number. This is what most people used today as it's intuitive and also
one of the first things that come to mind. I implemented this approach too,
[the code is here][d20-alternative-tuples], however, I'm going to use a
wrapper `class`, which in my opinion makes things a bit more intuitive and is
also slightly faster using CPython.

By default, in Python all instances of a class are different from each other
when compared, unless they implement special
[`__eq__()` or `__ne__()`][py-object-eq] methods. We're going to define a class
that only holds one property (the number we want to wrap) and implements no
methods except the [`__init__()`][py-object-init] constructor. Since we're going
to use this class a lot, listing the property name in the
[`__slots__`][py-class-slots] class variable will speed things up a bit (follow
the link to understand why).

```python
class Number:
    __slots__ = 'value'

    def __init__(self, value):
        self.value = int(value)
```

Now let's parse the input. It's going to be very easy as we have one integer per
line, just [`map()`][py-builtin-map] everything to a `Number`, which will also
take care of `str` to `int` conversion (`self.value = int(value)`), and store
all the objects in a `tuple`. To mix stuff around, we can later copy the content
of said `tuple` into a `list`, which will allow us to remove and insert elements
as we please, while still iterating over the elements in the original order.

```python
with open(...) as fin:
    order = tuple(map(Number, fin))
```

Onto the actual mixing, let's write a function for it. The rules to follow are
simple. For every number in the original order:

1. Find its index in the list using [`.index()`][py-list-index].
2. Remove it with [`.pop(index)`][py-list-pop].
3. Calculate its new index and re-insert it with [`.insert()`][py-list-insert].

Remember: the list we are dealing with is actually cyclic, so if we exceed the
length we should wrap back around. This can be easily done with a modulo (`%`)
operation: `index % len(numbers)` will always return an index between `0` and
`len(numbers) - 1`, wrapping back to `0` when `index == len(numbers)`. What's
even cooler is that this will also work out of the box with negative values,
given the way Python's modulo is defined.

Following the steps above, let's write a function to do the mixing and calculate
the final result. After mixing the numbers one by one according to their
original order, we'll simply scan the list to find the number whose `.value` is
`0` and then calculate the sum of the 1000th, 2000th and 3000th number past it.

```python
def mix(order):
    # Copy everything into a list to be able to move things around.
    numbers = list(order)

    for num in order:
        # Find the number.
        i = numbers.index(num)
        # Remove it.
        numbers.pop(i)
        # Calculate its new position.
        i = (i + num.value) % len(numbers)
        # Re-insert it.
        numbers.insert(i, num)

    for zero_idx, num in enumerate(numbers):
        if num.value == 0:
            break

    res  = numbers[(zero_idx + 1000) % len(numbers)].value
    res += numbers[(zero_idx + 2000) % len(numbers)].value
    res += numbers[(zero_idx + 3000) % len(numbers)].value
    return res
```

**A little digression**. It's worth noting that we are doing a lot of `.pop()`
and `.insert()` operations on a `list`. This is usually slow and requires
re-scanning the entire list to fix the position of any elements past the
insertion point. In fact, these operations take *O(n)* time. Another way of
solving the problem would be using [`collections.deque`][py-collections-deque],
which has fast pop and append operations on both ends, and exposes a
[`.rotate()`][py-deque-rotate] method to cyclically rotate elements around *n*
spots in *O(n)*.

The `deque` data structure was used by a lot of people, and I also wrote
[an alternative solution using it][d20-alternative-deque]. Even if at a first
glance it seems like it should be a faster solution, it really is not. This is
because we would still be doing 3 operations with complexity *O(n)* (one
`.index()` and two `.rotate()`), which is fundamentally the same we are already
doing with our list (one `.index()`, one `.pop()` and one `.insert()`). On top
of that, since under the hood
[`deque` is implemented as a doubly-linked list][misc-so-deque], the `.index()`
method needs to traverse a linked list of pointers, which is an inherently
slower operation compared to scanning a contiguous chunk of memory holding the
elements.

Now, getting back to the problem, we are basically done! All we need to do is
call the function to get our answer:

```python
answer = mix(order)
print('Part 1:', answer)
```

### Part 2

The numbers we had now change. Every number needs to be multiplied by
`811589153` before doing anything. Then, we need to do the same thing we did for
part 1, but this time the mixing happens *10 times in a row*.

Well, we already have the `mix()` function ready. We can effortlessly add a
parameter to specify the number of times to mix, and wrap the mixing code in one
more `for` loop:

```python
def mix(order, times=1): # Added times= parameter.
    numbers = list(order)

    for _ in range(times): # Mix as many times as needed.
        for num in order:
            i = numbers.index(num)
            numbers.pop(i)
            i = (i + num.value) % len(numbers)
            numbers.insert(i, num)

    for zero_idx, num in enumerate(numbers):
        if num.value == 0:
            break

    res  = numbers[(zero_idx + 1000) % len(numbers)].value
    res += numbers[(zero_idx + 2000) % len(numbers)].value
    res += numbers[(zero_idx + 3000) % len(numbers)].value
    return res
```

Now we can now modify the values of our numbers and run the algorithm again:

```python
for num in order:
    num.value *= 811589153

answer = mix(order, 10)
print('Part 2:', answer)
```

As simple as that!


Day 21 - Monkey Math
--------------------

[Problem statement][d21-problem] — [Complete solution][d21-solution] — [Back to top][top]

**Note**: my solution for part 2 of today's problem relies on the fact that the
input is a well-formed binary expression tree. This is not explicitly stated in
the problem statement, and is an assumption I (and many others) made to solve
the problem with a rather simple algorithm.

### Part 1

Today we are dealing with a [binary expression tree][wiki-expression-tree]. We
are given a list of variables of the form `name: value`, where each `name` is a
string, while each `value` can either be an expression to compute on two other
variables (`a <op> b`), or an integer. We need to calculate the value of `root`.

Let's start with input parsing. As already anticipated, we are dealing with a
tree, and `root` represents the root of the tree. We aren't explicitly told that
this is a tree (i.e. all nodes appear on the right at most once), we could
actually be dealing with a graph where multiple nodes can have edges pointing to
the same node. Nonetheless, as long as there are no loops, we are safe and the
expression result can be easily computed. As a side note, the inputs for today's
problem *do actually represent trees*.

Each node can either be a binary expression node referencing other two nodes or
a leaf (a simple integer). We'll create a dictionary of the form `{name: value}`
where `value` is either an integer or a 3-element list of the form
`[name1, op, name2]`. The way our input is given, creating this structure is
trivial. All we need to do is [`.strip()`][py-str-strip] and
[`.split()`][py-str-split] each line in the correct way. First split on `': '`
to get the left and right side, then check if the right side is an integer
(using e.g. [`.isdigit()`][py-str-isdigit]) to decide whether to parse it or
`.split()` again.

```python
T = {}
with open(...) as fin:
    for line in fin:
        a, b = line.strip().split(': ')
        T[a] = int(b) if b.isdigit() else b.split()
```

Our tree `T` now contains all the information we need to calculate the value of
the expression. Starting at `'root'`, we can perform a simple
[depth-first][algo-dfs] traversal of the tree: if we encounter a "value" node we
can just return the value; while if we encounter an "expresison" node we can
first find the left and right operands' values recursively, then perform the
needed operation and return its result.

To make our life easier, we can use a `dict` as map for the operations. We need
to perform addition (`+`), subtraction (`-`), multiplication (`*`) and division
(`/`). The [`operator`][py-operator] module has all these in the form of
functions taking two parameters. For the division, we'll use
[`floordiv`][py-operator-floordiv] (equivalent to the `//` operator).

```python
from operator import add, sub, mul, floordiv

OPMAP = {
    '+': add,
    '*': mul,
    '-': sub,
    '/': floordiv
}
```

To distinguish whether we are dealing with a value or expression node, we can
use [`isinstance()`][py-builtin-isinstance] to check whether `T[node]` is a
`list` or an `int`. We will treat `T` as a global variable for simplicity, but
it could also be passed as parameter.

```python
def calc(value, list):
        # This is a value node, just return the value.
        return value

    # This is an expression node.
    l, op, r = value
    # Compute left and right value.
    lvalue = calc(l)
    rvalue = calc(r)
    # Perform operation and return result.
    return OPMAP[op](lvalue, rvalue)
```

Since our input seems to be a well-formed tree, we're only going to visit each
node exactly once. If that was not the case though, and our input was an acyclic
graph, we could optimize the above function with the help of
[`@lru_cache()`][py-functools-lru_cache] to [memoize][wiki-memoization] node
values and avoid wasting time computing them multiple times.

To get our answer we can now simply call the function on `'root'`:

```python
answer = calc('root')
print('Part 1:', answer)
```

### Part 2

Now we are told that the `'root'` expression node is actually an equality check
between its left and right operand. Furthermore, we do not know the value of the
value node `'humn'`: we need to find a value for it such that the equality check
at `'root'` is satisfied.

The complexity of this second part of the problem depends on the form of the two
expressions on the left and right side of the root equality check. We know that
we are looking for exactly one solution, so we cannot be dealing with
polynomials of degree higher than 1, meaning that we cannot find an expression
node of the form `humn * humn`, or in general `A * b` where both `A` and `B`
include `humn` in their subtrees.

There's a small problem though: nobody technically guarantees that we cannot
encounter expression nodes of the form `humn + humn` (or `A + B` where either of
the two leads to `humn`) or similar. Encountering one of these would mean that
the input does not form a tree, but a graph, which would make the problem harder
to solve. Since as already stated in part 1, the inputs of today's problem are
all well-formed binary expression trees, we will assume that something like this
cannot happen. For this reason, I wrote an `is_tree()` check for this assumption
in my [complete solution][d21-solution].

What is happening now is that we essentially have one side of the tree at `root`
with an unknown value, but *we know it must match the value of the other side*.
Let's replace `T['humn']` with `None`, and modify the `calc()` function to tell
us which side has unknown value: whenever we encounter a value that is `None` or
an expression where one of the two operands has value `None`, we'll return
`None` to propagate it back to the top. While we are at it, let's also decorate
the function with [`@lru_cache()`][py-functools-lru_cache] since we're going to
call it multiple times for the same nodes now.

```diff
+@lru_cache()
 def calc(node):
     value = T[node]
     if not isinstance(value, list):
         return value

     l, op, r = value
     lvalue = calc(l)
     rvalue = calc(r)
+
+    if lvalue is None or rvalue is None:
+        return Noner
     return OPMAP[op](lvalue, rvalue)
```

**Note**: since we have decorated `calc` with `lru_cache`, we need to remember
calling `calc.cache_clear()` after using it for part 1, otherwise the cache will
hold the wrong values for part 2.

Now we can check which side of the `root` node has value `None`, and we'll know
that its expected value should be the one of the other side:

```python
T['humn'] = None

l, _, r = T['root']
lvalue = calc(l)
rvalue = calc(r)

if lvalue is None:
    # 'humn' is on this side of the tree.
    # The expected value of this side of the tree is rvalue.
    ...
else:
    # 'humn' is on this side of the tree.
    # The expected value of this side of the tree is lvalue.
    ...
```

To solve the problem and find the unknown value of `humn`, we can navigate the
tree recursively exploring the node whose value is unknown, keeping track of
what value it should have:

- If we are at `humn`, we just found its value: it's the expected value we are
  carrying around.
- Otherwise we must be at some expression node, where one of the two child nodes
  (left or right) has unknown value. We know the expected value of the current
  node. We can compute the expected value of the node with unknown value
  performing the opposite of the expression.

For example, assume that initially for `root` we have `lvalue = None` and
`rvalue = 123`: we know that `humn` is somewhere on the left of `root`, and that
the value of the left node should be `123`. We explore the left node, and find
an expression with operation `+`, `lvalue = 100` and `rvalue = None`. We know
that `lvalue + rvalue == 123`, and therefore `100 + rvalue == 123`. We can now
perform the opposite operation to find out that
`rvalue == 123 - lvalue == 123 - 100 == 23`. Now we can continue on the right
node knowing its expected value is `23`.

Each time we explore a new node, we can compute the new expected value of either
of the two children as follows (let's call the expected value `E` for
conciseness):

- If the operation is `+`: we know `E = L + R`, so `L = E - R` and `R = E - L`.
- If the operation is `*`: we know `E = L * R`, so `L = E / R` and `R = E / L`.
- If the operation is `-`: we know `E = L - R`, so `L = E + R` and `R = L - E`.
- If the operation is `/`: we know `E = L / R`, so `L = E * R` and `R = L / E`.

Notice how in the above list we have two expressions that stand out. While in
general we have `L_or_R = E <inverse_op> R_or_L`, for `-` and `/` we have
different formulas to compute `L` and `R`. This is because these operations are
not [commutative][wiki-commutative].

Nonetheless, we can build another `dict` to use as mapping for the operations to
perform in the same way we did for part 1. Each function will take `E` as first
aprameter and the other side as second parameter. This time though we'll also
need to know if the value that we want to calculate is the left or the right: we
can do this with a `bool`. We can mostly still use the functions from the
`operator` module, except for calculating the right side of `/` and `-`.

```python
# Calculate R or L knowing that E = L op R.
# True  = need to calculate L given E and R as parameters.
# False = need to calculate R given E and L as parameters.
REV_OPMAP = {
    ('+', True ): sub,
    ('+', False): sub,
    ('*', True ): floordiv,
    ('*', False): floordiv,
    ('-', True ): add,
    ('-', False): lambda x, l: l - x,
    ('/', True ): mul,
    ('/', False): lambda x, l: l // x,
}
```

We can now apply the logic explained above to recursively follow the side of the
tree where our "unknown value" (`humn`) is located and update its expected value
along the way:

```python
def find_value(node, expected):
    if node == 'humn':
        # We reached the node we wanted and we now know its value.
        return expected

    l, op, r = T[node]
    lvalue = calc(l)
    rvalue = calc(r)

    # We know expected = L op R...

    if lvalue is None:
        # Left side has unknown value, calculate its expected value and keep going.
        expected = REV_OPMAP[op, True](expected, rvalue)
        return find_value(l, expected)

    # Right side has unknown value, calculate its expected value and keep going.
    expected = REV_OPMAP[op, False](expected, lvalue)
    return find_value(r, expected)
```

We can now find the answer we were looking for:

```python
T['humn'] = None

l, _, r = T['root']
lvalue = calc(l)
rvalue = calc(r)

if lvalue is None:
    answer = find_value(l, rvalue)
else:
    answer = find_value(r, rvalue)
```

Since `root` is `L == R`, we could also re-write it as `L - R`, knowing that the
resoult should be `0`, and simplify the above logic:

```python
T['humn'] = None
T['root'][1] = '-'
answer = find_value('root', 0)
print('Part 2:', answer)
```


Day 24 - Blizzard Basin
-----------------------

[Problem statement][d24-problem] — [Complete solution][d24-solution] — [Back to top][top]

### Part 1

Today's problem involves pathfinding, but with a twist. We are in a rectangular
grid surrounded by walls (`#`), where each cell is either free or represents *a
blizzard* (`<`, `>`, `^`, `v`). Given a start (2nd column of the first row) and
a destination (second-to-last column of the last row), we need to navigate the
grid being careful not to step in a blizzard or into a wall.

Problem is, each instant of time, every blizzard moves forward one step in the
direction it is facing (i.e. `>` moves to the right). Whenever a blizzard
reaches one of the four walls of the grid, it wraps around the same row/column,
continuing from the opposite side. Furthermore, a single cell can contain more
than one blizzard (each going in a different direction) at any given time.

Each instant of time we can either move in one of the 4 cardinal directions
(north, south, east, west) or wait in place. We need to calculate the minimum
amount amount of time needed to reach the destination avoiding blizzards.

Let's start by parsing the input into a grid: after reading the entire input,
[`.splitlines()`][py-str-splitlines] is all we need.

```python
with open(...) as fin:
    grid = fin.read().splitlines()
```

Now, if it weren't for the added difficulty of the moving blizzards, today's
solution would be standard [BFS][algo-bfs] on a grid. However, we'll need to
simulate the evolution of the blizzard in time. Keeping around the actual grid
and editing its content each iteration is slow and error-prone. The simplest way
to represent cells occupied by a blizzard would be a `set()` of coordinates so
that we can easily check whether a certain position contains any blizzard with
`(r, c) in blizzard`. However, this is not enough as we also need to keep track
of the direction each blizzard is moving. To do this, we can use a dictionary of
the form `{coords: list_of_directions}`: each cell (at a given coordinate) can
contain more than one blizzard at a given time, so this is an easy way to track
both the number of blizzards present and all their directions.

A minimal example can help understand how multiple blizzards going in different
directions can end up overlapping on the same cell:

```none
#.#####       #.#####       #.#####       #.#####
#.>.<.#  ==>  #..2..#  ==>  #.<.>.#  ==>  #<...># ==> ...
#####.#       #####.#       #####.#       #####.#
```

To easily advance each blizzard in the right direction, we can remember
directions as tuples of the form `(delta_r, delta_c)`. Let's create a map that
associates each character representing a blizzard with one of these:

```python
DIRMAP = {
    '>': ( 0,  1),
    '<': ( 0, -1),
    'v': ( 1,  0),
    '^': (-1,  0),
}
```

We know that each blizzard will wrap around and continue from the opposite side
of the row/column once it reaches a wall: if we discard all walls and only
consider the internal rectangle (enclosed in the walls) as the grid to work on,
the first row and column will start at `0`, and wrapping around can later be
handled with a modulo operation, e.g. `(row + 1) % height`.

```none
  01234567
0 #.######            012345
1 #>>.<^<#          0 >>.<^<
2 #.<..<<#  =====>  1 .<..<<
3 #>v.><>#          2 >v.><>
5 ######.#
Actual grid      Simplified grid
```

Let's now iterate over the grid, ignoring the first and last row and the first
and last column of each row (which we know are all going to be walls). For each
blizzard we encounter, we'll remember its position and direction. The
[`enumerate()`][py-builtin-enumerate] built-in comes in handy here.

```python
bliz = {}

for r, row in enumerate(grid[1:-1]):
    for c, cell in enumerate(row[1:-1]):
        if cell in DIRMAP:
            # There's a blizzard here (< > ^ v). Its directoin (delta_r, delta_c)
            # is given by the DIRMAP we created above.
            bliz[r, c] = [DIRMAP[cell]]
```

Since we discarded the external walls, the actual height and width of the
internal rectangle are 2 units less than the original grid's height and width.
The starting position is now at the first column of the row immediately above
the first one, and the destination is at the last column of the row immediately
below the last one. Let's calculate these values for later:

```python
height, width = len(grid) - 2, len(grid[0]) - 2
src, dst = (-1, 0), (height, width - 1)
```

Now into the actual guts of the problem: let's write a function to "evolve" the
current blizzards moving each of them one step forward, and returning a new
dictionary representing the new state of the blizzards. Each key in the `bliz`
dictionary we just created represents the coordinates of a cell containing one
or more blizzards, and their directions are listed in the associated value (a
`list`).

We can iterate over the [`.items()`][py-dict-items] of the dictionary, applying
the deltas listed in the directions for each coordinate. A
[`defaultdict`][py-collections-defaultdict] of `list` makes the whole operation
more convenient.

```python
from collections import defaultdict

def evolve_blizzard(bliz, width, height):
    newbliz = defaultdict(list)

    for (r, c), directions in bliz.items():
        for dr, dc in directions:
            newr = (r + dr) % height
            newc = (c + dc) % width
            newbliz[newr, newc].append((dr, dc))

    return newbliz
```

Given the coordinates of our position and current the state of the blizzards, we
can now calculate all the possible neighboring coordinates we can move to. These
will be the ones inside the bounds of our simplified grid and not overlapping
with any blizzard. In addition to those, we can also stand still if a blizzard
does not hit us. Finally, one last thing to consider is that our destination is
at the last column and one row below the last row, which is technically out of
bounds: we can special-case this check.

Let's write a [generator function][py-generators] to `yield` all valid
coordinates we can move to given the current position.

```python
def neighbors(bliz, r, c, height, width):
    # Right above the destination? Even if out of bounds, that's also a valid position to move to.
    if r == height - 1 and c == width - 1:
        yield height, c

    # For each of the 4 cardinal directions...
    for dr, dc in ((0, 1), (1, 0), (0, -1), (-1, 0)):
        rr, cc = r + dr, c + dc
        # ... check if we are in bounds and if there is NO blizzard here...
        if 0 <= rr < height and 0 <= cc < width and (rr, cc) not in bliz:
            # ... if so, we can move here.
            yield rr, cc

    # We can also stand still if no blizzard hits us.
    if (r, c) not in bliz:
        yield r, c
```

Now for the heart of the problem: as anticipated, we can perform an iterative
[breadth-first search][algo-bfs] from the starting position until we reach the
destination, tracking *time* instead of *distance*. This works because each
"step" we take is unitary, meaning it advances the time of exactly 1 unit.
Contrary to a "traditional" BFS though, in this case we can re-visit cells more
than once. In fact, merely standing still means only advancing the time,
visiting the same cell two times in a row. We can therefore avoid keeping track
of visited cells, but we still need to keep track of where we are.

We'll keep track of all the possible positions we can be at the current time
using a `set`. A `list` or another similar dat structure would still work, but
we'd have to deal with unneeded duplicates, and a `set` takes care of those for
us. Initially (`time = 0`) this will only include the start position. We'll then
advance one step forward in time each iteration, evolving the blizzards and
figuring out the new reachable positions given by applying the `neighbors`
function to all the current positions we are tracking. If we ever find the
destination among those, we can stop and return the current time.

```python
def bfs(bliz, src, dst, height, width):
    positions = {src}
    time = 0

    # While the destination is not reached.
    while dst not in positions:
        # Advance time and evolve blizzards moving them around.
        time += 1
        bliz = evolve_blizzard(bliz, width, height)

        # For each possible position we are tracking, calculate the next valid
        # positions, and add them to a new set.
        new_positions = set()
        for pos in positions:
            neighs = neighbors(bliz, *pos, height, width)
            new_positions.update(neighs)

        # Track these new positions in the next iteration.
        positions = new_position

    return time
```

We can also refactor the above inner loop into an `advance()` generator function
that takes a set of positions and yields any new valid position:

```python
def advance(bliz, positions, height, width):
    for pos in positions:
        yield from neighbors(bliz, *pos, height, width)
```

This makes the body of our `bfs()` function slimmer:

```python
def bfs(bliz, src, dst, height, width):
    positions = {src}
    time = 0

    while dst not in positions:
        time += 1
        bliz = evolve_blizzard(bliz, width, height)
        positions = set(advance(bliz, positions, height, width))

    return time
```

All that's left to do is call the above function with the right parameters:

```python
time = bfs(bliz, src, dst, height, width)
print('Part 1:', time)
```

### Part 2

After reaching the destination, we need to go back to the start, and then go
back to the destination again. The end goal is still to figure out the minimum
amount of time needed, but the path is now longer.

No big deal, we already have almost all we need, we only need to make a few
modifications to our functions. First of all, since now we can also go back to
the starting position, we need to special-case that too in the `neighbors()`
function:

```diff
 def neighbors(bliz, r, c, height, width):
-    if r == height - 1 and c == width - 1:
+    if r == 0 and c == 0:
+        yield -1, 0
+     elif r == height - 1 and c == width - 1:
         yield height, c

     # ... unchanged ...
```

Secondly, we now need to remember the final state of all the blizzards after the
first search. We can just return that along with the time in our `bfs()`
function:

```diff
 def bfs(bliz, src, dst, height, width):
     # ... unchanged ...

-    return time
+    return time, bliz
```

After solving part 1, we'll overwrite the `bliz` variable with the new state:

```python
time1, bliz = bfs(bliz, src, dst, height, width)
print('Part 1:', time1)
```

And for part 2, we'll now perform two more `bfs()` calls: one to go back to
`src` from `dst`, and one to go back to `dst` again. The total time taken will
will be the sum of the 3 times.

```python
time2, blitz = bfs(bliz, dst, src, height, width)
time3, _     = bfs(bliz, src, dst, height, width)
total_time = time1 + time2 + time3
print('Part 2:', total_time)
```


Day 25 - Full of Hot Air
------------------------

[Problem statement][d25-problem] — [Complete solution][d25-solution] — [Back to top][top]

Last problem of the year, and a fairly simple one thankfully. We are given a
list of numbers in a weird base-5 representation called "SNAFU"
([LOL at this name choice][wiki-snafu]). The digits used are `210-=`, where `-`
means *-1* and `=` means *-2*. We need to sum all these numbers, and calculate
the total *in the same base* (i.e. using these digits).

The first thing we'll need is a function to convert from SNAFU (weird base 5) to
base 10. It's fairly straightforward: given a number, iterate over its digits,
convert them to their actual values, and multiply by the appropriate power of 5,
accumulating the result. For simplicity, let's use a `dict` to map SNAFU digits
to their actual values:

```python
VALUES = {'=': -2, '-': -1, '0': 0, '1': 1, '2': 2}
```

Then, for the actual conversion, we can either start with *5<sup>0</sup>* (1) or
and iterate over the digits in reverse order, or start with *5<sup>L-1</sup>*
(where *L* is the total number of digits) and iterate normally. I chose the
latter.

```python
def base10(n):
    power = 5 ** (len(n) - 1)
    res = 0

    for digit in n:
        res += VALUES[digit] * power
        power //= 5

    return res
```

We can now convert every number in our input to base 10 and calculate their sum.
It's just a question of iterating and stripping input lines:

```python
total = 0
with open(...) as fin:
    for line in fin:
        total += base10(line.strip())
```

Or more concisely, using [`map()`][py-builtin-map] + [`sum()`][py-builtin-sum],
with the help of [`.splitlines()`][py-str-splitlines] to automatically trim away
newlines:

```python
with open(...) as fin:
    total = sum(map(base10, fin.read().split()))
```

The opposite conversion, from base 10 to SNAFU, is a little bit trickier. We
cannot do a "normal" base conversion as we are used to (we are, right?), because
we have negative digits (`-`, `=`). However, we can start with the code for a
normal conversion and see how we can get there.

This is what a normal base 10 to base 5 conversion would look like:

```python
def base10_to_base5(n):
    res = ''

    while n:
        n, digit = divmod(n, 5)
        res += str(digit)

    return res[::-1]
```

The [`divmod()`][py-builtin-divmod] built-in used above simply calculates both
quotient and remainder of a division, it's the same as
`n, digit = n // 5, n % 5`.

Now, the problem with the above conversion algorithm is that we will get digits
higher than `2`, which are not contemplated in SNAFU notation and cannot be
represented. However, `3` can be seen as `5 - 2` and `4` can be seen as `5 - 1`.
In fact, we can represent `3` and `4` with two SNAFU digits: `3` is `1=`
(*1×5<sup>1</sup> - 2×5<sup>0</sup>*) and `4` is `1-` (*1×5<sup>1</sup> -
1×5<sup>0</sup>*). This also works for higher powers: *3×5<sup>7</sup> =
1x5<sup>8</sup> - 2×5<sup>7</sup>*; *4×5<sup>9</sup> = 1x5<sup>10</sup> -
1×5<sup>9</sup>*. Therefore, for any digit higher than `2`, we can *increment
the next digit of the number, and then "borrow" from it*.

Given the above, the function to convert a number from base 10 to SNAFU can be
written as follows:

```python
def snafu(n):
    res = ''

    while n:
        n, digit = divmod(n, 5)

        if digit > 2:
            # Add 1 more of the next (higher) power of 5
            n += 1

            # Borrow from it:
            if digit == 3:
                res += '=' # Take 2 x current power of 5.
            else: # digit == 4
                res += '-' # Take 1 x current power of 5.
        else:
            res += str(digit)

    return res[::-1]
```

Compacting and simplifying the above logic, we have:

```python
def snafu(n):
    res = ''

    while n:
        n, digit = divmod(n, 5)
        res += '012=-'[digit]
        n += digit > 2

    return res[::-1]
```

All that's left to do is convert the total we previously calculated:

```python
answer = snafu(total)
print('Part 1:', answer)
```

And as usual, no part 2 for day 25. ***Merry Christmas!***

---

*Copyright &copy; 2022 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2022-walkthrough
[d01]: #day-1---calorie-counting
[d02]: #day-2---rock-paper-scissors
[d03]: #day-3---rucksack-reorganization
[d04]: #day-4---camp-cleanup
[d05]: #day-5---supply-stacks
[d06]: #day-6---tuning-trouble
[d07]: #day-7---no-space-left-on-device
[d08]: #day-8---treetop-tree-house
[d09]: #day-9---rope-bridge
[d10]: #day-10---cathode-ray-tube
[d11]: #day-11---monkey-in-the-middle
[d12]: #day-12---hill-climbing-algorithm
[d13]: #day-13---distress-signal
[d14]: #day-14---regolith-reservoir
[d15]: #day-15---beacon-exclusion-zone
[d16]: #day-16---proboscidea-volcanium
[d18]: #day-18---boiling-boulders
[d19]: #day-19---not-enough-minerals
[d20]: #day-20---grove-positioning-system
[d21]: #day-21---monkey-math
[d24]: #day-24---blizzard-basin
[d25]: #day-25---full-of-hot-air

[d01-problem]: https://adventofcode.defaultdictcom/2022/day/1
[d02-problem]: https://advpairwiseentofcode.com/2022/day/2
[d03-problem]: https://adventofcode.com/2022/day/3
[d04-problem]: https://adventofcode.com/2022/day/4
[d05-problem]: https://adventofcode.com/2022/day/5
[d06-problem]: https://adventofcode.com/2022/day/6
[d07-problem]: https://adventofcode.com/2022/day/7
[d08-problem]: https://adventofcode.com/2022/day/8
[d09-problem]: https://adventofcode.com/2022/day/9
[d10-problem]: https://adventofcode.com/2022/day/10
[d11-problem]: https://adventofcode.com/2022/day/11
[d12-problem]: https://adventofcode.com/2022/day/12
[d13-problem]: https://adventofcode.com/2022/day/13
[d14-problem]: https://adventofcode.com/2022/day/14
[d15-problem]: https://adventofcode.com/2022/day/15
[d16-problem]: https://adventofcode.com/2022/day/16
[d18-problem]: https://adventofcode.com/2022/day/18
[d19-problem]: https://adventofcode.com/2022/day/19
[d20-problem]: https://adventofcode.com/2022/day/20
[d21-problem]: https://adventofcode.com/2022/day/21
[d24-problem]: https://adventofcode.com/2022/day/24
[d25-problem]: https://adventofcode.com/2022/day/25

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
[d24-solution]: solutions/day24.py
[d25-solution]: solutions/day25.py

[2018-d17-problem]:       https://adventofcode.com/2018/day/17
[2019-d18-p1]:            ../2019/README.md#part-1-17
[d08-p1]:                 #part-1-7
[d02-alternative]:        misc/day02/mathematical.py
[d08-alternative]:        misc/day08/faster_part1.py
[d14-italyinformatica]:   https://www.reddit.com/r/ItalyInformatica/comments/zlj7dj/adventofcode_2022_giorno_14/j05rz5p/
[d19-reddit]:             https://www.reddit.com/r/adventofcode/comments/zpihwi/2022_day_19_solutions/?sort=confidence
[d19-reddit-user]:        https://www.reddit.com/user/Coffee_Doggo
[d19-reddit-comment]:     https://www.reddit.com/r/adventofcode/comments/zpihwi/2022_day_19_solutions/j0vvtdt/
[d20-alternative-tuples]: misc/day20/tuples.py
[d20-alternative-deque]:  misc/day20/deque.py

[py-3-way-comparison]:   https://docs.python.org/3/reference/expressions.html#comparisons
[py-class-slots]:        https://docs.python.oattrgetterrg/3/reference/datamodel.html#slots
[py-cond-expr]:          https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-generator-expr]:     https://www.python.org/dev/peps/pep-0289/
[py-generators]:         https://docs.python.org/3/howto/functional.html#generators
[py-lambda]:             https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-list-comprehension]: https://docs.python.org/3/tutorial/datastructures.html#list-comprehensions
[py-loop-else]:          https://docs.python.org/3/tutorial/controlflow.html#break-and-continue-statements-and-else-clauses-on-loops
[py-set]:                https://docs.python.org/3/tutorial/datastructures.html#sets
[py-slicing]:            https://docs.python.org/3/glossary.html#term-slice
[py-tuple]:              https://docs.python.org/3/tutorial/datastructures.html#tuples-and-sequences
[py-unpacking]:          https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-divmod]:          https://docs.python.org/3/library/functions.html#divmod
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-eval]:            https://docs.python.org/3/library/functions.html#eval
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-isinstance]:      https://docs.python.org/3/library/functions.html#isinstance
[py-builtin-iter]:            https://docs.python.org/3/library/functions.html#iter
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-next]:            https://docs.p[d20-alt-deque].ython.org/3/library/functions.html#next
[py-builtin-ord]:             https://docs.python.org/3/library/functions.html#ord
[py-builtin-range]:           https://docs.python.org/3/library/functions.html#range
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-type]:            https://docs.python.org/3/library/functions.html#type
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-bytes-splitlines]:        https://docs.python.org/3/library/stdtypes.html#bytes.splitlines
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-copy-deepcopy]:           https://docs.python.org/3/library/copy.html#copy.deepcopy
[py-deque-rotate]:            https://docs.python.org/3/library/collections.html#collections.deque.rotate
[py-dict-items]:              https://docs.python.org/3/library/stdtypes.html#dict.items
[py-file-read]:               https://docs.python.org/3/library/io.html#io.BufferedIOBase.read
[py-file-readlines]:          https://docs.python.org/3/library/io.html#io.IOBase.readlines
[py-functools-cmp_to_key]:    https://docs.python.org/3/library/functools.html#functools.cmp_to_key
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-itertools-pairwise]:      https://docs.python.org/3/library/itertools.html#itertools.pairwise
[py-itertools-product]:       https://docs.python.org/3/library/itertools.html#itertools.product
[py-itertools-starmap]:       https://docs.python.org/3/library/itertools.html#itertools.starmap
[py-itertools-combinations]:  https://docs.python.org/3/library/itertools.html#itertools.combinations
[py-json-loads]:              https://docs.python.org/3/library/json.html#json.loads
[py-list]:                    https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-append]:             https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-index]:              https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-insert]:             https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-pop]:                https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:               https://docs.python.org/3/library/stdtypes.html#list.sort
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
[py-math-inf]:                hthttps://en.wikipedia.org/wiki/NP-completenessps://docs.python.org/3/library/re.html#re.Pattern.findall
[py-math-lcm]:                https://docs.python.org/3/library/math.html#math.lcm
[py-math-prod]:               https://docs.python.org/3/library/math.html#math.prod
[py-object-init]:             https://docs.python.org/3/reference/datamodel.html#object.__init__
[py-object-eq]:               https://docs.python.org/3/reference/datamodel.html#object.__eq__
[py-operator]:                https://docs.python.org/3/library/operator.html#
[py-operator-attrgetter]:     https://docs.python.org/3/library/operator.html#operator.attrgetter
[py-operator-floordiv]:       https://docs.python.org/3/library/operator.html#operator.floordiv
[py-operator-itemgetter]:     https://docs.python.org/3/library/operator.html#operator.itemgetter
[py-re]:                      https://docs.python.org/3/library/re.html
[py-re-pattern-findall]:      https://docs.python.org/3/library/re.html#re.Pattern.findall
[py-set-update]:              https://docs.python.org/3/library/stdtypes.html#frozenset.update
[py-str-isdigit]:             https://docs.python.org/3/library/stdtypes.html#str.isdigic
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-lstrip]:              https://docs.python.org/3/library/stdtypes.html#str.lstrip
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-replace]:             https://docs.python.org/3/library/stdtypes.html#str.replace
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-strip]:               https://docs.python.org/3/library/stdtypes.html#str.strip
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[algo-a-star]:         https://en.wikipedia.org/wiki/A*_search_algorithm
[algo-bfs]:            https://en.wikipedia.org/wiki/Breadth-first_search
[algo-dfs]:            https://en.wikipedia.org/wiki/Depth-first_search
[algo-floyd-warshall]: https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
[algo-quickselect]:    https://en.wikipedia.org/wiki/Quickselect

[wiki-ascii]:                 https://en.wikipedia.org/wiki/ASCII
[wiki-backtracking]:          https://en.wikipedia.org/wiki/Backtracking
[wiki-bounding-box]:          https://en.wikipedia.org/wiki/Minimum_bounding_box
[wiki-commutative]:           https://en.wikipedia.org/wiki/Commutative_property
[wiki-congruence]:            https://en.wikipedia.org/wiki/Congruence_relation
[wiki-crt]:                   https://en.wikipedia.org/wiki/Cathode-ray_tube
[wiki-dp]:                    https://en.wikipedia.org/wiki/Dynamic_programming
[wiki-euclidean-distance]:    https://en.wikipedia.org/wiki/Euclidean_distance
[wiki-euclidean-translation]: https://en.wikipedia.org/wiki/Euclidean_plane_isometry#Translations
[wiki-graph]:                 https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)
[wiki-json]:                  https://en.wikipedia.org/wiki/JSON
[wiki-lcm]:                   https://en.wikipedia.org/wiki/Least_common_multiple
[wiki-linear-equation]:       https://en.wikipedia.org/wiki/Linear_equation
[wiki-linear-time]:           https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-manhattan]:             https://en.wikipedia.org/wiki/Taxicab_geometry
[wiki-memoization]:           https://en.wikipedia.org/wiki/Memoization
[wiki-relief-valve]:          https://en.wikipedia.org/wiki/Relief_valve
[wiki-search-problem]:        https://en.wikipedia.org/wiki/Search_problem
[wiki-snafu]:                 https://en.wikipedia.org/wiki/SNAFU
[wiki-topographic-map]:       https://en.wikipedia.org/wiki/Topographic_map
[wiki-tree]:                  https://en.wikipedia.org/wiki/Tree_(data_structure)
[wiki-triangular-number]:     https://en.wikipedia.org/wiki/Triangular_number
[wiki-expression-tree]:       https://en.wikipedia.org/wiki/Binary_expression_tree


[misc-aoc-bingo]:     https://www.reddit.com/r/adventofcode/comments/k3q7tr/
[misc-numpy]:         https://numpy.org
[misc-numpy-views]:   https://numpy.org/doc/stable/user/basics.copies.html
[misc-py-sign]:       https://stackoverflow.com/a/1986776/3889449
[misc-py2-cmp]:       https://docs.python.org/2/library/functions.html#cmp
[misc-regexp]:        https://www.regular-expressions.info/
[misc-so-cmp_to_key]: https://stackoverflow.com/q/32752739/3889449
[misc-so-deque]:      https://stackoverflow.com/a/6257048/3889449
