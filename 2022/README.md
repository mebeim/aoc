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
emove the square root by elevating everything to the power of two, we are left
with the condition *dx<sup>2</sup>+dy<sup>2</sup> > 2*.

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
emulate the CRT monitor we'll use a list of strings, where each string is a row
of pixels, and we'll keep track of the current row in a separate string
variable. We'll use `'#'` to represent lit pixels, and `' '` (a space) for dark
pixels. Any time a new row needs to be added, well [`.append()`][py-list-append]
the current one to the list and reset it to an empty string.

Here's the code to add to the main loop we already wrote:

```diff
+crt = []
+row = ''

 for instr in program:
+    if x <= cycle % 40 <= x + 2:
+        row += '#'
+    else:
+        row += ' '
+
     cycle += 1

     if instr.startswith('addx'):
         if cycle % 40 == 20:
             total += cycle * x
+        elif cycle % 40 == 1:
+            crt.append(row)
+            row = ''
+
+        if x <= cycle % 40 <= x + 2:
+            row += '#'
+        else:
+            row += ' '

         cycle += 1
         x += int(instr[5:])

     if cycle % 40 == 20:
         total += cycle * x
+    elif cycle % 40 == 1:
+        crt.append(row)
+        row = ''
```

The [3-way comparison][py-3-way-comparison] `x <= y <= z` is equivalent to
`x <= y and y <= z`, but only evaluates `y` once, and only evaluates `z` if
`x <= y` is not satisfied. This is a nice little feature that makes bound
checking in Python much cooler than in other languages.

The addition of new pixels to the `row` variable (representing the current row as a
string) can also be done using a [tristate operator][py-cond-expr]:

```python
row += '#' if x <= cycle % 40 <= x + 2 else ' '
```

Now all that's left to do is print the rows in the `crt` list we populated and
read out the answer. We can do this with a good ol' `for` loop, or we could
[`.join()`][py-str-join] them together with a newline as a separator and print
them all at once.

```python
print('Part 2:\n', '\n'.join(crt), sep='')
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
class constructor (i.e. its [`__init__()`][py-class-init] method), but there are
a lot of them and I did not want to write a function taking so many parameters.

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
  the divisibility by both, we only need to keep `item % (d * q)` around, since
  a number divisible by `d` will also always be divisible by `d * q`, and vice
  versa.
- In the general case of N monkeys with N different divisors, we only need to
  keep item values *modulo the product of all the divisors*. This product is
  small enough and is also pre-computable and fixed through the entire
  simulation (since divisors are fixed). To be precise, we actually only need
  the [least common multiple][wiki-lcm] of the divisors.

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

[d01-problem]: https://adventofcode.defaultdictcom/2022/day/1
[d02-problem]: https://adventofcode.com/2022/day/2
[d03-problem]: https://adventofcode.com/2022/day/3
[d04-problem]: https://adventofcode.com/2022/day/4
[d05-problem]: https://adventofcode.com/2022/day/5
[d06-problem]: https://adventofcode.com/2022/day/6
[d07-problem]: https://adventofcode.com/2022/day/7
[d08-problem]: https://adventofcode.com/2022/day/8
[d09-problem]: https://adventofcode.com/2022/day/9
[d10-problem]: https://adventofcode.com/2022/day/10
[d11-problem]: https://adventofcode.com/2022/day/11

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

[2019-d18-p1]:     ../2019/README.md#part-1-17
[d02-alternative]: misc/day02/mathematical.py
[d08-alternative]: misc/day08/faster_part1.py

[py-3-way-comparison]:   https://docs.python.org/3/reference/expressions.html#comparisons
[py-class-init]:         https://docs.python.org/3/reference/datamodel.html#object.__init__
[py-class-slots]:        https://docs.python.org/3/reference/datamodel.html#slots
[py-cond-expr]:          https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-generator-expr]:     https://www.python.org/dev/peps/pep-0289/
[py-lambda]:             https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-list-comprehension]: https://docs.python.org/3/tutorial/datastructures.html#list-comprehensions
[py-set]:                https://docs.python.org/3/tutorial/datastructures.html#sets
[py-slicing]:            https://docs.python.org/3/glossary.html#term-slice
[py-tuple]:              https://docs.python.org/3/tutorial/datastructures.html#tuples-and-sequences
[py-unpacking]:          https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists
[py-with]:               https://peps.python.org/pep-0343/

[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-isinstance]:      https://docs.python.org/3/library/functions.html#isinstance
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-ord]:             https://docs.python.org/3/library/functions.html#ord
[py-builtin-range]:           https://docs.python.org/3/library/functions.html#range
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-type]:            https://docs.python.org/3/library/functions.html#type
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-bytes-splitlines]:        https://docs.python.org/3/library/stdtypes.html#bytes.splitlines
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-copy-deepcopy]:           https://docs.python.org/3/library/copy.html#copy.deepcopy
[py-file-read]:               https://docs.python.org/3/library/io.html#io.BufferedIOBase.read
[py-file-readlines]:          https://docs.python.org/3/library/io.html#io.IOBase.readlines
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-list]:                    https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-append]:             https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:               https://docs.python.org/3/library/stdtypes.html#list.sort
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
[py-math-lcm]:                https://docs.python.org/3/library/math.html#math.lcm
[py-operator]:                https://docs.python.org/3/library/operator.html
[py-operator-attrgetter]:     https://docs.python.org/3/library/operator.html#operator.attrgetter
[py-re-pattern-findall]:      https://docs.python.org/3/library/re.html#re.Pattern.findall
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-lstrip]:              https://docs.python.org/3/library/stdtypes.html#str.lstrip
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[algo-dfs]:         https://en.wikipedia.org/wiki/Depth-first_search
[algo-quickselect]: https://en.wikipedia.org/wiki/Quickselect

[wiki-ascii]:              https://en.wikipedia.org/wiki/ASCII
[wiki-congruence]:         https://en.wikipedia.org/wiki/Congruence_relation
[wiki-crt]:                https://en.wikipedia.org/wiki/Cathode-ray_tube
[wiki-euclidean-distance]: https://en.wikipedia.org/wiki/Euclidean_distance
[wiki-lcm]:                https://en.wikipedia.org/wiki/Least_common_multiple
[wiki-linear-time]:        https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-memoization]:        https://en.wikipedia.org/wiki/Memoization
[wiki-tree]:               https://en.wikipedia.org/wiki/Tree_(data_structure)

[misc-numpy]:       https://numpy.org
[misc-numpy-views]: https://numpy.org/doc/stable/user/basics.copies.html
[misc-py-sign]:     https://stackoverflow.com/a/1986776/3889449
[misc-regexp]:      https://www.regular-expressions.info/
