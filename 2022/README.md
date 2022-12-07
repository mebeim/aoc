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
`bytes.translat()` instead.

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
crates stacked on top of each other. We start with a few stacks of crates, which
is given as input in the following form:

```none
    [D]
[N] [C]
[Z] [M] [P]
 1   2   3
```

This represents the initial configuration of N stacks of crates (in the above
example we have N = 3, but in the real input N = 10). Following the initial
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

Fortunately, all we need to do to identify good columns is
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

We optimize the above operation by extracting all `n` crates at once and then
reversing their order doing `crate[::-1]`, a common Python trick to reverse an
indexable iterable through [slicing][py-slicing]:

```python
for n, i, j in moves:
    chunk = stacks[i][:n][::-1]
    stacks[i] = stacks[i][n:]
    stacks[j] = chunk + stacks[j]
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

Well, given the code we already wrote, this is really child's play: we can use
the same code as part 1, removing the reversing operation (`[::-1]`):

```python
# Restore initial state from the copy we made earlier
stacks = original

for n, i, j in moves:
    chunk = stacks[i][:n] # <- removed [::-1] from here
    stacks[i] = stacks[i][n:]
    stacks[j] = chunk + stacks[j]

top = ''.join(s[0] for s in stacks[1:])
print('Part 2:', top)
```


Day 6 - Tuning Trouble
----------------------

[Problem statement][d06-problem] — [Complete solution][d06-solution] — [Back to top][top]

### Part 1

Today's problem feels like it could have been an day 1 problem. In fact, I
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
start-of-packet, let alone 14), so let's also give our functionm the ability to
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
already present in `fs`. A [`deque`][py-collections-deque] is also useful to
process the input line by line while being able to peek at the next line without
consuming it, since we want to stop parsing the output of the `ls` command
whenever we encounter a line starting with `$`. We can peek the first element of
a `deque` with `d[0]`, and consume it by popping it `d.popleft()`. The same
could be done with a normal list through `l.pop(0)`, but the operation is much
more expensive as it internally requires to move all elements of the list back
one position after removing the first one.

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
            # until we either run out of lines or the next line is not a command
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

fs = {
    ()        : [('/',)]
    ('/',)    : [1000, 699, ('/', 'a')]
    ('/', 'a'): [100, 200]
}
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
            size += directory_size(subdir_or_size)

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
[`functools.lru_cache`][py-functools-lru_cache].

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
by `lru_cache` to be reused for subsequent calls.

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

[d01-problem]: https://adventofcode.com/2022/day/1
[d02-problem]: https://adventofcode.com/2022/day/2
[d03-problem]: https://adventofcode.com/2022/day/3
[d04-problem]: https://adventofcode.com/2022/day/4
[d05-problem]: https://adventofcode.com/2022/day/5
[d06-problem]: https://adventofcode.com/2022/day/6
[d07-problem]: https://adventofcode.com/2022/day/7

[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py
[d04-solution]: solutions/day04.py
[d05-solution]: solutions/day05.py
[d06-solution]: solutions/day06.py
[d07-solution]: solutions/day07.py

[d02-alternative]: misc/day02/mathematical.py

[py-cond-expr]:          https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-generator-expr]:     https://www.python.org/dev/peps/pep-0289/
[py-lambda]:             https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-list-comprehension]: https://docs.python.org/3/tutorial/datastructures.html#list-comprehensions
[py-slicing]:            https://docs.python.org/3/glossary.html#term-slice
[py-tuple]:              https://docs.python.org/3/tutorial/datastructures.html#tuples-and-sequences
[py-unpacking]:          https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists
[py-with]:               https://peps.python.org/pep-0343/

[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-isinstance]:      https://docs.python.org/3/library/functions.html#isinstance
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:             https://docs.python.org/3/library/functions.html#max
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-ord]:             https://docs.python.org/3/library/functions.html#ord
[py-builtin-type]:            https://docs.python.org/3/library/functions.html#type
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-list]:                    https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:               https://docs.python.org/3/library/stdtypes.html#list.sort
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-lstrip]:              https://docs.python.org/3/library/stdtypes.html#str.lstrip
[py-str-maketrans]:           https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-rstrip]:              https://docs.python.org/3/library/stdtypes.html#str.rstrip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
[py-str-translate]:           https://docs.python.org/3/library/stdtypes.html#str.translate

[algo-dfs]:         https://en.wikipedia.org/wiki/Depth-first_search
[algo-quickselect]: https://en.wikipedia.org/wiki/Quickselect

[wiki-ascii]:       https://en.wikipedia.org/wiki/ASCII
[wiki-linear-time]: https://en.wikipedia.org/wiki/Time_complexity#Linear_time
[wiki-memoization]: https://en.wikipedia.org/wiki/Memoization
[wiki-tree]:        https://en.wikipedia.org/wiki/Tree_(data_structure)
