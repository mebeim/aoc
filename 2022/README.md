Advent of Code 2022 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Calorie Counting][d01]
- [Day 2 - Rock Paper Scissors][d02]
- *Day 3 - Rucksack Reorganization (TODO)*
- [Day 4 - Camp Cleanup][d04]


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

---

*Copyright &copy; 2022 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2022-walkthrough
[d01]: #day-1---calorie-counting
[d02]: #day-2---rock-paper-scissors
[d04]: #day-4---camp-cleanup

[d01-problem]: https://adventofcode.com/2022/day/1
[d02-problem]: https://adventofcode.com/2022/day/2
[d04-problem]: https://adventofcode.com/2022/day/4

[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d04-solution]: solutions/day04.py

[d02-alternative]: misc/day02/mathematical.py

[py-list-comprehension]: https://docs.python.org/3/tutorial/datastructures.html#list-comprehensions
[py-list]:               https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:          https://docs.python.org/3/library/stdtypes.html#list.sort
[py-str-maketrans]:      https://docs.python.org/3/library/stdtypes.html#str.maketrans
[py-str-translate]:      https://docs.python.org/3/library/stdtypes.html#str.translate
[py-tuple]:              https://docs.python.org/3/tutorial/datastructures.html#tuples-and-sequences
[py-with]:               https://peps.python.org/pep-0343/

[py-builtin-map]: https://docs.python.org/3/library/functions.html#map
[py-builtin-max]: https://docs.python.org/3/library/functions.html#max
[py-builtin-min]: https://docs.python.org/3/library/functions.html#min
[py-str-split]:   https://docs.python.org/3/library/stdtypes.html#str.split

[algo-quickselect]: https://en.wikipedia.org/wiki/Quickselect

[wiki-linear-time]: https://en.wikipedia.org/wiki/Time_complexity#Linear_time
