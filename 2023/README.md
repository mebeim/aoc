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
<!--
- [Day 3 - ][d03]
- [Day 4 - ][d04]
- [Day 5 - ][d05]
- [Day 6 - ][d06]
- [Day 7 - ][d07]
- [Day 8 - ][d08]
- [Day 9 - ][d09]
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
To only extrac the first such character from the iterator returned by `filter()`
we can simply use [`next()`][py-builtin-next].

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

First two starts of the year done. Welcome to Advent of Code 2024!


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

---

*Copyright &copy; 2023 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2023-walkthrough
[d01]: #day-1---trebuchet
[d02]: #day-2---cube-conundrum
[d03]: #day-3---
[d04]: #day-4---
[d05]: #day-5---
[d06]: #day-6---
[d07]: #day-7---
[d08]: #day-8---
[d09]: #day-9---
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

[py-slicing]: https://docs.python.org/3/library/stdtypes.html#common-sequence-operations

[py-builtin-filter]: https://docs.python.org/3/library/functions.html#filter
[py-builtin-map]:    https://docs.python.org/3/library/functions.html#map
[py-builtin-max]:    https://docs.python.org/3/library/functions.html#max
[py-builtin-next]:   https://docs.python.org/3/library/functions.html#next
[py-builtin-range]:  https://docs.python.org/3/library/functions.html#range
[py-str-isdigit]:    https://docs.python.org/3/library/stdtypes.html#str.isdigic
[py-str-split]:      https://docs.python.org/3/library/stdtypes.html#str.split