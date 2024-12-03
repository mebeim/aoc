Advent of Code 2024 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Historian Hysteria][d01]
- [Day 2 - Red-Nosed Reports][d02]
- [Day 3 - Mull It Over][d03]
<!--
- [Day 4 - xxx][d04]
- [Day 5 - xxx][d05]
- [Day 6 - xxx][d06]
- [Day 7 - xxx][d07]
- [Day 8 - xxx][d08]
- [Day 9 - xxx][d09]
- [Day 10 - xxx][d10]
- [Day 11 - xxx][d11]
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

---

*Copyright &copy; 2024 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)


[top]: #advent-of-code-2024-walkthrough
[d01]: #day-1---historian-hysteria
[d02]: #day-2---red-nosed-reports
[d03]: #day-3---mull-it-over
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

[py-builtin-all]: https://docs.python.org/3/library/functions.html#all
[py-builtin-map]: https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]: https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]: https://docs.python.org/3/library/functions.html#zip
[py-list-count]:  https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-list-sort]:   https://docs.python.org/3/tutorial/datastructures.html#more-on-lists
[py-re-findall]:  https://docs.python.org/3/library/re.html#re.findall
