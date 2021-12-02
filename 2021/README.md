Advent of Code 2021 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Sonar Sweep][d01]
- [Day 2 - Dive!][d02]

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
by creating two new variables for the aim and the new depth. Other than that,
it's just additions and multiplications.

```python
aim = horiz = depth1 = depth2 = 0

for line in fin:
    cmd, x = line.split()
    x = int(x)

    if cmd == 'down':
        depth1 += x
        aim    += x
    elif cmd == 'up':
        depth1 -= x
        aim    -= x
    else:
        horiz  += x
        depth2 += aim * x

answer1 = horiz * depth1
answer2 = horiz * depth2

print('Part 1:', answer1)
print('Part 2:', answer1)
```

Ta-dah! As simple as that, we now have two more gold stars.

---

*Copyright &copy; 2021 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2021-walkthrough
[d01]: #day-1---sonar-sweep
[d02]: #day-2---dive

[d01-problem]: https://adventofcode.com/2021/day/1
[d02-problem]: https://adventofcode.com/2021/day/2

[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py

[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
