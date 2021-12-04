Advent of Code 2021 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - Sonar Sweep][d01]
- [Day 2 - Dive!][d02]
- [Day 3 - Binary Diagnostic][d03]

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
nums = set(nums)

# From MSB (shift = n_bits - 1) to LSB (shift = 0)
for shift in range(n_bits - 1, -1, -1):
    # Get the most common bit at this shift
    bit  = most_common_bit(nums, shift)
    keep = set()

    # Only keep numbers that have this bit set at this shift
    for n in nums:
        if (n >> shift) & 1 == bit:
            keep.add(n)

    nums = keep
    if len(nums) == 1:
        break

# Now we should only have one number left
only_one_left = nums.pop()
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
        nums = set(filter(lambda n: (n >> shift) & 1 == bit, nums))

        if len(nums) == 1:
            break

    return nums.pop()
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
        nums = set(filter(lambda n: (n >> shift) & 1 == bit, nums))

        if len(nums) == 1:
            break

    return nums.pop()
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

---

*Copyright &copy; 2021 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)

[top]: #advent-of-code-2021-walkthrough
[d01]: #day-1---sonar-sweep
[d02]: #day-2---dive
[d03]: #day-3---binary-diagnostic

[d01-problem]: https://adventofcode.com/2021/day/1
[d02-problem]: https://adventofcode.com/2021/day/2
[d03-problem]: https://adventofcode.com/2021/day/3

[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py

[d03-orginal]: original_solutions/day03.py


[py-lambda]:                  https://docs.python.org/3/tutorial/controlflow.html#lambda-expressions
[py-generator-expr]:          https://www.python.org/dev/peps/pep-0289/

[py-builtin-int]:             https://docs.python.org/3/library/functions.html#int
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-partial]:       https://docs.python.org/3/library/functools.html#functools.partial
[py-str-split]:               https://docs.python.org/3/library/stdtypes.html#str.split
