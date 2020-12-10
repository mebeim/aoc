Advent of Code 2019 walkthrough
===============================

Table of Contents
-----------------

- [Day 1 - The Tyranny of the Rocket Equation][d01]
- [Day 2 - 1202 Program Alarm][d02]
- [Day 3 - Crossed Wires][d03]
- [Day 4 - Secure Container][d04]
- [Day 5 - Sunny with a Chance of Asteroids][d05]
- [Day 6 - Universal Orbit Map][d06]
- [Day 7 - Amplification Circuit][d07]
- [Day 8 - Space Image Format][d08]
- [Day 9 - Sensor Boost][d09]
- [Day 10 - Monitoring Station][d10]
- [Day 11 - Space Police][d11]
- [Day 12 - The N-Body Problem][d12]
- [Day 13 - Care Package][d13]
- [Day 14 - Space Stoichiometry][d14]
- [Day 15 - Oxygen System][d15]
- [Day 16 - Flawed Frequency Transmission][d16]
- [Day 17 - Set and Forget][d17]
- [Day 18 - Many-Worlds Interpretation][d18]
- [Day 19 - Tractor Beam][d19]
- [Day 20 - Donut Maze][d20]
- [Day 21 - Springdroid Adventure][d21]
- [Day 22 - Slam Shuffle][d22]
- [Day 23 - Category Six][d23]
- [Day 24 - Planet of Discord][d24]
-  Day 25 - Cryostasis: *TODO*

Day 1 - The Tyranny of the Rocket Equation
------------------------------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution] — [Back to top][top]

### Part 1

We are given a list of integers as input:

```python
numbers = tuple(map(int, fin.readlines()))
```

We are asked to first apply a function to all of them, and them sum all the
results. The function is `x / 3 - 2`, where the division is an *integer*
division.

We can simply use the built-in [`map()`][py-builtin-map] and
[`sum()`][py-builtin-sum] functions to solve this in one line:

```python
total = sum(map(lambda n: n // 3 - 2, numbers))
print('Part 1:', total)
```

### Part 2

For the second part, we are asked to repeatedly apply the same function to each
number until it gets to zero (or under zero, in which case we should just treat
is as a zero). Then again, sum every single value we get after applying the
function.

```python
total = 0
for n in numbers:
    while n > 0:
        n = max(n // 3 - 2, 0)
        total += n

print('Part 2:', total)
```

First puzzle of the year, so not really that much of a challenge, but still fun!


Day 2 - 1202 Program Alarm
--------------------------

[Problem statement][d02-problem] — [Complete solution][d02-solution] — [Back to top][top]

### Part 1

Okay, I was not expecting a custom virtual machine for day 2, but here we go I
guess!

We are introduced to "Intcode", machine-code language that only uses integers.
The program source code is a list of integers separated by commas:

```python
program = list(map(int, fin.read().split(',')))
```

We are given instructions on how to interpret the numbers. In particular, there
are three [opcodes](https://en.wikipedia.org/wiki/Opcode):

- The value `1` means *add* together the values at the positions indicated by
  the next two numbers, and store the result at the position indicated by the
  third, then move forward 4 positions to get to the next instruction.
- The value `2` means *multiply*, and it works the same as *add*, except the
  operation is a multiplication.
- The value `99` means *stop*.

We are asked to set `program[0] = 1` and `program[1] = 12` before starting, and
then run the Intcode program until it halts: the output will be at position `0`.

Quite simple, we can just emulate it with a loop. To make it fancier, we can
import [`add`][py-operator-add] and [`mul`][py-operator-mul] from the
[`operator`][py-operator] module and use them instead of a chain of `if/elif`:
`add()` is a function that takes two arguments and performs the same operation
of the `+` operator, while `mul()` does the same for the `*` operator. Using
these might also come in handy if in the future more operations are added (we
could just have a dictionary of `{opcode: operator}`).

```python
from operator import add, mul

def run(program, v0, v1):
    program[0] = v0
    program[1] = v1
    pc = 0

    while program[pc] != 99:
        opcode = program[pc]
        op = add if op == 1 else mul
        program[pc + 1] = op(program[pc + 2], program[pc + 3])
        pc += 4

    return program[0]

output = run(program[:], 1, 12)
print('Part 1:', output)
```

I use `program[:]` here to create a copy of the list, instead of passing the
list itself, which would modify it irrevocably.

### Part 2

For the second part, we are asked to determine which pair of inputs produces the
output `19690720`. Both the input values are between `0` and `99` (included), so
we can just run a brute-force search trying all of them. To avoid writing two
loops using a temporary boolean value to `break` out of both, we can use the
[`product()`][py-itertools-product] generator from the
[`itertools`][py-itertools] module, which generates all possible tuples of
values from the
[cartesian product](https://en.wikipedia.org/wiki/Cartesian_product) of its
arguments.

```python
from itertools import product

for a, b in product(range(100), range(100)):
    if run(program[:], a, b) == 19690720:
        break

print('Part 2:', a * 100 + b)
```


Day 3 - Crossed Wires
---------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution] — [Back to top][top]

### Part 1

We are given two lines, each one is a list of moves in a 2D grid. There are two
wires, and each line represents a wire. Starting from the same position, the
moves describe the path that each wire takes on the grid.

A move is represented as a letter which tells us the direction of the move (`L`,
`R`, `U`, `D`) followed by a number which tells us how many steps to move in
such direction.

The two wires will intersect each other, and we are asked to calculate the
[Manhattan distance][algo-manhattan] from the origin to the closest
intersection.

First, parse the moves with [`map()`][py-builtin-map] and a simple function that
takes a string and splits it into direction and number of steps.

```python
def make_move(s):
    return s[0], int(s[1:])

lines = fin.readlines()
moves1 = tuple(map(make_move, line[0].split(',')))
moves2 = tuple(map(make_move, line[1].split(',')))
```

Now, since we need to calculate the intersections of the two paths, a `set`
comes in handy. For each wire, we start from the same arbitrary position, like
`(0, 0)` and then move one step at a time, each time updating the position
adding it to the set of visited positions.

```python
MOVE_DX = {'U': 0, 'D':  0, 'R': 1, 'L': -1}
MOVE_DY = {'U': 1, 'D': -1, 'R': 0, 'L':  0}

def get_visited(moves):
    visited = set()
    p = (0, 0)

    for d, n in moves:
        for _ in range(n):
            p = (p[0] + MOVE_DX[d], p[1] + MOVE_DY[d])
            visited.add(p)

    return visited

visited1 = get_visited(moves1)
visited2 = get_visited(moves2)
```

The two dictionaries `MOVE_DX` and `MOVE_DY` are just a common trick to make it
easier to apply a delta given a direction, instead of writing a long chain of
`if/elif` statements with a bunch of different assignments.

We then get the intersection of the two sets, and calculate the Manhattan
distance from each point to the origin, keeping the lowest value. Since the
origin is `(0, 0)`, the Manhattan distance from a point to the origin is simply
the sum of the absolute values of the two coordinates of the point.

```python
def manhattan(p):
    return abs(p[0]) + abs(p[1])

intersections = visited1 & visited2
min_distance = min(map(manhattan, intersections))
print('Part 1:', min_distance)
```

### Part 2

We are now asked to calculate the shortest cumulative distance (in steps) that
wires must travel to reach an intersection point. If a wire visits the same
position multiple times, we need to use the lowest number of steps it took to
get there.

Counting the steps is easy. For the second requirement we can just use a
dictionary `{position: n_steps}` to remember the lowest number of steps to get
to each position. We can easily modify the previously written function to also
count steps.

```python
def get_visited_and_steps(moves):
    p = (0, 0)
    cur_steps = 0
    visited = set()
    steps = {}

    for d, n in moves:
        for _ in range(n):
            p = (p[0] + MOVE_DX[d], p[1] + MOVE_DY[d])
            visited.add(p)
            cur_steps += 1

            if p not in steps:
                steps[p] = cur_steps

    return visited, steps

visited1, steps1 = get_visited_and_steps(moves1)
visited2, steps2 = get_visited_and_steps(moves2)
intersections = visited1 & visited2
best = min(steps1[p] + steps2[p] for p in intersections)

print('Part 2:', best)
```


Day 4 - Secure Container
------------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution] — [Back to top][top]

### Part 1

Bruteforcing passwords! We are given the lower and upper bounds for the value of
a six-digit password, and we need to determine how many valid passwords are in
such range.

A valid password must:

- Have at least two adjacent matching digits.
- Be composed of non-decreasing digits (from left to right).

An iterator over pairs of adjacent characters of a string can be easily obtained
using the [`zip()`][py-builtin-zip] built-in function. If we convert our values
in string form, this will make our life much easier. Since we are only dealing
with ASCII digits, and the ASCII values for digits are ordered just like the
digits, we don't even need to care about converting them back to integers to
compare them.

```python
digits = str(value)
pairs = tuple(zip(digits, digits[1:]))
```

To check if there are at least two adjacent matching digits, we can iterate over
the pairs of adjacent digits and check if any pair of equal digits exists using
the [`any()`][py-builtin-any] built-in function.

```python
has_matching_pair = any(a == b for a, b in pairs)
```

As per the second requirement, to check if a number is only composed of
non-decreasing digits, we can iterate over the pairs of adjacent digits and use
the [`all()`][py-builtin-all] built-in function to check if the condition is met
for each pair.

```python
is_non_decreasing = all(a <= b for a, b in pairs)
```

Now that we have the primitives to check if a value is a valid password, we can
simply bruteforce all the possible values in the given range and count how many
of them pass the checks:

```python
lo, hi = map(int, fin.read().split('-'))
n_valid = 0

for pwd in range(lo, hi + 1):
    digits = str(pwd)
    pairs = tuple(zip(digits, digits[1:]))

    is_non_decreasing = all(a <= b for a, b in pairs)
    has_matching_pair = any(a == b for a, b in pairs)

    if is_non_decreasing and has_matching_pair:
        n_valid += 1

print('Part 1:', n_valid)
```

### Part 2

For the second part, another constraint is added for the validity of a password:

- The two adjacent matching digits are not part of a larger group of matching
  digits.

This can be tricky to understand. To make it clearer, we can also say it like
this:

- There is at least one group of exactly two *isolated* adjacent matching
  digits.

To check if a group of two equal digits is isolated, we now need an iterator
over a *quadruplet* of consecutive digits. We can use [`zip()`][py-builtin-zip]
as before:

```python
quadruplets = zip(digits, digits[1:], digits[2:], digits[3:])
```

Then, using the same [`any()`][py-builtin-any] function as before, we also need
to account for isolated digits at the beginning and at the end of the string. We
can just cheat and add two random characters to the extremes of the string.

```python
digits = 'x' + digits + 'x'
has_isolated = any(a != b and b == c and c != d for a, b, c, d in quadruplets)
```

We can now count the number of valid passwords again:

```python
n_valid = 0

for pwd in range(lo, hi + 1):
    digits = str(pwd)
    pairs = zip(digits, digits[1:])

    is_non_decreasing = all(a <= b for a, b in pairs)

    if is_non_decreasing:
        digits = 'x' + digits + 'x'
        quadruplets = zip(digits, digits[1:], digits[2:], digits[3:])
        has_isolated = any(a != b and b == c and c != d for a, b, c, d in quadruplets)

        if has_isolated:
            n_valid += 1

print('Part 2:', n_valid)
```

Adding one nesting level makes things go a little bit faster since we only check
the quadruplets if the first check passes. Also, notice that wrapping
`zip(digits, digits[1:])` into `tuple()` is not needed anymore now, since we
only use the iterator once (and most importantly, we add the two `'x'` only
*after* using it.

Both parts could also be condensed in a single loop making it even cleaner,
which is what I did in the complete solution linked above.


Day 5 - Sunny with a Chance of Asteroids
----------------------------------------

[Problem statement][d05-problem] — [Complete solution][d05-solution] — [Back to top][top]

### Part 1

Second Intcode puzzle of the year. In addition to what we know from day 2, now
two more opcodes are added:

- Opcode `3`: take an integer as *input* and store it in the position indicated
  by the (only) given parameter (length: 2).
- Opcode `4`: *output* the value of the (only) given parameter (length: 2).

In addition to this, now opcode parameters become more complex to handle. In
particular, each opcode is either 1 or 2 digits. Every other more significant
digit is a *parameter mode* for the corresponding parameter.

Parameter modes are:

- `0`: position mode, the parameter refers to a memory address (that is, a
  position). The value to use is the number stored at that address. For
  destination parameters, it is still the location where to write.
- `1`: immediate mode, the parameter itself is interpreted as the value to use.
  This mode is not allowed for destination parameters.

Leading zero digits are left off. So, for example, `1002,2,3,4` now means:
`program[4] = program[2] + 3`, since parameter modes are (from left to right)
`0`, `1` and `0` (implicit leading zero).

The program we are given will only request one input, and we should provide it
with `1` as the only input value. It then outputs a series of numbers, and we
need to get the last one.

This parameter mode thing complicates our solution a fair amount, but it's still
doable. We now need to fetch the modes first, then evaluate them to compute the
needed values. Let's drop the use of the [`operator`][py-operator] module from
day 2, as it didn't turn out to be useful.

To parse opcode and parameter modes, we can just use integer division and
modulo:

```python
modes  = ((op // 100) % 10, (op // 1000) % 10, (op // 10000) % 10)
```

Other than this, we now need to look into memory only if the mode is `0`,
otherwise we can use the parameter value as is. We can just use an `if` for
this.

```python
param1 = prog[pc + 1]
if modes[0] == 0:
    param1 = prog[param1]
```

Our previously written `run()` function now becomes:

```python
def run(prog, input_value):
    pc = 0
    lastout = None

    while prog[pc] != 99:
        op = prog[pc]
        modes = ((op // 100) % 10, (op // 1000) % 10, (op // 10000) % 10)
        op = op % 10

        if op == 1: # add
            a, b, c = prog[pc + 1:pc + 4]
            if modes[0] == 0: a = prog[a]
            if modes[1] == 0: b = prog[b]
            prog[c] = a + b
            pc += 4
        elif op == 2: # mul
            a, b, c = prog[pc + 1:pc + 4]
            if modes[0] == 0: a = prog[a]
            if modes[1] == 0: b = prog[b]
            prog[c] = a * b
            pc += 4
        elif op == 3: # in
            a = prog[pc + 1]
            prog[a] = input_value
            pc += 2
        elif op == 4: # out
            a = prog[pc + 1]
            if modes[0] == 0: a = prog[a]
            lastout = a
            pc += 2

    return lastout
```

Cool, now let's just run it against our input and it's done:

```python
program = list(map(int, fin.read().split(',')))
result = run(program[:], 1)
print('Part 1:', result)
```

### Part 2

Ok, now things starts to get messy... four more opcodes are added:

- Opcode `5` is *jump if true*: if the first parameter is non-zero, it sets the
  instruction pointer to the value from the second parameter. Otherwise, it does
  nothing.
- Opcode `6` is *jump if false*: if the first parameter is zero, it sets the
  instruction pointer to the value from the second parameter. Otherwise, it does
  nothing.
- Opcode `7` is *less than*: if the first parameter is less than the second
  parameter, it stores `1` in the position given by the third parameter.
  Otherwise, it stores `0`.
- Opcode `8` is *equals*: if the first parameter is equal to the second
  parameter, it stores 1 in the position given by the third parameter.
  Otherwise, it stores `0`.

In addition to this, of course the new opcodes all need to support the parameter
modes described in part 1. The program now will need to be run with `5` as its
only input, and we still need to get the last output value.

The good thing is, the code we just wrote can be easily extended to support
these, we just need four more `elif` branches. To implement *less than* and
*equals*, and also for updating the program counter for the jump instructions,
Python [conditional expressions][py-cond-expr] come in handy:

```python
# less than:
prog[param3] = 1 if param1 < param2 else 0
```

Here are the added opcodes (continuing from the last branch in the previous
snippet):

```python
        # ...

        elif op == 5: # jnz
            a, b = prog[pc + 1:pc + 3]
            if modes[0] == 0: a = prog[a]
            if modes[1] == 0: b = prog[b]
            pc = b if a != 0 else pc + 3
        elif op == 6: # jz
            a, b = prog[pc + 1:pc + 3]
            if modes[0] == 0: a = prog[a]
            if modes[1] == 0: b = prog[b]
            pc = b if a == 0 else pc + 3
        elif op == 7: # lt
            a, b, c = prog[pc + 1:pc + 4]
            if modes[0] == 0: a = prog[a]
            if modes[1] == 0: b = prog[b]
            prog[c] = 1 if a < b else 0
            pc += 4
        elif op == 8: # eq
            a, b, c = prog[pc + 1:pc + 4]
            if modes[0] == 0: a = prog[a]
            if modes[1] == 0: b = prog[b]
            prog[c] = 1 if a == b else 0
            pc += 4

        # ...
```

Now we can just run the program with the updated code and the new input to get
the answer:

```python
result = run(program[:], 5)
print('Part 2:', result)
```


Day 6 - Universal Orbit Map
---------------------------

[Problem statement][d06-problem] — [Complete solution][d06-solution] — [Back to top][top]

### Part 1

We are given a list of "orbits". Each orbit is represented as the name of two
planets divided by a closed parenthesis `)` symbol. `A)B` means that planet `B`
orbits planet `A`. We are asked to count the total number of orbits, direct or
indirect.

A planet `X` indirectly orbits another planet `Y` if there is a chain of orbits
from `X` to `Y`. For example, if we have `A)B` and `B)C`, then `C` indirectly
orbits `A`. This chain can be arbitrarily long, and it's pretty obvious that
this ends up building a directed graph... or better, a tree, since a planet can
only directly orbit a single other planet (physics, heh).

We need an adequate data structure to keep track of who orbits who, let's call
the inside planet of an orbit the `parent` and the outside planet the `child`
for simplicity: we will build a dictionary `{child: parent}` to represent our
tree.

```python
lines = map(str.strip, fin.readlines())
orbits = tuple(line.split(')') for line in lines)

T = {child: parent for parent, child in orbits}
```

The simplest way to count all the orbits for a planet is now to just follow the
list of its parents until we get to the root, which will not appear as a key in
our tree dictionary (because it has no parent).

```python
def count_orbits(planet):
    total = 0
    while planet in T:
        total += 1
        planet = T[planet]

    return total
```

We don't pass `T` as a variable just for simplicity, since it's global anyway.
Seems pretty simple, the result is now just one [`map()`][py-builtin-map] and
[`sum()`][py-builtin-sum] away:

```python
total_orbits = sum(map(count_orbits, T))
print('Part 1:', total_orbits)
```

### Part 2

We now need to find the minimum number of "orbital transfers" needed to get the
planet `YOU` to orbit the same planet as `SAN`. We start at the planet that
`YOU` is orbiting, and we want to get to the planet that `SAN` is orbiting.

As an example, in the below situation we would need `4` transfers to get to
`SAN`:

               *YOU*
               /
          E - F - G                 E - F - G
         /                         /
    A - C - D          ==>    A - C - D
     \                         \
      B - SAN                   B - SAN
                                 \
                                 *YOU*

The path would be `F->E->C->A->B`, four arrows == four transfers.

Now our tree clearly became an undirected graph, since we don't need to respect
the orbit hierarchy to make a transfer. In other words, we don't care about who
is the child and who is the parent anymore. We need a different data structure:
a dictionary of sets `{planet: set_of_connected_planets}`. We can use the very
cool [`defaultdict`][py-collections-defaultdict] from the
[`collections`][py-collections] module, which is just like a normal `dict`, but
automatically creates entries when we try to access them. The source and
destination can just be taken from the `orbits` tuple we generated earlier.

```python
from collections import defaultdict

G = defaultdict(set)

for a, b in orbits:
    G[a].add(b)
    G[b].add(a)
```

After building the graph, all we need to do is apply a good shortest path
finding algorithm, like [Dijkstra's algorithm][algo-dijkstra].

For this purpose the [`heapq`][py-heapq] module is very useful: it provides the
heap data structure, which is capable of maintaining an ordered structure of
elements that lets us efficiently pop the smallest element. We'll use it as a
queue to hold planets to visit. We will also use the built-in
[`filter()`][py-builtin-filter] function for convenience. A `defaultdict` that
returns `float('inf')` is also useful to treat not-yet-seen planets as being
infinite steps away.

```python
import heapq

def dijkstra(G, src, dst):
    # List of (distance, planet) used as heap to choose the next planet to visit.
    queue = [(0, src)]

    visited = set()
    distance = defaultdict(lambda: float('inf'))
    distance[src] = 0

    while queue:
        dist, planet = heapq.heappop(queue)

        if planet == dst:
            return dist

        if planet not in visited:
            visited.add(planet)

            for neighbor in filter(lambda p: p not in visited, G[planet]):
                new_dist = dist + 1

                if new_dist < distance[neighbor]:
                    distance[neighbor] = new_dist
                    heapq.heappush(queue, (new_dist, neighbor))

    return float('inf')
```

Cool, now we can just call the function to get the answer:

```python
source = T['YOU']
destination = T['SAN']

min_transfers = dijkstra(G, source, destination)
print('Part 2:', min_transfers)
```


Day 7 - Amplification Circuit
-----------------------------

[Problem statement][d07-problem] — [Complete solution][d07-solution] — [Back to top][top]

### A working Intcode VM

This problem requires a working Intcode virtual machine built following
instructions in the day 2 and day 5 problem statements! The machine could be as
simple as a single function, or something more complicated like a class with
multiple methods.

I ended up using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.
The important thing here is that our VM needs to have the following features:

1. Possibility to stop after every output instruction to collect the outputs one
   by one.
2. Possibility to resume after previously stopping, also taking additional
   input.
3. Preferably the possibility to reset and restart easily. This could be more
   convenient than re-instantiating the whole thing every time.
4. Preferably, the possibility to pretty print each instruction for debugging
   purposes, if we ever get stuck somewhere.

My `IntcodeVM` accomplishes all the above through a `run()` method which takes
an optional `inp=` parameter (a list of input values), an optional `n_out=`
integer parameter (the number of output instructions to execute before pausing
and returning the accumulated outputs), and an optional `resume=` boolean
parameter (whether to restart or resume execution).

### Part 1

So, we are given an interesting task: we have 5 amplifiers connected in series,
each one running the same Intcode program (the puzzle input). We will need to
start each of them with a different initial *phase setting* as input (an integer
from `0` to `4`).

        O-------O  O-------O  O-------O  O-------O  O-------O
    0 ->| Amp A |->| Amp B |->| Amp C |->| Amp D |->| Amp E |-> output signal
        O-------O  O-------O  O-------O  O-------O  O-------O

After the first input, which is given by us, each machine's output is connected
to the next one's input, and the last machine will give us a final *output
signal*. The first machine will also get a `0` as second input to compensate for
the fact that its input is not connected to any other machine. We want to find
the best combination of phase settings such that the output signal is maximized.
The maximum output signal will be the answer to the puzzle.

So, first of all, let's parse the input and instantiate 5 different VMs:

```python
from lib.intcode import IntcodeVM

program = list(map(int, fin.read().split(',')))
vms = [IntcodeVM(program) for _ in range(5)]
```

A single run of the amplifiers to get one output signal can simply be done by
starting with a previous output of `[0]`, and looping through the VMs feeding
each one with one phase setting integer plus the previous output:

```python
phase_settings = (1, 4, 3, 2, 0)
out = [0]

for vm, inp in zip(vms, phase_settings):
    out = vm.run([inp, *out])

output_signal = out[0]
```

To solve the puzzle and find the maximum output signal, we need to test all
possible inputs, which means all possible
[permutations](https://en.wikipedia.org/wiki/Permutation) of the phase settings.
We can take advantage of the [`permutations()`][py-itertools-permutations]
generator function from the [`itertools`][py-itertools] module. This function
takes an iterable as its only required parameter, and returns a generator which
generates all the possible permutations of the items in the iterable.

All this talking and explaining finally boils down to the following code:

```python
from itertools import permutations

max_signal = float('-inf')

for inputs in permutations(range(5)):
    out = [0]

    for vm, inp in zip(vms, inputs):
        out = vm.run([inp, *out])

    if out[0] > max_signal:
        max_signal = out[0]

print('Part 1:', max_signal)
```

And we have our part one solution!

### Part 2

Things get a little bit more complicated. Machines are now connected in a
feedback loop, meaning that after starting each one with a different phase
setting and connecting them, we will also need to connect the last one to the
first one. The computation will be over after the fifth machine halts. Its last
output value will be the signal to maximize this time.

          O-------O  O-------O  O-------O  O-------O  O-------O
    0 -+->| Amp A |->| Amp B |->| Amp C |->| Amp D |->| Amp E |-.
       |  O-------O  O-------O  O-------O  O-------O  O-------O |
       |                                                        |
       '----<----------<----------<----------<----------<-------+
                                                                |
                                                                v
                                                            output signal

This time, the phase settings need to be 5 different values from `5` to `9`.

The approach is the same as before, but our VMs now need to support pausing and
resuming execution on demand. An initial cycle to restart the VMs and supply the
starting phase signal is needed, then we can keep them running until one of them
halts, and keep the last output of the fifth VM.

```python
max_signal = float('-inf')

for inputs in permutations(range(5, 10)):
    out = [0]

    for vm, inp in zip(vms, inputs):
        # reset and run until first output, then pause and return it
        out = vm.run([inp, *out], n_out=1)

    last_signal = out[0]

    while all(vm.running for vm in vms):
        for i, vm in enumerate(vms):
            # resume execution and run until first output, then pause and return it
            out = vm.run(out, n_out=1, resume=True)

            if not vm.running:
                break

            if i == 4:
                last_signal = out[0]

    if last_signal > max_signal:
        max_signal = last_signal

print('Part 2:', max_signal)
```

The lesson to learn from this puzzle is that code
[**reusability**](https://en.wikipedia.org/wiki/Reusability) and
[**extensibility**](https://en.wikipedia.org/wiki/Extensibility) are two very
important concepts in software engineering. Not having an already working VM
ready at hand would have made working towards a solution much slower. Not having
written easily extensible code for the VM would have been an annoyance too.


Day 8 - Space Image Format
--------------------------

[Problem statement][d08-problem] — [Complete solution][d08-solution] — [Back to top][top]

### Part 1

Pixels! For today's puzzle we have to deal with a strange image format. In
short, an image is composed by several layers, each 25x6 pixels in size, and our
input is composed of only one line: a long string which is the concatenation of
all the layers of the image, where one character represents one pixel.

It's convenient not to think about a layer as a rectangle of pixels for now,
since we are not asked to do any matrix operation on the pixels. We can just get
the input and split it into layers. We also don't need to worry about converting
characters to numbers.

```python
WIDTH, HEIGHT = 25, 6
SIZE = WIDTH * HEIGHT

chars = fin.readline().strip()
layers = [chars[i:i + SIZE] for i in range(0, len(chars), SIZE)]
```

We are assigned the pretty straightforward task to find the layer with the least
amount of `0` pixels, and count the number of `1` and `2` pixels in that layer,
multiplying those two numbers together to get a "checksum", which is the answer.

We can do this pretty cleanly using the [`min()`][py-builtin-min] function. With
the `key=` function parameter, we can say that we want to find a layer `l` such
that the count of zeroes is the minimum. So here's part one:

```python
best = min(layers, key=lambda l: l.count('0'))
checksum = best.count('1') * best.count('2')
print('Part 1:', checksum)
```

### Part 2

We are now told that each pixel can be either black (`0`), white (`1`) or
transparent (`2`), and to get the "real" image from all the layers, we need to
stack them up: since we can see through the transparent pixels, the final value
of a pixel in a given position of the image will be the one of the first pixel
in that position that is not transparent. The final reconstructed image will
represent a certain message, which is the answer.

As we just said, we can create the final image as a simple list, and then cycle
through each pixel of each layer, top to bottom, to find the first value which
is not transparent, assigning it to the final image.

```python
image = ['2'] * SIZE

for i in range(SIZE):
    for l in layers:
        if l[i] != '2':
            image[i] = l[i]
            break
```

Now we can just split the image in multiple rows (each 25 pixels wide) to see
the final result.

```python
decoded = ''

for i in range(0, SIZE, WIDTH):
    decoded += ''.join(image[i:i + WIDTH]) + '\n'

print('Part 2:', decoded, sep='\n')
```

Result:

    1110011110011000110010010
    1001010000100101001010100
    1001011100100001001011000
    1110010000100001111010100
    1000010000100101001010100
    1000010000011001001010010

Hmmm... it doesn't look that clear, does it? Let's replace black pixels with a
space and white pixels with an hashtag `#` and print that again. To do this we
can use a simple dictionary to map each pixel to the character we want, with the
help of [`map()`][py-builtin-map].

```python
conv = {'0': ' ', '1': '#'}
decoded = ''

for i in range(0, SIZE, WIDTH):
    decoded += ''.join(map(conv.get, image[i:i + WIDTH])) + '\n'

print('Part 2:', decoded, sep='\n')
```

Result:

    ###  ####  ##   ##  #  #
    #  # #    #  # #  # # #
    #  # ###  #    #  # ##
    ###  #    #    #### # #
    #    #    #  # #  # # #
    #    #     ##  #  # #  #

Now that's readable, and we successfully got our part 2 answer!



Day 9 - Sensor Boost
--------------------

[Problem statement][d09-problem] — [Complete solution][d09-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02] and [day 5][d05] problem statements! The
machine could be as simple as a single function, or something more complicated
like a class with multiple methods. Take a look at previous days to know more.

I will use and explain how to extend the simple single-function Intcode VM
created in day 5 of this walkthrough.

### Part 1

Looks like we need to add some functionality to our Intcode VM! The two main
features that need to be added to our VM are:

- The VM needs to remember a new global value called *relative base*, which
  starts as `0` and gets modified by the program.
- A new opcode, `9`: it adjusts the *relative base* by the value of its only
  parameter. The relative base increases (or decreases, if the value is
  negative) by the value of the parameter.
- A new parameter mode, `2`: *relative mode*. In this mode parameters are
  interpreted as an offset from the *relative base*. In this mode,
  reading/writing memory means computing the address by adding the value of the
  parameter to the *relative base* first. As an example, a destination parameter
  of value `3` in relative mode means writing to `mem[rel_base + 3]`.
- Support for very large numbers (we are using Python so it's already fine).
- Read/writes to memory beyond the size of the program: this can be easily
  achieved by simply appending to the memory a long list of zeroes.

We are given an input Intcode program which uses these new features, and we need
to simply run it providing `1` as the only input to get the final output, which
is the answer.

First of all, it's becoming hard to keep track of things, so let's use some
enum-like variables to represent opcodes and also use a dictionary to keep track
of the number of parameters for each opcode:

```python
OPADD, OPMUL, OPIN, OPOUT, OPJNZ, OPJZ, OPLT, OPEQ, OPREL = range(1, 10)
OPHALT = 99

OPCODE_NPARAMS = {
    OPADD : 3,
    OPMUL : 3,
    OPIN  : 1,
    OPOUT : 1,
    OPJNZ : 2,
    OPJZ  : 2,
    OPLT  : 3,
    OPEQ  : 3,
    OPREL : 1,
    OPHALT: 0
}
```

Relative mode needs to be handled differently for source and destination
parameters. If a parameter is source, then we should read
`mem[param + rel_base]`, otherwise we should write to the index
`param + rel_base`, not to the index `mem[param + rel_base]`. Let's keep track
of parameter modes and types the same way we just did for opcodes:

```python
MODE_POSITION, MODE_IMMEDIATE, MODE_RELATIVE = range(3)
TYPE_SRC, TYPE_DST = range(2)

OPCODE_PARAMTYPES = {
    OPADD : (TYPE_SRC, TYPE_SRC, TYPE_DST),
    OPMUL : (TYPE_SRC, TYPE_SRC, TYPE_DST),
    OPIN  : (TYPE_DST,),
    OPOUT : (TYPE_SRC,),
    OPJNZ : (TYPE_SRC, TYPE_SRC),
    OPJZ  : (TYPE_SRC, TYPE_SRC),
    OPLT  : (TYPE_SRC, TYPE_SRC, TYPE_DST),
    OPEQ  : (TYPE_SRC, TYPE_SRC, TYPE_DST),
    OPREL : (TYPE_SRC,),
    OPHALT: ()
}
```

Now we can take the `run()` function we wrote for [day 5][d05], and work from
there. Each iteration, we will first decode the opcode, its modes, types, and
parameters:

```python
op = prog[pc]
modes = ((op // 100) % 10, (op // 1000) % 10, (op // 10000) % 10)
op = op % 10

nparams = OPCODE_NPARAMS[op]
types   = OPCODE_PARAMTYPES[op]
params  = prog[pc + 1:pc + 1 + nparams]
```

Then, we will translate the parameters into the correct values according to
their types and modes:

```python
for i in range(len(params)):
    if modes[i] == MODE_POSITION:
        if types[i] == TYPE_SRC:
            params[i] = prog[params[i]]
    elif modes[i] == MODE_RELATIVE:
        if types[i] == TYPE_SRC:
            params[i] = prog[relative_base + params[i]]
        elif types[i] == TYPE_DST:
            params[i] += relative_base
```

The big work is done, now it's only matter of implementing the new opcode `9`,
and use the `params` for each opcode. Here's the final function:

```python
def run(prog, input_function, output_function):
    pc = 0
    relative_base = 0

    # Extend memory filling with zeros.
    prog = prog + [0] * 10000

    while prog[pc] != OPHALT:
        op = prog[pc]

        # Calculate parameter modes.
        modes = ((op // 100) % 10, (op // 1000) % 10, (op // 10000) % 10)
        op = op % 10

        # Get parameters and parameter types.
        nparams = OPCODE_NPARAMS[op]
        types   = OPCODE_PARAMTYPES[op]
        params  = prog[pc + 1:pc + 1 + nparams]

        # Translate parameters into the needed values based on the mode.
        for i in range(len(params)):
            if modes[i] == MODE_POSITION:
                if types[i] == TYPE_SRC:
                    params[i] = prog[params[i]]
            elif modes[i] == MODE_RELATIVE:
                if types[i] == TYPE_SRC:
                    params[i] = prog[relative_base + params[i]]
                elif types[i] == TYPE_DST:
                    params[i] += relative_base

        if op == OPADD:
            a, b, c = params
            prog[c] = a + b
            pc += 4
        elif op == OPMUL:
            a, b, c = params
            prog[c] = a * b
            pc += 4
        elif op == OPIN:
            a = params[0]
            prog[a] = input_function()
            pc += 2
        elif op == OPOUT:
            a = params[0]
            output_function(a)
            pc += 2
        elif op == OPJNZ:
            a, b = params
            pc = b if a != 0 else pc + 3
        elif op == OPJZ:
            a, b = params
            pc = b if a == 0 else pc + 3
        elif op == OPLT:
            a, b, c = params
            prog[c] = 1 if a < b else 0
            pc += 4
        elif op == OPEQ:
            a, b, c = params
            prog[c] = 1 if a == b else 0
            pc += 4
        elif op == OPREL:
            a = params[0]
            relative_base += a
            pc += 2
```

The function now takes three parameters: the program, one input function to be
called when the *input* instruction is executed, and one output function to be
called when the *output* instruction is executed. This way, it will be easier to
program dynamic input and output for future days. For part 1, we can define
these two functions pretty simply:

```python
in_func = lambda: 1
output_value = None

def out_func(v):
    global output_value
    output_value = v
```

Okay, let's run it on our input program and get the result:

```python
program = list(map(int, fin.read().split(',')))

run(program[:], in_func, out_func)
print('Part 2:', output_value)
```

### Part 2

Part 2 statement says "You now have a complete Intcode computer". Yay! No more
adding functionality!

This second part is very straightforward. We don't need to do anything, just run
the program again with `2` as its only input. We'll just redefine the input
function, and keep the rest the same. It literally takes it more to run it than
to write it.

```python
in_func = lambda: 2

run(program[:], in_func, out_func)
print('Part 1:', output_value)
```

And there it is, day 9 completed and we now have a complete Intcode VM! Nice.


Day 10 - Monitoring Station
---------------------------

[Problem statement][d10-problem] — [Complete solution][d10-solution] — [Back to top][top]

### Part 1

Very interesting puzzle today. We get to deal with some sort of "primitive ray
tracing" techniques. We are given a 2D ASCII art grid of asteroids in space.
Each asteroid is positioned at a fixed integer row and column. For the first
part, we are asked to find where it's best to build a station, by determining
which asteroid has the best field of view in terms of the number of other
asteroids that can be seen from it. We want to know how many asteroids can be
seen from the best asteroid.

Asteroids must be considered as points in space (no width nor height). Given a
asteroid `A`, another asteroid `B` is can be seen (in sight of) `A` if (and only
if) it is the closest asteroid on the line of sight connecting the two. A line
of sight is just a
[ray](https://en.wikipedia.org/wiki/Line_(geometry)#Ray) starting from `A` and
passing through `B`.

Let's get input parsing out of the way, we will just build a set of 2D points
from our input, adding one for each asteroid `#` in the ASCII art grid:

```python
grid = [l.rstrip() for l in fin]
asteroids = set()

for y, row in enumerate(grid):
    for x, cell in enumerate(row):
        if cell == '#':
            asteroids.add((x, y))
```

To tackle this geometrical problem, first of all we should notice that we do not
actually care about which asteroid is the closest to us on any given line of
sight, but we just care about how many *different* line of sights we have from
from each asteroid. Since on each line of sight there is only one asteroid that
can be seen, the number of different lines of sights is the only information we
need.

There are different methods to compute and represent the line of sight between
two asteroids `A` and `B`. What we care about here is that:

1. We want it to be precise, no floating point values involved, to avoid getting
   into the weirdness of broken floating point math when comparing values.
2. We want it to be simple and concise.

So how do you uniquely represent a line (or better, a ray) in a 2D plane? We
should know from any basic geometry class that the equation of a line on the
cartesian plane is
[`y = m*x + b`](https://en.wikipedia.org/wiki/Line_(geometry)#On_the_Cartesian_plane)...
but do we actually care about `b`? We do not, since what defines a line of sight
is only its slope `m`, and from the same basic geometry class we should also
know that the slope of the line between two points can be calculated as
`m = (By - Ay)/(Bx - Ax)`.

For each asteroid `A`, we want to calculate all the slopes of te rays between
itself and any other asteroid `B`. In order for this measurement to be
*accurate*, we will not do the division, but we will just represent `m` as an
[*irreducible fraction*](https://en.wikipedia.org/wiki/Irreducible_fraction),
storing its numerator and denominator. Since we also care about the direction of
each ray, along the slope fraction we will also need to keep the sign of the
numerator and denominator (i.e. do not simplify `-2/-4` as `1/2`, but as
`-1/-2`).

To reduce any fraction to an irreducible fraction the only thing we need is to
divide both numerator and denominator by their greatest common divisor. For this,
the [`gcd()`][py-math-gcd] function from the [`math`][py-math] module comes in
handy.

```python
def ray(ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    div = abs(gcd(dx, dy))
    return dx//div, dy//div
```

Now for each candidate asteroid, we can just count the number of different
rays (to all the other asteroids) by creating a [`set()`][py-set]. We will
keep track of the maximum number of asteroids that can be seen as well as the
asteroid from which it is possible (this is useful for part 2).

Here's our part 1 solution:

```python
station = None
max_in_sight = 0

for src in asteroids:
    lines_of_sight = set()

    for a in asteroids:
        if a == src:
            continue

        lines_of_sight.add(ray(*src, *a))

    in_sight = len(lines_of_sight)
    if in_sight > max_in_sight:
        max_in_sight = in_sight
        station = src

print('Part 1:', max_in_sight)
```

The syntax `*src` (and `*a`) here uses the Python
[*unpacking operator*][py-unpacking] to unpack a tuple `(x, y)` into two
different values (passed as arguments). The above snippet could be optimized by
memorizing the `ray()` function return value for each pair of asteroids using a
dictionary, but since the number of asteroids is quite small, in our case the
overhead of dictionary operations would only outweigh the saved computation
time.

### Part 2

In the second part of the problem, after planting our monitoring station on the
best asteroid, we now start to blast every asteroid in line of sight with a
laser beam. We want to know the coordinates of the 200th asteroid which will be
destroyed.

Starting facing north, we rotate the laser clockwise. Each time the laser beam
intersects with an asteroid, it destroys it, but it does *not* destroy any other
asteroid on the same line of sight. In other words, asteroids on the same LoS
are "shielded" by closer asteroids on the same LoS. The second closest asteroid
on a given line of sight will be destroyed on the second rotation of the
station, after the laser beam completes a full cycle.

First of all, the answer for part 1 was greater than 200, so we only need to
sweep for one cycle, since we have > 200 asteroids in direct line of sight. The
following solution makes this assumption, but it's trivial to generalize the
code just by adding one more loop to re-scan the asteroids after each full
rotation.

To know which asteroid will be destroyed as 200th, we need to order their
positions based on the ray on which they are placed. Contrary to the first part,
we now do care about one asteroid being the closest on a given ray. We can again
scan all asteroids to determine which one is the closest on each ray. This is as
simple as saving the asteroid and its distance in a dictionary
`{ray: (closest_asteroid, distance)}`. For the distance we can just use plain
[Manhattan distance][algo-manhattan], nothing fancier needed.

```python
def manhattan(ax, ay, bx, by):
    return abs(bx - ax) + abs(by - ay)

closest = {}

for a in asteroids:
    if a == station:
        continue

    r = ray(*station, *a)
    m = manhattan(*station, *a)

    if r not in closest or m < closest[r][1]:
        closest[r] = (a, m)
```

Now that we've got all the closest asteroids, we will need to order them. We
want to sort them by clockwise angle from north. To do this, we can calculate
the angle for every ray using the [`atan2()`][py-math-atan2] function. This
function takes `y` and `x` as parameters (in this exact order) and outputs a
value in [radians](https://en.wikipedia.org/wiki/Radian) ranging from `-math.pi`
to `math.pi`, considering the *east* direction as zero. To make the return value
of this function useful, we first need to convert the range from `[-pi, pi)` to
`[0, 2*pi)` (just add `+pi` to the result of `atan2()`), and then move the zero
value to north so that the north direction corresponds to `0` radians.

After thinking about it with the help of pen and paper, what we need is the
following:

```python
from math import atan2, pi as PI

def angle(ax, ay, bx, by):
    rad = atan2(by-ay, bx-ax) + PI
    rad = rad % (2*PI) - PI/2
    return rad if rad >= 0 else 2*PI + rad
```

Note that from the way we parsed the input, north corresponds to the negative Y
axis in our program, this needs to be carefully taken into account when writing
the above function! The `rad % (2*PI)` trick here is to avoid having a resulting
angle of `2*PI` for rays that are exactly facing north (in that case, we want
`0` instead).

We can now finally order the asteroids by angle using the built-in
[`sorted()`][py-builtin-sorted] function with our `angle()` function used as
sorting key, then take the 200th asteroid to get our answer:

```python
ordered = sorted(closest.values(), key=lambda am: angle(*station, *am[0]))
chosen_x, chosen_y = ordered[200 - 1][0]
answer = 100 * chosen_x + chosen_y
print('Part 2:', answer)
```


Day 11 - Space Police
---------------------

[Problem statement][d11-problem] — [Complete solution][d11-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.

### Part 1

Today's task is pretty simple. We are given an intcode program to run, which
should simulate a "painting robot". This robot moves on a grid to paint each
cell either black (`0`) or white (`1`). The grid is initially all black.

The robot starts facing up, and takes the color of the current cell he is on as
input, then outputs the color that should be painted on the cell, and a turn
instruction, which is either 90 degrees left (`0`) or 90 degrees right (`1`).
After that, it moves forward one cell, and the process continues until the robot
halts.

We are asked to determine how many panels are painted at least once.

This is a pretty simple task if we have a working Intcode VM. Let's parse the
input and instantiate the VM as usual:

```python
from lib.intcode import IntcodeVM

program = list(map(int, fin.read().split(',')))
robot = IntcodeVM(program)
```

As usual when dealing with movements on a grid, some support constants will make
our life easier to keep track of the position of the robot, its direction, etc:

```python
BLACK, WHITE = 0, 1
LEFT, RIGHT = 0, 1
NORTH, SOUTH, EAST, WEST = 'NSEW'

# New direction turning LEFT or RIGHT based on current direction.
DIRMAP = {
    NORTH: (WEST, EAST),
    SOUTH: (EAST, WEST),
    EAST: (NORTH, SOUTH),
    WEST: (SOUTH, NORTH)
}

# Delta to move when facing a secific direction.
MOVEMAP = {
    NORTH: (-1, 0),
    SOUTH: (+1, 0),
    EAST: (0, +1),
    WEST: (0, -1)
}
```

After defining those, we can create a function to build the grid of painted
cells for us. We can assign an arbitrary position as starting point (let's say
`(0, 0)`), and then update it according to the robot movement. Each time we
update the position, we also add it to a dictionary `{position: color}`, which
will represent a
[*sparse matrix*](https://en.wikipedia.org/wiki/Sparse_matrix#Dictionary_of_keys_(DOK)).
A [`defaultdict`][py-collections-defaultdict] will also make our life easier
when dealing with unvisited positions (which are all initially black).

We will run the robot in a loop and pause its execution every two `out`
instructions to collect the new color and turn direction. We will then update
the grid and the current position, and we'll keep going until the robot halts.

```python
def run_robot(robot, starting_color):
    pos       = (0, 0)
    curdir    = NORTH
    grid      = defaultdict(lambda: BLACK)
    grid[pos] = starting_color

    robot.reset()

    while True:
        out = robot.run([grid[pos]], n_out=2, resume=True)

        if not out:
            break

        color, turn = out
        grid[pos] = color
        curdir = DIRMAP[curdir][turn]
        dx, dy = MOVEMAP[curdir]
        pos = (pos[0] + dx, pos[1] + dy)

    return grid
```

We can see how `DIRMAP` and `MOVEMAP` are useful here: they save us the trouble
of creating countless `if/elif` statements for each direction and turn.

Now that we have a function which runs the robot and builds a grid, since we
want to know the total number of cells that have been painted by the robot, the
answer is just the length of the `grid`.

```python
grid = run_robot(robot, BLACK)
n_painted = len(grid)
print('Part 1:', n_painted)
```

### Part 2

The initial cell where the robot starts is now white (any other cell is still
black). We need to run the robot in the same way as before, and then read what
was painted on the grid: we should see some ASCII-art letters.

Okay, so the function we just wrote stays the same, we just need to call it with
`starting_color` set to `WHITE`. After getting the new grid, we can determine
the bounds by looking at the minimum and maximum `x` and `y` values in the keys
of the dictionary. We can then iterate with two `for` loops on the full range of
possible coordinates, and check the color of each cell. Since we are using a
`defaultdict`, we don't even need to worry about non-existing keys, as their
value will always be initialized to `BLACK`. We will build our matrix filling it
with spaces if a cell is black, and hashes (`#`) if a cell is white.

```python
def sparse_to_matrix(grid):
    minx = min(x for x, _ in grid)
    maxx = max(x for x, _ in grid)
    miny = min(y for _, y in grid)
    maxy = max(y for _, y in grid)

    height = maxx - minx + 1
    width  = maxy - miny + 1
    matrix = [([' '] * width) for _ in range(height)]

    for x in range(height):
        for y in range(width):
            if grid[minx + x, miny + y] == WHITE:
                matrix[x][y] = '#'

    return matrix
```

Now we only need to run the robot again, build the matrix and print it out line
by line, joining the characters in each row.

```python
grid = run_robot(robot, WHITE)
pic = sparse_to_matrix(grid)

print('Part 2:')
for row in pic:
    print(''.join(row))
```

The result should be something like this:

     ##  #    ###  #### ###    ## #### ###
    #  # #    #  # #    #  #    #    # #  #
    #    #    ###  ###  #  #    #   #  #  #
    # ## #    #  # #    ###     #  #   ###
    #  # #    #  # #    #    #  # #    #
     ### #### ###  #### #     ##  #### #

And today's puzzle is completed!


Day 12 - The N-Body Problem
---------------------------

[Problem statement][d12-problem] — [Complete solution][d12-solution] — [Back to top][top]

### Part 1

For today's puzzle we get to work with 3D coordinates. We are given exactly four
points in the 3D space, which represent four moons in space. All moons attract
and are attracted by each other. We need to simulate 1000 steps of moon movement
knowing that each step:

1. Each moon's velocity on a given axis changes by `+1` for each other moon
   which has a higher coordinate value on that axis, and by `-1` for each other
   moon which has a lower coordinate value.
2. Each moon's position changes according to its velocity. In other words,
   velocity is added to the current position to get the next position.

Moons start with velocity `(0, 0, 0)` and positions given by our input. After
simulating 1000 steps, we need to calculate the total energy in the system,
knowing that the energy of each moon is the product of its *potential energy*
and its *kinetic energy*, and that:

- Potential energy = sum of the absolute values of the moon's coordinates.
- Kinetic energy = sum of the absolute values of the moon's velocity in each
  coordinate.

First of all, let's parse the input: each moon's initial position is in the form
`<x=1, y=2, z=3>`, so matching wth a regular expression using the
[`re`][py-re] module is the easiest way to go:

```python
exp = re.compile(r'-?\d+')
initial_positions = [list(map(int, exp.findall(line))) for line in fin]
```

So, let's get a decent data structure to hold position and velocity of a moon:
a [`namedtuple`][py-collections-namedtuple] is the easiest way to go:

```python
from collections import namedtuple

# we will have m = Moon([px, py, pz], [vx, vy, vz])
Moon = namedtuple('Moon', ['pos', 'vel'])
moons = [Moon(pos.copy(), [0, 0, 0]) for pos in initial_positions]
```

As the problem states, for every moon, each step the following happens:

```python
for other_moon in moons:
    if other_moon is moon:
        continue

    if other_moon.pos[0] > moon.pos[0]:
        moon.vel[0] += 1
    elif other_moon.pos[0] < moon.pos[0]:
        moon.vel[0] -= 1

    # same for dimensions 1 and 2 (y and z)

moon.pos[0] += moon.vel[0]
# same for dimensions 1 and 2 (y and z)
```

If we apply the above to all moons, putting the whole thing in a `for` loop, we
can easily simulate 1000 steps.

We can take advantage of the [`combinations()`][py-itertools-combinations]
function from the [`itertools`][py-itertools] module instead of two `for` loops
to efficiently get all the unique couples of moons. This means that we'll need
to modify the velocity of both inside the loop, but that's no problem! Now let's
dive into it and simulate the first 1000 steps.

```python
from itertools import combinations

for step in range(1000):
    for moon1, moon2 in combinations(moons, 2):
        for dim in range(3):
            if moon2.pos[dim] > moon1.pos[dim]:
                moon1.vel[dim] += 1
                moon2.vel[dim] -= 1
            elif moon2.pos[dim] < moon1.pos[dim]:
                moon1.vel[dim] -= 1
                moon2.vel[dim] += 1

    for moon in moons:
        for dim in range(3):
            moon.pos[dim] += moon.vel[dim]
```

We could optimize this a little bit further by pre-calculating `range(3)` and
turing it into a tuple to use each time, but we are not going for this level of
optimization here, just a reasonably good and cool looking solution.

Anyway, now we only need to calculate the total energy as described in the
problem statement, and we get the answer. The classic [`map()`][py-builtin-map]
& [`sum()`][py-builtin-sum] approach works like a charm as usual.

```python
potential = (sum(map(abs, m.pos)) for m in moons)
kinetic   = (sum(map(abs, m.vel)) for m in moons)
total     = sum(p * k for p, k in zip(potential, kinetic))
print('Part 1:', total)
```

### Part 2

For the second part of this problem we are told that the initial state of the
system (initial positions and velocities) will somehow end up repeating itself
at some very, very far point in the future (millions of millions of steps).
Clearly, bruteforcing is unfeasible (or, well, probably going to take ages), so
we want a smarter solution.

If we take a look at each dimension, we can see that they are independent from
each other. Velocity and position of a moon on the X axis will never affect
velocity or position of any other moon on a *different* axis. Therefore, if we
want to find the same state again, we can split the problem in three and find
out how much time it takes for each dimension to go back to the initial state.
This simplifies things by an order of magnitude, and makes it possible to find
the solution in a very reasonable amount of time, by advancing each direction by
its own until it gets back to the initial state, then saving the number of steps
it took for it to reset.

We'll end up with three different periods, and when different things repeat with
different periods, they will all repeat together exactly at the least common
multiple of those periods.

The inner loops we wrote for part 1 basically remain the same, we'll just bring
the `for dim in range(3)` loop that iterates over dimensions at the top level,
then add some state checking logic. The initial position of each moon is saved
in `initial_positions`, and the initial velocity is always `[0, 0, 0]`, so we
can just check these values. We continue from the previous `step` until we find
all periods. Since we already are using `itertools`, let's also use it to count
to infinity with the [`count()`][py-itertools-count] generator.

Here we go:

```python
from itertools import count

periods = []
start = step + 1

for dim in range(3):
    for period in count(start):
        back_to_initial = True

        for moon, initial_pos in zip(moons, initial_positions):
            if moon.vel[dim] != 0 or moon.pos[dim] != initial_pos[dim]:
                back_to_initial = False
                break

        if back_to_initial:
            break

        for moon1, moon2 in combinations(moons, 2):
            if moon2.pos[dim] > moon1.pos[dim]:
                moon1.vel[dim] += 1
                moon2.vel[dim] -= 1
            elif moon2.pos[dim] < moon1.pos[dim]:
                moon1.vel[dim] -= 1
                moon2.vel[dim] += 1

        for moon in moons:
            moon.pos[dim] += moon.vel[dim]

    periods.append(period)
```

Let's calculate the least common multiple of all periods to get our answer.
We'll use [`gcd()`][py-math-gcd] (greatest common divisor) from the
[`math`][py-math] module to write our own `lcm` function, and
[`reduce()`][py-functools-reduce] from [`functools`][py-functools] as a cool
functional way to apply it to the three periods (since our `lcm()` will take two
arguments).

```python
from math import gcd
from functools import reduce

def lcm(a, b):
    return abs(a * b) // gcd(a, b)

total_steps = reduce(lcm, periods, 1)
print('Part 2:', total_steps)
```

### Reflections

By observing the behavior of moons, we can notice that their velocity only gets
to zero one time before going back to the initial state. This means that we
could just check until all moon velocities hit 0 and ignore their position. Once
they do, in exactly double the number of steps they will all converge back to
the initial position. I happened to discover this myself by accident for a
little bug I encountered why cleaning up my solution and writing about it here.
I ended up using this assumption in my complete solution.

Our "initial state check" code then becomes just:

```python
if all(m.vel[dim] == 0 for m in moons):
    break
```

This property is pretty cool, but I am not enough of a mathematician to write a
proof for it for N objects (in our case 4). It's easy to see that it holds true
for two objects and one dimension, as Reddit user
[u/encse](https://www.reddit.com/user/encse) points out in
[a comment](https://www.reddit.com/r/adventofcode/comments/e9o2sk/2019_day_12_part_2accidental_optimization_why_is/fak6kcw/).

Two objects accelerate towards each other starting with v = 0. When meeting in
the middle, the acceleration changes sign and they begin to slow down to v = 0.
At this point the distance is the same as it was at the beginning, but the
objects swapped place. It now takes the same amount of time to get back to the
original position. In particular, those two objects will keep swapping places
over and over again until the end of time, since that in our magic physics
system acceleration never decreases with distance. This can be easy extended in
N dimensions, since dimensions are independent, *but* is not as simple to
generalize for more than two objects... this could even *not* hold true for more
than two objects.

As quite the number of people seem to have tested out, for more than two object
it seems like the periodicity of the system depends on the starting position,
and only particular starting positions seem to cause the system to be periodic.
There most probably are much more starting positions that lead to divergence
than ones that lead to periodicity! So our puzzle input seems to have been
tailored to be solvable. Quite interesting!


Day 13 - Care Package
---------------------

[Problem statement][d13-problem] — [Complete solution][d13-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.

### Part 1

Another Intcode challenge! We are given an Intcode program, and we are told that
it runs on an arcade cabinet. The program will draw on the screen of the cabinet
by outputting groups of three values: `x`, `y`, and a "tile ID". The tile ID
represents which tile is to be drawn:

- `0` is an empty tile. No game object appears in this tile.
- `1` is a wall tile. Walls are indestructible barriers.
- `2` is a block tile. Blocks can be broken by the ball.
- `3` is a horizontal paddle tile. The paddle is indestructible.
- `4` is a ball tile. The ball moves diagonally and bounces off objects.

We are then asked to count the number of block tiles that are drawn when running
the program.

Having a working Intcode VM, this is a pretty simple task:

```python
from lib.intcode import IntcodeVM

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)
out = vm.run()
```

We can then parse the output in blocks of size 3 with a simple `for`, and count
the number of blocks. Since we don't know if a block is going to be drawn
multiple times in the same position, we'll use a `set` to keep track of all the
positions where a block was drawn.

```python
blocks = set()

for i in range(0, len(out), 3):
    x, y, tile = out[i:i + 3]

    if tile == 2:
        blocks.add((x, y))

print('Part 1:', len(blocks))
```

### Part 2

Now things get fun! The program is running a fully functioning brick breaker
arcade game. We can see from part 1 the description of each tile. The game is
simplified since the ball always moves in a diagonal direction and does not
change angle when hit (like in a normal brick breaker game).

We are asked to *play the game* and win by destroying all blocks, and provide
the final score as the answer. To communicate the score, the program will output
the two invalid coordinates `-1, 0` and then the score. We need to replace the
first number in the program with a `2` to play the game first.

To play the game, after each output (group of 3 values), we are supposed to give
the program an input. We can input `-1` to move the paddle left one position,
`1` to move it right one position, and `0` to stay still.

If we take a look at the program output from part 1, and arrange the drawn tiles
in a grid, we get something like this:

    ++++++++++++++++++++++++++++++++++++++++++++
    +                                          +
    +     # ### ### #   ## # #   ###### # ## # +
    +  #         ## #  #  ### ##          ###  +
    +   #  #    ##   # #     #### #  # #  ## # +
    + # # ####  #  ####### ##   # #### ##      +
    +  #  # # ###     ## #  ## ### # #  ####   +
    +   # # # # #  #   # ## # #  ##  ##### # # +
    +  #####  ## ####  # # # ## # ##### # #    +
    + # # ####  #    # #   # #    ##   #### ## +
    + #  # #   # #  ##     ### # # #  ###### # +
    + #### #  #  # #   ## # ###  #  #  ## #    +
    +  #      #  #  #  # ### ## # # ##  #  #   +
    +  #####  #   # #        ## # #  # # #  #  +
    +  #       ### ## #   #  #### # # # # # #  +
    +  ## ####  ####  # #   #      #  #  #  #  +
    + #######  #      # ##   ####### # # # # # +
    + ##  ##   # # #  #       ##  ##### ## #   +
    +                                          +
    +                   o                      +
    +                                          +
    +                                          +
    +                     =                    +

So, how do we actually play the game? We need to come up with an AI that plays
for us if we don't want to wait for ages before each block is destroyed.

Well, if we just follow the ball around with our paddle, we will basically
always be under it and we'll never lose. Eventually, all blocks will get
destroyed and we'll have our final score. We can just run the program step by
step in a loop, and check if we need to move based on the ball position in
respect to the paddle position.

The solution is pretty straightforward:

```python
# Convenience enum for tiles.
EMPTY, WALL, BLOCK, PADDLE, BALL = range(5)

vm.orig_code[0] = 2
vm.reset()

score    = 0
paddle_x = 0
inp      = []

while True:
    out = vm.run(inp, resume=True, n_out=3)
    if not out:
        break

    x, y, tile = out

    # Don't move by default.
    inp = [0]

    if (x, y) == (-1, 0):
        # Update current score on special coordinates.
        score = tile
        continue

    if tile == PADDLE:
        # When the paddle gets re-drawn, update its position.
        paddle_x = x
    elif tile == BALL:
        # When the ball gets re-drawn, follow it.
        if x > paddle_x:
            inp = [1]
        elif x < paddle_x:
            inp = [-1]

print('Part 2:', score)
```

The emulation of the whole program until the win takes some seconds, but then we
get our answer as expected.


Day 14 - Space Stoichiometry
----------------------------

[Problem statement][d14-problem] — [Complete solution][d14-solution] — [Back to top][top]

### Part 1

Alright! I was wondering when we would have encountered some good old
[topological sorting](https://en.wikipedia.org/wiki/Topological_sorting)!

For today's puzzle, we are given a list of chemical recipes, in the form:

    3 A, 4 B, 1 C => 2 X

Each chemical appears on the right side only once, except for `ORE`, which is a
primitive element and does not need to be produced by chemical reaction. Each
reaction gives specific quantities for its inputs and output. Reactions cannot
be *partially* run, so only whole integer multiples of these quantities can be
used. However, we can have leftover elements when we are done, meaning that, for
example, in the above recipe, using `100 A`, `100 B` and `100 C`, we would end
up consuming `75 A`, `100 B` and `25 C`, producing `50 X`, with `25 A` and
`75 C` left unconsumed. Leftover elements can of course still be used in other
reactions.

We want to know the *minimum* amount of `ORE` needed to produce `1 FUEL`.

Alright, let's get to it. The reason I immediately mentioned topological sorting
at the very beginning is because when you have a situation like this, with a set
of dependencies that you want to resolve, the solution will inevitably require
some sort of topological sorting. The important part to notice here, which is
also what differentiates this situation from a plain and simple topological
sort, is that we can keep leftover chemicals from a recipe in order to re-use
them and save resources.

Each line of input identifies a "recipe": some quantity of different ingredients
is needed to produce some quantity of product chemical. If we want to produce a
chemical, we will need to have already produced all of its ingredients, which
means having already produced all the ingredients of each of them, and so on.

We will organize recipes in a dictionary
`{product_name: (product_qty, ingredients)}`, `product_qty` will be the amount
of product produced by the recipe, and `ingredients` will be a list of tuples
`(qty, ingredient_name)`. This will allow to easily keep track of each recipe
and its requirements.

```python
recipes = {}

for line in map(str.rstrip, fin):
    left, right = line.split(' => ')
    product_qty, product_name = right.split()

    ingredients = []
    for el in left.split(', '):
        qty, name = el.split()
        ingredients.append((int(qty), name))

    recipes[product_name] = (int(product_qty), ingredients)
```

So for example, parsing `3 A, 4 B, 1 C => 2 X` would yield:

```python
{'X': (2, [(3, 'A'), (4, 'B'), (1, 'C')])}
```

The following solution is kind-of inspired by the [Kahn's algorithm][algo-kahn]
(I'm saying kind-of since we have a different scenario and differently shaped
graph here).

We can solve the problem using a queue of chemicals that we need to produce
(along with their quantities), also keeping track of leftover quantities in a
another dictionary. We start with only `1 FUEL` in our queue, and while it is
not empty we'll pop one chemical at a time and produce it.

When producing a chemical, we'll first check if we already have some (if not all
the needed quantity) in our leftovers, taking as much as possible from there
first. After that, if there still is some amount to produce, we will calculate
how many times the recipe for the chemical needs to be applied to get at least
the needed quantity (using [`ceil()`][py-math-ceil] to round up). We will then
add each of the ingredients needed to produce that quantity in the queue,
ensuring that they'll be produced later at some point. In all of this, each time
we need to produce some `ORE`, we'll instead just increase a counter variable
keeping track of the total amount of ore needed.

The code almost speaks for itself, here it is:

```python
from math import ceil

def needed_ore(recipes, fuel_qty):
    # Star with only FUEL in the queue of chemicals to produce.
    queue = deque([(fuel_qty, 'FUEL')])
    leftover = defaultdict(int)
    total_ore = 0

    # While there's something to produce.
    while queue:
        needed_qty, chemical = queue.popleft()

        # If it's ORE, just increase the total.
        if chemical == 'ORE':
            total_ore += needed_qty
            continue

        # If there's already the needed quantity left over, just use that.
        if leftover[chemical] >= needed_qty:
            leftover[chemical] -= needed_qty
            continue

        # Otherwise take all that's left.
        needed_qty -= leftover[chemical]
        leftover[chemical] = 0

        # Get the recipe for the chemical and see how many times it needs to be applied.
        recipe_qty, ingredients = recipes[chemical]
        multiplier = ceil(needed_qty / recipe_qty)

        # Add to the queue the right quantity of each ingredient.
        for qty, el in ingredients:
            queue.append((qty * multiplier, el))

        # Add any excess produced chemical to the leftovers.
        leftover[chemical] += multiplier * recipe_qty - needed_qty

    return total_ore
```

And there we have it, we now only need to call the function and part 1 will be
solved:

```python
ore = needed_ore(recipes, 1)
print('Part 1:', ore)
```

### Part 2

For the second part, we now have the opposite task as before. We need to
calculate the maximum amount of fuel that we can produce with *1 trillion* units
of `ORE`.

Since we already have a function ready to calculate the needed amount of ore
given some required fuel quantity, we can just use [binary search][algo-binsrc]
to find the right value. We'll just need to get a good upper bound first,
applying the function to increasing values of `FUEL` until too much `ORE` is
needed.

Well, there's not much to say. Let's do some good old binary search and get our
answer:

```python
AVAILABLE_ORE = 10**12

hi = 2
while needed_ore(recipes, hi) < AVAILABLE_ORE:
    hi *= 2

lo = hi//2

while hi - lo > 1:
    x = (lo + hi) // 2
    ore = needed_ore(recipes, x)

    if ore > AVAILABLE_ORE:
        hi = x
    else:
        lo = x

fuel = lo
print('Part 2:', fuel)
```

Just for fun,
[here's the dependency graph for my puzzle input](misc/day14/chemicals.png).
Quite messy, right?

Day 15 - Oxygen System
----------------------

[Problem statement][d15-problem] — [Complete solution][d15-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.

### Part 1

Intcode *and* maze exploration! Today's problem is pretty fun.

We are given an Intcode program to interact with. The program is capable of
remotely controlling a droid, which is situated somewhere in an unknown area. We
don't know anything about the area surrounding the droid, but we know that there
can be walls in our way, and that our goal is to reach an *oxygen system*. The
area in which the droid can move is in fact a 2D maze, and the droid moves from
one cell to another in four possible directions.

The droid starts on an empty cell, and we can tell it to move in a specific
direction (north, south, east, west), getting back one of three possible
answers:

- `0`: the droid hit a wall and its position has not changed.
- `1`: the droid has moved one step in the requested direction.
- `2`: the droid has moved one step in the requested direction, and its new
  position is the location of the oxygen system.

With this in mind, we need to find the length of shortest possible path (in
steps) from the initial position of the droid to the oxygen system.

Well, if this was just a path finding problem where we are given the maze, that
would have been pretty simple: we could have just ran a simple
[Breadth-first search][algo-bfs] and we would have gotten the answer (in a graph
where all weights are equal BFS finds the shortest path, and there's no need to
use something smarter like Dijkstra's algorithm). In this case though, we have
no clue about how the maze is shaped, and we don't know where the destination
could be.

One pretty silly way of finding the oxygen system would be to just move randomly
throwing random directions to the robot and recording the output until the
oxygen system is found. This however would be very slow and most importantly
wouldn't give us a complete picture of the maze (which is needed if we want to
find the best path, and not just one random path).

Testing out random moves can however give us a rough estimation of what the maze
looks like locally to the starting point, which can be useful to then choose the
appropriate exploration technique. If we check around the starting position, we
notice that the maze is composed of 1-cell wide corridors, and it seems
simply-connected. Here's what it looked like for me:

     ###
    #  @#
    # ##
    #   #
     ## #
      # #
      # #

This is very good to know, since it makes it possible to use the simplest known
maze solving algorithm to explore the maze: the
[wall follower][algo-wall-follower]. From Wikipedia:

> If the maze is simply connected, that is, all its walls are connected together
> or to the maze's outer boundary, then by keeping one hand in contact with one
> wall of the maze the solver is guaranteed not to get lost and will reach a
> different exit if there is one; otherwise, the algorithm will return to the
> entrance having traversed every corridor next to that connected section of
> walls at least once.

We can apply the wall-follower algorithm to explore the whole maze (which means
finding the location of every single wall, and also to find the oxygen system.

Let's parse the input and instantiate our Intcode VM first:

```python
from lib.intcode import IntcodeVM

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)
```

Let's also define some useful constants to make our life easier when dealing
with directions, turns, et cetera:

```python
# Possible droid answers:
WALL, EMPTY, OXYGEN = 0, 1, 2
# Possible directions:
NORTH, SOUTH, WEST, EAST = 1, 2, 3, 4
# Directions after turning clockwise from a known direction:
CLOCKWISE = (None, EAST, WEST, NORTH, SOUTH)
# Directions after turning counter-clockwise from a known direction:
COUNTER_CLOCKWISE = (None, WEST, EAST, SOUTH, NORTH)

# Delta to apply to row and column indexes
# when moving in a certain direction:
MOVE_DELTA = {
    NORTH: (-1, 0),
    SOUTH: (+1, 0),
    EAST: (0, +1),
    WEST: (0, -1)
}
```

To apply the wall follower algorithm (more precisely, the right-hand rule),
we'll do the following:

1. Start facing any direction (we'll use `NORTH`).
2. Try turning clockwise and making one step to see if there's a wall.
3. If there is a wall, try going straight instead (in the currently facing
   direction).
4. If there's no wall, change the current direction to the new one and memorize
   the position as free.
5. After moving, update the current position and the current facing direction.
6. If at any time the current position and direction are the same as the
   starting position and direction, stop: we got back to the beginning and
   therefore explored the whole maze.

The above rules are a little simplified, but the code is clear enough. We will
keep track of which cells are empty (and therefore valid to step on) simply
using a `set`: this is easier than building a matrix (since we don't even know
the size of the maze) or keeping track of *all* kind of cells in a sparse
matrix. When we don't hit a wall, we also check if we found the oxygen system
and return it along with the generated maze when done.

To move the robot in a given direction and check its output we just run one VM
resuming from where we left off and stopping after the first `out` instruction:

```python
def check_move(vm, move):
    return vm.run([move], n_out=1, resume=True)[0]
```

Here's the code for what I just explained:

```python
def wall_follower(vm, startpos, startdir=NORTH):
    curpos, curdir = startpos, startdir
    maze = set()
    oxygen = None

    while True:
        # Try turning right.
        newdir = CLOCKWISE[curdir]
        dr, dc = MOVE_DELTA[newdir]
        newpos = (curpos[0] + dr, curpos[1] + dc)
        cell = check_move(vm, newdir)

        if cell == WALL:
            # If we hit a wall, try going straight instead.
            dr, dc = MOVE_DELTA[curdir]
            newpos = (curpos[0] + dr, curpos[1] + dc)
            cell = check_move(vm, curdir)

            if cell == WALL:
                # If we hit a wall again, rotate 90 degrees counter-clockwise
                # and repeat the whole thing again.
                curdir = COUNTER_CLOCKWISE[curdir]
            else:
                # If we don't hit a wall, save the current position as valid in
                # the maze while also checking if we found the oxygen system.
                if cell == OXYGEN:
                    oxygen = newpos
                maze.add(newpos)

                # Then update the current position.
                curpos = newpos
        else:
            # If we don't hit a wall, save the current position as valid in
            # the maze while also checking if we found the oxygen system.
            if cell == OXYGEN:
                oxygen = newpos
            maze.add(newpos)s

            # Then update current position and direction.
            curpos = newpos
            curdir = newdir

        # Stop if we ever get back to the initial state.
        if curpos == startpos and curdir == startdir:
            break

    return maze, oxygen
```

We can now build our maze and get the position of the oxygen system with a
single function call. It doesn't really matter which position we choose as
starting point, we just need to remember it for later.

```python
startpos = (0, 0)
maze, oxygen = wall_follower(vm, startpos)
```

Now that we have a maze to work with, and we know the position of our goal, we
can simply apply BFS to find the shortest path to the oxygen system. Let's just
first define a simple neighbor function to make our life easier:

```python
def neighbors4(maze, r, c):
    for pos in ((r+1, c), (r-1, c), (r, c+1), (r, c-1)):
        if pos in maze:
            yield pos
```

The BFS implementation is pretty simple and basically identical to the Wikipedia
pseudocode, so I'm not going to spend much time commenting on it. The
[`filter()`][py-builtin-filter] built-in function is used as a convenient way to
avoid already visited neighbors.

```python
def bfs_shortest(maze, src, dst):
    visited = set()
    queue = deque([(0, src)])

    while queue:
        dist, node = queue.popleft()

        if node == dst:
            return dist

        if node not in visited:
            visited.add(node)

            for n in filter(lambda n: n not in visited, neighbors4(maze, *node)):
                queue.append((dist + 1, n))

    return -1
```

The answer is now just one function call away:

```python
min_dist = bfs_shortest(maze, startpos, oxygen)
print('Part 1:', min_dist)
```

### Part 2

For the second part, we are told that once the oxygen system is found, the droid
will activate it to restore the oxygen, which will fill up the maze. We need to
find the amount of minutes that the oxygen takes to reach every cell of the
maze, knowing that the oxygen spreads in all available directions at a speed of
one step per minute.

Well, since we have the full maze, the solution is pretty simple. We can just
apply BFS again, but this time without stopping at any given destination, and
continuing until we reach the farthest cell of the maze. Given the way BFS
works, the last cell we'll check will also be the farthest possible, so we can
just remove the `break` statement from within our loop, and return the ltest
value of `dist` after the `queue` is emptied.

```python
def bfs_farthest(maze, src):
    visited = set()
    queue = deque([(0, src)])

    while queue:
        dist, node = queue.popleft()

        if node not in visited:
            visited.add(node)

            for n in filter(lambda n: n not in visited, neighbors4(maze, *node)):
                queue.append((dist + 1, n))

    return dist
```

Pretty simple, huh? We just solved part 2:

```python
time = bfs_farthest(maze, oxygen)
print('Part 2:', time)
```


Day 16 - Flawed Frequency Transmission
--------------------------------------

[Problem statement][d16-problem] — [Complete solution][d16-solution] — [Back to top][top]

### Part 1

Although the problem statement for today's input is basically a reading
comprehension challenge, the first part of this problem is pretty simple. If
something is unclear, I'd recommend reading the original problem statement
linked above, specially because there are some clear examples that I'm not going
to replicate here.

Given a list of digits, and the pattern `p = (0, 1, 0, -1)`. We need to
transform it *100 times* applying the following steps:

- For each digit at index `i` in the list (`i` starting from `0`), its new
  value is obtained as follows:
    - Calculate a new pattern `P` where each number of `p` is repeated `i+1`
      times.
    - Extend `P` repeating it until its length is at least that of the list of
      digits, and then *skip the first number*.
    - Multiply each `j`-th digit of the list by the corresponding `j`-th number
      of the new pattern `P`.
    - Sum all the numbers together and take the last digit of the sum (positive
      regardless of the sign of the sum). This is the value of the new digit at
      position `i` in the new list.

After applying the above, we need to provide the first 8 digits of the newly
obtained list (concatenated together) as the answer to the problem.

So, after parsing the input (making a copy is useful to reuse the list for part
2):

```python
original = list(map(int, fin.read().strip()))
digits = original[:]
```

The first thing that one might think to generate the repeating pattern each time
is something like the following:

```python
def gen_pattern(n):
    pattern = []

    for p in (0, 1, 0, -1):
        for _ in range(n):
            pattern.append(p)

    return pattern
```

While the above snippet works just fine for small values of `n`, it becomes a
real struggle for larger values, and is very slow either way. Also, the pattern
still needs to be extended, and we then need to skip the first number.

If we take a look at the pattern `(0, 1, 0, -1)`, and read above again:

> - Multiply each `j`-th digit of the list by the corresponding `j`-th number
>   of the new pattern `P`.

This means that:

1. Since we are repeating each number in the pattern a bunch of times, we would
   end up multiplying a bunch of digits by `0`, therefore we could just "ignore"
   them.
2. For the other two pattern values, we can completely ignore the fact that the
   operation to perform is a multiplication, since they are `1` and `-1`
   respectively.

A single iteration (for the `i-th` digit) of the algorithm we need to apply can
then be simplified by skipping chunks of numbers that would end up being
multiplied by zero, and also just sum up all other chunks, adding (`1`) or
subtracting (`-1`) the result from the final sum each time.

In other words, we can do this for each digit:

1. Take `i` as the index of the digit we want to calculate in the new list.
2. Skip the first `i` digits of the list (first pattern number is `0`).
3. Sum the next chunk of digits and add that to the total (second pattern number
   is `1`).
4. Skip the next chunk of digits (third pattern number is `0`).
5. Sum the next chunk of digits and subtract that from the total (fourth pattern
   number is `-1`).
6. Take the total modulo 10 as the new `i-th` digit.

Put the above in a loop that repeats 100 times, and we got our part 1 solution:

```python
length = len(digits)

for _ in range(100):
    old = digits[:]

    for i in range(length):
        # Skip first chunk of digits corresponding to zeroes in the pattern.
        j = i

        step = i + 1
        total = 0

        while j < length:
            # Sum all digits where pattern is 1 and add to total.
            total += sum(old[j:j + step])
            # Skip all digits where pattern is 0.
            j += 2 * step

            # Sum all digits where pattern is -1 and subtract from total.
            total -= sum(old[j:j + step])
            # Skip all digits where pattern is 0.
            j += 2 * step

        digits[i] = abs(total) % 10
```

Now just take the first 8 numbers, concatenate them as a string and that's it.
We can just convert those to string using [`map()`][py-builtin-map] and
[`str()`][py-builtin-str] and then [`join()`][py-str-join] the result.

```python
answer = ''.join(map(str, digits[:8]))
print('Part 1:', answer)
```

### Part 2

For part 2 we are asked to do the same thing as part 1, but with a couple more
rules:

1. Take the first 7 digits of the input as a number `N`.
2. Repeat the input list of integers 10000 (ten thousand) times.
3. After the 100th iteration, skip `N` digits of the result and take the next 8.

As it turns out, repeating the list 10000 times makes things a little bit more
complicated... our previous silly algorithm would take ages with the new input
(which for me is now 6.5 million digits long). We need to find a clever
optimization.

In order to optimize the code, we need to notice something, which becomes clear
after looking at some examples:

    Input signal: 12345678

    1*1  + 2*0  + 3*-1 + 4*0  + 5*1  + 6*0  + 7*-1 + 8*0  = 4
    1*0  + 2*1  + 3*1  + 4*0  + 5*0  + 6*-1 + 7*-1 + 8*0  = 8
    1*0  + 2*0  + 3*1  + 4*1  + 5*1  + 6*0  + 7*0  + 8*0  = 2
    1*0  + 2*0  + 3*0  + 4*1  + 5*1  + 6*1  + 7*1  + 8*0  = 2
    1*0  + 2*0  + 3*0  + 4*0  + 5*1  + 6*1  + 7*1  + 8*1  = 6 <--
    1*0  + 2*0  + 3*0  + 4*0  + 5*0  + 6*1  + 7*1  + 8*1  = 1 <--
    1*0  + 2*0  + 3*0  + 4*0  + 5*0  + 6*0  + 7*1  + 8*1  = 5 <--
    1*0  + 2*0  + 3*0  + 4*0  + 5*0  + 6*0  + 7*0  + 8*1  = 8 <--

    After 1 phase: 48226158
                       ^^^^

In particular, we can see that since we are extending those zeroes, towards the
last part we basically end up with the sum of the last few digits as a result,
because the first `0` in the pattern was repeated so many times that it
annihilated the majority of the digits.

More accurately, for any index `i >= n/2` (where `n = len(digits)`), we end up
just summing the last `n-i` digits. This is clear from the above example, where
it can be seen that:

              ...  = 4
              ...  = 8
              ...  = 2
              ...  = 2
    5 + 6 + 7 + 8  = 6 (abs(26) % 10)
        6 + 7 + 8  = 1 (abs(21) % 10)
            7 + 8  = 5 (abs(15) % 10)
                8  = 8 (abs(8) % 10)

Since the problem tells us to *skip* some digits first, we now don't need to
calculate *all* of them. This is clearly related to what we just noticed: if the
number of skipped digits is higher than `n/2` we can apply this much faster
simplified approach. As it turns out, for our input the number of digits to skip
is actually very large (about 90% of the digits we have), and therefore this
solution can be applied! Clever.

So let's generate the new longer list of digits and skip the first part:

```python
to_skip = int(''.join(map(str, original[:7])))
assert to_skip >= len(original)/2

digits = (original * 10000)[to_skip:]
length = len(digits)
```

We can work our way backwards from the last digit (which is only the sum of
itself), and then simply keep adding digits as we go back in a reverse loop.
This is also known as *cumulative sum* or
[*running total*](https://en.wikipedia.org/wiki/Running_total).

Indexing backwards in Python means using the somehow weird inverse
[`range()`][py-range] notation: `range(n, -1, -1)`, which means "start from `n`
and advance in steps of `-1` until the number right before `-1`.

```python
for _ in range(100):
    for i in range(length - 2, -1, -1):
        digits[i] += digits[i + 1]
        digits[i] %= 10
```

We can improve the performance of the above snippet just a bit by storing the
cumulative sum into a separate variable, limiting the amount of times the
`digits` list is indexed:

```python
for _ in range(100):
    cusum = 0
    for i in range(length - 1, -1, -1):
        cusum += digits[i]
        digits[i] = cusum % 10

answer = ''.join(map(str, digits[:8]))
print('Part 2:', answer)
```

We could also apply this optimization to the second half of the numbers from
part 1 too, but since those are only 650, that would really just save us a few
milliseconds (I nevertheless do this in my complete solution linked above, since
it's straightforward).

### Reflections

Although the solution to part 2 is clever, it still runs pretty slowly on
CPython 3 (don't get scared by the name, it's just the standard Python
implementation). Part 1 plus part 2 take around 17s with CPython 3, while with
[PyPy3](https://pypy.org) the whole thing takes ~430ms, which is far more
reasonable.

To optimize further, we can use the good old Python trick of moving the
algorithm inside a function. "Why would this speed up things?" you say? Because
inside functions the
[`LOAD_FAST`](https://docs.python.org/3/library/dis.html#opcode-LOAD_FAST)
Python opcode is used, which is much faster than the
[`LOAD_GLOBAL`](https://docs.python.org/3/library/dis.html#opcode-LOAD_GLOBAL)
opcode used for global variables (used all over the place in the main body of
the script). Simply moving the second part inside a function gives me a speedup
of about 35% in CPython 3 and 16% in PyPy3, with the new times being ~11s and
~350ms respectively. Conclusion: running Python code in the global namespace
sucks!

With this said, CPython still takes too much for my taste. I am not sure if this
is because there is some other significant optimization to be made (or any other
clever trick) for CPython, but it nonetheless bothers me a bit, particularly
because Advent of Code puzzles are supposed to be solvable in any programming
language (interpreted or not) taking *way less* than that to compute if the
right algorithm is applied (which is the case here).

After looking at other solutions on today's
[Reddit solution megathread](https://www.reddit.com/r/adventofcode/comments/ebai4g),
I noticed various people using compiled programming languages (C, C++, Rust, Go)
and reporting times in the ballpark of ~200ms, very close to my ~350ms on PyPy3.
Usually when the major speedup reason is switching to a compiled language, then
the speedup is much grater (50x, 100x). Therefore it *seems* like we already
have the optimal solution, and CPython is to blame for the poor performance...
sad :(.


Day 17 - Set and Forget
-----------------------

[Problem statement][d17-problem] — [Complete solution][d17-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.

### Part 1

Intcode robots... with a twist! Today we are given an intcode program which we
need to use to interface with a robot which is stuck on an articulated path of
scaffolds. The program works with ASCII values, and it prints a 2D ASCII-art
grid representating the field where the robot operates. Scaffolds are marked
with hashes (`#`) and space with dots (`.`). Our robot is marked with an
arrow-like character depending on the direction it is looking (`^`, `v`, `<`,
`>`).

For the first part, we are asked to localize all scaffold intersections on the
grid, and provide the sum of the product of their coordinates as the answer.

As we can see from the examples, scaffold lines are always one cell apart from
each other, and intersections look like this:

    ..#..........
    ..#..........
    #######...###
    #.#...#...#.#
    #############
    ..#...#...#..
    ..#####...^..

We can start by collecting all values of the grid simply by running the program.
Since the program outputs ASCII values, we can translate the output list into a
string by mapping it with the built-in [`chr()`][py-builtin-chr] function, which
transforms an integer value into an ASCII character, and then use
[`.splitliens()`][py-str-splitlines] to split it into a list of strings (one per
line). Since the program also prints a double newline at the end, let's also
[`.strip()`][py-str-strip] those away.

```python
from lib.intcode import IntcodeVM

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)
out = vm.run()
grid = ''.join(map(chr, out)).strip().splitlines()
```

To check for intersections, we can now just look at each cell that is a
scaffold, and see if all the four adjacent cells are scaffolds. To do this, we
can take advantage of the [`sum()`][py-builtin-sum] function, which treats
boolean values as `0` or `1`, iterating over neighbors cells just by adding or
subtracting `1` to the row and column. We know that intersections cannot be on
the edge of the grid, so no bound checking is needed. Each time we encounter an
intersection, we add the product of its coordinates to the total. While we are
at it, let's also remember the starting position and direction of the robot,
which will be useful for part 2.

```python
NORTH, SOUTH, WEST, EAST = range(4)
EMPTY, SCAFFOLD = '.#'
rows, columns = len(grid), len(grid[0])
answer = 0

for r in range(1, rows - 1):
    for c in range(1, columns - 1):
        if grid[r][c]  == SCAFFOLD:
            n = sum((grid[rr][cc] == SCAFFOLD for rr, cc in ((r+1, c), (r-1, c), (r, c+1), (r, c-1))))

            if n == 4:
                answer += r * c
        elif grid[r][c] in '^v<>':
            startpos = (r, c)
            startdir = '^v<>'.index(grid[r][c])

print('Part 1:', answer)
```

### Part 2

Things get tricky now. We need to help the robot traverse the whole path of
scaffolds without falling (stepping on an empty cell). To do this, we need to
provide a program for the robot to execute.

We need to define three functions, `A`, `B` and `C`. Each function is a list of
basic commands separated by commas:

- `L` means "turn left".
- `R` means "turn right".
- A positive integer number means "go forward" for the specified number of
  steps.

We then need to define a main program as a list of functions to execute (`A`,
`B`, or `C`) separated by commas. Both the main program and the functions need
to be at most 20 characters long (commas included).

After defining the three functions and the main program, we can feed them to the
robot as input, changing the first number in the Intcode program to `2` before
running it. The robot will execute the main program and then output a large
value (not in the ASCII range) as a result, which will be our answer.

This task looks a lot like a very naive compression algorithm. The first thing
we need to do is to translate the entire scaffold path into a list of basic
commands (or moves) accepted by the robot. Once we have the full list, we can
then reduce it by grouping repeating sublists of moves into functions.

After that, let's define the usual bunch of useful enums to simplify changing
direction and position (similar to what we did for part 1 of [day 15][d15]):

```python
# Directions after turning left from a known direction:
LEFT = (WEST, EAST, SOUTH, NORTH)
# Directions after turning right from a known direction:
RIGHT = (EAST, WEST, NORTH, SOUTH)
# Delta to apply to row and column indexes when moving in a certain direction:
MOVE_DELTA = ((-1, 0), (+1, 0), (0, -1), (0, +1))
```

Now we can start traversing te scaffold path. We'll apply the simplest possible
strategy: completely ignore intersections and keep moving straight as long as we
can, incrementing a step counter each time. If we encounter an empty cell ahead
of us, we'll check if we can turn left or right: if we can, we'll take the turn
and reset the counter, otherwise we'll stop because it means we have reached the
end of the path.

To avoid having to deal with any kind of bound checking while traversing the
scaffold path, we'll just pad the entire grid with two additional rows and
columns of empty cells (one at the beginning and one at the end). Then, since we
padded the grid, before we begin we need to add `1` to the previously saved
starting coordinates. We will also convert each move to string (even numbers)
when adding it to the final list of moves, to make it easier to work with
afterwards.

```python
def get_moves(grid, startpos, startdir):
    columns = len(grid[0])

    # Pad the grid with two more empty lines and columns.
    grid = [EMPTY * columns] + grid + [EMPTY * columns]
    for i in range(len(grid)):
        grid[i] = EMPTY + grid[i] + EMPTY

    r, c = startpos
    curdir = startdir
    moves = []
    steps = 0
    r += 1
    c += 1

    while 1:
        # Try moving straight in the current direction.
        dr, dc = MOVE_DELTA[curdir]
        newr, newc = r + dr, c + dc

        # If possible, update the counter and skip to the next iteration.
        if grid[newr][newc] == SCAFFOLD:
            steps += 1
            r, c = newr, newc
            continue

        # Otherwise, try turning left.
        newdir = LEFT[curdir]
        dr, dc = MOVE_DELTA[newdir]
        newr, newc = r + dr, c + dc

        # If possible, remember the turn.
        if grid[newr][newc] == SCAFFOLD:
            turn = 'L'
        else:
            # Otherwise, try turning right.
            newdir = RIGHT[curdir]
            dr, dc = MOVE_DELTA[newdir]
            newr, newc = r + dr, c + dc

            # If possible, remember the turn.
            if grid[newr][newc] == SCAFFOLD:
                turn = 'R'
            else:
                # Otherwise give up, we reached the end.
                # Add the last step counter and stop.
                moves.append(str(steps))
                break

        # Save the number of steps we made and the turn we took after them.
        if steps > 0:
            moves.append(str(steps))
        moves.append(turn)

        # Update position and direction and reset the counter.
        r, c = newr, newc
        curdir = newdir
        steps = 1

    return moves
```

The result of the above function will be a long list of moves, like for example
`['R', '6', 'L', '6', 'L', '10', ...]`.

We now need to "compress" recurring sequences of moves into three functions. We
know that functions need to be at most 20 characters long (including commas) and
that we can only use functions in the main program, so we cannot leave any move
out.

Since all moves need to belong to a function, this means that the first function
we want to find will inevitably correspond with the first few moves of our list.
In other words, it means that `func_a = moves[:la]` for some length `la` that we
still need to find. After that, we could then have other occurrences of
`func_a`, followed by the second function. In other words:
`func_b = moves[sb:sb + lb]` for some starting position `sb` (after `la`) and
some length `lb`. The same goes for the last function: after any additional
occurrence of `func_a` and `func_b`, we'll have `func_c = moves[sc:sc + lc]` for
some starting position `sc` (after `sb + lb`) and some length `lc`.

Here's an example:

    0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18 19 20 21
    R  5  R  3  L  8  R  4  L  8  R  4  R  5  R  3  R  6  L  8  L  6  ...
    ----------  ----------  ----------  ----------  ----------------
    func_a      func_b      func_b      func_a      func_c

In this example we have `la = 4`, `sb = 4`, `lb = 4`, `sc = 16` and `lc = 6`.
The important thing to notice is that in order to find `func_c` we skipped one
more occurrence of `func_a` and one more of `func_b`. This is the key point to
consider when searching for the three functions.

Trying to solve this with pen and paper really helps understanding the
algorithm, so if the following doesn't seem clear at first, just try writing it
down solving it by hand a couple of times.

In order to find the functions, we can use three nested `for` loops to find the
correct `la`, `lb` and `lc`. In between the three loops, we will skip already
found functions advancing the starting positions `sb` and `sc`. In the innermost
loop, we'll try to match the whole list of moves one function at a time, and if
we get to the end without any mismatch, we will have found our three functions.

The length in characters of each function needs to be at most `20`, so this
means a maximum of `10` moves (assuming 1 character long moves and 9 commas to
separate them). A function of only one move also doesn't seem to make sense. We
will therefore search for `la`, `lb` and `lc` in a `range(2, 11)`. To also make
sure not to cross the 20 chars limit, we will check the character length of the
the functions too.

Let's get into the code, we'll again define a function to make it cleaner:

```python
def find_functions(moves):
    for la in range(2, 11):
        # Pick a func_a.
        func_a = moves[:la]

        # Skip all successive occurrences of func_a.
        sb = la
        while moves[sb:][:la] == func_a:
            sb += la

        for lb in range(2, 11):
            # Pick a func_b.
            func_b = moves[sb:sb + lb]

            # Skip any additional occurrences of func_a or func_b.
            sc = sb + lb
            while 1:
                if moves[sc:][:la] == func_a:
                    sc += la
                elif moves[sc:][:lb] == func_b:
                    sc += lb
                else:
                    break

            for lc in range(2, 11):
                # Pick a func_c.
                func_c = moves[sc:sc + lc]

                # Try to get to the end only matching these three functions.
                ok = True
                i = sc
                while i < len(moves):
                    if moves[i:][:la] == func_a:
                        i += la
                    elif moves[i:][:lb] == func_b:
                        i += lb
                    elif moves[i:][:lc] == func_c:
                        i += lc
                    else:
                        ok = False
                        break

                if ok:
                    A = ','.join(func_a)
                    B = ','.join(func_b)
                    C = ','.join(func_c)

                    # Perform a final check on the real lengths of the functions.
                    if len(A) <= 20 and len(B) <= 20 and len(C) <= 20:
                        return A, B, C
```

We now have all we need to solve the problem. After getting the moves and
finding the three functions, we can just convert the original "uncompressed"
list of moves into a string of comma separated commands, and just
[`.replace()`][py-str-replace] every occurrence of the functions we just found
with their corresponding letter.

```python
moves = get_moves(grid, startpos, startdir)
A, B, C = find_functions(moves)
main = ','.join(moves).replace(A, 'A').replace(B, 'B').replace(C, 'C')
```

We can now feed the main program and the functions to our Intcode-powered robot,
along with a `n` to signal that we do not want debug information, and then
collect the last output value as the answer (let's also not forget to change the
first value of the program to `2`).

```python
vm.reset()
vm.code[0] = 2
robot_prog = list(map(ord, '{}\n{}\n{}\n{}\nn\n'.format(main, A, B, C)))
answer = vm.run(robot_prog)[-1]
print('Part 2:', answer)
```


Day 18 - Many-Worlds Interpretation
-----------------------------------

[Problem statement][d18-problem] — [Complete solution][d18-solution] — [Back to top][top]

### Part 1

I hope you're ready for some path finding and exploration algorithms, because oh
boy, things are going to get wild today! Hardest puzzle so far, and (hopefully)
maybe even *the* hardest this year. Prepare for a long walkthrough, let's dive
in!

We are given an ASCII art maze with empty cells (`.`), walls (`#`), keys
(lowercase letters) and doors (uppercase letters). We (`@`) are stuck in the
middle of the maze, and need to find a way to collect *all* the keys, in the
minimum amount of steps possible. That number of steps is the answer to the
puzzle.

The maze itself is a pretty standard 2D maze where we can only move in four
directions (up, down, left, right) and not in diagonal. There is a twist though:
we cannot pass through a door unless we collect the corresponding key first.
Each uppercase letter in the maze is a door which is opened by the corresponding
key, which is a lowercase letter. In other words, a door can be treated like a
wall `#` if we don't have its key, and like an empty cell `.` otherwise.

It's important to familiarize with the problem before starting to think about a
solution right away, therefore you should probably read the original problem
statement (linked above), which also contains examples. Done? Okay, let's go!

There are a lot of points in the maze which are empty spaces. To make the graph
simpler, and therefore also speed-up any exploration that we are going to run on
it, we can build a simpler graph which only has keys, doors and the starting
position as nodes. Every edge of this graph will have a weight representing the
minimum number of steps needed to move between the two nodes.

Our graph will be a simple dictionary in the form `{node: [(neighbor,
weight)]}`, that is a dictionary that associates each node to a list of
neighbors and the minimum steps needed to reach them. To create such a list for
each node, we will need a function that, given the position of a node in the
maze, can tell us which other nodes are directly reachable from it (i.e.
adjacent) and with how many steps (i.e. the weight of the edge). For now, we
will just pretend that we already magically have a function `find_adjacent()`
that does this for us: it takes a position as argument and returns a list of
nodes and distances that are reachable from that position.

Our `build_graph()` function will then iterate over the given maze grid and call
`find_adjacent()` each time it encounters a node, then store this info in the
graph dictionary. Very straightforward really. Other than this, we will also
extract the coordinates of the starting position (which becomes useful for part
2).

```python
def build_graph(grid):
    graph = {}
    startpos = None

    for r, row in enumerate(grid):
        for c, cell in enumerate(row):
            if cell not in '#.':
                graph[cell] = find_adjacent(grid, (r, c))

                if cell == '@':
                    startpos = (r, c)

    return graph, startpos
```

Nice, now we need to write `find_adjacent()`. Since we are in a 2D grid where we
are only allowed to move up, down, left and right and the distance between cells
is always `1`, we can use [Breadth First Search][algo-bfs] to explore it.
Starting from a given position, we will build
[a queue](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)) of nodes to
visit with their associated distances. Initially, this queue will only contain
the neighbor cells around the starting position, with a distance of `1`. We will
use a [`deque`][py-collections-deque] from the [`collections`][py-collections]
module as our queue. A `deque` (double-ended queue) is nothing more than a list
that supports very fast append and remove operations from each of its ends.

To determine which neighbors of a cell can be visited (excluding walls), we can
write a simple helper function (we'll make it a generator, since it's usually
faster, more pythonic and also 100% cooler):

```python
def neighbors4(grid, r, c):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        rr, cc = (r + dr, c + dc)

        if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
            if grid[rr][cc] != '#':
                yield (rr, cc)
```

Now, back to BFS. We will pop one cell at a time from the queue. Each time we
do, we'll mark that cell as visited by adding it to a `visited` set. Then, if it
is a door or a key, we'll add its identifying letter to a list of found nodes,
otherwise we'll add all its neighbors (that we have not visited) to the queue as
well. When the queue becomes empty, we will have visited all immediately
reachable objects from the source position.

Here it is:

```python
def find_adjacent(grid, src):
    queue = deque()
    visited = {src}
    found = []

    # Start by adding all neighbors of the source to the queue, with a distance of 1 step.
    for n in neighbors4(grid, *src):
        queue.append((1, n))

    while queue:
        # Get the next node to visit and its saved distance.
        dist, node = queue.popleft()

        if node not in visited:
            visited.add(node)

            cell = grid[node[0]][node[1]]

            # Check if this cell is a key or door...
            if 'a' <= cell <= 'z' or 'A' <= cell <= 'Z':
                # ... and if it wasn't already found.
                if cell not in found:
                    # If so, add it to the found list along with its distance.
                    found.append((cell, dist))
                    continue

            # Otherwise, add all unvisited neighbors to the queue with a distance increased of 1 step.
            for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
                queue.append((dist + 1, neighbor))

    return found
```

Done, now our `find_adjacent()` function returns a list of adjacent nodes and
minimum steps to reach them. Moreover, given the way we are exploring, the list
will be sorted by increasing distance. It is also important to note that the
list of adjacent nodes will never include the start (`@`), as we are only
interested in starting from there, not going back to it. Here's an example:

```python
>>> grid = [
        '#############',
        '#...@.......#',
        '#.#########.#',
        '#..a.B.c#b.A#',
        '#############',
    ]

>>> find_adjacent(grid, (1, 4))
[('a', 7), ('A', 9)]
```

Now we can parse our maze into a graph. Let's test it out on the above example:

```python
>>> G, startpos = build_graph(grid)
>>> G
{'@': [('a', 7), ('A', 9)],
 'A': [('b', 2), ('a', 16)],
 'B': [('c', 2), ('a', 2)],
 'a': [('B', 2), ('A', 16)],
 'b': [('A', 2)],
 'c': [('B', 2)]}
>>> startpos
(1, 4)
```

The above corresponds to a graph like this:

      a--B--c
     / \
    @---A--b

Cool! Now back to the real problem: this problem of finding all the keys looks
like the
[traveling salesman problem](https://en.wikipedia.org/wiki/Travelling_salesman_problem),
except we don't care about going back to the start, and we have "obstacle"
nodes in our way (the doors).

The problem of visiting every single node with the minimum total distance is
[NP-complete](https://en.wikipedia.org/wiki/NP-completeness), meaning that it
can only be solved by trying all possible different paths. Our problem is also
NP-complete.

A naive recursive bruteforce solution is therefore not only correct, but also
the best possible way to solve the problem (in terms of time complexity). Given
an initial source and set of found keys (which will initially be empty), we want
to do the following:

1. If we found all the keys, the minimum number of steps needed to reach the
   solution is `0` (we already have the solution), so we'll return `0`.
2. Otherwise, for every key `k` that can be reached from the start position, we
   will make a recursive call to determine what's the required number of steps
   to get all the remaining keys having moved to the position of `k` and having
   taken `k`. We will then take the smallest of those and return it.

What keys can we reach starting from a given node and having a certain set of
already collected keys? And with how many steps? We still don't know yet, but as
we did before, we can solve this one function at a time. For now, let's again
make a "leap of faith" and pretend that we already magically have a function
`reachable_keys()` that takes care of this.

Let's write the exploring function. It takes more to explain it than to write
it, really. Here it is:

```python
from math import inf as INFINITY

def minimum_steps(src, n_find, mykeys=set()):
    # src   : starting node
    # n_find: number of keys that I still need to find
    # mykeys: set of keys that I already found

    if n_find == 0:
        # I know the solution, it's 0 since I already found all the keys.
        return 0

    best = INFINITY

    # I don't know the solution, but I can find it by checking every
    # possible move recursively.
    for k, d in reachable_keys(src, mykeys):
        # Take k and move there.
        newsrc  = k
        newkeys = mykeys | {k}
        dist    = d

        # See what's the solution to find all other keys having taken k.
        dist += minimum_steps(newsrc, n_find - 1, newkeys)

        # Update the current solution if this one is better.
        if dist < best:
            best = dist

    return best
```

It seems pretty clear that all we have left do now is writing a good
`reachable_keys()` function. We have a graph with weighted edges: [Dijkstra's
algorithm][algo-dijkstra] is for sure the easiest way to find all reachable keys
and the smallest amount of steps to reach each of them.

We can adapt the function we wrote for [day 6][d06] part 2. There are three main
differences from day 6 here:

1. We have different weighs on each edge: for this we can just add the right
   weight instead of just `1` each time we add a neighbor to the queue.
2. We do not want to reach a specific node, but we want to explore all reachable
   nodes: for this we can just keep going until the queue is empty, effectively
   removing the `break`, and add each key we find to a list.
3. We can pass through a door only if we have the corresponding key: for this,
   we will pass the set of keys as an argument, and check it each time we see
   a door.

Sounds intricate, but it's simpler than it looks. Let's make the code mainly
speak for itself, with the help of some comments.

```python
import heapq

def reachable_keys(src, mykeys):
    # src   : starting node
    # mykeys: set of keys that I already found

    queue = []
    distance = defaultdict(lambda: INFINITY)
    reachable = []

    # Start by adding all neighbors of the source to the queue,
    # with the weight of the edge as distance.
    for neighbor, weight in G[src]:
        queue.append((weight, neighbor))

    # Initialize the heap structure to keep it sorted.
    heapq.heapify(queue)

    while queue:
        # Get the next nearest node to visit and its saved distance.
        dist, node = heapq.heappop(queue)

        # If it's a key and we don't already have it...
        if node.islower() and node not in mykeys:
            # Add it to the reachable keys also saving the distance.
            reachable.append((node, dist))
            # Proceed to the next in queue, don't explore neighbors.
            continue

        # If we do not have key for a door...
        if node.lower() not in mykeys:
            # Proceed to the next in queue, don't explore neighbors.
            continue

        # Otherwise (no new key and no locked door) for each neighbor...
        for neighbor, weight in G[node]:
            new_dist = dist + weight

            # If the distance to reach it is better than what we already
            # have, add it to the queue.
            if new_dist < distance[neighbor]:
                distance[neighbor] = new_dist
                heapq.heappush(queue, (new_dist, neighbor))

    return reachable
```

We now have everything we need. Computing the answer is only a few function
calls away:

```python
maze = tuple(list(l.strip()) for l in fin)

G, startpos = build_graph(maze)
total_keys  = sum(node.islower() for node in G)
min_steps   = minimum_steps('@', total_keys)

print('Part 1:', min_steps)
```

*But wait!* We run the program and it seems to hang indefinitely... what did we
do wrong? Is it stuck in a loop? Is it too slow? Is recursion stabbing us in the
back? What is going on?

As it turns out, like I said before, since the only way to find the answer is to
try all different paths, this means trying around `total_keys!` paths in the
worst case (that exclamation mark there stands for "factorial"). We have 26 keys
in our input, which means at most 26! = 403291461126605635584000000 possible
paths. Well... that doesn't look like a reasonable number at all, we would
probably reach the heat death of the universe before my poor Intel i7-870
desktop spits out an answer.

To work this out, we need to notice a couple of interesting facts first:

1. If we ever find ourselves at the same node with the same set of already
   collected keys, the set of reachable keys will always be the same (and with
   the exact same distances too). Therefore for the same arguments, the
   `reachable_keys()` function will always return the same result.
2. If we ever find ourselves at the same node with the same keys, the minimum
   number of steps to collect all the remaining keys will always be the same.
   Therefore for the same arguments, the `minimum_steps()` function will always
   return the same result.

As it turns out, the `reachable_keys()` and `minimum_steps()` functions will get
called a very large amount of times, and due to the nature of our exploration,
most of the times they will end up being called with the exact same arguments.
This means that they will do the same heavy computation each time, resulting in
an enormous amount of unneeded work.

We can associate each unique value of arguments with their respective result,
for both the functions. To do this, the simplest way is to use a dictionary
`{arguments: result}`, with a tuple of the arguments as key. Each time the
function is called we can look up the dictionary: if we already have a solution,
then we'll return it, otherwise we'll do the computation and add it to the
dictionary before returning it.

The technique of caching the result of a function based on its arguments to
avoid to reapeat work is called
[*memoization*](https://en.wikipedia.org/wiki/Memoization). The Wikipedia page
does a good job of explaining why memoization is important in recursive
functions like this, so I'd suggest to read it in case you are not familiar with
the concept. In terms of Python code, it means something like this:

```python
def expensive_function(a, b, c, cache={}): # The cache={} dictionary here is only
    if (a, b, c) in cache:                 # created once at the time of definition
        return cache[a, b, c]              # of the function! If we do not pass
                                           # any value to overwrite it, it keeps
    # compute result...                    # being the same dictionary.

    cache[a, b, c] = result
    return result

expensive_function(1, 2, 3) # first call, takes a while
expensive_function(1, 2, 3) # instantaneous, returns cached value
```

Python (>= 3.2) also has a very cool way of painlessly handling memoization. All
we need is the [`@lru_cache`][py-functools-lru_cache] decorator from the
[`functools`][py-functools] module, which automagically does all of the above
for us with a single line of code.
[LRU](https://en.wikipedia.org/wiki/Cache_replacement_policies#Least_recently_used_(LRU))
is a caching strategy that discards the least recently used value when too many
values are cached.

```python
@lru_cache(maxsize=1000)
def expensive_function(a, b, c):
    # compute result...
    return result
```

The `maxsize` argument of `@lru_cache` is the maximum number of most recently
used results to keep, and it can be set to `None` for unlimited.

There is still *one little problem* though. Since `@lru_cache` too uses a
dictionary to cache arguments and results, all the arguments need to be
hashable. However in our functions the `mykeys` argument is a `set`, and as it
turns out, since a `set` is a mutable collection, it cannot be hashed. For this,
the [`frozenset`][py-frozenset] comes to the rescue! It's basically the same as
a `set`, but it does not support removing or adding values: it is immutable, and
therefore can be hashed. Given the way we have written our functions, we just
need to change the only occurrence of `set()` in the definition of
`minimum_steps()` and everything will work out of the box. Let's be generous and
cache ~1 million most recently used values for each function:

```python
@lru_cache(2**20)
def minimum_steps(src, n_find, mykeys=frozenset()):
    # ... unchanged ...

@lru_cache(2**20)
def reachable_keys(src, mykeys):
    # ... unchanged ...
```

Let's try it again:

```python
min_steps = minimum_steps('@', total_keys)
print('Part 1:', min_steps)
```

And it's instantaneous! We now have a very clean part 1 solution. One last thing
that we can do to make things even faster, is to also cache the `distance`
dictionary used for Dijkstra in `reachable_keys()`, since for a given set of
keys it will always be the same. We can do this by creating a dummy function
that defaults to returning a `defaultdict(lambda: INFINITY)`, and just decorate
it with `@lru_cache`:

```python
@lru_cache(2**20)
def distance_for_keys(keys):
    return defaultdict(lambda: INFINITY)

@lru_cache(2**20)
def reachable_keys(src, mykeys):
    queue = []
    distance = distance_for_keys(mykeys)
    reachable = []

    # ... unchanged ...
```

This cuts down execution time by another 30% on my machine, not bad. Let's move
on to part 2 and see what comes next.

### Part 2

The maze splits into four different sub-mazes. Each of the four neighbor cells
of the starting position becomes a wall, and we now have four different bots,
placed on the four *diagonal* neighbor cells of the original starting position.

Here's an example to make it clearer:

    #############       #############
    #.....#b....#       #.....#b....#
    #B###.#####A#       #B###.#####A#
    #..c#.......#       #..c#@#@....#
    #####.@.#####  ==>  #############
    #.......#...#       #....@#@#...#
    #####.#.#.#C#       #####.#.#.#C#
    #a....#...#d#       #a....#...#d#
    #############       #############

Only one robot can be moved at once, but when a robot collects a key, the key is
shared: it opens the relative door instantly even if it's in another quadrant.
We need to find the minimum number of steps for the four robots to collect all
the keys in the maze.

Okay, very interesting. Let's think about what these new rules mean in terms of
modifications to our functions and data structures used for part 1:

1. The fact that new maze is now split into four smaller isolated mazes is
   really not a problem given the way we generate the graph. We can still use
   the same function to build our graph, editing the grid first to reflect the
   new situation. The resulting graph dictionary will include information for
   all the four isolated graphs.
2. The path finding algorithm implemented in `reachable_keys()` does not change,
   we will only need to call it multiple times now (one for each bot).
3. The recursive solution function `minimum_steps()` needs to be changed. In
   addition to not knowing which key is best to pick at any given time, we now
   also don't know which bot is best to move. *However* we can easily test all
   of them just like we did for different keys!

Point number 3 is the culprit here: the only *real* difference from part 1 is
that now our search space is multiplied by the number of robots. In other words,
we have to do what we already do for the keys once for each robot. In terms of
code, this means adding another `for` loop in the function, and taking a
collection of starting positions instead of just a single one.

Since a source in our graph is identified by a single character, if we pass a
string to our updated `minimum_steps()` function, we can treat each character as
a source iterating over the string without a problem, and a simple string
`.replace()` is all we'll need to move one of the bots.

Here's the updated function:

```python
@lru_cache(2**20)
def minimum_steps(sources, n_find, mykeys=frozenset()):
    if n_find == 0:
        return 0

    best = INFINITY

    # For every robot...
    for src in sources:
        # For every key reachable by that robot...
        for k, d in reachable_keys(src, mykeys):
            # Take the key and move the robot there.
            newkeys    = mykeys | {k}
            newsources = sources.replace(src, k)
            dist       = d

            # See what's the solution to find all other keys having
            # taken k with this particular robot.
            dist += explore(new_sources, n_find - 1, new_keys)

            # Update the current solution if this one is better.
            if dist < best:
                best = dist

    return best
```

You know what's the cool part? Given the way we call the above function for part
1 (`minimum_steps('@', total_keys)`), the part 1 code doesn't even need to be
edited: a string of length 1 can already be iterated over!

We now need to edit the grid removing the starting position and adding the new
starting positions and walls. This is where the `startpos` that was previously
returned by `build_graph()` becomes useful.

```python
# Make left, right, top, bottom cells walls.
for r, c in neighbors4(maze, *startpos):
    maze[r][c] = '#'

# Remove original position (make it a wall) and add four new starting positions.
startr, startc = startpos
maze[startr][startc] = '#'
maze[startr - 1][startc - 1] = '1'
maze[startr + 1][startc - 1] = '2'
maze[startr + 1][startc + 1] = '3'
maze[startr - 1][startc + 1] = '4'
```

We use the characters `'1'` through `'4'` here just because the nodes in our
graph are identified by their corresponding character on the grid, and we want
to have four different identifiers of course.

Since we are going to re-start the search using the new graph, first we'll need
to clear all the data previously cached by `@lru_cache`. This can be easily done
by calling `.cache_clear()` on every decorated function that we used.

```python
minimum_steps.cache_clear()
reachable_keys.cache_clear()
distance_for_keys.cache_clear()
```

We can now re-build the graph using the updated maze and run the solution
starting from all the sources identified by the characters in the string
`'1234'`.

```python
G, _      = build_graph(maze)
min_steps = explore('1234', total_keys)
print('Part 2:', min_steps)
```

Beautiful! Another two stars to add to our collection.


Day 19 - Tractor Beam
---------------------

[Problem statement][d19-problem] — [Complete solution][d19-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `intcode_oneshot()` function](lib/intcode.py) to solve this
puzzle, which is a very simple and fast Intcode VM implementation, useful if I
need to restart the same program over and over.

### Part 1

We are once again in a 2-dimensional space, and we are projecting a beam (let's
see it as a beam of light).

The beam starts at the top left (coordinates `(0, 0)`) and "lights up" cells in
a cone, like this:

         X
       0-->     9
      0#.........
    Y |.#........
      v..##......
       ...###....
       ....###...
       .....####.
       ......####
       ......####
       .......###
      9........##

The problem is that we cannot see the beam. The only thing we can do to
determine if a cell is hit by the beam or not is to deploy a drone to go check
that cell's coordinates and report back to us.

We are given an Intcode program to run: this program takes two inputs (the two
coordinates `x` and `y` to check) and outputs a single value: `0` or `1` whether
the cell at the specified coordinates is hit by the beam or not.

Our task for the first part of the problem is to determine how many cells are
hit by the beam in the 50 by 50 square from `(0, 0)` to `(49, 49)`.

Let's get the Intcode program as always:

```python
program = list(map(int, fin.read().split(',')))
```


We now just need to write two for loops from `0` to `49`:

```python
total = 0
for x in range(50):
    for y in range(50):
        total += next(intcode_oneshot(program, (x, y)))

print('Part 1:', total)
```

My `intcode_oneshot()` function is actually a generator, hence the need for
[`next()`][py-builtin-next] to get the first (and only) output value.

If we want to play it cool we can wrap the program execution in a little helper
function and write a one-liner solution using [`map()`][py-builtin-map] and
[`sum()`][py-builtin-sum], generating all the possible coordinates with the
[`product()`][py-itertools-product] from the [`itertools`][py-itertools] module.

```python
from itertools import product

def run(inp):
    return next(intcode_oneshot(program, inp))

total = sum(map(run, product(range(50), range(50))))
print('Part 1:', total)
```

The `run()` function above will come in handy very soon for part 2.

### Part 2

We are now asked to find a spot *inside* the beam where a square of 100 by 100
cells can fit. This means something like this (using a 5 by 5 square for
simplicity):

    #.........................
    .#........................
    ..##......................
    ...###....................
    ....###...................
    .....####.................
    ......#####...............
    ......######..............
    .......#######............
    ........###OOOOO..........
    .........##OOOOO##........
    ..........#OOOOO###.......
    ...........OOOOO#####.....
    ...........OOOOO#######...
    ............############..

It's quite obvious that the square could fit inside the beam even farther away
from the origin (since the beam always expands), but we need to fit the square
as close as possible to the origin `(0, 0)`. Our answer will be `x * 10000 + y`,
where `x` and `y` are the coordinates of the top left corner of the square.

To solve this, we can search for a vertical line of at least 100 cells that are
hit by the beam, and then, starting from the 100th cell from the bottom, check
if a line of at least 100 horizontal cells is hit by the beam.

Something like this:

              1111111111222222
    01234567890123456789012345
    #.........................
    .#........................
    ..##......................
    ...###....................
    ....###...................
    .....####.................
    ......###AA...............
    ......###ABB..............
    .......##AB###............
    ........#ABCCCCC..........
    .........ABC######........
    ..........BC#######.......
    ...........C#########.....
    ...........C###########...
    ............############..

We can see in the simplified example above that the first column containing 5
cells hit by the beam (marked with `A`) does not however have enough space on
the right side, and the same goes for the second column (marked with `B`). The
third one (marked with `C`) is the first column to also have enough space on its
right, and therefore fits the square nicely. In the case of the columns marked
with `A` and `B` we have a width of 2 on the right, while in the case of the
column marked with `C` we have a width of 5.

The simplest strategy to find the right column is to start from the top, then
proceed down until we find the first cell hit by the beam, and keep going until
we find the last cell. From there, go up 100 cells to the position of the
potential top-left corner, and then start looking right one cell at a time: if
at least 100 cells are available on the right, we have a good spot for the
square to fit.

Let's write a function that given an `x` coordinate checks the maximum width
that is available on the right side of the column. We'll start from the top
(`(x, 0)`), going down until we find the beam, then keep going down until we
find the end, and get 100 cells back up. After that, if we're still inside the
beam, we'll save the `y` coordinate (as it is the `y` value of the potential top
left corner of the square) and start moving to the right, until we get out of
the beam. For all these iterations we can make good use of
[`count()`][py-itertools-count] from the [`itertools`][py-itertools] module,
which is just like a `range()`, but counts to infinity. We'll also make the
function return the `y` value of the top left corner.

```python
from itertools import count

def get_width(x):
    # Start from the top and continue until we hit the beam.
    for top in count(0):
        if run((x, top)) == 1:
            break

    # If there's no beam 100 cells down, the column is too short.
    if run((x, top + 100)) == 0:
        return 0, 0

    # Advance until the end of the beam.
    for bottom in count(top + 100 + 1):
        if run((x, bottom)) == 0:
            break

    # Save the y coordinate of the potential top left corner.
    y = bottom - 100

    # Advance to the right until we get out of the beam.
    for width in count(1):
        if run((x + width, y)) == 0:
            break

    # Return the width we just found and the saved coordinate.
    return width, y
```

A naive solution to the problem would be to just scan every single column with a
`for`, starting from a small number (the first few columns don't seem to have
cells hit by the beam for some reason) and calling `get_width()` until we get a
width greater or equal to 100:

```python
for x in count(50):
    width, y = get_width(x)
    if width >= 100:
        break

answer = x * 10000 + y
```

This solution however is not optimal at all. Since the beam always increases in
height and width, we can apply [binary search][algo-binsrc] to find the column
we want way faster.

```python
def bin_search(lo, hi):
    best = None

    while hi - lo > 1:
        x = (lo + hi) // 2

        width, y = get_width(x)

        if width > 100:
            hi = x
            best = (x, y)
        elif width < 100:
            lo = x

    return best
```

We can run the above with `lo = 0, hi = 10000` since the solution asks for
`x * 10000 + y`, which is a clear indicator of the fact that `x` must be
below 10000. There's a little problem though: our `get_width()` function is not
really monotonically increasing. Instead, some times we encounter weird local
maximums, like the following:

    x     width
    1070  97
    1071  99  <-- local max
    1072  98
    1073  100 <-- local max
    1074  99
    1075  101 <-- local max
    1076  100
    1077  102 <-- local max
    1078  101

This means that our `bin_search()` function could end up finding, for example,
`x = 1075, width = 101`, since it is right after `x = 1074, width = 99`. This is
no problem though: we can use the binary search to look for a good enough
solution, and then just check if there's a better solution in the neighborhood
(a few steps earlier).

```python
# Find a good enough solution.
approx_x, approx_y = bin_search(10, 9999)
best_x, best_y = approx_x, approx_y

# Refine looking back a few steps.
for x in range(approx_x, approx_x - 10, -1):
    width, y = get_width(x)

    if width >= 100:
        best_x, best_y = x, y

answer = best_x * 10000 + best_y
print('Part 2:', answer)
```

And there it is, *almost* just binary search. This runs an order of magnitude
faster than a linear search from the start, and we have our part 2 solution in
a fraction of a second!


Day 20 - Donut Maze
-------------------

[Problem statement][d20-problem] — [Complete solution][d20-solution] — [Back to top][top]

### Part 1

Okay, we're getting pretty insane with graphs. Today was a very interesting
puzzle, a recursive maze with portals!

We are given yet another 2D ASCII art maze. Same as other days, dots `.` are
empty space and hashes `#` are walls. As usual, moving from an empty cell to
another only costs 1 step, and we can only move in four directions (up, down,
left, right).

What changes now is that there are *portals*. The maze is shaped like a donut
(well, a rectangular donut), and on each of the two sides (internal and
external) we have two-letter labels. Each dot `.` near a label is a portal
(there is only one dot near each label). Each portal appears two times: one on
the inside and one on the outside of the donut maze. The only two portals that
do not appear twice are `AA` and `ZZ`, which are, respectively, our source and
destination.

Portals work pretty simply: when standing on the empty cell corresponding to a
portal, you can decide to take it, and teleport to its sibling (with the same
label) on the other side of the donut. Doing this only takes 1 step. You can see
where this is going... we are asked to find the minimum number of steps to go
from `AA` to `ZZ`, considering that we can pass through portals as well as just
walk through the corridors like a classical maze.

Okay, let's parse the input right away. We'll just build a big `tuple` of
strings, only stripping newlines. Keeping track of the highest row and column is
also useful, we'll see why in a moment.

```python
grid = tuple(l.strip('\n') for l in fin)
MAXROW, MAXCOLUMN = len(grid) - 1, len(grid[0]) - 1
```

Well, first of all, we can transform the maze in a simple undirected weighted
graph, just like we did for [day 18][d18] part 1. The code is basically the
same, with the exception that we now have two-letter labels, and not single
letter ones. Labels are also just *next* to portals, they are not the portals
themselves. Our graph will be in the form
`{portal_label: [(neighbor, distance), (...)]}`.

First, let's just copy paste our generator function (also from day 18) to find
all neighbors of a cell in the grid. In addition to walls `#`, we also need to
avoid the spaces without considering them neighbors, since the grid we are given
is full of them (of course, being a donut).

```python
def neighbors4(grid, r, c):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        rr, cc = (r + dr, c + dc)

        if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
            if grid[rr][cc] not in '# ':
                yield (rr, cc)
```

A function that is able to detect if a cell is a portal, and parse its label,
would be very useful. To do this we can just check if:

1. The cell is a dot `.`.
2. There is a neighbor cell that is an uppercase letter.
3. That cell also has another neighbor cell that is an uppercas letter.

In order to reconstruct the label we can then look at which of the two letters
comes first (either is above or to the left), and also at the position of the
outermost letter: if it's on the edge of the grid, then the label is an outside
label. This is where the two global variables `MAXROW` and `MAXCOLUMN` that we
defined earlier are useful.

Since we have to keep track of the side of the portals (inside or outside),
let's create a [`namedtuple`][py-collections-namedtuple] to represent them. We
don't really care about the position of a portal in the final graph that we are
going to build, so we can just omit it.

```python
Portal = namedtuple('Portal', ['label', 'side'])

def portal_from_grid(grid, r, c):
    if grid[r][c] != '.':
        return None

    # Get first letter.
    valid = False
    for n1r, n1c in neighbors4(grid, r, c):
        letter1 = grid[n1r][n1c]
        if 'A' <= letter1 <= 'Z':
            valid = True
            break

    # If no letters nearby, the position (r, c) is not a portal.
    if not valid:
        return None

    # Get the second letter.
    for n2r, n2c in neighbors4(grid, n1r, n1c):
        letter2 = grid[n2r][n2c]
        if 'A' <= letter2 <= 'Z':
            break

    # Order the letters in the right way (top to bottom and left to right).
    if n2r > n1r or n2c > n1c:
        key = letter1 + letter2
    else:
        key = letter2 + letter1

    # Check if the outermost letter is on the edge. If so, the label is external.
    if n2r == 0 or n2c == 0 or n2r == MAXROW or n2c == MAXCOLUMN:
        return Portal(key, 'out')

    return Portal(key, 'in')
```

Nice, now we can identify if a given cell in the donut maze is a portal. To
build a decent graph we can adapt the two functions `build_graph()` and
`find_adjacent()` from [day 18][d18] to work with labels. We will still use
[BFS][algo-bfs], but instead of checking for single letters in the grid (which
was needed for day 18), we will just call the `portal_from_grid()` function we
just defined.

```python
from collections import deque

def find_adjacent(grid, src):
    visited = {src}
    queue   = deque()
    found   = []

    # Start by adding all neighbors of the source to the queue, with a distance of 1 step.
    for n in neighbors4(grid, *src):
        queue.append((1, n))

    while queue:
        # Get the next node to visit and its saved distance.
        dist, node = queue.popleft()

        if node not in visited:
            visited.add(node)

            # Check if this cell is a portal...
            portal = portal_from_grid(grid, *node)

            # If so add it to the found list along with its distance.
            if portal is not None:
                found.append((portal, dist))
                continue

            # Otherwise, add all unvisited neighbors to the queue with a distance increased of 1 step.
            for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
                queue.append((dist + 1, neighbor))

    return found
```

Now our `build_graph()` function can just call `find_adjacent()` for each portal
if finds in the maze grid, and save everything in our graph dictionary. Pretty
straightforward:

```python
def build_graph(grid):
    graph = {}

    for r, row in enumerate(grid):
        for c in range(len(row)):
            portal = portal_from_grid(grid, r, c)

            if portal is not None:
                graph[portal] = find_adjacent(grid, (r, c))

    return graph
```

We can now build a very nice weighted graph to start working with:

```python
G = build_graph(grid)
```

Let's find the entrance and exit portals, and also link each pair of portals
with the same label together, with a cost of `1`. We can use
[`combinations()`][py-itertools-combinations] to efficiently iterate over all
the *unique* pairs of portals, like we did in [day 12][d12].

```python
from itertools import combinations

for portal in G:
    if portal.label.startswith('AA'):
        ENTRANCE = portal
    if portal.label.startswith('ZZ'):
        EXIT = portal

for p1, p2 in combinations(G, 2):
    if p1.label == p2.label:
        G[p1].append((p2, 1))
        G[p2].append((p1, 1))
```

Now we can write the real algorithm, and of course, [Dijkstra][algo-dijkstra]
comes to the rescue once again! Just like in [day 18][d18] and [day 6][d06]
(this time more similar to day6 though, we do have both source and destination).
I find it quite awesome how it resembles the Wikipedia page pseudocode. I'm not
going to add comments here since we already used this algorithm multiple times
and it's pretty standard anyway.

```python
import heapq
from collections import defaultdict
from math import inf as INFINITY

def dijkstra(G, src, dst):
    distance = defaultdict(lambda: INFINITY)
    queue    = [(0, src)]
    visited  = set()

    distance[src] = 0

    while queue:
        dist, node = heapq.heappop(queue)
        if node == dst:
            return dist

        if node not in visited:
            visited.add(node)

            for neighbor, weight in filter(lambda n: n[0] not in visited, G[node]):
                new_dist = dist + weight

                if new_dist < distance[neighbor]:
                    distance[neighbor] = new_dist
                    heapq.heappush(queue, (new_dist, neighbor))

    return INFINITY
```

Now we can just ask `dijkstra()` to find the shortest path from the entrance to
the exit for us:

```python
min_steps = dijkstra(G, ENTRANCE, EXIT)
print('Part 1:', min_steps)
```

And there we have it! Part 1 completed.

### Part 2

For the second part, the problem becomes quite funny. I would suggest reading
the original problem statement linked above since it's not that simple to
understand at the first read.

Our donut maze now became recursive!

- Each of the *inner* portals brings us to the outer portal of an *identical*
  maze, at a different depth level. This means, that we can now travel from
  portal `XX_out_depth0` to portal `XX_in_depth0`, and then to `XX_out_depth1`.
- Each of the *outer* portals brings us to the inner portal of the previous
  depth level, except for depth 0 portals.
- The entrance and exit can only be used from depth 0.
- No outer portal at depth 0 can be used.

We still have to find a way to travel from `AA` to `ZZ`, but this time we'll
have to go in and out of different levels of the same maze to find the shortest
path.

So... this became pretty complicated. Didn't it? Well, not really. If we think
about it, the only thing that changed is that we have a lot more edges. We could
generate a new bigger graph of course, but that sounds like a waste. What we can
do to efficiently solve this is to just write a neighbor finder function, that
automatically handles depths for us. The graph can then stay the same, and only
the `dijkstra()` function will ever see different nodes.

First of all, let's add depth to our portals, re-defining the `namedtuple` that
we created before:

```python
Portal = namedtuple('Portal', ['label', 'side', 'depth'])
```

In the `portal_from_grid()` function, we will now return all depth `0` portals:

```python
def portal_from_grid(grid, r, c):

    # ... unchanged ...

    if n2r == 0 or n2c == 0 or n2r == MAXROW or n2c == MAXCOLUMN:
        return Portal(key, 'out', 0)

    return Portal(key, 'in', 0)
```

Now we need a function to get the "recursive" neighbors of a portal, at
different depths. We now know that for a given `portal`:

- If it's a `depth == 0` portal:
    - If it's an *inner* portal: it's connected to its *outer* sibling at depth
      1, plus any if its original *inner* neighbors at the same depth 0. The
      only outer portals it can be connected to (if they are neighbors) are the
      entrance and exit portals.
    - If it's an *outer* portal: it's only connected to its original *inner*
      neighbors at the same depth 0.

- If it's a `depth == d > 0` portal:
    - If it's an *inner* portal: it's connected to its *outer* sibling at depth
      `d + 1`, plus any other original neighbor at the same depth (excluding
      entrance and exit that do not exist at depths > 0).
    - If it's an *outer* portal: it's connected to its *inner* sibling at depth
      `d - 1`, plus any other original neighbor at the same depth (excluding
      entrance and exit that do not exist at depths > 0).

So let's build a function that given a portal, follows exactly these rules to
find its neighbors. In our graph dictionary `G`, we only have depth `0` portals,
so when we check for neighbors we first create the exact same portal but with
`depth = 0`, and then look in the graph. We can then do all the calculations we
want. All of the above, can be written into this cool "recursive portal"
neighbor resolver function:

```python
def recursive_neighbors(portal):
    depth0_portal    = Portal(portal.label, portal.side, 0)
    depth0_neighbors = G[depth0_portal]
    neighbors = []

    if portal.side == 'in':
        n = Portal(portal.label, 'out', portal.depth + 1)
        neighbors.append((n, 1))

    if portal.depth == 0:
        for n, d in depth0_neighbors:
            if n.side == 'in' or n == ENTRANCE or n == EXIT:
                neighbors.append((n, d))
    else:
        if portal.side == 'out':
            n = Portal(portal.label, 'in', portal.depth - 1)
            neighbors.append((n, 1))

        for n, d in depth0_neighbors:
            if n != ENTRANCE and n != EXIT:
                n = Portal(n.label, n.side, portal.depth)
                neighbors.append((n, d))

    return tuple(neighbors)
```

Now we only need to tell our `dijkstra()` function to use
`recursive_neighbors()` instead of directly looking at the graph. To do this
very cleanly, we can pass the function that we want to use to get neighbors as
an argument, falling back to the `.get()` method of the graph dictionary if
nothing is passed. This also makes it so we don't need to change the code for
part 2.

```python
def dijkstra(G, src, dst, get_neighbors=None):
    if get_neighbors is None:
        get_neighbors = G.get

    # ... unchanged ...

        if node not in visited:
            visited.add(node)

            neighbors = get_neighbors(node)

            for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):

                # ... unchanged ...
```

And there we have it. Let's re-build our graph with the now updated portals.
This time we do *not* need to link together portals with the same label,
everything will be handled by our `recursive_neighbors()` function.

```python
G = build_graph(grid)

# Recalculate entrance and exit as well
# since we added 'depth' to our Portal namedtuple.
for p in G:
    if p.label.startswith('AA'):
        ENTRANCE = p
    if p.label.startswith('ZZ'):
        EXIT = p
```

And finally, find the minimum number of steps to solve part 2:

```python
min_steps = dijkstra(G, ENTRANCE, EXIT, get_neighbors=recursive_neighbors)
print('Part 2:', min_steps)
```

As a final sidenote, we could also decorate the `portal_from_grid()` and
`recursive_neighbor()` functions with [`@lru_cache`][py-functools-lru_cache] to
not waste time re-computing already calculated values, just like we did in [day
18][d18]. This time it doesn't have much of an impact though, because the
algorithm is much more lightweight, and we rarely pass through the same portal
twice, so the code runs nice and fast either way.


Day 21 - Springdroid Adventure
------------------------------

[Problem statement][d21-problem] — [Complete solution][d21-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.

### Part 1

Okay, I was expecting some more Intcode... but NOT another assembly language
built on top of Intcode! This is insane, I love it (I just hope to not see it
again).

For today's puzzle we are given an Intcode program which is an interpreter for
another assembly language called *"Springscript"*. Springscript is very, very
simple: it only works with boolean values, it only has three instructions, and
only has two read/write registers. The two registers are `T` (temporary) and `J`
(jump).

The instructions are:

- `AND X Y`: sets `Y` to `X & Y` (logical AND).
- `OR X Y`: sets `Y` to `X | Y` (logical OR).
- `NOT X Y`: sets `Y` to `!X` (negation).

We need to write a Springscript program to control a *springdroid*. A
springdroid is a simple robot that walks in a straight line one cell at a time,
and can also jump. A jump makes the springdroid land on the fourth cell from its
initial position.

Our springdroid is walking on our spaceship's hull, which is full of holes. It
needs to get to the other side of the hull, and we need to write a program to
help it make it through without falling into any hole. For this purpose, we are
given access to *four* read only values: `A`, `B`, `C`, and `D`. `A` is `true`
if there is ground on the next cell from the current position, `B` is `true` if
there is ground on the second cell, and so on until `D` (4th cell).

We need to feed our Intcode interpreter with ASCII values representing a valid
Springscript program, which controls the springdroid. The Springscript program
that we are going to feed to the robot will be run every single time the robot
moves forward into a new cell, to decide whether to jump or not: the robot will
perform a jump if the `J` register is `true` at the end of our Springscript.

After providing a valid Springscript program we start the robot with the special
command `WALK` followed by a newline. If the springdroid makes it through, the
Intcode program outputs the value of "hull damage" reported by the springdroid,
which is the answer to the puzzle. If however the springdroid falls into a hole,
the intcode program reports on its output an ASCII art visualization of the last
few steps before the death of the springbot, so that we are able to debug the
code and figure out what we did wrong.

Okay, pretty long explanation, but the solution is pretty simple. We can only
look forward up to 4 cells, and if we decide to jump, we land on the fourth.
This means that there cannot be a hole which is larger than 3 cells, otherwise
there is no solution.

If we need to account for a hole, whether it is of 1, 2 or 3 cells, we actually
only care if we have a fourth cell available to land on after jumping. We can
check if *any* of the next 3 cells is a hole, and then jump if there is ground
on the fourth one.

Here's a few visual examples:

    @
    #####  => No need to jump.
     ABCD

    @
    # ###  => Need to jump, or we'll fall.
     ABCD

    @
    ##  #  => Don't really need to jump, but doing so does not hurt.
     ABCD

    @
    ## #   => Jumping would make us fall, don't jump.
     ABCD

The above strategy fails for a situation like the following:

    @
    ### # ##  #####  => Should not jump right away, but wait two more steps first.
     ABCD

...but with the limited amount of knowledge that we have (only the next 4
cells), it is impossible to predict such a situation. Therefore it makes sense
to make the assumption that this will never happen. I know, figuring out
constraints based on the expected solution is more meta-puzzling than it should,
but bear with me.

The solution we just thought of can be seen as a simple boolean equation:

    J = (!A | !B | !C) & D

Which can be simplified as:

    J = !(A & B & C) & D

In order to translate this into Springcode, we need to first compute the
expression in the parentheses, and then `AND` the result with `D`. Pretty
simple, we don't even need to use the temporary register for this. Here's the
Springscript program:

```python
NOT A J  # J = !A
NOT J J  # J = A
AND B J  # J = A & B
AND C J  # J = A & B & C
NOT J J  # J = !(A & B & C)
AND D J  # J = !(A & B & C) & D
```

We should already have confidence when interacting with our Intcode VM. We only
need to feed it with the ASCII values of our springscript. Also, let's not
forget the `WALK` command at the end. To convert all characters of the
Springscript to their ASCII values we can use [`ord()`][py-builtin-ord] along
with [`map()`][py-builtin-map] to apply it to every character. To easily write
multiple lines of Springscript we can use a triple-quoted docstring.

```python
program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)

springscript = """\
NOT A J
NOT J J
AND B J
AND C J
NOT J J
AND D J
WALK
"""

inp = list(map(ord, springscript))
out = vm.run(inp)[-1]
print('Part 1:', out)
```

### Part 2

Things get more difficult. We are now given access to *five more* cells ahead of
us. We can now look at values `E` through `I`, representing cells from 5th to
9th after the current position. The jump still lands us on the 4th cell. We are
asked to do the same thing as in part 1, this time using the `RUN` command at
the end instead of `WALK`.

This is trickier. While first we could just make sure that there was ground on
the fourth cell and then blindly jump if there was any hole ahead, we now cannot
do the same, because a situation like the following is now possible:

    @
    ### # ##  #####
     ABCDEFGHI

This time though, we have the knowledge to be able to solve this: the 5 new
values from `E` to `I` will help us. To fix our solution (adapting it from part
1), we need to consider what happens exactly in the edge-case scenario above.

If we run our part 1 code with the new `RUN` command, our poor springbot will
fall into space and the Intcode program will print a snapshot of its death. We
can print it to the terminal to analyze it and understand what is going on:

```python
out = vm.run(springscript)
sys.stdout.write(''.join(map(chr, out)))
```

It produces the following output (letters and comments added by me):

    .................
    .................
    @................
    #####.#.##..#####

    .................
    .................
    .@...............
    #####.#.##..#####

    .................
    .................
    ..@..............  Here we decide to jump prematurely,
    #####.#.##..#####  because C is empty and D is ground.
       ABCDEFGHI
    .................
    ...@.............
    .................
    #####.#.##..#####

    ....@............
    .................
    .................
    #####.#.##..#####

    .................
    .....@...........
    .................
    #####.#.##..#####

    .................
    .................
    ......@..........  We then end up on a single isolated block.
    #####.#.##..#####  Now D is not ground, and we do not jump!
           ABCDEFGHI
    .................
    .................
    .................
    #####.#@##..#####  Therefore we fall right into the hole.

If we better analyze the situation in which we prematurely decide to jump:

      @
    ##### # ##  #####
       ABCDEFGHI

We notice that we could actually wait two more steps until jumping. We cannot
jump now, because even if we land on `D`, we wouldn't have the chance to make
another jump landing on `H`, because it's empty. If we instead wait, two steps
later `D` is going to be ground, and `H` is going to be ground as well:

        @
    ##### # ##  #####
         ABCDEFGHI

Therefore:

- We can jump if `A` is empty and `D` is ground.
- We can also jump if `B` is empty and `D` is ground.
- We *cannot* jump if `C` is empty and `D` is ground, in this case we also need
  `H` to be ground, to assure that an eventual next jump would be performed in
  a situation like the one above.

So this means jumping if `!C & H`, plus the other two conditions of our initial
solution:

    J = (!A & D) | (!B & D) | (!C & D & H)
                                      ^^^ added

Which can be simplified grouping by `D` into:

    J = (!A | !B | (!C & H)) & D

In terms of Springscript:

```python
NOT C J  # J = !C
AND H J  # J = !C & H

NOT B T
OR T J   # J = !B | (!C & H)

NOT A T
OR T J   # J = !A | !B | (!C & H)

AND D J  # J = (!A | !B | (!C & H)) & D
RUN
```

We don't know right off the bat if there could be other edge cases that we did
not consider, but we can for sure try running the code to see if it works. Since
we are still programming our Springscript, we can separate parts of the script
with newlines to make it clearer, and replace double newlines before feeding it
into the Intcode interpreter.

```python
springscript = """\
NOT C J
AND H J

NOT B T
OR T J

NOT A T
OR T J

AND D J
RUN
"""

inp = list(map(ord, springscript.replace('\n\n', '\n')))
out = vm.run(inp)[-1]
print('Part 2:', out)
```

As it turns out, the code runs fine and we get a really big number as the last
output value. This means we got it right! The springdroid safely makes it to the
other side, and we get our part 2 solution.


Day 22 - Slam Shuffle
---------------------

[Problem statement][d22-problem] — [Complete solution][d22-solution] — [Back to top][top]

### Part 1

Very tough mathematical puzzle today, but the hard stuff comes in part 2, for
now we can relax.

We have a deck of cards, precisely 10007 cards numbered from `0` to `10006`. We
need to apply a certain list of moves to shuffle the deck, and determine the
position of the card numbered `2019` after the deck has been shuffled.

There are three possible kind of moves:

1. **Deal into new deck**: we take cards out from the top of the deck, one at a
   time to build a new deck. This effectively inverts the order of cards in the
   deck. Example:

        Deck:     0 1 2 3 4
        *deal into new deck*
        New deck: 4 3 2 1 0

2. **Deal with step `n`**: we start with an empty table with as many "slots" as
   the number of cards, then start taking cards from the top of the stack.
   Starting from the leftmost slot on the table, each card we draw, we put it
   down in the current slot and then we move forward `n` slots (cycling back
   from the beginning after the last slot). After dealing all the cards in the
   deck, the table will be full of shuffled cards, and we create the new deck
   collecting all the cards from left (top of new deck) to right (bottom of new
   deck). Example:

        Deck:  0 1 2 3 4

        *deal with step 3*

        Deck:   0  1  2  3  4
        Table: [0][ ][ ][ ][ ]

        Deck:         2  3  4
        Table: [0][ ][ ][1][ ]

        Deck:            3  4
        Table: [0][2][ ][1][ ]

        Deck:               4
        Table: [0][2][ ][1][3]

        Deck:
        Table: [0][2][4][1][3]

        New deck: 0 2 4 1 3

3. **Cut `n` cards**: we take the first `n` cards from the top of the deck, and
   move them to the bottom. If `n` is negative, then we take the bottom `abs(n)`
   cards and move them to the top instead. Example:

        Deck:     0 1 2 3 4
        *cut 3 cards*
        New deck: 3 4 0 1 2

        Deck:     0 1 2 3 4
        *cut -4 cards*
        New deck: 1 2 3 4 0

Our input is a list of moves in the above form, and as we said, we want to
determine the position of the card numbered `2019` after the deck has been
shuffled.

Okay, so, first of all, let's parse the input. We can just iterate over the
lines of input and since integers are always the last word of a line we don't
even need RegExps. We can use three enum-like variables to easily represent the
different moves and build a list of moves.

```python
DEAL_NEW, DEAL_INC, CUT = 1, 2, 3

moves = []
for l in fin:
    if 'deal into' in l:
        moves.append((DEAL_NEW, 0))
    elif 'deal with' in l:
        n = int(l[l.rfind(' '):])
        moves.append((DEAL_INC, n))
    elif 'cut' in l:
        n = int(l[l.rfind(' '):])
        moves.append((CUT, n))
```

Now we can start solving the problem: the first thing that comes to mind is to
just build a list of `10007` numbers from `0` to `10006` and apply the moves
literally to the list. It's very simple, and would get the job done for sure,
but we don't really need to. We want to build a cleaner solution.

If we take a closer look at each of the different kind of moves, possibly with
the help of pen and paper, we quickly realize that it's pretty easy to calculate
the new index of a given card knowing its previous index. Specifically, we can
observe that:

1. The "deal into new deck" move is equivalent to reversing the deck, therefore
   a card with index `i` moves to index `size - i - 1` (where `size` is the
   size of the deck, i.e. the number of cards in the deck).

2. If we try to apply the move "deal with increment `n`" literally:

   ```python
   deck     = list(range(10007))
   new_deck = [-1] * 10007 # -1 just as a placeholder
   n = 5 # some random increment

   for i in range(len(deck)):
       new_deck[(i * n) % len(deck)] = deck[i]
   ```

   We realize that a card with index `i` moves to index `(i*n) % size`. That
   `% size` is needed since we want to cycle back, so for example index `8`
   ends up back to index `8 % 7 == 1`.

3. As per the "cut `n` cards" move, if `n` is negative, the move is equivalent
   to "cut `size - abs(n)`" (or just `size + n` since `n` is negative).
   Therefore all these moves can be first converted to positive values for
   simplicity. After doing that, if we try applying the move literally:

   ```python
   deck = list(range(10007))
   n = 5 # some random cut size

   if n < 0:
       n = len(deck) + n

   new_deck = deck[n:] + deck[:n]
   ```

   We realize that all cards with index lower than `n` end up being shifted
   right by the number of remaining cards, so the new index becomes
   `i + (size - n)`, and all cards with index greater or equal to `n` end up
   being shifted left of `n` places, so their new index becomes `i - n`.

If we apply all the above, we can quickly calculate the new index of the card
`2019` after the moves, without the need of any list. We can create a function
to apply the shuffling and give us the new index of a given card.

```python
def shuffle(index, n_cards, moves):
    for move, n in moves:
        if move == DEAL_NEW:
            index = n_cards - index - 1
        elif move == DEAL_INC:
            index = (index * n) % n_cards
        elif move == CUT:
            if n < 0:
                n += n_cards

            if index < n:
                index += n_cards - n
            else:
                index -= n

    return index
```

Now we can just apply our function to get the new position of the card `2019`,
which is the answer to the puzzle.

```python
final_index = shuffle(2019, 10007, moves)
print('Part 1', final_index)
```

### Part 2

Now comes the brain smashing part. Brace yourself, this is not going to be
simple at all. This second part is what easily makes this problem the most
complicated of the year so far, and it's basically 90% math and 10% programming.
Also, some knowledge of
[modular arithmetic](https://en.wikipedia.org/wiki/Modular_arithmetic) is
probably required, but I'll try to make it as simple and painless as I can.

So, as usual with problems that require to apply some simple sequentaial
operations a given number of times, we are now obviously asked to do the same
for an *insane* amount of times. The second part of this problem asks us to
apply the same moves as part 1, but with 119315717514047 cards, and repeating
the shuffling process exactly 101741582076661 times. This time we are interested
in *which card* will be at position `2020` after all the shuffling.

Okay, don't even try to think about blindly applying the same algorithm as
before. It would basically be impossible to get an answer in less than a century
of computation time. And even then, now we are asked for the *value* of the card
at final position 2020, not the position of a card with a known value, so the
approach would need to be modified. Given the huge numbers, we need to simplify
the problem even more... much, much more. Let's dive in the math.

The first thing we notice is that all the involved numbers (10007,
119315717514047 and 101741582076661) are primes. This is a quite interesting
fact that will help us a lot later.

If we take a look at the starting deck of cards, we notice that cards in the
deck start with the value `0`, and successive values increase at a fixed rate of
`1`. We could therefore write a function `f(i)` to get the value of a card from
its index, and in the case of the starting deck it would be: `f(i) = i`.

Consider the following starting deck of 7 cards:

    0 1 2 3 4 5 6 7

We can see that it *starts* with card `0`, and each following card value
increases by a fixed *step* of `1`. The function `f(i)` can be in general
expressed as `f(i) = step * i + start`. A starting deck has `step = 1` and
`start = 0`.

If we also take into account the fact that all indexes need to be modulus
`size`, then the formula becomes `(step * i + start) % size`. In the case of the
starting deck, it doesn't matter whether we apply the modulo or not, but we'll
see that in other decks it does. From now on, we will be using the keyword `mod`
instead of the symol `%`, since it's clearer and it's also the standard
mathematical way of writing it.

If we try applying some moves to the deck above to see if this property keeps
holding, we notice the following:

1. The property still holds after applying a "deal new" move (vertical for
   easier understanding). For example:

        0  ->  6  =  (-1 * 0  + 6) mod 7
        1  ->  5  =  (-1 * 1  + 6) mod 7
        2  ->  4  =  (-1 * 2  + 6) mod 7
        3  ->  3  =  (-1 * 3  + 6) mod 7
        4  ->  2  =  (-1 * 4  + 6) mod 7
        5  ->  1  =  (-1 * 5  + 6) mod 7
        6  ->  0  =  (-1 * 6  + 6) mod 7

        => Start = 6, Step = -1

2. It still holds after applying a "deal with increment" move. For example, with
   increment 3:

        0  ->  0  =  (5 * 0 + 0) mod 7
        1  ->  5  =  (5 * 1 + 0) mod 7
        2  ->  3  =  (5 * 2 + 0) mod 7
        3  ->  1  =  (5 * 3 + 0) mod 7
        4  ->  6  =  (5 * 4 + 0) mod 7
        5  ->  4  =  (5 * 5 + 0) mod 7
        6  ->  2  =  (5 * 6 + 0) mod 7

        ==> Start = 0, Step = 5

3. It still holds after applying a "cut" move. For example, cutting 4 cards:

        0  ->  4  =  (1 * 0 + 4) mod 7
        1  ->  5  =  (1 * 1 + 4) mod 7
        2  ->  6  =  (1 * 2 + 4) mod 7
        3  ->  0  =  (1 * 3 + 4) mod 7
        4  ->  1  =  (1 * 4 + 4) mod 7
        5  ->  2  =  (1 * 5 + 4) mod 7
        6  ->  3  =  (1 * 6 + 4) mod 7

        ==> Start = 4, Step = 1

4. And most importantly the property still holds after applying any combination
   of different moves! For example, applying "deal with increment 3", then
   "cut 4" and then "deal new":

        0  ->  1  = (2 * 0 + 1) mod 7
        1  ->  3  = (2 * 1 + 1) mod 7
        2  ->  5  = (2 * 2 + 1) mod 7
        3  ->  0  = (2 * 3 + 1) mod 7
        4  ->  2  = (2 * 4 + 1) mod 7
        5  ->  4  = (2 * 5 + 1) mod 7
        6  ->  6  = (2 * 6 + 1) mod 7

        ==> Start = 1, Step = 2

In addition to the above, since all math is done modulo `size`. This means that
a `step = -1` in a deck of `size = 7` is the exact same as a step of `6` (as you
can see from point 1 in the above list).

The implication of all this, is that we can *uniquely identify* a deck of cards
just by knowing two numbers (other than the size): `start`, `step`. The `size`
of the decks always stays the same after applying any move. We now need to
understand how each different move transforms `start` and `step`. If we do so,
we will have a very good and concise way to tell what happens to a deck after
applying any list of moves.

Let's see if we can figure this out:

1. The "deal new" move: as we said before, this move "inverts" the cards. This
   means that the `step` will just flip sign (from positive to negative or
   vice-versa), while the new `start` will be exactly the last card value of the
   previus deck, which means just going back one step (since we are always
   moving in a cycle modulo `size`).

        new_start = (start - step) mod size
        new_step  = -step mod size

2. The "deal with increment `n`" move: this is the most complicated move. The
   starting value is not changed, since we always pick the first card of the
   deck to start. The `step` changes, but *how* does it change? It doesn't seem
   that obvious this time.

   We can however find the new `step` value in respect to the previous one as
   the difference between the new indexes of the first two cards in the previous
   deck. For example, here:

        1 3 5 0 2 4 6   (start = 1, step = 2, size = 7)

        *deal with increment 5*

        1 0 6 5 4 3 2   (start = 1, step = 6, size = 7)

   We can see that the first card is still `1`, and has index `0` in both decks.
   The second card was `3`: it had index `1` in the previous deck, and it has
   index `5` in the new deck (which is the same as the increment, since we move
   forward 5 positions from the start). The new increment
   *in respect to the previous deck* can be found by solving the modular
   equation `5*x == 1 (mod 7)`, which in general becomes:

        n*x == 1 (mod size)

   Note that here `==` means
   [*"congruent"*](https://en.wikipedia.org/wiki/Congruence_relation) under
   modulo `size`.

   If we want to find `x`, we are tempted to write `x == 1/n (mod size)`.
   However there is no such thing as division in modular arithmetic!
   The expression needs to be rewritten as:

        x == 1 * n^-1 == n^-1 (mod size)

   Here `^` means "to the power of". Finding `n^-1` means finding the
   [*modular multiplicative inverese*](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse)
   of `n` modulo `size`. This can be easily found applying
   [Euler's theorem](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse#Using_Euler's_theorem).
   For Euler's theorem, the value of `n^-1` modulo `size`,
   **when `size` is a prime number**, is congruent to `n^(size-2)` (always
   modulo `size`). Remember the first thing we noticed before about those big
   numbers? Yes, they are all prime numbers. Therefore this formula can be
   applied.

   The value of `x` is then congruent to `n^(size-2)`, and it represents the
   step relative to the previous deck. The new step of the new deck is then:

        new_step = (step * x) mod size = (step * n^(size-2)) mod size

3. The "cut `n`" move: the new `start` is "shifted" and becomes the `n`-th value
   of the previous deck, while the step stays the same since the cards are only
   cyclically shifted. Remember that we work with positive `n` here, since as
   we already saw a negative cut move can be easily transformed into an
   equivalent positive cut move.

        new_start = (start + step * n) mod size

Now we know how to transform `start` and `step` when applying any move. Based on
the above, we can write a simple Python function that does this for us. Starting
from 3.8, Python supports direct calculation of the modular multiplicative
inverse of a number with the built-in [`pow()`][py-builtin-pow] function
specifying `-1` as second argument and the modulus as third. I do not have such
a recent Python version installed, but as explained above in point 2, we can use
Euler's theorem and just compute `pow(n, size - 2, size)`.

Usually, it would be impossible to calculate such a huge power (in our case
`n^(101741582076661 - 2)`), as the result grows exponentially, and the number of
digits becomes too large to even be stored in memory. Modular powers are much
easier to calculate though, and there are
[several methods](https://en.wikipedia.org/wiki/Modular_exponentiation) to do it
very efficently. In particular, Python uses
[binary exponentiation](https://en.wikipedia.org/wiki/Exponentiation_by_squaring)
to compute modular powers.

Another even faster approach to calculate the modular inverse without even
dealing with powers would be to use the
[extended Euclidean algorithm](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse#Extended_Euclidean_algorithm),
but that's more comlpicated.

Here's the new function:

```python
def transform(start, step, size, moves):
    for move, n in moves:
        if move == DEAL_NEW:
            start = (start - step) % size
            step = -step % size
        elif move == DEAL_INC:
            step = (step * pow(n, size - 2, size)) % size
        elif move == CUT:
            if n < 0:
                n += size

            start = (start + step * n) % size

    return start, step
```

We now have the `start` and `step` of the new deck after applying all the moves
in our input. There is still a problem though: we need to apply those
101741582076661 times in a row.

The initial deck has `step = 1, start = 0`, with a formula of:

    f(i) = 1i + 0

The new deck, after applying all moves, will have some arbitrary values for
those. Let's rename `step = a` and `start = b` to be concise. In general, we
will have:

    f(i) = ai + b

If we apply the same moves again, we will have:

    f(f(i)) = a(ai + b) + b = (a^2)i + ab + b

And if we continue applying the same moves over and over:

    f(f(f(i)))       = a(a(ai + b) + b) + b               = (a^3)i + (a^2)b + ab + b
    f(f(f(f(i))))    = a(a(a(ai + b) + b) + b) + b        = (a^4)i + (a^3)b + (a^2)b + ab + b
    f(f(f(f(f(i))))) = a(a(a(a(ai + b) + b) + b) + b) + b = (a^5)i + (a^4)b + (a^3)b + (a^2)b + ab + b
    ... and so on ...

You can clearly see where this is going. In general, after `N` repetitions of
the same moves, we will have:

    (a^N)i + b + ab + (a^2)b + (a^3)b + ... + (a^(N-1))b

The value of `a^N` modulo `size` is easy to calculate, but what about all those
`b` terms? Well, if we look closer, we recognize that it is the
[sum of the first `N` terms a geometric series](https://en.wikipedia.org/wiki/Geometric_series#Formula):
specifically, the geometric series with first term `b` and ratio `a`. As we all
know from our math classes (of course right?) the sum of the first `N` terms of
a geometric series starting with `b` and with ratio `a` is:

    S = b((1 - a^N)/(1 - a))

We are still working modulo `size`, so the above can be rewritten as:

    S = (b * (1 - a^N) * (1 - a)^-1) mod size

And as we just learned:

    (1 - a)^-1 == (1 - a)^(size - 2) (mod size)

In Python, we can calculate the whole thing as:

```python
S = b * (1 - pow(a, N, size)) * pow(1 - a, size - 2, size)
```

So there we go, we can now calculate the new `start` and `step` values after
applying the same set of moves multiple times.

```python
def repeat(start, step, size, repetitions):
    final_step = pow(step, repetitions, size)
    final_start = (start * (1 - final_step) * pow(1 - step, size - 2, size)) % size

    return final_start, final_step
```

We can finally calculate our final `start` and `step` values:

```python
start, step, size = 0, 1, 119315717514047
repetitions = 101741582076661

start, step = transform(start, step, size, moves)
start, step = repeat(start, step, size, repetitions)
```

And if we want to know the value of the card at position `2020`, it's now just a
simple calculation:

```python
value = (start + step * 2020) % size
print('Part 2:', value)
```

### Reflections

We can use the logic of the second part to solve part 1 too. Since part 1 asks
for the position of the value 2019 (and not the value at position 2019), we can
just invert the formula after using `transform` to calculate `start` and `step`:

```python
start, step = transform(0, 1, 10007, moves)

# value == (start + step * i)    (mod size)
# value - start == step * i      (mod size)
# i == (value - start)/step      (mod size)
# i == (value - start) * step^-1 (mod size)

i = ((2019 - start) * pow(step, size - 2, size)) % size
```

Today's problem is a lot more about math than programming. One could in fact
argue that this isn't even a programming problem, but a modular arithmetic one.

Even though I know some modular arithmetic, I did *not* figure out part 2 by
myself, and I would like to thank [mcpower](https://twitter.com/mcpowr) for
providing a very helpful short explanation of the problem
[in a reddit comment](https://www.reddit.com/r/adventofcode/comments/ee0rqi/2019_day_22_solutions/fbnkaju/)
in the solution megathread.

Personally, I don't see this problem as a good fit for AoC, because it's not
really about programming, but more about math, and I would not expect a
programmer to be familiar with all the concepts and theorems needed to solve
this problem. With this said, this might be more fun for other people than
implementing path finding algorithms, and the whole thing is of course
subjective.


Day 23 - Category Six
---------------------

[Problem statement][d23-problem] — [Complete solution][d23-solution] — [Back to top][top]

### Prerequisites

This problem requires a working Intcode virtual machine built following
instructions in the [day 2][d02], [day 5][d05] and [day 9][d09] problem
statements! The machine could be as simple as a single function, or something
more complicated like a class with multiple methods. Take a look at previous
days to know more.

I will be using [my `IntcodeVM` class](lib/intcode.py) to solve this puzzle.

### Part 1

Another Intcode puzzle! This time though, it is no ordinary task: we are asked
to build a network of Intcode computers. Each computer is running the program
that we are given as input, and can communicate with the rest of the network
through input and output instructions that simulate a
[Network Interface Card](https://en.wikipedia.org/wiki/Network_interface_controller).

We need to simulate a network of 50 Intcode computers, with addresses from `0`
to `49`. Each computer of the network starts reading it's *network address* as
input, and then starts doing... whatever it is supposed to do. To talk to other
computers on the network, a computer first outputs an address, and then two
integers `x` and `y`, which represent the network packet to be sent over the
network to the specified address.

Computers can send packets at any time, and they should keep each packet they
receive until it's consumed by the needed amount of `in` instructions. When a
computer requests input, the first available packet in the queue should be
provided (first `x`, then `y`), and if no packet is available, the integer `-1`
should be provided.

We are asked to simulate this network until some computer tries to send a packet
to the address `255`: the `y` value of such special packet is the answer to the
puzzle.

First of all, let's create our network:

```python
from lib.intcode import IntcodeVM

program = list(map(int, fin.read().split(',')))
network = [IntcodeVM(program) for _ in range(50)]
```

Since a single VM can output as many packets as it wants before requesting to
read again, we will synchronize the VMs on the `in` instruction. In particular,
my `IntcodeVM` class has a method `.run()` which supports a positive integer
parameter `n_in=`, to pause the execution and return after exactly the specified
number of `in` instructions are executed.

For each VM in the network, it's useful to keep track of two different things:

1. A queue of packets that the VM received and needs to read. We need to enqueue
   packets received from other VMs, since we don't want to lose any.
2. The current outgoing packet. We do not know if a packet is always sent all at
   once with 3 consecutive `out` instructions, or if there can be any `in`
   instructions in between.

With this said, we can initialize two new properties exactly for this purpose on
each of our `IntcodeVM` instances. This could also be done using global
variables (like lists of 50 elements), but doing so with real properties seems
way easier. To create the packet queue of each VM, a
[`deque`][py-collections-deque] comes in handy.

```python
from collections import deque

for i, vm in enumerate(network):
    vm.packet_queue = deque([i])
    vm.out_packet = []
```

The `packet_queue` of each `vm` is initialized as containing the VM's address,
since it's the first thing it will read.

Now we will need to implement the sending and receiving logic. To do this, I
will overwrite the `.read()` and `.write()` methods of my class with new
functions to handle packets correctly. To get a reference to the `vm` when
executing the new functions, we can use a wrapper function and call it passing
the `vm` as first argument. The wrapper function will define and return a new
function to be used which will remember the value of the `vm` instance passed to
the wrapper. This is also known as a
[*closure*](https://en.wikipedia.org/wiki/Closure_(computer_programming)). Doing
so, we can emulate the behavior of the `self` parameter used in classes even in
our externally defined function.

Each time a VM writes, we will add the new value to its incomplete `out_packet`,
and once that packet is complete (i.e. reaches a length of 3), we will add it
to the queue of the corresponding destination VM, resetting it to empty. To keep
track of whichever value will be sent to the special address `255` we will use a
global variable `special_packet`.

```python
def vm_write_for(self):
    def vm_write(v):
        global special_packet

        self.out_packet.append(v)

        if len(self.out_packet) == 3:
            destination, *packet = self.out_packet
            self.out_packet = []

            if destination == 255:
                special_packet = packet
            else:
                network[destination].packet_queue.extend(packet)

    return vm_write
```

Each time a VM reads, we will check if its packet queue contains anything: if
so, we'll pop the first value (on the left) and return it, otherwise, we'll
return `-1`.

```python
def vm_read_for(self):
    def vm_read():
        if self.packet_queue:
            return self.packet_queue.popleft()
        return -1

    return vm_read
```

Pretty simple really. Now we can override the `.read()` and `.write()` methods
of my `IntcodeVM` class with the new ones:

```python
for vm in network:
    vm.read = vm_read_for(vm)
    vm.write = vm_write_for(vm)
```

After this, all that's left to do is to start with a `special_packet` set to
`None`, and run each VM until the `special_packet` gets written by someone.

```python
special_packet = None

while special_packet is None:
    for vm in network:
        vm.run(n_in=1, resume=True)

special_y = special_packet[1]
print('Part 1:', special_y)
```

Nice! We have a functioning Intcode VM network, and we solved the first part of
the puzzle. Let's move to the next one.

### Part 2

We know that Intcode computers in the network can receive `-1` as input when no
packets to be read are in the queue. Now, if every single VM is continuously
trying to read while no packet is available, we have to consider the network
*idle*. Every time the network becomes idle, the *last* special packet that was
sent to address `255`, is sent to the VM with address `0`, and this will make the
network continue exchanging data until it becomes idle again.

We are asked to find the first special packet `y` value that is sent twice in a
row to the VM with address `0`.

Okay, so now we need to account for idle network too. The simplest way to do
this is to add some other properties to our VMs, in particular a `idle` boolean
value, and a `unserviced_reads` integer value which counts the number of reads
that did not get any packet data (i.e. `-1`).

```python
for vm in network:
    vm.idle = False
    vm.unserviced_reads = 0
```

Each time a VM reads `-1`, we will increase its number of `unserviced_reads`,
and set the VM as `idle` if the number gets above or equal to 2. When a VM reads
something that is not `-1`, or when it writes something out, we will reset
`idle` to `False`, and `unserviced_reads` to `0`. This will make the network
become idle when all the VMs read nothing for two times in a row. We do not need
a queue for special packets since we are told to only keep the last one.

Let's modify our read and write functions to account for the above:

```python
def vm_read_for(self):
    def vm_read():
        if self.packet_queue:
            self.idle = False
            self.unserviced_reads = 0
            return self.packet_queue.popleft()

        self.unserviced_reads += 1
        if self.unserviced_reads > 1:
            self.idle = True

        return -1

    return vm_read

def vm_write_for(self):
    def vm_write(v):
        global special_packet

        self.idle = False
        self.unserviced_reads = 0
        self.out_packet.append(v)

        if len(self.out_packet) == 3:
            destination, *packet = self.out_packet
            self.out_packet = []

            if destination == 255:
                special_packet = packet
            else:
                network[destination].packet_queue.extend(packet)

    return vm_write


for vm in network:
    vm.read = vm_read_for(vm)
    vm.write = vm_write_for(vm)
```

We can now run the same loop as above, but this time we will check if the
network is idle each iteration. To check this we can use the built-in
[`all()`][py-builtin-all] function. Each time the network is idle, we can then
"wake up" VM number `0` and send it the last special packet. When we do, we will
also check the last special `y` value sent to VM number `0`, and break out of
the loop when the same value is sent two times in a row.

```python
last_special_y = None
done = False

while not done:
    for vm in network:
        vm.run(n_in=1, resume=True)

        if all(vm.idle for vm in network):
            # Stop if the same special y is received two times.
            if special_packet[1] == last_special_y:
                done = True
                break

            # Wake up VM #0 and send it the last special packet.
            network[0].idle = False
            network[0].packet_queue.extend(special_packet)

            last_special_y = special_packet[1]
            special_packet = []

print('Part 2:', last_special_y)
```

Welcome to *IntcodeNET* I guess!


Day 24 - Planet of Discord
--------------------------

[Problem statement][d24-problem] — [Complete solution][d24-solution] — [Back to top][top]

### Part 1

Ah, don't you love
[Conway's Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life)?
I sure do.

Today's puzzle consists of a simplified version of Conway's Game of Life:
instead of "alive" and "dead" cells we have cells with bugs (`#`) or empty cells
(`.`). We start with a given 5-by-5 grid of cells with some bugs in it, and we
know that each minute the situation evolves following two very simple rules:

1. A bug dies (leaving the cell empty) *unless* there is exactly one bug
   adjacent to it.
2. An empty cell becomes infested with a bug if exactly one or two bugs are
   adjacent to it.
3. If neither of the two happens, the cell keeps its state.

Here "adjacent" means (as usual) immediately up, down, left or right. It's
important to remember that this process happens in every location
*simultaneously*; that is, within the same minute, the number of adjacent bugs
is counted for every cell first, and only then the cells are updated.

We need to simulate the evolution of the given grid until a certain
configuration appears twice. For that configuration, we'll need to calculate the
"biodiversity rating" as the answer. To calculate the biodiversity rating, we
assign each cell from left to right and from top to bottom a power of two: `2^0
= 1` to the first one, `2^1 = 2` to the second, and so on. The total
biodiversity rating will be the sum of all these powers for cells that contain
bugs.

Okay, looks simple enough. Let's parse the input first: we'll transform bugs and
empty cells into `1` and `0` respectively, to make it easier to count the number
of bugs near a cell. Some other global variables like number of rows and columns
will also be useful later.

```python
orig_grid = list(list(l.strip()) for l in fin)

ROWS = len(orig_grid)
COLS = len(orig_grid[0])
MAXROW = ROWS - 1
MAXCOL = COLS - 1
EMPTY, BUG = 0, 1

for r, c in product(range(ROWS), range(COLS)):
    orig_grid[r][c] = BUG if orig_grid[r][c] == '#' else EMPTY
```

We'll use our usual `neighbors4` function to get the neighbors of a cell in the
grid (we should have memorized this by now given the amount of times we used it)
and then another helper function that just sums the values in the grid for the
cells returned by `neighbors4` to count how many bugs are adjacent to a given
cell. We can do this pretty seamlessly using [`sum()`][py-builtin-sum].

```python
def neighbors4(grid, r, c):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        nr, nc = r + dr, c + dc

        if 0 <= nr < ROWS and 0 <= nc < COLS:
            yield nr, nc

def neighbors4_alive(grid, r, c):
    return sum(grid[nr][nc] for nr, nc in neighbors4(grid, r, c))
```

Let's write a function to compute the new state of a cell (bug or empty) after
one generation given the previous grid. We already have a function to count
alive neighbors, so it's just a matter of applying the three rules listed above.

```python
def evolve(grid, r, c):
    alive = neighbors4_alive(grid, r, c)

    if grid[r][c] == BUG:
        if alive == 1:
            return BUG
        return EMPTY

    if alive == 1 or alive == 2:
        return BUG
    return EMPTY
```

Now, to evolve the whole grid and get the new grid after one generation, we can
apply this function to every single cell of the grid. Let's write another
function to do just that: it'll create a new empty 5-by-5 grid and then fill
each cell with the result of evolving the previous one. We will be using the
very handy [`product()`][py-itertools-product] generator function from the
[`itertools`][py-itertools] module a few times in the rest of the program as a
more compact way of writing two nested `for` loops.

```python
def nextgen(grid):
    new_grid = [[EMPTY] * COLS for _ in range(ROWS)]

    for r, c in product(range(ROWS), range(COLS)):
        new_grid[r][c] = evolve(grid, r, c)

    return new_grid
```

Now we only need to keep simulating the evolution of the grid until we get the
same grid twice. In order to keep track of alredy seen grids we can use a simple
set, converting the grid from `list` of `list` to `tuple` of `tuple` before
adding it to the set (since lists are mutable and therefore not hashable). We'll
make a copy of the original starting grid using [`deepcopy()`][py-copy-deepcopy]
from the [`copy`][py-copy] module in order to preserve the original one for part
2.

```python
grid = deepcopy(orig_grid)
seen = set()

while True:
    state = tuple(map(tuple, grid))
    if state in seen:
        break

    seen.add(state)
    grid = nextgen(grid)
```

Once the above loop exits, `grid` will hold the first grid that appeared two
times. We can then calculate the total biodiversity rating with a simple loop:

```python
total, biodiv = 0, 1
for r, c in product(range(ROWS), range(COLS)):
    if grid[r][c] == BUG:
        total += biodiv
    biodiv *= 2

print('Part 1:', total)
```

### Part 2

Oh no, recursive madness again! Similarly to what happened for [day 20][d20]
part 2, the problem now becomes recursive.

The central cell of our grid (that is `(2, 2)`) now becomes special: it becomes
a smaller 5-by-5 grid itself. Every side of this smaller grid is adjacent to the
grid above. In addition to this, this property repeats infinitely recursively,
meaning that our base grid is too in the middle of a bigger grid, and so on.

To better understand this, here's an example right from the problem statement:

      1 |  2 |    3    | 4  | 5
    ----+----+---------+----+----
      6 |  7 |    8    | 9  | 10
    ----+----+---------+----+----
        |    |A|B|C|D|E|    |
        |    |-+-+-+-+-|    |
        |    |F|G|H|I|J|    |
        |    |-+-+-+-+-|    |
     11 | 12 |K|L|?|N|O| 14 | 15
        |    |-+-+-+-+-|    |
        |    |P|Q|R|S|T|    |
        |    |-+-+-+-+-|    |
        |    |U|V|W|X|Y|    |
    ----+----+---------+----+----
     16 | 17 |    18   | 19 | 20
    ----+----+---------+----+----
     21 | 22 |    23   | 24 | 25

Here, the internal grid has cells labeled with letters, while the external grid
has cells labeled with numbers. The `?` in the center of the smaller grid
represents another grid. In this example cell `12` is adjacent to `7`, `11`,
`17`, as well as `A`, `F`, `K`, `P`, `U`. On the other hand, cell `C` is
adjacent to `B`, `H`, `D`, and `8`. Cell `U` is adjacent wih both `12` and `18`.

In short, every external cell is now also adjacent to a single cell of an higher
level grid, and each cell adjacent to the center is now adjacent to the 5 cells
of the side of a deeper level grid.

Starting from the same initial grid, we now also need to take the above into
account when evolving each cell, keeping in mind that every other grid at
different depth levels starts without bugs. We need to count the total number of
bugs present in the whole recursive grid after 200 minutes (that is, 200
generations).

The simplest way to represent this recursive grid madness is to use a
dictionary. We know that all grids except the one at level `0` are empty at
first, so we can sart with a dictionary containing only the starting grid. We
will also consider the center of a grid to always be empty.

```python
CENTER_ROW, CENTER_COL = ROWS // 2 + 1, COLS // 2 + 1

grid = deepcopy(orig_grid)
grid[CENTER_ROW][CENTER_COL] = EMPTY
grids = {0: grid}
```

Clearly our `evolve()` function which calculates the new state of a cell given a
grid and two coordinates is no longer useful. Let's write a new function which
does the same for our recursive grid. In order to evolve a single cell, in
addition to the grid containing the cell, we now also need to look at the inner
and outer grids.

We'll need to apply the following rules:

- When looking at a cell that is on a side of the grid, we will also check if
  the corresponding outer grid has a bug in the cell that is adjacent to the
  side containing the given cell.
- When looking at a cell that is adjacent to the center, we will also count the
  bugs on all the cells on the side of the inner grid that is adjacent to the
  given cell.

In addition to the above, for each cell we will still check neighbors on its
grid regardless of the position of the cell.

Transleted into code, the above becomes something like this:

```python
def recursive_evolve(grid, grid_outer, grid_inner, r, c):
    alive = 0

    if grid_outer is not None:
        if c == 0 and grid_outer[CENTER_ROW][CENTER_COL - 1]: # left
            alive += 1
        if r == 0 and grid_outer[CENTER_ROW - 1][CENTER_COL]: # up
            alive += 1
        if c == MAXCOL and grid_outer[CENTER_ROW][CENTER_COL + 1]: # right
            alive += 1
        if r == MAXROW and grid_outer[CENTER_ROW + 1][CENTER_COL]: # down
            alive += 1

    if grid_inner is not None:
        if (r, c) == (CENTER_ROW, CENTER_COL - 1): # left
            alive += sum(grid_inner[i][0] for i in range(ROWS))
        elif (r, c) == (CENTER_ROW - 1, CENTER_COL): # up
            alive += sum(grid_inner[0][i] for i in range(COLS))
        elif (r, c) == (CENTER_ROW, CENTER_COL + 1): # right
            alive += sum(grid_inner[i][MAXCOL] for i in range(ROWS))
        elif (r, c) == (CENTER_ROW + 1, CENTER_COL): # down
            alive += sum(grid_inner[MAXROW][i] for i in range(COLS))

    alive += neighbors4_alive(grid, r, c)

    if grid[r][c] == BUG:
        if alive == 1:
            return BUG
        return EMPTY

    if alive == 1 or alive == 2:
        return BUG
    return EMPTY
```

The check for `is not None` is needed since we are going to use `None` when a
grid has an empty inner or outer grid (instead of wasting time counting on an
empty grid).

We now need a recursive version of the `nextgen()` function, to get the next
generation of a grid given its depth. This function will just apply
`recursive_evolve()` to every cell of a given grid, also taking into account the
relative inner and outer grids. We will also call this function to generate
newer grids. we know that each minute new bugs can potentially evolve in the two
innermost and outermost grids, so we'll create a new innermost and outermost
grid each time using the same function.

```python
def recursive_nextgen(grids, depth):
    if depth in grids:
        grid = grids[depth]
    else:
        # Creaete an empty grid if there's no grid at the current depth.
        grid = [[EMPTY] * COLS for _ in range(ROWS)]

    new_grid = [[EMPTY] * COLS for _ in range(ROWS)]
    grid_outer = grids.get(depth + 1)
    grid_inner = grids.get(depth - 1)

    for r, c in product(range(ROWS), range(COLS)):
        # Skip the center cell.
        if (r, c) == (CENTER_ROW, CENTER_COL):
            continue

        new_grid[r][c] = recursive_evolve(grid, grid_outer, grid_inner, r, c)

    return new_grid
```

Every generation, we will evolve every single grid in the dictionary and then
add two new innermost and outermost grids. Pretty straightforward.

```python
min_depth = 0
max_depth = 0

for _ in range(200):
    new_grids = {}

    for depth in grids:
        new_grids[depth] = recursive_nextgen(grids, depth)

    min_depth -= 1
    new_grids[min_depth] = recursive_nextgen(grids, min_depth)

    max_depth += 1
    new_grids[max_depth] = recursive_nextgen(grids, max_depth)

    grids = new_grids

bugs = sum(sum(sum(c == BUG for c in row) for row in grid) for grid in grids.values())
print('Part 2:', bugs)
```

Yeah, that triple nested [`sum()`][py-builtin-sum] is pretty funny, isn't it?
Day 24 completed, only one left!

---

*Copyright &copy; 2020 Marco Bonelli. This document is licensed under the [Creative Commons BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license.*

![License icon](https://licensebuttons.net/l/by-nc-sa/4.0/88x31.png)


[top]: #advent-of-code-2019-walkthrough
[d01]: #day-1---the-tyranny-of-the-rocket-equation
[d02]: #day-2---1202-program-alarm
[d03]: #day-3---crossed-wires
[d04]: #day-4---secure-container
[d05]: #day-5---sunny-with-a-chance-of-asteroids
[d06]: #day-6---universal-orbit-map
[d07]: #day-7---amplification-circuit
[d08]: #day-8---space-image-format
[d09]: #day-9---sensor-boost
[d10]: #day-10---monitoring-station
[d11]: #day-11---space-police
[d12]: #day-12---the-n-body-problem
[d13]: #day-13---care-package
[d14]: #day-14---space-stoichiometry
[d15]: #day-15---oxygen-system
[d16]: #day-16---flawed-frequency-transmission
[d17]: #day-17---set-and-forget
[d18]: #day-18---many-worlds-interpretation
[d19]: #day-19---tractor-beam
[d20]: #day-20---donut-maze
[d21]: #day-21---springdroid-adventure
[d22]: #day-22---slam-shuffle
[d23]: #day-23---category-six
[d24]: #day-24---planet-of-discord

[d01-problem]: https://adventofcode.com/2019/day/1
[d02-problem]: https://adventofcode.com/2019/day/2
[d03-problem]: https://adventofcode.com/2019/day/3
[d04-problem]: https://adventofcode.com/2019/day/4
[d05-problem]: https://adventofcode.com/2019/day/5
[d06-problem]: https://adventofcode.com/2019/day/6
[d07-problem]: https://adventofcode.com/2019/day/7
[d08-problem]: https://adventofcode.com/2019/day/8
[d09-problem]: https://adventofcode.com/2019/day/9
[d10-problem]: https://adventofcode.com/2019/day/10
[d11-problem]: https://adventofcode.com/2019/day/11
[d12-problem]: https://adventofcode.com/2019/day/12
[d13-problem]: https://adventofcode.com/2019/day/13
[d14-problem]: https://adventofcode.com/2019/day/14
[d15-problem]: https://adventofcode.com/2019/day/15
[d16-problem]: https://adventofcode.com/2019/day/16
[d17-problem]: https://adventofcode.com/2019/day/17
[d18-problem]: https://adventofcode.com/2019/day/18
[d19-problem]: https://adventofcode.com/2019/day/19
[d20-problem]: https://adventofcode.com/2019/day/20
[d21-problem]: https://adventofcode.com/2019/day/21
[d22-problem]: https://adventofcode.com/2019/day/22
[d23-problem]: https://adventofcode.com/2019/day/23
[d24-problem]: https://adventofcode.com/2019/day/24
[d01-solution]: solutions/day01.py
[d02-solution]: solutions/day02.py
[d03-solution]: solutions/day03.py
[d04-solution]: solutions/day04.py
[d05-solution]: misc/day05/walkthrough_solution.py
[d06-solution]: solutions/day06.py
[d07-solution]: solutions/day07.py
[d08-solution]: solutions/day08.py
[d09-solution]: misc/day09/walkthrough_solution.py
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
[d23-solution]: solutions/day23.py
[d24-solution]: solutions/day24.py

[py-cond-expr]:               https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-builtin-str]:             https://docs.python.org/3/library/functions.html#func-str
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-ord]:             https://docs.python.org/3/library/functions.html#ord
[py-builtin-chr]:             https://docs.python.org/3/library/functions.html#chr
[py-builtin-next]:            https://docs.python.org/3/library/functions.html#next
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-builtin-pow]:             https://docs.python.org/3/library/functions.html#pow
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
[py-str-strip]:               https://docs.python.org/3/library/stdtypes.html#str.strip
[py-str-replace]:             https://docs.python.org/3/library/stdtypes.html#str.replace
[py-str-splitlines]:          https://docs.python.org/3/library/stdtypes.html#str.splitlines
[py-range]:                   https://docs.python.org/3/library/stdtypes.html#range
[py-set]:                     https://docs.python.org/3/library/stdtypes.html?#set
[py-frozenset]:               https://docs.python.org/3/library/stdtypes.html?#frozenset
[py-operator]:                https://docs.python.org/3/library/operator.html
[py-operator-add]:            https://docs.python.org/3/library/operator.html#operator.add
[py-operator-mul]:            https://docs.python.org/3/library/operator.html#operator.mul
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-namedtuple]:  https://docs.python.org/3/library/collections.html#collections.namedtuple
[py-collections-deque]:       https://docs.python.org/3/library/collections.html#collections.deque
[py-heapq]:                   https://docs.python.org/3/library/heapq.html
[py-itertools]:               https://docs.python.org/3/library/itertools.html
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-itertools-product]:       https://docs.python.org/3/library/itertools.html#itertools.product
[py-itertools-permutations]:  https://docs.python.org/3/library/itertools.html#itertools.permutations
[py-itertools-combinations]:  https://docs.python.org/3/library/itertools.html#itertools.combinations
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-re]:                      https://docs.python.org/3/library/re.html
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-math]:                    https://docs.python.org/3/library/math.html
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
[py-math-ceil]:               https://docs.python.org/3/library/math.html#math.ceil
[py-math-atan2]:              https://docs.python.org/3/library/math.html#math.atan2
[py-copy]:                    https://docs.python.org/3/library/copy.html
[py-copy-deepcopy]:           https://docs.python.org/3/library/copy.html#copy.deepcopy
[py-unpacking]:               https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[algo-manhattan]:     https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:      https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-bfs]:           https://en.wikipedia.org/wiki/Breadth-first_search
[algo-kahn]:          https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
[algo-binsrc]:        https://en.wikipedia.org/wiki/Binary_search_algorithm
[algo-wall-follower]: https://en.wikipedia.org/wiki/Maze_solving_algorithm#Wall_follower
