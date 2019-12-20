AoC 2019 walkthrough
====================

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
-  Day 11 - Space Police: *TODO*
- [Day 12 - The N-Body Problem][d12]
- [Day 13 - Care Package][d13]
-  Day 14 - Oxygen System: *TODO*
-  Day 15 - Set and Forget: *TODO*
- [Day 16 - Flawed Frequency Transmission][d16]
-  Day 17 - Set and Forget: *TODO*
- [Day 18 - Many-Worlds Interpretation][d18]
-  Day 19 - Tractor Beam: *TODO*
- [Day 20 - Donut Maze][d20]


Day 1 - The Tyranny of the Rocket Equation
------------------------------------------

[Problem statement][d01-problem] — [Complete solution][d01-solution]

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
        n = max(n // 3 - 2)
        total += n

print('Part 2:', total)
```

First puzzle of the year, so not really that much of a challenge, but still fun!


Day 2 - 1202 Program Alarm
--------------------------

[Problem statement][d02-problem] — [Complete solution][d02-solution]

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

Quite simple, we can just emuate it with a loop. To make it fancier, we can
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
we can just run a brute-force search trying all of them:

```python
for a in range(100):
    for b in range(100):
        if run(program[:], a, b) == 19690720:
            break

print('Part 2:', a * 100 + b)
```


Day 3 - Crossed Wires
---------------------

[Problem statement][d03-problem] — [Complete solution][d03-solution]

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

First, parse the moves with [`map()`][py-builtin-map] and a simple funciton that
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
`if/ifelse` statements with a bunch of different assignments.

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

We are now asked to calculate the shortest cumualative distance (in steps) that
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

visited1, steps1 = get_visited(moves1)
visited2, steps2 = get_visited(moves2)
intersections = visited1 & visited2
best = min(steps1[p] + steps2[p] for p in intersections)
print('Part 2:', best)
```


Day 4 - Secure Container
------------------------

[Problem statement][d04-problem] — [Complete solution][d04-solution]

### Part 1

Bruteforcing passwords! We are given the lower and upper bounds for the value of
a six-digit password, and we need to determine how many valid passwords are in
such range.

A valid password must:

- Have at least two adjacent matching digits.
- Be composed of non-decreasing digits (from left to right).

An iterator over pairs of adjacent characters of a string can be easily obtained
using the [`zip()`][py-builtin-zip] build-in function. If we convert our values
in string form: this will make our life much easier. Since we are only dealing
with ASCII digits, and the ASCII values for digits are ordered just like the
digits, we don't even need to care about converting them back to integers to
compare them.

```python
digits = str(value)
pairs = tuple(zip(digits, digits[1:]))
```

To check if there are at least two adjacent matching digits, we can iterate over
the pairs of adjacent digits and check if any pair of equal digits exists using
the [`any()`][py-builtin-any] build-in function.

```python
has_matching_pair = any(a == b for a, b in pairs)
```

As per the second requirement, to check if a number is only composed of
non-decreasing digits, we can iterate over the pairs of adjacent digits and use
the [`all()`][py-builtin-all] build-in function to check if the condition is met
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

[Problem statement][d05-problem] — [Complete solution][d05-solution]

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

[Problem statement][d06-problem] — [Complete solution][d06-solution]

### Part 1

We are given a list of "orbits". Each orbit is represented as the name of two
planets divided by a closed parens `)` symbol. `A)B` means that planet `B`
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
destination can just be taken by the old `T` tree.

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

        if planet not in visited:
            visited.add(planet)

            if planet == dst:
                return dist

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

[Problem statement][d07-problem] — [Complete solution][d07-solution]

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
feedback loop, meaning that after stargint each one with a different phase
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

[Problem statement][d08-problem] — [Complete solution][d08-solution]

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
multiplying those two numbers togeter to get a "checksum", which is the answer.

We can do this pretty cleanly using the [`min()`][py-builtin-min] function. With
the `key=` function parameter, we can say that we want to find a layer `l` such
that the count of zeroes is the minimum. So here's part one:

```python
best = min(layers, key=lambda l: l.count('0'))
checksum = best.count('1') * best.count('2')
print('Part 1:', checksum)
```

### Part 2

We are now todl that each pixel can be either black (`0`), white (`1`) or
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

Now that's readable, and we succesfully got our part 2 answer!



Day 9 - Sensor Boost
--------------------

[Problem statement][d09-problem] — [Complete solution][d09-solution]

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

[Problem statement][d10-problem] — [Complete solution][d10-solution]

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
divide both numerator and denominator by their gratest common divisor. For this,
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
overhead of dictionary operations would only outweight the saved computation
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
on a given line of sight will be destroied on the second rotation of the
station, after the laser beam completes a full cycle.

First of all, the answer for part 1 was greater than 200, so we only need to
sweep for one cycle, since we have > 200 asteroids in direct line of sight. The
following solution makes this assumption, but it's trivial to generalize the
code just by adding one more loop to re-scan the asteroids after each full
rotation.

To know which asteroid will be destroyed as 200th, we need to order their
positions based on the ray on which they are placed. Contraty to the first part,
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
function takes `y` and `x` as parameteers (in this exact order) and outputs a
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


Day 12 - The N-Body Problem
---------------------------

[Problem statement][d12-problem] — [Complete solution][d12-solution]

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
to efficently get all the unique couples of moons. This means that we'll need to
modify the velocity of both inside the loop, but that's no problem! Now let's
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
optimization here, just a reasonably good and cool loking solution.

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
We'll use [`gcd()`][py-math-gcd] (gratest common divisor) from the
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

### Considerations

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

This property is pretty cool, but I am not enough of a matematician to write a
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

[Problem statement][d13-problem] — [Complete solution][d13-solution]

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
by outputing groups of three values: `x`, `y`, and a "tile ID". The tile ID
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


Day 16 - Flawed Frequency Transmission
--------------------------------------

[Problem statement][d16-problem] — [Complete solution][d16-solution]

### Part 1

Although the problem statement for today's input is basically a reading
comprehension challenge, the first part of this problem is pretty simple. If
something is uncleaer, I'd recommend reading the original problem statement
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
still needs to be exended, and we then need to skip the first number.

If we take a look at the pattern `(0, 1, 0, -1)`, and read above again:

> - Multiply each `j`-th digit of the list by the corresponding `j`-th number
>   of the new pattern `P`.

This means that:

1. Since we are repeating each number in the pattern a bunch of times, we would
   end up multiplying a bunch of digits by `0`, therefore we could just "ignore"
   them.
2. For the other two pattern values, we can completely ignore the fact that the
   opretion to perform is a multiplication, since they are `1` and `-1`
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
2. Repeat the input list of intgers 10000 (ten thousand) times.
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

### Considerations

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
[`LOAD_GLOBAL`](https://docs.python.org/3/library/dis.html#opcode-LOAD_GLOBAL),
opcode used for global variables (used all over the place in the main body of
the script). Simply moving the second part inside a function gives me a speedup
of about 35% in CPython 3 and 16% in PyPy3, with the new times being ~11s and
~350ms respectively. Conclusion: running Python code in the global namespace
sucks!

With this said, CPython still takes too much for my taste. I am not sure if this
is because there is some other significant optimization to be made (or any other
clever trick) for CPython, but it nonetheless bothers me a bit, particualrly
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


Day 18 - Many-Worlds Interpretation
-----------------------------------

[Problem statement][d18-problem] — [Complete solution][d18-solution]

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
is always `1`, we can use the [Breadth First Search][algo-bfs] to explore it.
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
list of adjacent nodes will never include the start (`@`), as we only are
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
def expensive_function(a, b, c, cache={}): # The cache={} dictionaty here is only
    if (a, b, c) in cache:                 # created once at the time of definition
        return cache[a, b, c]              # of the function! If we do not pass
                                           # any value to overwrite it, it keeps
    # compute result...                    # being the same dictionaty.

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

There is still *one little problem* thouhg. Since `@lru_cache` too uses a
dictionary to cache arguments and resutls, all the arguments need to be
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
string to our updated `minimum_steps()` function, we can treat each characer as
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
graph are identified by thir corresponding character on the grid, and we want
to have four different identifiers of course.

Since we are going to re-start the search using the a new graph, first we'll
need to clear all the data previously cached by `@lru_cache`. This can be easily
done by calling `.cache_clear()` on every decorated function that we used.

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


Day 20 - Donut Maze
-------------------

[Problem statement][d20-problem] — [Complete solution][d20-solution]

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
- No otuer portal at depth 0 can be used.

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
[d12]: #day-12---the-n-body-problem
[d13]: #day-13---care-package
[d16]: #day-16---flawed-frequency-transmission
[d18]: #day-18---many-worlds-interpretation
[d20]: #day-20---donut-maze

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
[d12-problem]: https://adventofcode.com/2019/day/12
[d13-problem]: https://adventofcode.com/2019/day/13
[d16-problem]: https://adventofcode.com/2019/day/16
[d18-problem]: https://adventofcode.com/2019/day/18
[d20-problem]: https://adventofcode.com/2019/day/20
[d01-solution]: day01_clean.py
[d02-solution]: day02_clean.py
[d03-solution]: day03_clean.py
[d04-solution]: day04_clean.py
[d05-solution]: misc/day05/walkthrough_solution.py
[d06-solution]: day06_clean.py
[d07-solution]: day07_clean.py
[d08-solution]: day08_clean.py
[d09-solution]: misc/day09/walkthrough_solution.py
[d10-solution]: day10_clean.py
[d12-solution]: day12_clean.py
[d13-solution]: day13_clean.py
[d16-solution]: day16_clean.py
[d18-solution]: day18_clean.py
[d20-solution]: day20_clean.py

[py-cond-expr]:               https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-builtin-str]:             https://docs.python.org/3/library/functions.html#func-str
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-builtin-sorted]:          https://docs.python.org/3/library/functions.html#sorted
[py-str-join]:                https://docs.python.org/3/library/stdtypes.html#str.join
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
[py-itertools-permutations]:  https://docs.python.org/3/library/itertools.html#itertools.permutations
[py-itertools-combinations]:  https://docs.python.org/3/library/itertools.html#itertools.combinations
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-re]:                      https://docs.python.org/3/library/re.html
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-functools-lru_cache]:     https://docs.python.org/3/library/functools.html#functools.lru_cache
[py-math]:                    https://docs.python.org/3/library/math.html
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
[py-math-atan2]:              https://docs.python.org/3/library/math.html#math.atan2
[py-unpacking]:               https://docs.python.org/3/tutorial/controlflow.html#unpacking-argument-lists

[algo-manhattan]: https://en.wikipedia.org/wiki/Taxicab_geometry#Formal_definition
[algo-dijkstra]:  https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
[algo-bfs]:       https://en.wikipedia.org/wiki/Breadth-first_search
