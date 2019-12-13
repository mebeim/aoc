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
- [Day 12 - Day 12 - The N-Body Problem][d12]
- [Day 13 - Care Package][d13]


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
Manhattan distance from the origin to the closest intersection.

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
finding algorithm, like
[Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).

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


[d01]: #day-1---the-tyranny-of-the-rocket-equation
[d02]: #day-2---1202-program-alarm
[d03]: #day-3---crossed-wires
[d04]: #day-4---secure-container
[d05]: #day-5---sunny-with-a-chance-of-asteroids
[d06]: #day-6---universal-orbit-map
[d07]: #day-7---amplification-circuit
[d08]: #day-8---space-image-format
[d09]: #day-9---sensor-boost
[d12]: #day-12---the-n-body-problem
[d13]: #day-13---care-package

[d01-problem]: https://adventofcode.com/2019/day/1
[d02-problem]: https://adventofcode.com/2019/day/2
[d03-problem]: https://adventofcode.com/2019/day/3
[d04-problem]: https://adventofcode.com/2019/day/4
[d05-problem]: https://adventofcode.com/2019/day/5
[d06-problem]: https://adventofcode.com/2019/day/6
[d07-problem]: https://adventofcode.com/2019/day/7
[d08-problem]: https://adventofcode.com/2019/day/8
[d09-problem]: https://adventofcode.com/2019/day/9
[d12-problem]: https://adventofcode.com/2019/day/12
[d13-problem]: https://adventofcode.com/2019/day/13
[d01-solution]: day01_clean.py
[d02-solution]: day02_clean.py
[d03-solution]: day03_clean.py
[d04-solution]: day04_clean.py
[d05-solution]: misc/day05/walkthrough_solution.py
[d06-solution]: day06_clean.py
[d07-solution]: day07_clean.py
[d08-solution]: day08_clean.py
[d09-solution]: misc/day09/walkthrough_solution.py
[d12-solution]: day12_clean.py
[d13-solution]: day13_clean.py

[py-cond-expr]:               https://docs.python.org/3/reference/expressions.html#conditional-expressions
[py-builtin-map]:             https://docs.python.org/3/library/functions.html#map
[py-builtin-sum]:             https://docs.python.org/3/library/functions.html#sum
[py-builtin-min]:             https://docs.python.org/3/library/functions.html#min
[py-builtin-zip]:             https://docs.python.org/3/library/functions.html#zip
[py-builtin-any]:             https://docs.python.org/3/library/functions.html#any
[py-builtin-all]:             https://docs.python.org/3/library/functions.html#all
[py-builtin-filter]:          https://docs.python.org/3/library/functions.html#filter
[py-builtin-enumerate]:       https://docs.python.org/3/library/functions.html#enumerate
[py-operator]:                https://docs.python.org/3/library/operator.html
[py-operator-add]:            https://docs.python.org/3/library/operator.html#operator.add
[py-operator-mul]:            https://docs.python.org/3/library/operator.html#operator.mul
[py-collections]:             https://docs.python.org/3/library/collections.html
[py-collections-defaultdict]: https://docs.python.org/3/library/collections.html#collections.defaultdict
[py-collections-namedtuple]:  https://docs.python.org/3/library/collections.html#collections.namedtuple
[py-heapq]:                   https://docs.python.org/3/library/heapq.html
[py-itertools]:               https://docs.python.org/3/library/itertools.html
[py-itertools-permutations]:  https://docs.python.org/3/library/itertools.html#itertools.permutations
[py-itertools-combinations]:  https://docs.python.org/3/library/itertools.html#itertools.combinations
[py-itertools-count]:         https://docs.python.org/3/library/itertools.html#itertools.count
[py-re]:                      https://docs.python.org/3/library/re.html
[py-functools]:               https://docs.python.org/3/library/functools.html
[py-functools-reduce]:        https://docs.python.org/3/library/functools.html#functools.reduce
[py-math]:                    https://docs.python.org/3/library/math.html
[py-math-gcd]:                https://docs.python.org/3/library/math.html#math.gcd
