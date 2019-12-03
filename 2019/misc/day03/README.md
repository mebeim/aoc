Day 3 2019, upping the ante
===========================

The script provided here is a solution to the more general problem where we can
have an arbitrary number of wires in an arbitrary big N-dimensional space.

For simplicity's sake, N is chosen to be 26, just so that each direction in the
26-dimentional space can be associated to an alphabet letter.

Moves are represented as an alphabet letter followed by a positive integer x: an
uppercase letter means "go forward x steps" in that direction, while a lowercase
letter means "go backward x steps".


Generating the input
--------------------

While the idea itself works just fine, the problem with this generalized puzzle
is that it is more complicated to generate a valid input than to solve it.

I couldn't come up with a simple way of doing so. The provided example input is
nothing else than my original puzzle input with two more points (basically
copies of the original ones) and one more (very silly and manually added)
dimension 'C', with the letters 'R', 'L', 'U', 'D' replaced with 'A', 'a', 'B',
'b' respectively.

To generate a valid input for the problem, the following constraints should be
respected:

 1. Wires cannot pass through to the origin (except when they start).
 2. Wires cannot immediately go back on the same directionafter one move (e.g.
    a move 'M' followed by a move 'm').
 3. All wires must cross together at least once in one point.
 4. Ideally, more full intersections should be present, otherwise the problem is
    just simplified.

Constraints 3 and 4 here are not simple to respect and make it difficult to
generate a valid input.
