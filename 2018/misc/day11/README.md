Generate a video animation of the grid (and the solutions) for different inputs of the puzzle. Using PyPy3 is recommended since it is way faster than CPython. [YouTube video example](https://www.youtube.com/watch?v=hqq_EE6H5UY).

Note that the algorithm for generating solutions is not optimized at all, so it might take quite some time to generate all the frames you want.

	$ pypy3 generate_grids.py
	$ ./generate_animation.py

Manual tuning of the aspect of the resulting video can be done editing variables in `generate_animation.py`.
