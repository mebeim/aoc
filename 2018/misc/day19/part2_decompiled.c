r0 = 0;
r4 = 1LL;

do {
	r5 = 1LL;
	do {
		if ( r5 * r4 == 10551319 )
			r0 += r4;
		++r5;
	} while ( r5 <= 10551319 );
	++r4;
} while ( r4 != 10551320 );


// Rewritten cleanly:

r0 = 0;        // Accumulator.
r2 = 10551319; // N

for (r4 = 1; r4 <= r2; r4++) {
	for (r5 = 1; r5 <= r2; r5++) {

		// If A*B == N then A is a divisor of N.

		if (r4 * r5 == r2)
			r0 += r4; // Add A to accumulator.
	}
}

// r0 now holds the sum of the divisors of N (1 and N included).
