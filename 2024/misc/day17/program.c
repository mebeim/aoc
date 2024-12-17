/**
 * gcc -g -O3 -o program program.c
 * ida64 program
 */

#include <stdio.h>

#define combo(v) ((v) <= 3 ? (v) : (v) == 4 ? a : (v) == 5 ? b : (v) == 6 ? c : 0)

/*
	adv x: a = a / (1 << combo(x))
	bxl x: b ^= x
	bst x: b = combo(x) % 8
	jnz x: if a != 0: pc = x
	bxc x: b ^= c
	out x: print(combo(x) % 8)
	bdv x: b = a / (1 << combo(x))
	cdv x: c = a / (1 << combo(x))

	(2, 4) bst a
	(1, 6) bxl 6
	(7, 5) cdv b
	(4, 6) bxc 6
	(1, 4) bxl 4
	(5, 5) out b
	(0, 3) adv 3
	(3, 0) jnz 0
*/

void __attribute__((noinline)) run(unsigned long long a) {
	unsigned long long b = 0;
	unsigned long long c = 0;

label:
	b = combo(4) % 8;
	b ^= 6;
	c = a / (1 << combo(5));
	b ^= c;
	b ^= 4;
	printf("%llu,", combo(5) % 8);
	a /= 1 << combo(3);

	if (a != 0)
		goto label;

	printf("\n");
}

int main(void) {
	run(66171486);
}
