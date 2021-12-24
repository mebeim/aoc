#include <stdio.h>
#include <stdint.h>

// Step 1: compile with gcc -O3 x.c -ox
// Step 2: decompile with IDA
// Step 3: profit

#define add(a, b) (a) += (b)
#define mul(a, b) (a) *= (b)
#define div(a, b) (a) /= (b)
#define mod(a, b) (a) %= (b)
#define eql(a, b) (a) = ((a) == (b))
#define inp(a)    (a) = (input[i++])

unsigned input[14];

int main(void) {
	long x, y, z, w;
	int i;

	for (int zzz = 0; zzz < 14; zzz++)
		scanf("%u", input + zzz);

	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 12);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 4);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 15);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 11);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 11);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 7);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -14);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 2);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 12);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 11);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -10);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 13);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 11);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 9);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 13);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 12);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -7);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 6);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 1);
	add(x, 10);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 2);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -2);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 11);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -1);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 12);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -4);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 3);
	mul(y, x);
	add(z, y);
	inp(w);
	mul(x, 0);
	add(x, z);
	mod(x, 26);
	div(z, 26);
	add(x, -12);
	eql(x, w);
	eql(x, 0);
	mul(y, 0);
	add(y, 25);
	mul(y, x);
	add(y, 1);
	mul(z, y);
	mul(y, 0);
	add(y, w);
	add(y, 13);
	mul(y, x);
	add(z, y);

	printf("z: %ld\n", z);
}
