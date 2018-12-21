#include <stdio.h>
#include <stdlib.h>

#ifndef DEBUG
	#define fprintf(...) do {} while(0)
	#define fflush(...) do {} while(0)
#endif

typedef long long int reg;

int main(int argc, char* argv[]) {
	reg r0 = atoll(argv[1]);
	reg ip = 0;
	reg r2 = 0;
	reg r3 = 0;
	reg r4 = 0;
	reg r5 = 0;

 LL0: fprintf(stderr, "%2d\n", 0); fflush(stderr);   r5 = 123;
 LL1: fprintf(stderr, "%2d\n", 1); fflush(stderr);   r5 &= 456;
 LL2: fprintf(stderr, "%2d\n", 2); fflush(stderr);   r5 = (r5 == 72) ? 1 : 0;
 LL3: fprintf(stderr, "%2d\n", 3); fflush(stderr);   if (r5) goto LL5;
 LL4: fprintf(stderr, "%2d\n", 4); fflush(stderr);   goto LL1;
 LL5: fprintf(stderr, "%2d\n", 5); fflush(stderr);   r5 = 0;
 LL6: fprintf(stderr, "%2d\n", 6); fflush(stderr);   r4 = r5 | 65536;
 LL7: fprintf(stderr, "%2d\n", 7); fflush(stderr);   r5 = 13159625;
 LL8: fprintf(stderr, "%2d\n", 8); fflush(stderr);   r3 = r4 & 255;
 LL9: fprintf(stderr, "%2d\n", 9); fflush(stderr);   r5 += r3;
LL10: fprintf(stderr, "%2d\n", 10); fflush(stderr);  r5 &= 0xffffff;
LL11: fprintf(stderr, "%2d\n", 11); fflush(stderr);  r5 *= 65899;
LL12: fprintf(stderr, "%2d\n", 12); fflush(stderr);  r5 &= 0xffffff;
LL13: fprintf(stderr, "%2d\n", 13); fflush(stderr);  r3 = (256 > r4) ? 1 : 0;
LL14: fprintf(stderr, "%2d\n", 14); fflush(stderr);  if (r3) goto LL16;
LL15: fprintf(stderr, "%2d\n", 15); fflush(stderr);  goto LL17;
LL16: fprintf(stderr, "%2d\n", 16); fflush(stderr);  goto LL28;
LL17: fprintf(stderr, "%2d\n", 17); fflush(stderr);  r3 = 0;
LL18: fprintf(stderr, "%2d\n", 18); fflush(stderr);  r2 = r3 + 1;

	// Optimization:
	r3 = r4/256;
	r2 = r4/256 + 1;

	fprintf(
		stderr,
		"ip %2d: muli        2      256 2 | %12d %8d %8d %8d %8d %13d\n",
		20, r0, ip, r2, r3, r4, r5
	);
	fflush(stderr);

LL19: fprintf(stderr, "%2d\n", 19); fflush(stderr);  r2 *= 256;
LL20: fprintf(stderr, "%2d\n", 20); fflush(stderr);  r2 = (r2 > r4) ? 1 : 0;
LL21: fprintf(stderr, "%2d\n", 21); fflush(stderr);  if (r2) goto LL23;
LL22: fprintf(stderr, "%2d\n", 22); fflush(stderr);  goto LL24;
LL23: fprintf(stderr, "%2d\n", 23); fflush(stderr);  goto LL26;
LL24: fprintf(stderr, "%2d\n", 24); fflush(stderr);  r3 += 1;
LL25: fprintf(stderr, "%2d\n", 25); fflush(stderr);  goto LL18;
LL26: fprintf(stderr, "%2d\n", 26); fflush(stderr);  r4 = r3;
LL27: fprintf(stderr, "%2d\n", 27); fflush(stderr);  goto LL8;

	printf("--- 0x%x\n", r5);

LL28: fprintf(stderr, "%2d\n", 28); fflush(stderr);  r3 = (r5 == r0) ? 1 : 0;
LL29: fprintf(stderr, "%2d\n", 29); fflush(stderr);  if (r3) goto END;
LL30: fprintf(stderr, "%2d\n", 30); fflush(stderr);  goto LL6;
 END: return 0;
}
