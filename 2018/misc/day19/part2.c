/**
 * Just compile with -O3 and let gcc
 * do half the job for you.
 */

typedef long long int reg;

int main() {
	reg r0 = 1;
	reg r1 = 0;
	reg r2 = 0;
	reg r3 = 0;
	reg r4 = 0;
	reg r5 = 0;

	goto IP17;

IP1:
	r4 = 1;
IP2:
	r5 = 1;
IP3:
	r1 = r4 * r5;

	if (r1 == r2)
		goto IP7;
	else
		goto IP6;

IP6:
	goto IP8;
IP7:
	r0 += r4;
IP8:
	r5++;

	if (r5 > r2)
		goto IP12;
	else
		goto IP3;

IP12:
	r4++;

	if (r4 > r2)
		goto END;
	else
		goto IP2;

IP17:
	r2 += 2;
	r2 *= r2;
	r2 *= 19;
	r2 *= 11;

	r1 += 3;
	r1 *= 22;
	r1 += 17;

	r2 += r1;

	r1 = 27;
	r1 *= 28;
	r1 += 29;
	r1 *= 30;
	r1 *= 14;
	r1 *= 32;

	r2 += r1;
	r0 = 0;

	goto IP1;

END:
	return r0;
}
