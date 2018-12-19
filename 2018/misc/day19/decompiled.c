r0 = 0;
r4 = 1LL;
do
{
	r5 = 1LL;
	do
	{
		if ( r5 * r4 == 10551319 )
			r0 += r4;
		++r5;
	}
	while ( r5 <= 10551319 );
	++r4;
}
while ( r4 <= 10551319 );
return r0;
