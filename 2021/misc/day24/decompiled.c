int __cdecl main(int argc, const char **argv, const char **envp)
{
  char *v3; // rbx
  char *v4; // rsi
  __int64 v5; // r8
  _BOOL8 v6; // rax
  __int64 v7; // rsi
  __int64 v8; // rdi
  __int64 v9; // rsi
  __int64 v10; // rsi
  __int64 v11; // rdi
  __int64 v12; // rsi
  __int64 v13; // rdi
  __int64 v14; // rsi
  __int64 v15; // rsi
  __int64 v16; // rdi
  __int64 v17; // rsi
  __int64 v18; // rdi

  v3 = (char *)input;
  do
  {
    v4 = v3;
    v3 += 4;
    __isoc99_scanf(&unk_2004, v4, envp);
  }
  while ( &input[14] != (unsigned int *)v3 );
  v5 = input[1];
  v6 = (input[0] + 4LL) * (input[0] != 12LL) % 26 + 15 != v5;
  v7 = (v5 + 11) * v6 + (25 * v6 + 1) * (input[0] + 4LL) * (input[0] != 12LL);
  v8 = (input[2] + 7LL) * (v7 % 26 + 11 != input[2]) + (25LL * (v7 % 26 + 11 != input[2]) + 1) * v7;
  v9 = (input[3] + 2LL) * (v8 % 26 - 14 != input[3]) + v8 / 26 * (25LL * (v8 % 26 - 14 != input[3]) + 1);
  v10 = (input[4] + 11LL) * (v9 % 26 + 12 != input[4]) + v9 * (25LL * (v9 % 26 + 12 != input[4]) + 1);
  v11 = (input[5] + 13LL) * (v10 % 26 - 10 != input[5]) + v10 / 26 * (25LL * (v10 % 26 - 10 != input[5]) + 1);
  v12 = (input[6] + 9LL) * (v11 % 26 + 11 != input[6]) + (25LL * (v11 % 26 + 11 != input[6]) + 1) * v11;
  v13 = (input[7] + 12LL) * (v12 % 26 + 13 != input[7]) + (25LL * (v12 % 26 + 13 != input[7]) + 1) * v12;
  v14 = (input[8] + 6LL) * (v13 % 26 - 7 != input[8]) + v13 / 26 * (25LL * (v13 % 26 - 7 != input[8]) + 1);
  v15 = (input[9] + 2LL) * (v14 % 26 + 10 != input[9]) + v14 * (25LL * (v14 % 26 + 10 != input[9]) + 1);
  v16 = (input[10] + 11LL) * (v15 % 26 - 2 != input[10]) + v15 / 26 * (25LL * (v15 % 26 - 2 != input[10]) + 1);
  v17 = (input[11] + 12LL) * (v16 % 26 - 1 != input[11]) + v16 / 26 * (25LL * (v16 % 26 - 1 != input[11]) + 1);
  v18 = (input[12] + 3LL) * (v17 % 26 - 4 != input[12]) + v17 / 26 * (25LL * (v17 % 26 - 4 != input[12]) + 1);
  printf(
    "z: %ld\n",
    (input[13] + 13LL) * (v18 % 26 - 12 != input[13]) + v18 / 26 * (25LL * (v18 % 26 - 12 != input[13]) + 1));
  return 0;
}
