	.file	"part2.c"
	.intel_syntax noprefix
	.text
	.section	.text.startup,"ax",@progbits
	.p2align 4,,15
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	mov	esi, 1
	xor	eax, eax
.L4:
	mov	rcx, rsi
	mov	edx, 10551319
	.p2align 4,,10
	.p2align 3
.L3:
	lea	rdi, [rax+rsi]
	cmp	rcx, 10551319
	cmove	rax, rdi
	add	rcx, rsi
	sub	rdx, 1
	jne	.L3
	add	rsi, 1
	cmp	rsi, 10551320
	jne	.L4
	rep ret
.L5:
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.3.0-27ubuntu1~18.04) 7.3.0"
	.section	.note.GNU-stack,"",@progbits
