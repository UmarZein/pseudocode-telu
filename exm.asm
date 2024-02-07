	.text
	.file	"my_module"
	.globl	main
	.p2align	4, 0x90
	.type	main,@function
main:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	leaq	_GLOBAL_OFFSET_TABLE_(%rip), %rax
	movabsq	$123123123456789, %rsi
	movq	%rsi, (%rsp)
	movabsq	$.Lhey@GOTOFF, %rdi
	addq	%rax, %rdi
	xorl	%eax, %eax
	callq	printf@PLT
	xorl	%eax, %eax
	popq	%rcx
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end0:
	.size	main, .Lfunc_end0-main
	.cfi_endproc

	.type	.Lhey,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lhey:
	.asciz	"Hello, %lli!"
	.size	.Lhey, 13

	.section	".note.GNU-stack","",@progbits
