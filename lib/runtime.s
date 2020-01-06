.section .text

.global printString
.global printInt
.global error
.global readInt
.global readString
.global _concat

printString:
    pushq %rdx
    pushq %rsi
    pushq %rdi
    movq 32(%rsp), %rax
    movl (%rax), %edx   #len
    leaq 4(%rax), %rsi  #string
    mov $1, %rax	    #write
	mov $1, %rdi	    #stdout
	syscall
    movl $1, %eax	    #write
    movl $1, %edx       #one character
    pushq $10           #newline
    movq %rsp, %rsi     #string
    syscall
    addq $8, %rsp
    popq %rdi
    popq %rsi
    popq %rdx
    ret

printInt:
    pushq %rdi
    pushq %rdx
    pushq %r8
    pushq %rsi
	pushq %rbp
	movq %rsp, %rbp
    movq 48(%rbp), %rax
    movl $10, %r8d
    subq $8, %rsp
    cmpq $0, %rax
    jge _printInt_chkcond
    movq %rax, %r8
    movb $45, (%rsp)        #minus sign
    movq %rsp, %rsi         #string
    movl $1, %edx           #length
    movl $1, %eax           #write
    movl $1, %edi           #stdout
    syscall
    movq %r8, %rax
    negq %rax
    movl $10, %r8d
    jmp _printInt_chkcond
_printInt_loop:
    xorq %rdx, %rdx
    divq %r8
	movb %dl, (%rsp)	    #[rsp + 1] <- rax % 10
	addb $48, (%rsp)		#[rsp + 1] = [rsp - 1] + '0'
    subq $1, %rsp
_printInt_chkcond:
    testq %rax, %rax
	jnz _printInt_loop
    leaq 1(%rsp), %rsi     #string
    leaq -8(%rbp), %rdx
    subq %rsp, %rdx         #length
    mov $1, %rax	        #write
	mov $1, %rdi	        #stdout
	syscall
    movl $1, %eax	    #write
    movl $1, %edx       #one character
    pushq $10           #newline
    movq %rsp, %rsi     #string
    syscall
	movq %rbp, %rsp
    popq %rbp
    popq %rsi
    popq %r8
    popq %rdx
    popq %rdi
	ret

_serror:
    .long 14
    .ascii "runtime error\12"

error:
    pushq $_serror
    call printString
    movl $60, %eax      #exit
    movl $1, %edi       #code
    syscall

readInt:
    pushq %rdi
    pushq %rdx
    pushq %rsi
    pushq %r8
    pushq %rbx
    xorq %rbx, %rbx
    xorq %r8, %r8
    xorq %rdi, %rdi     #stdin
    movq $1, %rdx       #count
    pushq $0
    movq %rsp, %rsi     #buf
    xorq %rax, %rax     #read
    syscall
    testl %eax, %eax
    jz _readInt_loop_end
    cmpb $45, (%rsp)
    jne _readInt_chkcond
    movl $1, %r8d
_readInt_loop:
    xorq %rax, %rax     #read
    syscall
_readInt_chkcond:
    testl %eax, %eax
    jz _readInt_loop_end
    cmpb $48, (%rsp)
    jl _readInt_loop_end
    cmpb $57, (%rsp)
    jg _readInt_loop_end
    leaq -24(%rbx, %rbx, 4), %rbx
    shlq $1, %rbx
    addq (%rsp), %rbx
    jmp _readInt_loop
_readInt_loop_end:
    testb %r8b, %r8b
    jz _positive_result
    negq %rbx
_positive_result:
    movq %rbx, %rax
    addq $8, %rsp
    popq %rbx
    popq %r8
    popq %rsi
    popq %rdx
    popq %rdi
    ret

#rdi -> size
_allocString:
    pushq %rcx
    pushq %rdx
    pushq %rsi
    pushq %rdi
    pushq %r8
    pushq %r9
    pushq %r10
    pushq %r11
    pushq %rbp
    movq %rsp, %rbp
    andq $-16, %rsp
    addq $4, %rdi   #4 bytes for size
    call malloc
    movq %rbp, %rsp
    popq %rbp
    popq %r11
    popq %r10
    popq %r9
    popq %r9
    popq %rdi
    popq %rsi
    popq %rdx
    popq %rcx
    ret

readString:
    pushq %rdi
    pushq %rdx
    pushq %rsi
    pushq %rcx
    pushq %r8
    pushq %rbp
    movq %rsp, %rbp
    xorq %rdi, %rdi     #stdin
    movq $1, %rdx       #count
    subq $7, %rsp
_readString_loop:
    dec %rsp
    movq %rsp, %rsi     #buf
    xorq %rax, %rax     #read
    syscall
_readString_chkcond:
    testl %eax, %eax
    jz _readString_end_loop
    cmpb $10, (%rsp)
    jne _readString_loop
_readString_end_loop:
    leaq -8(%rbp), %rdi
    subq %rsp, %rdi     #length
    call _allocString
    movl %edi, (%rax)   #set length
    leaq -8(%rbp), %rsi #copy from
    leaq 4(%rax), %r8   #copy to
    xorl %ecx, %ecx
    jmp _cpyString_chkcond
_cpyString_body:
    movb (%rsi), %cl
    movb %cl, (%r8)
    decq %rsi
    incq %r8
    decq %rdi
_cpyString_chkcond:
    testq %rdi, %rdi
    jne _cpyString_body
    mov %rbp, %rsp
    popq %rbp
    popq %r8
    popq %rcx
    popq %rsi
    popq %rdx
    popq %rdi
    ret

_concat:
    pushq %rbx
    pushq %rdx
    pushq %rdi
    pushq %rcx
    pushq %rsi
    movq 48(%rsp), %rbx
    movq 56(%rsp), %rdx
    movl (%rbx), %edi
    addl (%rdx), %edi
    call _allocString
    movl %edi, (%rax)
    movl (%rbx), %ecx
    leaq 4(%rbx), %rsi
    leaq 4(%rax), %rdi
    rep movsb
    movl (%rdx), %ecx
    leaq 4(%rdx), %rsi
    rep movsb
    popq %rsi
    popq %rcx
    popq %rdi
    popq %rdx
    popq %rbx
    ret
