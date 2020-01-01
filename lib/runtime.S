.section .text

#TODO inline
#printStringLen(rsi -> string, rdx -> len)
_printStringLen:
	mov $1, %rax	#write
	mov $1, %rdi	#stdout
	syscall
	ret

printString:
    pushq %rdx
    pushq %rsi
    pushq %rdi
    movq 32(%rsp), %rax
    movl (%rax), %edx
    leaq 4(%rax), %rsi
    call _printStringLen
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
    movq 48(%rbp), %rdi
    subq $7, %rsp
    jmp _printInt_chkcond
_printInt_loop:
    movl $-858993459, %edx	#counting edi % 10
	movl %edi, %eax
	mull %edx
	shrl $3, %edx			#edx = edi / 10
	movl %edx, %r8d
	movl $10, %eax
	mull %edx
	subl %edx, %edi
	subq $1, %rsp
	movb %dil, (%rsp)	    #[rsp + 1] <- edi % 10
	addb $48, (%rsp)		#[rsp + 1] = [rsp - 1] + '0'
	movl %r8d, %edi			#edi = edi / 10
_printInt_chkcond:
    testl %edi, %edi
	jnz _printInt_loop
    leaq -8(%rbp), %rsi
    leaq -7(%rbp), %rdx
    subq %rsp, %rdx
	call _printStringLen
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
    pushq _serror
    call printString
    movl $60, %eax      #exit
    movl $1, %edi       #code
    syscall

readInt:
    pushq %rdi
    pushq %rdx
    pushq %rsi
    pushq %rbx
    xorq %rdi, %rdi     #stdin
    movq $1, %rdx       #count
    pushq $0
    movq %rsp, %rsi     #buf
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
    addq ($rsp), %rbx
    jmp _readInt_loop
_readInt_loop_end:
    movq %rbx, %rax
    addq $8, %rsp
    popq %rbx
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
    andq $16, %rsp
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
    pushq %rbp
    movq %rsp, %rbp
    xorq %rdi, %rdi     #stdin
    movq $1, %rdx       #count
    addq $7, %rsp
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
    leaq 7(%rbp), %rdi
    subq %rsp, %rdi
    call _allocString
    movl %edi, (%rax)   #set length
    movl %edi, %ecx     #copy length
    leaq 8(%rbp), %rsi  #copy from
    leaq 4(%rax), %rdi  #copy to
    rep movsb
    mov %rbp, %rsp
    popq %rbp
    popq %rcx
    popq %rsi
    popq %rdx
    popq %rdi

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
