.section .text

.global malloc

#assuming c convention to be able to link with libc malloc
malloc:
    movq %rdi, %rdx
    movq $12, %rax      #brk
    xorq %rdi, %rdi     #0 to get current brk
    syscall
    movq %rax, %rdi
    addq %rdx, %rdi     #new brk
    movq %rax, %rdx
    movq $12, %rax      #brk
    syscall
    cmpq %rax, %rdi
    je _success
    xorq %rax, %rax     #return null
    ret
_success:
    movq %rdx, %rax
    ret
