.data
    n: .word 10
    
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    # You should store the output into x10
    addi t0, zero, 0
    jal ra, cal

    cal: 
        #save a0, ra for later use
        addi sp, sp ,-8
        sw a0, 0(sp)
        sw ra, 4(sp)
        
        #determine if n is >= 2
        addi t0, zero, 2
        bge a0, t0, else
        
        #if not, return a T(1)=2
        addi t0, zero, 2
        addi sp, sp, 8
        jr ra
    
    else: 
        #get a n/2 and calculate T(n/2)
        addi t3, zero, 2
        div a0, a0, t3
        jal cal
        
        #bring back t1(aka n), ra & bring sp to original
        lw t1, 0(sp)
        lw ra, 4(sp)
        addi sp, sp, 8
        
        #calculate T(n)
        addi t3, zero, 5
        mul t0, t0, t3
        addi t3, zero, 6
        mul t2, t1, t3
        addi t0, t0, 4
        add t0, t0, t2
        jr ra 

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall