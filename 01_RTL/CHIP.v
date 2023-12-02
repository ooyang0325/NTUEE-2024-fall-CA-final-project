//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
//◆ auipc, jal, jalr
//◆ add, sub, and, xor
//◆ addi, slli, slti, srai
//◆ lw, sw
//◆ mul
//◆ beq, bge, blt, bne
//◆ ecall (the end of program)

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration
    //opcode
    parameter AUIPC = 7'b0010111;
    parameter JAL = 7'b1101111;
    parameter JALR = 7'b1100111;
    parameter ADD = 7'b0110011;
    parameter SUB = 7'b0110011;
    parameter AND = 7'b0110011;
    parameter XOR = 7'b0110011;
    parameter ADDI = 7'b0010011;
    parameter SLLI = 7'b0010011;
    parameter SLTI = 7'b0010011;
    parameter SRAI = 7'b0010011;
    parameter LW = 7'b0000011;
    parameter SW = 7'b0100011;
    parameter MUL = 7'b0110011;
    parameter BEQ = 7'b1100011;
    parameter BGE = 7'b1100011;
    parameter BLT = 7'b1100011;
    parameter BNE = 7'b1100011;
    parameter ECALL = 7'b1110011;

    //funct3
    parameter JALR_FUNCT3 = 3'b000;
    parameter ADD_FUNCT3 = 3'b000;
    parameter SUB_FUNCT3 = 3'b000;
    parameter AND_FUNCT3 = 3'b111;
    parameter XOR_FUNCT3 = 3'b100;
    parameter ADDI_FUNCT3 = 3'b000;
    parameter SLLI_FUNCT3 = 3'b001;
    parameter SLTI_FUNCT3 = 3'b010;
    parameter SRAI_FUNCT3 = 3'b101;
    parameter LW_FUNCT3 = 3'b010;
    parameter SW_FUNCT3 = 3'b010;
    parameter MUL_FUNCT3 = 3'b000;
    parameter BEQ_FUNCT3 = 3'b000;
    parameter BGE_FUNCT3 = 3'b101;
    parameter BLT_FUNCT3 = 3'b100;
    parameter BNE_FUNCT3 = 3'b001;
    parameter ECALL_FUNCT3 = 3'b000;

    //funct7
    parameter ADD_FUNCT7 = 7'b0000000;
    parameter SUB_FUNCT7 = 7'b0100000;
    parameter XOR_FUNCT7 = 7'b0000000;
    parameter SLLI_FUNCT7 = 7'b0000000;
    parameter SRAI_FUNCT7 = 7'b0100000;
    parameter MUL_FUNCT7 = 7'b0000001;


// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;

        reg [6: 0] opcode;
        reg [2: 0] funct3;
        reg [6: 0] funct7;
        reg [4: 0] rs1, rs2, rd;
        reg [31: 0] rs1_data, rs2_data, write_data;
        reg [31: 0] imm;
        reg regwrite;
        reg mul_ready, mul_valid; //for multi-cycle operation
        reg [2: 0] mul_mode;
        reg [63: 0] mul_result;
        reg [31: 0] mul_in_a, mul_in_b;
        reg [31: 0] inst;
        reg [1:0] state, state_nxt;
        


// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),          
        .rs1    (rs1),                
        .rs2    (rs2),                
        .rd     (rd),                 
        .wdata  (write_data),             
        .rdata1 (rs1_data),           
        .rdata2 (rs2_data)
    );

    MULTDIV_unit muldiv_unit(
        .clk(i_clk),
        .rst_n(i_rst_n),
        .valid(mul_valid),
        .ready(mul_ready),
        .mode(mul_mode),
        .in_A(mul_in_a),
        .in_B(mul_in_b),
        .out(mul_result)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
        end
        else begin
            PC <= next_PC;
        end
    end

    always @(*) begin
        inst = i_IMEM_data;
        opcode = inst[6:0];
        funct3 = inst[14:12];
        funct7 = inst[31:25];
        rs1 = inst[19:15];
        rs2 = inst[24:20];
        rd = inst[11:7];
        regwrite = 0;
        mul_valid = 0;
        mul_mode = 0;
        mul_in_a = 0;
        mul_in_b = 0;
        next_PC = PC + 4;
        case(opcode) 
            7'b0010111: begin //auipc
                regwrite = 1;
                imm = inst[31:12];
                write_data = PC + {imm, 12'b0};
            end
            7'b1101111: begin //jal
                regwrite = 1;
                imm[20:0]  = {inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};
                next_PC = $signed({1'b0, PC}) + $signed(imm[20:0]);
                write_data = PC + 4;
            end
            7'b1100111: begin //jalr
                regwrite = 1;
                imm[11:0] = inst[31:20];
                next_PC = $signed({1'b0, rs1_data}) + $signed(imm[11:0]);
                write_data = PC + 4;
            end
            
        endcase

    end

endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module MULDIV_unit(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    // Definition of ports
    input clk, rst_n, valid
    input mode[1:0]; // 0: shift left, 1: shift right, 2: mul
    output ready;
    input [31:0] in_A, in_B;
    output [63:0] out;

    // definition of state
    reg [1:0] state, state_nxt;
    parameter S_IDLE = 2'b00, S_ONE_CYCLE_OP = 2'b01, S_MULTI_CYCLE_OP = 2'b10;

    // definition of internal signals
    reg [31:0] operand_a, operand_b, operand_a_nxt, operand_b_nxt;
    reg [31:0] result;
    reg done;
    reg [63:0] alu_out;
    reg [4:0] counter, counter_nxt;
    reg rdy, rdy_nxt;
    assign ready = rdy;
    assign out = alu_out;

    always @(*) begin
        if (valid) begin
            operand_a_nxt = in_A;
            operand_b_nxt = in_B;
        end
        else begin
            operand_a_nxt = operand_a;
            operand_b_nxt = operand_b;
        end
    end

    always @(*) begin
        case(state)
            S_IDLE: begin
                if(!valid) begin
                    state_nxt = S_IDLE;
                end
                else begin
                    case(mode)
                        2'b00: begin
                            state_nxt = S_ONE_CYCLE_OP;
                        end
                        2'b01: begin
                            state_nxt = S_ONE_CYCLE_OP;
                        end
                        2'b10: begin
                            state_nxt = S_MULTI_CYCLE_OP;
                        end
                        default: begin
                            state_nxt = S_IDLE;
                        end
                    endcase
                end
            end
            S_ONE_CYCLE_OP: begin
                state_nxt = S_IDLE;
            end
            S_MULTI_CYCLE_OP: begin
                if(counter == 31) begin
                    state_nxt = S_IDLE;
                end
                else begin
                    state_nxt = S_MULTI_CYCLE_OP;
                end
            end
        endcase
    end

    always @(*) begin
        if (state == S_MULTI_CYCLE_OP) begin
            if(counter == 31) begin
                rdy_nxt = 1;
                counter_nxt = 0;
            end
            else begin
                rdy_nxt = 0;
                counter_nxt = counter + 1;
            end
        end
        else if (state == S_ONE_CYCLE_OP) begin
            rdy_nxt = 1;
            counter_nxt = 0;
        end
        else begin
            rdy_nxt = 0;
            counter_nxt = 0;
        end
    end

    always @(*) begin
        case(mode)
            2'b00: begin
                alu_out = operand_a <<< operand_b;
            end
            2'b01: begin
                alu_out = operand_a >> operand_b;
            end
            2'b10: begin
                    if(operand_b[counter]) begin
                        alu_out = alu_out + (operand_a <<< counter);
                    end
                    else begin
                        alu_out = alu_out;
                    end
                    if(counter == 31) begin //output the lower 32 bits
                    alu_out = alu_out[31:0];
                    end
                    else begin
                        alu_out = alu_out;
                    end
            end
            default: begin
                alu_out = 0;
            end
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE;
            operand_a <= 0;
            operand_b <= 0;
            result <= 0;
            done <= 0;
            temp <= 0;
            alu_out <= 0;
            counter <= 0;
            rdy <= 0;
        end
        else begin
            state <= state_nxt;
            operand_a <= operand_a_nxt;
            operand_b <= operand_b_nxt;
            alu_out <= alu_out;
            counter <= counter_nxt;
            rdy <= rdy_nxt;
        end
    end
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available
    );

    assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    assign o_mem_cen = i_proc_cen;              //
    assign o_mem_wen = i_proc_wen;              //
    assign o_mem_addr = i_proc_addr;            //
    assign o_mem_wdata = i_proc_wdata;          //
    assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: BONUS

endmodule