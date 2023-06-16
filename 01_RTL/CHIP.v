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
        output [BIT_W-1:0]  o_DMEM_wdata                                                        //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    parameter Branch_7 = 7'b1100011;
    parameter BEQ_3 = 3'b000;
    parameter BNE_3 = 3'b001;
    parameter BLT_3 = 3'b100;
    parameter BGE_3 = 3'b101;
    
    parameter SW_7 = 7'b0100011;

    parameter LW_7 = 7'b0000011;

    parameter JALR_7 = 7'b1100111;

    parameter JAL_7 = 7'b1101111;

    parameter AUIPC_7 = 7'b0010111;
    
    parameter ALU_7 =7'b0110011;
    parameter XOR_3 = 3'b100;
    parameter AND_3 = 3'b111;
    parameter Arithmetic_3 = 3'b000;
    parameter ADD_7 = 7'b0000000;
    parameter SUB_7 = 7'b0100000;
    parameter MUL_7 = 7'b0000001;
    
    parameter IMM_7 = 7'b0010011;
    parameter ADDI_3 = 3'b000;
    parameter SLTI_3 = 3'b010;
    parameter SRAI_3 = 3'b101;
    parameter SLLI_3 = 3'b001;
    
    parameter IF = 3'b000;
    parameter ID = 3'b001;
    parameter EX = 3'b010;
    parameter ME = 3'b011;
    parameter WB = 3'b100;
    parameter MEM =3'b101;
    parameter EXE =3'b110;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg[2:0] state, next_state;

        reg [BIT_W-1:0] PC, next_PC;
        reg[6:0] opcode, opcode_nxt;
        reg[2:0] func3, func3_nxt;
        reg[6:0] func7, func7_nxt;
        reg[4:0] rs1, rs1_nxt;
        reg[4:0] rs2, rs2_nxt;
        reg[4:0] rd, rd_nxt;

        reg[BIT_W-1:0] rs1_data, rs2_data;
        reg[BIT_W-1:0] rs1_data_nxt, rs2_data_nxt;
        reg[BIT_W-1:0] imm, imm_nxt;
        reg[BIT_W-1:0] result,result_nxt;

        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;
        wire reg_wen;
        wire [BIT_W-1:0]rs1_out, rs2_out;
        reg [BIT_W-1:0] nxt_pc,pc;
        wire [BIT_W-1:0]mul_out;
        wire mul_valid;
        wire mul_ready;
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
    assign reg_wen= (state==WB && (opcode==ALU_7||opcode==IMM_7||opcode==LW_7||opcode==JALR_7||opcode==JAL_7||opcode==AUIPC_7));
    assign mem_wen= (opcode==SW_7);
    assign o_IMEM_cen= (state==IF);
    assign o_IMEM_addr =PC;
    assign o_DMEM_wen = (opcode==SW_7);
    assign o_DMEM_cen = ((state==ME)&&(opcode==LW_7||opcode==SW_7));
    assign o_DMEM_addr=result;
    assign o_DMEM_wdata = rs2_data;
    assign mul_valid=(state==EX && opcode==ALU_7&&func7==MUL_7);
    

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (reg_wen),          
        .rs1    (i_IMEM_data[19:15]),                
        .rs2    (i_IMEM_data[24:20]),                  
        .rd     (rd),                 
        .wdata  (result),             
        .rdata1 (rs1_out),           
        .rdata2 (rs2_out)
    );

    MULDIV_unit MUL(
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .i_valid(mul_valid),
        .in_a(rs1_data),
        .in_b(rs2_data),
        .out(mul_out),
        .o_ready(mul_ready)
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit
    always@(*)begin
        if(i_DMEM_stall)begin
            next_state=(state==ME) ?MEM:state;
            
        end 
        else begin
            if(mul_valid||(state==EXE&&!mul_ready)) next_state=EXE;
            else begin
                case(state)
                    IF: next_state = ID;
                    ID: next_state = EX;
                    EX: next_state = ME;
                    EXE: next_state = ME;
                    ME: next_state = WB;
                    MEM: next_state =WB;
                    WB: next_state = IF;
                    default: next_state=state;
                endcase
                
            end 
        end
    end

    always@(*)begin 
        if(i_DMEM_stall) begin
            opcode_nxt=opcode;
            func7_nxt=func7;
            func3_nxt=func3;
            rs1_data_nxt=rs1_data;
            rs2_data_nxt =rs2_data;
            rs1_nxt=rs1;
            rs2_nxt=rs2;
            rd_nxt=rd;
            next_PC=PC;
            nxt_pc=pc;
            imm_nxt=imm;
            result_nxt=result;
        end
        else begin
            
            if(mul_valid||(state==EXE&&!mul_ready)) begin
                opcode_nxt=opcode;
                func7_nxt=func7;
                func3_nxt=func3;
                rs1_data_nxt=rs1_data;
                rs2_data_nxt =rs2_data;
                rs1_nxt=rs1;
                rs2_nxt=rs2;
                rd_nxt=rd;
                next_PC=PC;
                nxt_pc=PC+4;
                imm_nxt=imm;
                result_nxt=mul_out;
            end
            else begin
                opcode_nxt=(state==IF)?i_IMEM_data[6:0]:opcode;
                func7_nxt=(state==IF)?i_IMEM_data[31:25]:func7;
                func3_nxt=(state==IF)?i_IMEM_data[14:12]:func3;
                rs1_nxt=(state==IF)?i_IMEM_data[19:15]:rs1;
                rs2_nxt=(state==IF)? i_IMEM_data[24:20]:rs2;
                rd_nxt=(state==IF)?i_IMEM_data[11:7]:rd;
                
                if(state==IF) begin
                    
                    case(i_IMEM_data[6:0])
                        AUIPC_7:imm_nxt= {i_IMEM_data[31:12],12'b0};
                        JAL_7:imm_nxt= (i_IMEM_data[31]==1)? {11'h7FF,i_IMEM_data[31],i_IMEM_data[19:12],i_IMEM_data[20],i_IMEM_data[30:21],1'b0} : {11'h0,i_IMEM_data[31],i_IMEM_data[19:12],i_IMEM_data[20],i_IMEM_data[30:21],1'b0};
                        JALR_7,LW_7:imm_nxt= (i_IMEM_data[31]==1)? {20'hFFFFF,i_IMEM_data[31:20]} : {20'b0,i_IMEM_data[31:20]};
                        Branch_7:imm_nxt= (i_IMEM_data[31]==1)? {19'h7FFFF,i_IMEM_data[31],i_IMEM_data[7],i_IMEM_data[30:25],i_IMEM_data[11:8],1'b0}  :  {19'b0,i_IMEM_data[31],i_IMEM_data[7],i_IMEM_data[30:25],i_IMEM_data[11:8],1'b0};
                        SW_7:imm_nxt= (i_IMEM_data[31]==1)? {20'hFFFFF,i_IMEM_data[31:25],i_IMEM_data[11:7]} : {20'b0,i_IMEM_data[31:25],i_IMEM_data[11:7]};
                        IMM_7:begin
                            case(i_IMEM_data[14:12])
                                ADDI_3,SLTI_3:imm_nxt= (i_IMEM_data[31]==1)? {20'hFFFFF,i_IMEM_data[31:20]} : {20'b0,i_IMEM_data[31:20]};
                                SRAI_3 ,SLLI_3:imm_nxt= {27'b0,i_IMEM_data[24:20]};
                                default:imm_nxt=0;
                            endcase 
                        end 
                        default:imm_nxt=0;
                    endcase
                end
                else imm_nxt=imm;

                rs1_data_nxt=(state==ID)?rs1_out:rs1_data;
                rs2_data_nxt=(state==ID)?rs2_out:rs2_data;

                if(state==EX) begin
                    case(opcode)
                        Branch_7:begin
                            case(func3)
                                BEQ_3: nxt_pc =($signed(rs1_data)==$signed(rs2_data))?PC+$signed(imm):PC+4;
                                BNE_3: nxt_pc =($signed(rs1_data)!=$signed(rs2_data))?PC+$signed(imm):PC+4;
                                BLT_3: nxt_pc =($signed(rs1_data)<$signed(rs2_data))?PC+$signed(imm):PC+4;
                                BGE_3: nxt_pc =($signed (rs1_data)>=$signed(rs2_data))?PC+$signed(imm):PC+4;
                                default: nxt_pc=PC+4;
                            endcase
                            result_nxt=result;
                        end 
                        SW_7:begin
                            result_nxt=rs1_data+$signed(imm);
                            nxt_pc=PC+4;
                        end
                        LW_7:begin
                            result_nxt=rs1_data+$signed(imm);
                            nxt_pc=PC+4;
                        end
                        JALR_7: begin
                            nxt_pc= rs1_data+$signed(imm);
                            result_nxt= PC+4;
                        end 
                        JAL_7:begin
                            nxt_pc= PC+$signed(imm);
                            result_nxt =PC+4;
                        end
                        AUIPC_7: begin
                            result_nxt= PC+$signed(imm);
                            nxt_pc= PC+4;
                        end
                        IMM_7: begin
                            case(func3)
                                ADDI_3: result_nxt= rs1_data+$signed(imm);
                                SLTI_3: result_nxt= ($signed(rs1_data) < $signed(imm)) ? 32'b1 : 32'b0;
                                SRAI_3: result_nxt= $signed(rs1_data)>>>imm;
                                SLLI_3: result_nxt = rs1_data<<imm;
                                default: result_nxt=0;
                            endcase
                            nxt_pc= PC+4;
                        end
                        ALU_7:begin
                            case(func3)
                                Arithmetic_3:begin 
                                    case(func7)
                                        ADD_7: result_nxt=rs1_data+rs2_data;
                                        SUB_7: result_nxt=rs1_data-rs2_data;
                                        MUL_7: result_nxt=mul_out;
                                        default: result_nxt=0;
                                    endcase
                                end 
                                AND_3: result_nxt=rs1_data&rs2_data;
                                XOR_3: result_nxt=rs1_data^rs2_data;
                                default: result_nxt=0;
                            endcase
                            nxt_pc= PC+4;
                        end
                        default :begin
                            nxt_pc=PC;
                            result_nxt=result; 
                        end 
                    endcase
                end
                else begin
                    result_nxt = (state==MEM &&opcode == LW_7) ? i_DMEM_rdata : result;
                    nxt_pc=pc;//next_PC=PC;
                end 
                next_PC=(next_state==WB)? pc:PC;
            end 
            
        end  
    end
    always@(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n) begin 
            opcode<=0;
            func3<=0;
            func7<=0;
            rs1_data<=0;
            rs2_data<=0;
            rs1<=0;
            rs2<=0;
            rd <=0;
            state<=IF;
            result<=0;
            imm<=0;
            pc<=0;
        end 
        else begin 
            rs1_data<=rs1_data_nxt;
            rs2_data<=rs2_data_nxt;
            func3<=func3_nxt;
            func7<=func7_nxt;
            opcode<=opcode_nxt;
            rs1<=rs1_nxt;
            rs2<=rs2_nxt;
            rd <=rd_nxt;
            state<=next_state;
            result<=result_nxt;
            imm<=imm_nxt;
            pc<=nxt_pc;
        end 
    end
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
        end
        else begin
            PC <= next_PC;
        end
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

module MULDIV_unit(
    input i_clk,
    input i_rst_n,
    input i_valid, //enable
    input [31:0]in_a,
    input [31:0]in_b,
    output [31:0]out,
    output o_ready // output valid
    // TODO: port declaration
    );
    parameter S_IDLE = 4'd1;
    parameter S_MUL = 4'd2;
    parameter S_OUT = 4'd3;

    // Todo: HW2
    reg ready;
    reg[63:0] shift_reg;
    reg [1:0] state;
    reg [1:0] next_state;
    wire [31:0]alu_a;

    wire [31:0]adder;
    reg [4:0]counter;
    assign o_ready=ready;
    assign alu_a = shift_reg[63:32];
    assign out=shift_reg[31:0];
    assign adder = alu_a+((out[0]==1)?in_b:0);
    always @(*) begin
        case(state)
            S_IDLE:
                next_state = (i_valid)? S_MUL : S_IDLE;
            S_MUL:
                next_state = (counter == 5'd31)? S_OUT : S_MUL;
            S_OUT:
                next_state = S_IDLE;
            default:
                next_state = S_IDLE;
        endcase

    end
    always @(posedge i_clk or negedge i_rst_n) begin
        if(!i_rst_n ) begin
            shift_reg <= {64'b0};
            counter <= 0;
            state<= S_IDLE;
            ready<=0;
        end
        else begin
            counter <= (state==S_MUL)? counter+1:0;
            state <= next_state;
            shift_reg<= (state ==S_IDLE &&i_valid) ? {32'b0,in_a}:
                        (state==S_MUL)? {adder,out[31:1]} : shift_reg;
            ready<= (state==S_OUT)? 1:0;
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
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W-1:0]  o_mem_wdata,
            input [BIT_W-1:0] i_mem_rdata,
            input i_mem_stall
    );

    //---------------------------------------//
    //          default connection           //
    assign o_mem_cen = i_proc_cen;        //
    assign o_mem_wen = i_proc_wen;        //
    assign o_mem_addr = i_proc_addr;      //
    assign o_mem_wdata = i_proc_wdata;    //
    assign o_proc_rdata = i_mem_rdata;    //
    assign o_proc_stall = i_mem_stall;    //
    //---------------------------------------//

    // Todo: BONUS
endmodule