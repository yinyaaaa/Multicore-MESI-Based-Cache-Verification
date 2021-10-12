//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_lv1_interface.sv
// Description: Basic CPU-LV1 interface with assertions
// Designers: Venky & Suru
//=====================================================================


interface cpu_lv1_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;

    reg   [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1_reg    ;

    wire  [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1        ;
    logic [ADDR_WID_LV1 - 1   : 0] addr_bus_cpu_lv1        ;
    logic                          cpu_rd                  ;
    logic                          cpu_wr                  ;
    logic                          cpu_wr_done             ;
    logic                          data_in_bus_cpu_lv1     ;

    assign data_bus_cpu_lv1 = data_bus_cpu_lv1_reg ;

//Assertions
//ASSERTION1: cpu_wr and cpu_rd should not be asserted at the same clock cycle
    property prop_simult_cpu_wr_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr);
    endproperty

    assert_simult_cpu_wr_rd: assert property (prop_simult_cpu_wr_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_simult_cpu_wr_rd Failed: cpu_wr and cpu_rd asserted simultaneously"))

//Add assertions at this interface
    //Assertion 1
    property cpu_rd_finishes;
        @(posedge clk)
          $rose(cpu_rd) |=> ##[0:$] $rose(data_in_bus_cpu_lv1) & data_bus_cpu_lv1 ##1 $fell(cpu_rd);
    endproperty

    assert_cpu_rd_finishes: assert property (cpu_rd_finishes)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion cpu_rd_finishes Failed: cpu_rd did not deassert after seeing data in bus"))
    
    //Assertion 2
    property cpu_wr_finishes;
        @(posedge clk)
          $rose(cpu_wr) |=> ##[0:$] $rose(cpu_wr_done);
    endproperty

    assert_cpu_wr_finishes: assert property (cpu_wr_finishes)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion cpu_wr_finishes Failed: cpu_wr_done did not assert following cpu_wr assertion"))
    
    //Assertion 3
    property data_not_unknown_wr;
        @(posedge clk)
          $rose(cpu_wr) |-> !$isunknown(data_bus_cpu_lv1);
    endproperty

    assert_data_not_unknown_wr: assert property (data_not_unknown_wr)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion data_not_unknown_wr Failed: Data is unknown"))
    
    //Assertion 4
    property addr_not_unknown;
        @(posedge clk)
          $rose(cpu_rd) | $rose(cpu_wr) |-> !$isunknown(addr_bus_cpu_lv1);
    endproperty

    assert_addr_not_unknown: assert property (addr_not_unknown)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion addr_not_unknown Failed: Address is unknown"))

endinterface
