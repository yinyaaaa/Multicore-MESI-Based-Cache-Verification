//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_interface.sv
// Description: Basic system bus interface including arbiter
// Designers: Venky & Suru
//=====================================================================

interface system_bus_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1        = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1        = `ADDR_WID_LV1       ;
    parameter NO_OF_CORE            = 4;

    wire [DATA_WID_LV1 - 1 : 0] data_bus_lv1_lv2     ;
    wire [ADDR_WID_LV1 - 1 : 0] addr_bus_lv1_lv2     ;
    wire                        bus_rd               ;
    wire                        bus_rdx              ;
    wire                        lv2_rd               ;
    wire                        lv2_wr               ;
    wire                        lv2_wr_done          ;
    wire                        cp_in_cache          ;
    wire                        data_in_bus_lv1_lv2  ;

    wire                        shared               ;
    wire                        all_invalidation_done;
    wire                        invalidate           ;

    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_snoop;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_snoop;
    logic                       bus_lv1_lv2_gnt_lv2  ;
    logic                       bus_lv1_lv2_req_lv2  ;

//Assertions
//property that checks that signal_1 is asserted in the previous cycle of signal_2 assertion
    property prop_sig1_before_sig2(signal_1,signal_2);
    @(posedge clk)
        signal_2 |-> $past(signal_1);
    endproperty

//ASSERTION1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))

    //Add assertions at this interface
    //There are atleast 20 such assertions. Add as many as you can!!
    //ASSERTION 2: lv2_rd should be followed by data_in_bus_lv1_lv2 and both should be deasserted acc to HAS
    property valid_lv2_rd_txn;
        @(posedge clk)
        lv2_rd |=> ##[0:$] data_in_bus_lv1_lv2 ##1 !lv2_rd ;
    endproperty

    assert_valid_lv2_rd_txn: assert property (valid_lv2_rd_txn)
    else
        `uvm_error("system_bus_interface", "Assertion valid_lv2_rd_txn failed: lv2_rd=>data_in_bus_lv1_lv2=>!lv2_rd sequence is not followed")

    //ASSERTION 3: If data_in_bus_lv1_lv2 is asserted, lv2_rd should be high
    property valid_data_in_lv2_bus_rd;
        @(posedge clk)
        (data_in_bus_lv1_lv2===1'bz) ##1 (data_in_bus_lv1_lv2==1'b1) |-> lv2_rd;
    endproperty

    assert_valid_data_in_lv2_bus_rd: assert property (valid_data_in_lv2_bus_rd)
    else
        `uvm_error("system_bus_interface", "Assertion valid_data_in_lv2_bus_rd failed: lv2_rd not high when data_in_bus_lv1_lv2 asserted")

    //ASSERTION 4: lv2_wr should be followed by lv2_wr_done and both should be deasserted acc to HAS
    property valid_lv2_wr_txn;
        @(posedge clk)
        lv2_wr |=> ##[0:$] lv2_wr_done ##1 !lv2_wr ##1 !lv2_wr_done ;
    endproperty

    assert_valid_lv2_wr_txn: assert property (valid_lv2_wr_txn)
    else
        `uvm_error("system_bus_interface", "Assertion valid_lv2_wr_txn failed: lv2_wr=>lv2_wr_done=>!lv2_wr=>!lv2_wr_done sequence is not followed")
    //ASSERTION 5: We can only write to D cache
    property wr_d_cache;
        @(posedge clk)
            $rose(lv2_wr) |-> addr_bus_lv1_lv2 >= 32'h4000_0000;
    endproperty
    assert_wr_d_cache: assert property(wr_d_cache)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_wr_d_cache Failed: try to write to I cache"))
    //ASSERTION 7: req should be followed by gnt
    property gnt_after_req;
        @(posedge clk)
          $rose(|bus_lv1_lv2_req_proc) |=> ##[0:$] $rose(bus_lv1_lv2_gnt_proc);
    endproperty
    assert_gnt_after_req: assert property (gnt_after_req)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion gnt_after_req Failed: No gnt after a req"))

    //ASSERTION 8: data sent only after access granted 
    property data_sent_only_after_gnt;
        @(posedge clk)
          $rose(|bus_lv1_lv2_gnt_proc) |=> ##[0:$] (data_in_bus_lv1_lv2 && !$isunknown(data_bus_lv1_lv2));
    endproperty
        assert_data_sent_only_after_gnt: assert property (data_sent_only_after_gnt)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion data_sent_only_after_gnt Failed: Data was sent before gnt was received"))
    
    //ASSERTION 9: invalidate doneafter invalidate
    property invalidate_done_after_invalidate;
        @(posedge clk)
          $rose(invalidate) |=> ##[0:$] $rose(all_invalidation_done);
    endproperty

    assert_invalidate_done_after_invalidate: assert property (invalidate_done_after_invalidate)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion invalidate_done_after_invalidate Failed: invalidate_done not asserted after invalidate"))

    //ASSERTION 10: onehot
    property onehot_lv2_gnt;
        @(posedge clk)
            $onehot(bus_lv1_lv2_gnt_proc) | !(|bus_lv1_lv2_gnt_proc);
    endproperty
    assert_onehot_lv2_gnt: assert property(onehot_lv2_gnt)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_onehot_lv2_gnt Failed: onehot bus_lv1_lv2_gnt_proc"))

    //ASSERTION 11: snoop_req should be followed by snoop_gnt
    property snoop_gnt_after_snoop_req;
        @(posedge clk)
          $rose(|bus_lv1_lv2_req_snoop) |-> ##[2:$] $rose(bus_lv1_lv2_gnt_snoop);
    endproperty
    assert_snoop_gnt_after_req: assert property (gnt_after_req)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion snoop_gnt_after_snoop_req Failed: No snoop_gnt after a snoop_req"))

    //ASSERTION 12: bus_rd deasserts after data_in_bus asserts
    property bus_rd_deassert_after_data_in_bus;
        @(posedge clk)
          $rose(data_in_bus_lv1_lv2) && bus_rd |=> $fell(bus_rd);
    endproperty
    assert_bus_rd_deassert_after_data_in_bus: assert property (bus_rd_deassert_after_data_in_bus)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion bus_rd_deassert_after_data_in_bus Failed: bus_rd did not deassert after data_in_bus_lv1_lv2 asserted"))

    //ASSERTION 13: bus_rdx deasserts after data_in_bus asserts
    property bus_rdx_deassert_after_data_in_bus;
        @(posedge clk)
          $rose(data_in_bus_lv1_lv2) && bus_rdx |=> $fell(bus_rdx);
    endproperty
    assert_bus_rdx_deassert_after_data_in_bus: assert property (bus_rdx_deassert_after_data_in_bus)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion bus_rdx_deassert_after_data_in_bus Failed: bus_rdx did not deassert after data_in_bus_lv1_lv2 asserted"))
endinterface
