//=====================================================================
// Project: 4 core MESI cache design
// File Name: LRU_test.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class LRU_test extends base_test;

    //component macro
    `uvm_component_utils(LRU_test)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "LRU_TEST", LRU_test_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing LRU_test test" , UVM_LOW)
    endtask: run_phase

endclass : LRU_test


// Sequence for a read-miss on I-cache
class LRU_test_seq extends base_vseq;
    //object macro
    `uvm_object_utils(LRU_test_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="LRU_test_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 32'h5550_AAAA;})  
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 32'h5551_AAAA;}) 
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 32'h5552_AAAA;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 32'h5553_AAAA;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 32'h5554_AAAA;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 32'h5555_AAAA;})    
    endtask

endclass : LRU_test_seq
