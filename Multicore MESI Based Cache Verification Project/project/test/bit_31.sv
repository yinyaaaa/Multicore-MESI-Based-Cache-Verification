class bit_31 extends base_test;

    //component macro
    `uvm_component_utils(bit_31)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", bit_31_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing bit_31 test" , UVM_LOW)
    endtask: run_phase
endclass


// Sequence for a read-miss on I-cache
class bit_31_seq extends base_vseq;
    //object macro
    `uvm_object_utils(bit_31_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="bit_31_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_info(get_type_name(), $sformatf("Sending transaction on CPU 0"), UVM_LOW);
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == READ_REQ; address == 31'h1555_AAAA;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == WRITE_REQ; address == 31'h1555_AAAA;})    
    endtask
endclass