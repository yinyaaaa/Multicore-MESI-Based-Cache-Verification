class signal_write extends base_test;

    //component macro
    `uvm_component_utils(signal_write)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "signal_write_seq", signal_write_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing signal_write test" , UVM_LOW)
    endtask: run_phase
endclass


// Sequence for a read-miss on I-cache
class signal_write_seq extends base_vseq;
    //object macro
    `uvm_object_utils(signal_write_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="signal_write_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_info(get_type_name(), $sformatf("Sending transaction on CPU 0"), UVM_LOW)
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0],{request_type == WRITE_REQ; address == 32'h5555_AAAA;}) 
    endtask
endclass