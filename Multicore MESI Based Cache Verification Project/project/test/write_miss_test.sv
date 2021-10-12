class write_miss_test extends base_test;

    //component macro
    `uvm_component_utils(write_miss_test)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_miss_test_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_miss_test test" , UVM_LOW)
    endtask: run_phase
endclass

class write_miss_test_seq extends base_vseq;
    //object macro
    `uvm_object_utils(write_miss_test_seq)

    cpu_transaction_c multi_txn[`MAX_CORES:0];
    cpu_transaction_c single_txn;

    //constructor
    function new (string name="write_miss_test_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        int rand_proc;
        logic[31:0] addr;
        if(!std::randomize(addr, rand_proc) with {rand_proc >= 0; rand_proc < `MAX_CORES; addr > `DATA_ADDR_START;}) begin
            `uvm_fatal(get_type_name(), "Randomization error");
        end
        `uvm_do_on_with(single_txn, p_sequencer.cpu_seqr[rand_proc], {address == addr; request_type == WRITE_REQ;});
    endtask
endclass
