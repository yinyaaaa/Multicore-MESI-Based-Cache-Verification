class diff_offset_test extends base_test;

    //component macro
    `uvm_component_utils(diff_offset_test)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", diff_offset_test_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing diff_offset_test test" , UVM_LOW)
    endtask: run_phase
endclass

class diff_offset_test_seq extends base_vseq;
    //object macro
    `uvm_object_utils(diff_offset_test_seq)

    cpu_transaction_c multi_txn[`MAX_CORES:0];
    cpu_transaction_c single_txn;

    //constructor
    function new (string name="diff_offset_test_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        int rand_proc;
        logic[31:0] addr1, addr2;
        if(!std::randomize(addr1, addr2, rand_proc) with {rand_proc >= 0; rand_proc < `MAX_CORES; addr1[31:2] == addr2[31:2]; addr1[1:0] != addr2[1:0];}) begin
            `uvm_fatal(get_type_name(), "Randomization error");
        end
        `uvm_do_on_with(single_txn, p_sequencer.cpu_seqr[rand_proc], {address == addr1; request_type == READ_REQ;});
        `uvm_do_on_with(single_txn, p_sequencer.cpu_seqr[rand_proc], {address == addr2; request_type == READ_REQ;});
    endtask
endclass
