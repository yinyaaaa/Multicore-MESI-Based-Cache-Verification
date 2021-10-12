class shared_data_test extends base_test;

    //component macro
    `uvm_component_utils(shared_data_test)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", shared_data_test_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing shared_data_test test" , UVM_LOW)
    endtask: run_phase
endclass

class shared_data_test_seq extends base_vseq;
    //object macro
    `uvm_object_utils(shared_data_test_seq)

    cpu_transaction_c multi_txn[`MAX_CORES:0];
    cpu_transaction_c single_txn;

    //constructor
    function new (string name="shared_data_test_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        int rand_proc;
        logic[31:0] fixed_address;
        if(!std::randomize(fixed_address, rand_proc) with {rand_proc >= 0; rand_proc < `MAX_CORES;}) begin
            `uvm_fatal(get_type_name(), "Randomization error");
        end
        for(int i = 0; i < `MAX_CORES; i++) begin
            automatic int k = i;
            fork
                begin
                    `uvm_info(get_type_name(), $sformatf("Sending transaction on CPU %0d", k), UVM_LOW);
                    `uvm_do_on_with(multi_txn[k], p_sequencer.cpu_seqr[k], {address == fixed_address; request_type == READ_REQ;});
                end
            join_none
        end
        wait fork;
        `uvm_do_on_with(single_txn, p_sequencer.cpu_seqr[rand_proc], {address == fixed_address; request_type == READ_REQ;});
    endtask
endclass
