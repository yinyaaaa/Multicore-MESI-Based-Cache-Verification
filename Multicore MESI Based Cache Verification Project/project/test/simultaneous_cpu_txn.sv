class simultaneous_cpu_txn extends base_test;

    //component macro
    `uvm_component_utils(simultaneous_cpu_txn)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", simultaneous_cpu_txn_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing simultaneous_cpu_txn test" , UVM_LOW)
    endtask: run_phase
endclass

class simultaneous_cpu_txn_seq extends base_vseq;
    //object macro
    `uvm_object_utils(simultaneous_cpu_txn_seq)

    cpu_transaction_c trans[`MAX_CORES:0];

    //constructor
    function new (string name="simultaneous_cpu_txn_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        for(int i = 0; i < `MAX_CORES; i++) begin
            automatic int k = i;
            fork
                begin
                    `uvm_info(get_type_name(), $sformatf("Sending transaction on CPU %0d", k), UVM_LOW);
                    `uvm_do_on(trans[k], p_sequencer.cpu_seqr[k])
                end
            join_none
        end
        wait fork;
    endtask
endclass
