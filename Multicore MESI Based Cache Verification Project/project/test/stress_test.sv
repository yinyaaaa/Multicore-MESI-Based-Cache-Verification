class stress_test extends base_test;

    //component macro
    `uvm_component_utils(stress_test)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", stress_test_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing stress_test test" , UVM_LOW)
    endtask: run_phase
endclass

class stress_test_seq extends base_vseq;
    //object macro
    `uvm_object_utils(stress_test_seq)

    cpu_transaction_c trans[`MAX_CORES:0];

    //constructor
    function new (string name="stress_test_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        int iterations;
        bit a = std::randomize(iterations) with {iterations <= 50; iterations > 0;};
        for(int j = 0; j < iterations; j++) begin
            for(int i = 0; i < `MAX_CORES; i++) begin
                automatic int k = i;
                automatic int l = j;
                fork
                    begin
                        `uvm_info(get_type_name(), $sformatf("Sending transaction %0d on CPU %0d", l, k), UVM_LOW);
                        `uvm_do_on(trans[k], p_sequencer.cpu_seqr[k])
                    end
                join_none
            end
        end
        wait fork;
    endtask
endclass
