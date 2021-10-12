//=====================================================================
// Project: 4 core MESI cache design
// File Name: test_lib.svh
// Description: Base test class and list of tests
// Designers: Venky & Suru
//=====================================================================
//TODO: add your testcase files in here
`include "common_test_defs.sv"
`include "base_test.sv"
`include "read_miss_icache.sv"
`include "simultaneous_cpu_txn.sv"
`include "shared_data_test.sv"
`include "write_miss_test.sv"
`include "consecutive_write_test.sv"
`include "read_write_test.sv"
`include "diff_offset_test.sv"
`include "bit_31.sv"
`include "LRU_test.sv"
`include "signal_write.sv"
`include "lru.sv"
`include "stress_test.sv"