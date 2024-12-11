`include "component_register.sv"

class register_transaction #(parameter WIDTH = 8); ;

    // signals
    rand logic [WIDTH-1:0] data_in;

    // constraints
    // make sure data is 0 10% of the time, 1 10% of the time,
    // and everything else 80% of the time
    constraint data_ranges { data_in dist{'0 :/ 10, '1 :/ 10, [1:2**WIDTH-2] :/ 80}; }

endclass

module register_tb;

    // constants
    localparam int DIRECTED_TESTS = 1; // determine whether to run directed tests
    localparam int NUM_TESTS = 1000;
    localparam int WIDTH = 8;

    // signals
    logic clk, rst;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    // instantiate DUT
    component_register #(.WIDTH(WIDTH)) DUT (.*);

    // generate clock
    initial begin : clk_gen
        clk = '0;
        while (1) #5 clk = ~clk;
    end

    // reset inputs
    task reset();
        // assert reset and set other signals low
        rst = '1;
        data_in = '0;

        // wait a couple cycles
        for (int i = 0; i < 5; i++)
            @(posedge clk);

        // deassert reset
        @(negedge clk);
        rst <= '0;
        @(posedge clk);

    endtask

    // write all possible values to register
    task write_all();
        for (int i = 0; i < WIDTH; i++) begin
            data_in = i;
            @(posedge clk);
            @(negedge clk);

            // print first 5 writes
            if (i < 5) begin
                $display("Writing %d", data_in);
            end
        end
    endtask

    // create register_transaction object
    register_transaction #(.WIDTH(WIDTH)) item;

    // track failures
    int failures = 0;

    // drive inputs
    initial begin : drive_inputs

        // display that ram tb starting
        $display("Starting component_register testbench...");

        // reset DUT
        $display("Resetting DUT...");
        reset();
        $display("Reset DUT.");

        // write to all addresses and then read
        if (DIRECTED_TESTS) begin
            $display("Displaying first 5 write tests...");
            write_all();
            $display("All directed write tests completed.");
        end
        
        // print first couple of tests
        $display("Displaying first 5 of %d random tests...", NUM_TESTS);

        // create register_transaction object
        item = new();

        // start tests
        for (int i = 0; i < NUM_TESTS; i++) begin

            // assign random values
            if (item.randomize() == 0) $error("Randomization failed");

            // assign to actual pins
            data_in = item.data_in;

            // display inputs
            if (i < 5) begin
                $display("Test %d at time %0t", i+1, $time);
                $display("data_in: %d", data_in);
            end

            // wait for posedge
            @(posedge clk);
            @(negedge clk);

        end

        // end tests
        disable clk_gen;
        $display("%d tests finished with %d failires.", DIRECTED_TESTS ? 256+NUM_TESTS : NUM_TESTS, failures);

    end

    // ASSERTS!!!!!!!!! to check functionality

    // check register outputs are valid
    property out_correct_check;
        @(posedge clk) disable iff (rst) data_out == $past(data_in);
    endproperty

    // calling assert properties
    assert property (out_correct_check) else begin
        $display("ERROR with out_correct_check: out=%d but supposed to be %d", data_out, $past(data_in));
        failures++;
    end

endmodule