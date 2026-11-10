# Examples
Useful `Makefile` targets in `_objects/<example_name>`:
* `make obj_dir/V<name>`: compile the generated RTL with Verilator.
* `make gdb`: compile the C++ model of your design in debug mode, then run it under GDB.
* `make <name>.hpp.gcov`: generate coverage statistics for the C++ model of your design (shows which rules fire, how often they fire, and why they fail when they do).
* `make NCYCLES=25 gtkwave.verilator`: compile the generated RTL with Verilator in `--trace` mode, then a VCD trace over 25 cycles and open it in GTKWave.

The Makefiles that `cuttlec` generates include targets for generating ECP5 and ICE40 bitstreams.
