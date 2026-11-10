/*! Verilator driver for the UART testbench !*/
#include "verilator.hpp"
#include "Vtop.h"

int main(int argc, char** argv) {
  return _main<KoikaToplevel<Vtop>>(argc, argv);
}
