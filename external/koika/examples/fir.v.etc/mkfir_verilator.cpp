// A Verilator driver for the Bluespec implementation of the fir.v example
// Derived from ocaml/backends/resources/verilator.cpp
#include "verilator.hpp"
#include "Vmkfir.h"

class TB : public KoikaToplevel<Vmkfir> {
  using KoikaToplevel<Vmkfir>::dut;

public:
  void run(uint64_t ncycles) {
    KoikaToplevel<Vmkfir>::run(ncycles);
    printf("%d", dut.rd);
  }

  TB() : KoikaToplevel<Vmkfir>{} {}
};

int main(int argc, char** argv) {
  return _main<TB>(argc, argv);
}
