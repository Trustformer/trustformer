default: all

# --------------------------------------------------------------------- Rocq

coq:
	dune build coq/

copy_build: coq
	@mkdir -p build
	@cp -au _build/default/build/. build/

# ------------------------------------------------------------------ Verilog

ML_FILES := $(wildcard build/*.ml)

VERILOG_FILES := $(patsubst build/%.ml,build/%.v,$(ML_FILES))

build/%.v: build/%.ml
	cuttlec -T verilog $<

compile: copy_build
	@$(MAKE) --no-print-directory $(VERILOG_FILES)

all: compile

# -------------------------------------------------------------------- Tests

check: all
	@scripts/check-drivers.sh build/*.v

sim: all
	@scripts/run-sim.sh

test: all
	@scripts/check-drivers.sh build/*.v
	@scripts/run-sim.sh

clean:
	rm -rf build/*

.PHONY: coq copy_build compile all check sim test clean default
