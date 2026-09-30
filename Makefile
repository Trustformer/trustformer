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
	@python3 scripts/check-drivers.py build/*.v

sim: all
	@python3 scripts/run-sim.py

test: all
	@python3 scripts/check-drivers.py build/*.v
	@python3 scripts/run-sim.py

clean:
	rm -rf build/*

.PHONY: coq copy_build compile all check sim test clean default
