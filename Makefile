
default: all

coq:
	@echo "This does not work currently :("
	exit 1
	mkdir -p build
	dune build @coq/all

ML_FILES := $(wildcard build/*.ml)

VERILOG_FILES := $(patsubst build/%.ml,build/%.v,$(ML_FILES))

build/%.v: build/%.ml
	cuttlec -T verilog $<

compile: $(VERILOG_FILES)

# --

all: coq compile

clean:
	dune clean
	rm -rf build

.PHONY: coq all clean
