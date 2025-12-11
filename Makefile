
default: all

coq:
	dune build

ML_FILES := $(wildcard build/*.ml)

VERILOG_FILES := $(patsubst build/%.ml,build/%.v,$(ML_FILES))

build/%.v: build/%.ml
	cuttlec -T verilog $<

compile: $(VERILOG_FILES)

copy_build:
	@if [ -d _build/default/build/. ]; then \
		mkdir -p build; \
		rsync -aru _build/default/build/. build; \
	fi

# --

all: coq copy_build 
	$(MAKE) compile

test: copy_build 
	$(MAKE) compile
# For now test just builds & compiles

clean:
	rm -rf build/*

.PHONY: coq all test clean copy_build compile
