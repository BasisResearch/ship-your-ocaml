# ocamlrun (OCaml 4.14.4 bytecode runtime) for bare-metal RV64 (HTIF), with
# a bytecode executable embedded in the image.
#
#   make                 ./ocamlrun-riscv-htif.elf running tests/while.ml
#   make PROG=path.byte ARGS='"-version",'   embed another bytecode exe
#   make run             run the ELF on the Sail Lean emulator (EMU=...)
#   make difftest        host ocamlrun vs the ELF on tests/difftest/*.ml
#   make clean
#
# The host compiler is OCaml 4.14.4 built from the same vendored source
# (see README: ~/toolchains/ocaml-4.14.4); bytecode executables are only
# portable between runtimes of the same version.

OCAML_DIR := ../vendor/ocaml-4.14.4
RT        := $(OCAML_DIR)/runtime
HOST_OCAML ?= $(HOME)/toolchains/ocaml-4.14.4/bin
OCAMLC    ?= $(HOST_OCAML)/ocamlc
OCAMLRUN  ?= $(HOST_OCAML)/ocamlrun

# Cross toolchain: the xPack riscv-none-elf-gcc 15.2.0 (GCC 15.2.0 +
# newlib 4.5.0.20241231), the release that built ship-your-interpreter's
# proof ELF and ship-your-lua's ELF.
XPACK_GCC    := $(firstword $(wildcard $(HOME)/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin/riscv-none-elf-gcc))
RISCV_CC     ?= $(if $(XPACK_GCC),$(XPACK_GCC),riscv-none-elf-gcc)
# Same ISA/ABI/code model as the WHILE HTIF build: plain rv64i (the Lean
# emulator's model has no M/F/D; mul/div and doubles come from libgcc's
# soft routines), lp64, medany. The -f flags are the runtime's own
# (OC_CFLAGS in Makefile.config). -DSHRINKED_GNUC turns off THREADED_CODE
# (config.h): caml_interprete dispatches through one C switch and the
# loaded code stays opcodes (no caml_thread_code rewrite to label
# addresses), so the code in memory is the bytecode itself -- the same
# choice as ship-your-lua's LUA_USE_JUMPTABLE=0.
RISCV_CFLAGS ?= -std=gnu11 -O2 -Wall -march=rv64i -mabi=lp64 -mcmodel=medany \
                -fno-strict-aliasing -fwrapv -fno-common -fno-tree-vrp \
                -DCAML_NAME_SPACE -DCAMLDLLIMPORT= -DSHRINKED_GNUC -DOCAML_HTIF \
                -Isrc/config/caml -Isrc/config -I$(RT)

# The runtime's BYTECODE_C_SOURCES minus main.c (replaced by src/main.c)
# and unix.c's dynamic-loading paths (compiled out by s.h).
RT_SRC := interp misc stacks fix_code startup_aux startup_byt freelist \
  major_gc minor_gc memory alloc roots_byt globroots fail_byt signals \
  signals_byt printexc backtrace_byt backtrace compare ints eventlog \
  floats str array io extern intern hash sys meta parsing gc_ctrl md5 obj \
  lexing callback debugger weak compact finalise custom dynlink \
  afl unix bigarray memprof domain skiplist codefrag
RT_C := $(patsubst %,$(RT)/%.c,$(RT_SRC))

PROG_SRC ?= tests/while.ml
PROG     ?= build/prog.byte
# Extra command-line arguments, as C string literals each followed by a
# comma, e.g. ARGS='"-version",'.
ARGS     ?=
# Baked-in OCAMLRUNPARAM (e.g. s=8M for an 8M-word minor heap).
RUNPARAM ?=
# Extra files for the in-memory file system: /path=hostfile ...
FILES    ?=
ELF      ?= ocamlrun-riscv-htif.elf
EMU      ?= $(HOME)/vsa-b3-work/bin/lean_riscv_emulator
BUILD    ?= build

all: $(ELF)

$(BUILD)/prims.c: src/gen_prims.sh $(RT_C)
	@mkdir -p $(BUILD)
	src/gen_prims.sh $(RT) $(abspath $@)

build/prog.byte: $(PROG_SRC)
	@mkdir -p build
	cd build && $(OCAMLC) -o prog.byte $(abspath $(PROG_SRC))

$(BUILD)/embed.S: src/gen_embed.sh $(PROG) FORCE
	@mkdir -p $(BUILD)
	src/gen_embed.sh /prog=$(abspath $(PROG)) $(FILES) > $@.tmp
	cmp -s $@.tmp $@ || mv $@.tmp $@; rm -f $@.tmp

# The .S files are assembled to named objects first: assembling them inline
# leaves the preprocessor's random temp-file names in the symbol table,
# which would make the ELF's bytes (and ELF.sha256) irreproducible.
$(BUILD)/crt0.o: src/crt0.S
	@mkdir -p $(BUILD)
	$(RISCV_CC) $(RISCV_CFLAGS) -c -o $@ $<

$(BUILD)/embed.o: $(BUILD)/embed.S
	$(RISCV_CC) $(RISCV_CFLAGS) -c -o $@ $<

$(ELF): $(RT_C) src/main.c $(BUILD)/crt0.o src/htif.c src/stubs.c src/link.ld $(BUILD)/embed.o $(BUILD)/prims.c src/config/caml/m.h src/config/caml/s.h
	$(RISCV_CC) $(RISCV_CFLAGS) '-DOCAML_ARGS=$(ARGS)' '-DOCAMLRUNPARAM="$(RUNPARAM)"' \
	    -nostartfiles -T src/link.ld -o $@ \
	    $(BUILD)/crt0.o src/htif.c src/stubs.c $(BUILD)/embed.o src/main.c $(BUILD)/prims.c $(RT_C) -lm

run: $(ELF)
	$(EMU) $(ELF)

difftest:
	./tests/difftest.sh

clean:
	rm -rf build ocamlrun-riscv-htif.elf

FORCE:
.PHONY: all run difftest clean FORCE
