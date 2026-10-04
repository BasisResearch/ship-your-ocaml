#!/usr/bin/env python3
"""Generate OCaml/Vm/Layout.lean from the bare-metal ocamlrun ELF.

    python3 scripts/gen_layout.py [--elf c/ocamlrun-riscv-htif.elf] > OCaml/Vm/Layout.lean

Everything is read from the binary or the vendored headers, nothing typed:
  * symbol addresses (nm): caml_interprete, Caml_state, caml_global_data,
    caml_atom_table, caml_something_to_do, tohost, _exit;
  * best-fit free-list layout: target-compiler sizeof/offsetof on freelist.c;
  * Caml_state field offsets: 8 bytes per DOMAIN_STATE entry, in the order
    of runtime/caml/domain_state.tbl;
  * caml_interprete's dispatch loop: the loop head (the `lw` of the opcode
    word through the pc register), the jump-table base and the register
    allocation of the interpreter's C locals at the loop head, recovered
    from the disassembly by pattern (and checked: the script fails if a
    pattern is not found exactly once):
       pc     : the base register of the loop head's `lw a5,0(pc)`
       sp     : the base register of ACC0's `ld accu,0(sp)`
       accu   : ACC0's destination
       env    : ENVACC1's base register (`ld accu,8(env)`)
       extra  : the register APPLY1 tags with `slli r,r,1; addi r,r,1`
"""
import argparse
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path
from gen_primitive_census import primitive_names

ROOT = Path(__file__).resolve().parent.parent
TOOLS = os.path.expanduser(
    "~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-")


def collector_layout():
    """Ask the target compiler for the actual freelist.c structure layout."""
    fields = {
        "bf_small_count": "BF_NUM_SMALL",
        "bf_small_size": "sizeof(bf_small_fl[0])",
        "off_bf_small_free": "offsetof(__typeof__(bf_small_fl[0]), free)",
        "off_bf_small_merge": "offsetof(__typeof__(bf_small_fl[0]), merge)",
        "bf_large_size": "sizeof(large_free_block)",
        **{f"off_bf_{name}": f"offsetof(large_free_block, {name})"
           for name in ("isnode", "left", "right", "prev", "next")},
        "gc_blue": "Caml_blue",
        "gc_white": "Caml_white",
        "gc_black": "Caml_black",
        "phase_mark": "Phase_mark",
        "phase_clean": "Phase_clean",
        "phase_sweep": "Phase_sweep",
        "phase_idle": "Phase_idle",
        "tag_abstract": "Abstract_tag",
        "value_bytes": "sizeof(value)",
        "header_bytes": "sizeof(header_t)",
        **{f"off_ref_table_{name}": f"offsetof(struct caml_ref_table, {name})"
           for name in ("base", "end", "threshold", "ptr", "limit", "size", "reserve")},
        **{f"off_ephe_ref_table_{name}": f"offsetof(struct caml_ephe_ref_table, {name})"
           for name in ("base", "end", "threshold", "ptr", "limit", "size", "reserve")},
        "ephe_ref_elt_size": "sizeof(struct caml_ephe_ref_elt)",
        "off_ephe_ref_ephe": "offsetof(struct caml_ephe_ref_elt, ephe)",
        "off_ephe_ref_offset": "offsetof(struct caml_ephe_ref_elt, offset)",
    }
    source = ('#include <stddef.h>\n#include ' +
              json.dumps(str(ROOT / "vendor/ocaml-4.14.4/runtime/freelist.c")) +
              '\n#include \"caml/minor_gc.h\"\nconst unsigned long boot_offsets[] '
              '__attribute__((section(".boot_offsets"), used)) = {\n' +
              ',\n'.join(fields.values()) + '\n};\n')
    with tempfile.TemporaryDirectory(prefix="ocaml-layout-") as tmp:
        obj = Path(tmp) / "offsets.o"
        raw = Path(tmp) / "offsets.bin"
        subprocess.run([TOOLS + "gcc", "-x", "c", "-std=gnu11", "-O0",
                        "-march=rv64i", "-mabi=lp64", "-DCAML_NAME_SPACE",
                        "-DCAMLDLLIMPORT=", "-DSHRINKED_GNUC",
                        "-I" + str(ROOT / "c/src/config/caml"),
                        "-I" + str(ROOT / "c/src/config"),
                        "-I" + str(ROOT / "vendor/ocaml-4.14.4/runtime"),
                        "-c", "-", "-o", str(obj)], input=source, text=True, check=True)
        subprocess.run([TOOLS + "objcopy", "--dump-section", f".boot_offsets={raw}",
                        str(obj), str(Path(tmp) / "copy.o")], check=True)
        values = struct.unpack("<" + "Q" * len(fields), raw.read_bytes())
    return dict(zip(fields, values))

def htif_layout():
    """Measure htif.c tables and flags with the same RV64 ABI as the image."""
    fields = {"htif_max_files": "MAX_FILES", "htif_max_fds": "MAX_FDS",
              "htif_max_dirs": "MAX_DIRS"}
    for typ, members in {
        "mfile": "used dir linked parent name nlen data size cap opens ro",
        "mfd": "kind node pos flags",
        "baremetal_dir": "used node pos ent",
    }.items():
        fields[f"htif_size_{typ}"] = f"sizeof(struct {typ})"
        for member in members.split():
            fields[f"htif_off_{typ}_{member}"] = f"offsetof(struct {typ}, {member})"
    fields["htif_off_direct_name"] = "offsetof(struct direct, d_name)"
    fields["htif_name_capacity"] = "sizeof(((struct direct *)0)->d_name)"
    for constant in "FD_FREE FD_STDIN FD_STDOUT FD_STDERR FD_FILE O_ACCMODE O_WRONLY O_RDWR O_CREAT O_EXCL O_TRUNC O_APPEND O_DIRECTORY".split():
        fields["htif_" + constant.lower()] = constant
    source = ('#define OCAML_HTIF 1\n#include ' +
              json.dumps(str(ROOT / "c/src/htif.c")) +
              '\nconst unsigned long htif_offsets[] '
              '__attribute__((section(".htif_offsets"), used)) = {\n' +
              ',\n'.join(fields.values()) + '\n};\n')
    with tempfile.TemporaryDirectory(prefix="htif-layout-") as tmp:
        obj, raw = Path(tmp) / "offsets.o", Path(tmp) / "offsets.bin"
        subprocess.run([TOOLS + "gcc", "-x", "c", "-std=gnu11", "-O0",
                        "-march=rv64i", "-mabi=lp64",
                        "-I" + str(ROOT / "c/src/config"),
                        "-c", "-", "-o", str(obj)], input=source, text=True, check=True)
        subprocess.run([TOOLS + "objcopy", "--dump-section", f".htif_offsets={raw}",
                        str(obj), str(Path(tmp) / "copy.o")], check=True)
        values = struct.unpack("<" + "Q" * len(fields), raw.read_bytes())
    return dict(zip(fields, values))

ABI = {"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7,
       "s0": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15,
       "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22,
       "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29,
       "t5": 30, "t6": 31}


def die(msg):
    sys.exit(f"gen_layout.py: {msg}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", default=str(ROOT / "c/ocamlrun-riscv-htif.elf"))
    ap.add_argument("--census", default=str(ROOT / "results/census.json"))
    a = ap.parse_args()

    nm = subprocess.run([TOOLS + "nm", a.elf], capture_output=True, text=True,
                        check=True).stdout
    sym = {}
    for line in nm.splitlines():
        p = line.split()
        if len(p) == 3:
            sym[p[2]] = int(p[0], 16)
    need = ["caml_interprete", "Caml_state", "caml_global_data", "caml_atom_table",
            "caml_something_to_do", "tohost", "_exit", "caml_main", "main",
            "caml_start_code", "caml_code_size", "caml_int64_ops", "caml_int32_ops",
            "caml_nativeint_ops", "channel_operations", "caml_all_opened_channels",
            "embedded_files", "embedded_argv", "embedded_env", "__embed_start",
            "__heap_end", "__stack_top", "caml_prim_table", "_start",
            "__bss_start", "__bss_end", "__global_pointer$", "environ"]
    need += ["_open", "_read", "_write", "_lseek", "_close", "_fstat", "_stat",
             "_unlink", "rename", "opendir", "readdir", "closedir", "_gettimeofday",
             "_times", "files", "fds", "dirs", "fs_ready"]
    need += primitive_names()
    need += ["caml_fl_p_allocate", "caml_fl_p_add_blocks", "caml_gc_phase", "caml_gc_sweep_hp"]
    need += ["caml_callback_depth"]
    need += ["caml_allocated_words", "caml_stack_usage_hook", "oldify_todo_list", "caml_ephe_none"]
    need += ["pool", "caml_stat_alloc_noexc", "malloc", "caml_init_domain"]
    need += ["main_argv", "caml_exe_name", "oo_last_id", "caml_copy_double"]
    need += ["bf_small_fl", "bf_small_map", "bf_large_tree", "bf_large_least",
             "caml_fl_cur_wsz"]
    for n in need:
        if n not in sym:
            die(f"symbol {n} not found")

    tbl = (ROOT / "vendor/ocaml-4.14.4/runtime/caml/domain_state.tbl").read_text()
    fields = re.findall(r"^DOMAIN_STATE\([^,]+,\s*(\w+)\)", tbl, flags=re.M)
    off = {f: 8 * i for i, f in enumerate(fields)}

    arms = json.load(open(a.census))["caml_interprete"]
    head = int(arms["loop_head"], 16)
    table = int(arms["table"], 16)
    dis = subprocess.run([TOOLS + "objdump", "-d", a.elf,
                          f"--start-address=0x{sym['caml_interprete']:x}",
                          f"--stop-address=0x{sym['caml_interprete'] + 0x2000:x}"],
                         capture_output=True, text=True, check=True).stdout
    ins = {}
    for line in dis.splitlines():
        m = re.match(r"^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(\S+)\s*(.*)$", line)
        if m:
            ins[int(m.group(1), 16)] = (m.group(2), m.group(3).split("#")[0].strip())

    # Native interpreter frame: recover the contiguous ABI saves at entry.
    entry = sym["caml_interprete"]
    mn, ops = ins[entry]
    frame_match = re.fullmatch(r"sp,sp,-(\d+)", ops)
    if mn != "addi" or not frame_match:
        die("interpreter frame allocation changed")
    frame_bytes = int(frame_match.group(1))
    saved_regs = []
    cursor = entry + 4
    while cursor in ins and ins[cursor][0] == "sd":
        saved_match = re.fullmatch(r"(\w+),(\d+)\(sp\)", ins[cursor][1])
        if not saved_match:
            die("interpreter native save shape changed")
        reg, offset = saved_match.group(1), int(saved_match.group(2))
        saved_regs.append((ABI[reg], offset))
        cursor += 4
    if {r for r, _ in saved_regs} != {1, 8, 9, *range(18, 28)}:
        die("interpreter ABI save set changed")
    if any(offset + 8 > frame_bytes for _, offset in saved_regs):
        die("interpreter save outside native frame")

    # caml_main's return after the real interpreter invocation (the earlier
    # null-code invocation initializes the interpreter). Check each restored
    # slot against an actual save in the same function.
    main_dis = subprocess.run([TOOLS + "objdump", "-d", a.elf, "--disassemble=caml_main"],
                              capture_output=True, text=True, check=True).stdout
    main_ins = {}
    for line in main_dis.splitlines():
        match = re.match(r"^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(\S+)\s*(.*)$", line)
        if match:
            main_ins[int(match[1], 16)] = (match[2], match[3].split("#")[0].strip())
    main_entry = min(main_ins)
    main_alloc = re.fullmatch(r"sp,sp,-(\d+)", main_ins[main_entry][1])
    if main_ins[main_entry][0] != "addi" or not main_alloc:
        die("caml_main frame allocation changed")
    main_frame_bytes = int(main_alloc[1])
    main_return = max(pc for pc, (mn, ops) in main_ins.items()
                      if mn == "jal" and "<caml_interprete>" in ops) + 4
    main_saved_regs = []
    cursor = main_return
    while main_ins[cursor][0] != "ret":
        mn, ops = main_ins[cursor]
        if mn == "ld":
            match = re.fullmatch(r"(\w+),(\d+)\(sp\)", ops)
            if not match or ("sd", ops) not in main_ins.values():
                die("caml_main return slot has no matching native save")
            main_saved_regs.append((ABI[match[1]], int(match[2])))
        cursor += 4
    if {r for r, _ in main_saved_regs} != {1, 8, 9, 18, 19, 20}:
        die("caml_main return save set changed")
    if any(offset + 8 > main_frame_bytes for _, offset in main_saved_regs):
        die("caml_main save outside native frame")

    # The nonlocal return reloads the initial local-roots pointer saved before setjmp.
    roots_loads = [(pc, re.fullmatch(r"a2,(\d+)\(sp\)", ops))
                   for pc, (mn, ops) in ins.items() if mn == "ld"]
    roots_offsets = [int(match[1]) for pc, match in roots_loads if match
                     and ins.get(pc + 12) == ("sd", f"a2,{off['local_roots']}(a5)")]
    if len(roots_offsets) != 1:
        die("interpreter nonlocal local-roots restoration changed")
    saved_roots_offset = roots_offsets[0]
    if ("sd", f"a3,{saved_roots_offset}(sp)") not in ins.values():
        die("interpreter initial local-roots save is absent")

    # Nonlocal-jump environment: stores and loads must agree for every ABI slot.
    jump_slots = {}
    for fn, op in [("setjmp", "sd"), ("longjmp", "ld")]:
        jump_dis = subprocess.run([TOOLS + "objdump", "-d", a.elf, f"--disassemble={fn}"],
                                  capture_output=True, text=True, check=True).stdout
        slots = []
        for line in jump_dis.splitlines():
            match = re.match(r"^\s*[0-9a-f]+:\s+[0-9a-f]{8}\s+" + op + r"\s+(\w+),(\d+)\(a0\)", line)
            if match:
                slots.append((ABI[match[1]], int(match[2])))
        jump_slots[fn] = slots
    if jump_slots["setjmp"] != jump_slots["longjmp"] or {r for r, _ in jump_slots["setjmp"]} != {1, 2, 8, 9, *range(18, 28)}:
        die("setjmp/longjmp environment layout changed")
    jump_saved = jump_slots["setjmp"]

    def arm(name, k=0):
        return ins[int(arms["arms"][name]["addr"], 16) + 4 * k]

    mn, ops = ins[head]
    m = re.fullmatch(r"(\w+),0\((\w+)\)", ops)
    if mn != "lw" or not m:
        die(f"loop head {head:#x} is not `lw r,0(pc)`: {mn} {ops}")
    pc_reg = m.group(2)
    mn, ops = arm("ACC0")
    m = re.fullmatch(r"(\w+),0\((\w+)\)", ops)
    if mn != "ld" or not m:
        die(f"ACC0 is not `ld accu,0(sp)`: {mn} {ops}")
    accu_reg, sp_reg = m.group(1), m.group(2)
    mn, ops = arm("ENVACC1")
    m = re.fullmatch(r"(\w+),8\((\w+)\)", ops)
    if mn != "ld" or not m or m.group(1) != accu_reg:
        die(f"ENVACC1 is not `ld accu,8(env)`: {mn} {ops}")
    env_reg = m.group(2)
    mn1, ops1 = arm("APPLY1", 1)
    mn2, ops2 = arm("APPLY1", 2)
    m = re.fullmatch(r"(\w+),(\w+),0x1", ops1)
    if mn1 != "slli" or not m or m.group(1) != m.group(2) or mn2 != "addi" \
            or ops2 != f"{m.group(1)},{m.group(1)},1":
        die(f"APPLY1 does not tag extra_args: {mn1} {ops1}; {mn2} {ops2}")
    extra_reg = m.group(1)

    # Fixed loop registers are established immediately before the loop head.
    bound_mn, bound_ops = ins[head - 28]
    bound_match = re.fullmatch(r"(\w+),(\d+)", bound_ops)
    if bound_mn != "li" or not bound_match:
        die("expected opcode-bound initialization before dispatch")
    bound_reg, bound_value = bound_match.group(1), int(bound_match.group(2))

    def fixed_pair(addr, expected):
        mn1, ops1 = ins[addr]
        mn2, ops2 = ins[addr + 4]
        hi = re.fullmatch(r"(\w+),0x([0-9a-f]+)", ops1)
        lo = re.fullmatch(r"(\w+),(\w+),(-?\d+)", ops2)
        if mn1 != "auipc" or mn2 != "addi" or not hi or not lo:
            die("expected fixed-register auipc/addi pair")
        if hi.group(1) != lo.group(1) or lo.group(1) != lo.group(2):
            die("mismatched fixed-register pair")
        value = addr + (int(hi.group(2), 16) << 12) + int(lo.group(3))
        if value != expected:
            die(f"fixed register value {value:#x} != {expected:#x}")
        return hi.group(1)

    table_reg = fixed_pair(head - 24, table)
    pending_reg = fixed_pair(head - 16, sym["caml_something_to_do"])
    domain_reg = fixed_pair(head - 8, sym["Caml_state"])

    collector = collector_layout()
    prim_start = int(arms["arms"]["C_CALL1"]["addr"], 16)
    prim_stop = prim_start + 4 * arms["arms"]["C_CALL1"]["own"]
    prim_offsets = []
    for line in dis.splitlines():
        site = re.match(r"^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+ld\s+.*#\s*([0-9a-f]+)\s+<caml_prim_table\+0x([0-9a-f]+)>", line)
        if site and prim_start <= int(site[1], 16) < prim_stop:
            offset = int(site[3], 16)
            if int(site[2], 16) != sym["caml_prim_table"] + offset:
                die("inconsistent primitive-table contents address")
            prim_offsets.append(offset)
    if len(prim_offsets) != 1:
        die("C_CALL1 must load caml_prim_table.contents exactly once")

    w = sys.stdout.write
    w("/-!\n# Layout of the bare-metal `ocamlrun` (generated)\n\n"
      "Generated by `scripts/gen_layout.py` from `c/ocamlrun-riscv-htif.elf`\n"
      "(symbols, the disassembly of `caml_interprete`) and\n"
      "`runtime/caml/domain_state.tbl` (`Caml_state` field offsets). Do not edit.\n-/\n\n"
      "namespace OCaml.Vm.Layout\n\n")
    for n in need:
        w(f"/-- `{n}` -/\ndef sym_{n.lstrip('_').replace('$', '')} : Nat := 0x{sym[n]:x}\n")
    w(f"\n/-- `caml_interprete`'s dispatch loop head (fetch of the opcode word). -/\n"
      f"def loopHead : Nat := 0x{head:x}\n")
    w(f"/-- The switch jump table (`int32` offsets from its own base). -/\n"
      f"def jumpTable : Nat := 0x{table:x}\n\n")
    w("/-! GPR indices holding `caml_interprete`'s locals at `loopHead`. -/\n")
    for k, r in [("pc", pc_reg), ("sp", sp_reg), ("accu", accu_reg), ("env", env_reg),
                 ("extra", extra_reg), ("dispatchTable", table_reg),
                 ("opcodeBound", bound_reg), ("pending", pending_reg), ("domain", domain_reg)]:
        w(f"/-- `{k}` lives in `{r}` -/\ndef reg_{k} : Nat := {ABI[r]}\n")
    w(f"\n/-- Largest opcode accepted by the dispatch bound check. -/\ndef opcodeBound : Nat := {bound_value}\n")
    w(f"\n/-- `caml_prim_table.contents`, recovered from C_CALL1. -/\ndef off_prim_contents : Nat := {prim_offsets[0]}\n")
    w("\n/-! Native interpreter frame, recovered from the prologue saves. -/\n")
    w(f"def interpFrameBytes : Nat := {frame_bytes}\n")
    w(f"def interpSavedRootsOffset : Nat := {saved_roots_offset}\n")
    w("def interpSavedRegs : List Nat := [" + ", ".join(str(r) for r, _ in saved_regs) + "]\n")
    w("def interpSaveOffset : Nat → Nat\n")
    for reg, offset in saved_regs:
        w(f"  | {reg} => {offset}\n")
    w("  | _ => 0\n")
    w("\n/-! Native caml_main frame, checked against saves and the final return. -/\n")
    w(f"def camlMainFrameBytes : Nat := {main_frame_bytes}\n")
    w("def camlMainSavedRegs : List Nat := [" + ", ".join(str(r) for r, _ in sorted(main_saved_regs)) + "]\n")
    w("def camlMainSaveOffset : Nat → Nat\n")
    for reg, offset in sorted(main_saved_regs):
        w(f"  | {reg} => {offset}\n")
    w("  | _ => 0\n")
    w("\n/-! Nonlocal-jump buffer slots, matched between setjmp and longjmp. -/\n")
    w(f"def jumpBufferBytes : Nat := {max(off for _, off in jump_saved) + 8}\n")
    w("def jumpSavedRegs : List Nat := [" + ", ".join(str(r) for r, _ in jump_saved) + "]\n")
    w("def jumpSaveOffset : Nat → Nat\n")
    for reg, offset in jump_saved:
        w(f"  | {reg} => {offset}\n")
    w("  | _ => 0\n")
    w("\n/-! `Caml_state` field offsets (bytes). -/\n")
    for f in ["young_limit", "young_ptr", "young_start", "young_end", "young_alloc_start",
              "young_alloc_end", "minor_heap_wsz", "stack_low", "stack_high", "stack_threshold", "extern_sp",
              "trapsp", "trap_barrier", "external_raise", "exn_bucket", "backtrace_active",
              "requested_major_slice", "requested_minor_gc", "local_roots",
              "stat_minor_words", "stat_promoted_words", "stat_major_words",
              "stat_minor_collections", "stat_major_collections", "stat_heap_wsz",
              "stat_top_heap_wsz", "stat_compactions", "stat_forced_major_collections",
              "stat_heap_chunks", "ref_table", "ephe_ref_table", "custom_table",
              "in_minor_collection"]:
        w(f"def off_{f} : Nat := {off[f]}\n")
    w("\n/-! Collector structure offsets and constants, measured by the RV64 compiler\n"
      "from runtime/freelist.c. -/\n")
    for name, value in collector.items():
        w(f"def {name} : Nat := {value}\n")
    w("\n/-! HTIF table layout measured from c/src/htif.c by the RV64 compiler. -/\n")
    for name, value in htif_layout().items():
        w(f"def {name} : Nat := {value}\n")
    w("\nend OCaml.Vm.Layout\n")


if __name__ == "__main__":
    main()
