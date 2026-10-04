#!/usr/bin/env python3
"""Instantiate ordinary/recursive closure nursery reservations over shared scalar inputs."""
import argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
TEMPLATE = r'''import OCaml.Vm.Sim.@native@NurseryInput
import OCaml.Vm.Sim.@native@ReserveSegment
import OCaml.Vm.Sim.@native@ReservePins
import OCaml.Vm.Sim.@native@ReserveLayout

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The native @family@ reservation consumes the transported nursery observations
and reserves its metadata and captures without entering the GC slow path. -/
theorem @family@_reserve {pl : Place} {pc sp @functions@count a domain limit : Nat} {accu : BitVec 64} {c d : Config}
    (space : @native@NurseryInput sp @functions@count a domain limit accu c)
    (front : @native@Prefixed c pl pc sp @functions@count accu d) :
    ∃ nb after, StepsN nb d after ∧ @native@Reserved c pl pc sp @functions@count a domain accu after := by
  have nursery := space.after front
  have domainRead : RamReadAt Layout.sym_Caml_state 8 := ⟨by decide, by decide, by decide⟩
  have youngRead := nursery.youngWrite.read
  have limitRead : RamReadAt domain 8 := by simpa only [Layout.off_young_limit, Nat.add_zero] using nursery.limitRead
  have youngAddress : BitVec.ofNat 64 domain + sign_extend (m := 64) (0x008#12) =
      BitVec.ofNat 64 (domain + Layout.off_young_ptr) := by rw [BitVec.ofNat_add]; rfl
  have readWord (address : Nat) : sign_extend (m := 64) (bytesT8 d.σ.mem address) = word d address := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have domainValue := (readWord Layout.sym_Caml_state).trans nursery.domainValue
  have youngValue := (readWord (domain + Layout.off_young_ptr)).trans nursery.youngValue
  have limitValue : sign_extend (m := 64) (bytesT8 d.σ.mem domain) = BitVec.ofNat 64 limit := by
    simpa only [Layout.off_young_limit, Nat.add_zero] using (readWord (domain + Layout.off_young_limit)).trans nursery.limitValue
  have limitNat : (BitVec.ofNat 64 limit).toNat = limit :=
    Nat.mod_eq_of_lt (by have upper := nursery.headerWrite.upper; have capacity := nursery.capacity; omega)
  have guard : @compare@ (BitVec.ofNat 64 (a - 8)) (BitVec.ofNat 64 limit) = @guard@ := by
    apply @guardProof@
    rw [nursery.headerWrite.read.toNat, limitNat]
    exact nursery.capacity
@sizeWord@  have address := @arithmetic@ a (@size@) nursery.room (by have small := nursery.small; omega)
  have bp : SegSt (@entry@#64) [⟨Register.@inputRegister@, BitVec.ofNat 64 (@input@)⟩]
      (fun σ => Vsa.Sim.Code.Caml@native@ReserveLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨front.good, front.pcAt, ⟨@inputProof@, trivial⟩,
      front.good.minstret, front.tick, @family@_reserve_loaded front.image, rfl, rfl⟩
  obtain ⟨nextMemory, written⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (domain + Layout.off_young_ptr) (sdData_val (BitVec.ofNat 64 (a - 8))) := ⟨_, rfl⟩
  have run := tr_@family@_reserve (BitVec.ofNat 64 (@input@)) d.σ.mem d.σ
  simp only [@family@_reserve_domain, show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, domainRead.toNat@sizeSimp@] at run
  have first := run domainRead.lower domainRead.upper domainRead.htif (BitVec.ofNat 64 domain) domainValue.symm
  simp only [youngAddress, youngRead.toNat, limitRead.toNat] at first
  have second := first youngRead.lower youngRead.upper youngRead.htif (BitVec.ofNat 64 (a + 8 * (@size@))) youngValue.symm
    limitRead.lower limitRead.upper limitRead.htif (BitVec.ofNat 64 limit) limitValue.symm
  simp only [@addressSimp@address] at second
  obtain ⟨nb, after, _, steps, post⟩ := second nursery.youngWrite.lower nursery.youngWrite.upper nursery.youngWrite.htif nursery.youngWrite.aligned
    (image_entry_code nursery.image (List.mem_cons_self :
      (domain + Layout.off_young_ptr, 8, BitVec.ofNat 64 (a - 8)) ∈ grabReserveLog domain a) (by decide) (by decide))
    nextMemory written guard d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked (allowed := @family@ReserveWrites) (by decide)
  have reserveMemory : after.σ.mem = writeLog d.σ.mem (grabReserveLog domain a) := by
    rw [memory, written]; rfl
  have fullMemory : after.σ.mem = writeLog c.σ.mem (closurePushLog sp count accu ++ grabReserveLog domain a) := by
    rw [reserveMemory, front.memory, writeLog_append]
  exact ⟨nb, after, steps, post.good, post.tick, image_of_writeLog front.image nursery.image reserveMemory,
    post.pcAt, front.fields.frame frame (by decide), @sizePost@PinsHold.get post.pins ⟨0, by simp⟩, fullMemory,
    (front.frame.trans frame).widenChecked (allowed := @family@ReservationWrites) (by decide)⟩

end OCaml.Vm.Sim
'''

def render(recursive):
    family='closurerec' if recursive else 'closure'
    native='Closurerec' if recursive else 'Closure'
    size='closurerecSize functions count' if recursive else 'count + 2'
    mapping={
        'family':family,'native':native,'functions':'functions ' if recursive else '',
        'size':size,'compare':'zopz0zKzJ_u' if recursive else 'zopz0zI_u',
        'guard':'true' if recursive else 'false',
        'guardProof':'bgeu_of_le' if recursive else 'bltu_false_of_ge',
        'sizeWord':'' if recursive else '  have sizeWord := addiw_nat_add count 3 (offset := 0x003#12) (by decide) (by have small := front.fields.nurseryBound; omega)\n',
        'arithmetic':'nursery_add_reservation' if recursive else 'nursery_sub_reservation',
        'entry':'0x8000289c' if recursive else '0x800029e8',
        'inputRegister':'x10' if recursive else 'x17',
        'input':size if recursive else 'count',
        'inputProof':'front.sizeReg' if recursive else 'front.fields.countReg',
        'sizeSimp':', show sign_extend (m := 64) (0xff8#12) = -(8#64) from by decide, BitVec.zero_add' if recursive else ', sizeWord',
        'addressSimp':'' if recursive else 'show count + 3 = count + 2 + 1 by omega, ',
        'sizePost':'(frame.frame Register.x10 (by decide)).trans front.sizeReg, ' if recursive else '',
    }
    out=TEMPLATE
    for key,value in mapping.items():out=out.replace('@'+key+'@',value)
    assert '@' not in out
    return '-- GENERATED by scripts/gen_closure_reserve.py; do not edit.\n'+out

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    for recursive in [False,True]:
        native='Closurerec' if recursive else 'Closure'
        p=ROOT/f'OCaml/Vm/Sim/{native}Reserve.lean';out=render(recursive)
        if args.check:
            if not p.exists() or p.read_text()!=out:raise SystemExit(f'drift: {p}')
        else:p.write_text(out)
    print('Closure nursery adapters current')
