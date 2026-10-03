import OCaml.Vm.Gc.Generated.Forwarded
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.Queue

namespace OCaml.Vm.Gc.Forwarded
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc LeanRV64DExecutable

/-- Total header and forwarding-pointer reads, before the root store. -/
def loads (source : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (source - 8#64).toNat, read8 c.σ.mem source.toNat]

/-- Already-forwarded does not mean Forward_tag: this is the zero header
installed when a nursery object has already been copied. -/
structure Input (source root : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs source root)
  header : word c (source - 8#64).toNat = 0
  headerRead : ReadWindow (source - 8#64) 8
  pointerRead : ReadWindow source 8
  rootWrite : WriteWindow root 8

theorem access {source root c} (input : Input source root c) :
    ChainAccess c.σ.mem (regs source root) (loads source c) blocks := by
  refine ChainAccess.cons ⟨?_, ?_⟩ (ChainAccess.cons ⟨?_, True.intro⟩
    (ChainAccess.cons ⟨?_, True.intro⟩ ChainAccess.nil))
  · simp only [caml_oldify_oneX9ae4TSeg, AccessPlan]
    chain_facts True.intro
    apply input.headerRead.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, regs, srcVal, lookupG,
      Functions.sign_extend, Sail.BitVec.signExtend]
    bv_omega
  · simpa [caml_oldify_oneX9ae4TSeg, TermFactsO, TermFactsT, runGM, stepGM,
      regs, loads, stepLdsM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
      read8_value, word, Functions.sign_extend, Sail.BitVec.signExtend, guardB]
      using input.header
  · simp only [caml_oldify_oneX9ae4TSeg, caml_oldify_oneX9bf8Seg, AccessPlan]
    chain_facts True.intro
    apply input.pointerRead.ld rfl ?_ (read8_pins _ _)
    simp [eaddrM, mkLine, decodeM, regs, loads, srcVal, lookupG, eraseG,
      runGM, stepGM, stepLdsM, wvalM, Functions.sign_extend, Sail.BitVec.signExtend]
  · simp only [caml_oldify_oneX9ae4TSeg, caml_oldify_oneX9bf8Seg,
      caml_oldify_oneX9bfcSeg, AccessPlan]
    chain_facts True.intro
    apply input.rootWrite.sd rfl ?_
    simp [eaddrM, mkLine, decodeM, regs, loads, srcVal, lookupG, eraseG,
      runGM, stepGM, stepLdsM, wvalM, Functions.sign_extend, Sail.BitVec.signExtend]

/-- Complete generated block result plus the actual root update. Stops at
oldify's native epilogue; prologue/range checks and return are separate seams. -/
structure Post (source root : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs source root) (loads source before) before after
  rootWord : word after root.toNat = word before source.toNat
  memory : after.σ.mem = writeLog before.σ.mem [(root.toNat, 8, word before source.toNat)]
  pc : PCAt exitPc after
  code : Code.Caml_oldify_oneLoaded after.σ.mem

theorem forwarded_machine {source root c} (input : Input source root c) :
    FnSummary pc (fun d => d = c) (Post source root c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs source root) (loads source c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [8,9]; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = writeLog c.σ.mem [(root.toNat, 8, word c source.toNat)] := by
    rw [post.memory, writes]
    simp only [loads, List.tail_cons, List.headD_cons, read8_value, word]
  refine ⟨post, ?_, memory, ?_, oldifyCode_after input.code facts post⟩
  · change bytesT after.σ.mem _ 8 = _
    rw [memory, word_writeLog]
  · rw [PCAt, post.pc, endpoint]

/-- The actual root store realizes the typed relocation action. The partial
relocation invariant must identify the forwarding word with that action;
this theorem does not assume a collector execution or ScanCoherent. -/
theorem Post.slot_relocates {source root before after μ pl v}
    (post : Post source root before after)
    (represented : (Eqv.val v id).P pl root.toNat before)
    (sourceWord : word before root.toNat = source)
    (forwarding : word before source.toNat = relocWord μ pl v source) :
    (Eqv.val v id).P (reloc μ pl) root.toNat after := by
  apply (Eqv.val v id).transport μ pl root.toNat root.toNat before after represented
  change word after root.toNat = relocWord μ pl v (word before root.toNat)
  rw [post.rootWord, sourceWord, forwarding]

/-- Intrusive queue links directly supply both values consumed by the
forwarded path, independently of the next-source link. -/
theorem Post.target_from_links {q next root before after}
    (post : Post q.source root before after) (links : PendingCopy.Links q next before) :
    word after root.toNat = q.target := post.rootWord.trans links.target

/-- Updating a separate root slot preserves the work queue through its Eqv
frame. The enclosing heap/stack geometry supplies the two footprints. -/
theorem Post.queue_frame {source root before after qs pl}
    (post : Post source root before after) (queue : WorkQueue.View qs pl before)
    (links : WorkQueue.LinksOutside qs [(root.toNat, 8, word before source.toNat)])
    (head : OutLRange [(root.toNat, 8, word before source.toNat)]
      Layout.sym_oldify_todo_list 8) : WorkQueue.View qs pl after := by
  exact queue.frame_log post.memory links head

end OCaml.Vm.Gc.Forwarded
