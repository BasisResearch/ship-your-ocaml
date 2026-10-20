import OCaml.Vm.Sim.OpenOutPlaced

/-!
# The loop geometry at `caml_ml_open_descriptor_out`'s return

Two steps from the entry `c`: the custom block's allocation
(`LoopGeometry.alloc_log`, to a config `c₁` that differs from `c` only in its
`young_ptr` word), then the opening (`LoopGeometry.openChan`, to the return
`d`, with the new record's separation `open_out_placed`). The geometry reads
the configuration only through the `Caml_state`/primitive-table pointers, the
allocation pointers and the open-channel list, which agree at `c₁` and `d`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel

/-- Eight kept bytes give a kept word. -/
theorem word_of_kept {c d : Config} {a : Nat}
    (kept : ∀ j, j < 8 → (d.σ.mem[a + j]?).getD 0 = (c.σ.mem[a + j]?).getD 0) : word d a = word c a := by
  unfold word; exact bytesT_keep kept

/-- **The loop geometry of the opened state** at the return. -/
theorem open_out_geometry {L : OCaml.Layout} {P : Prog} {s s' : St} {pl : Place} {cp : ChanPlace}
    {spV high : Nat} {ch : Chan}
    {live : Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {H : List (Nat × Nat)} {cap cap' charge : Nat} {sp ra r0 r1 r2 v head : BitVec 64} {c d : Config}
    (custom : Gc.CustomMemCall Ready state)
    {code : Channel.OpenCode} (o : OpenedOut code live Ready state k H cap' charge sp ra r0 r1 r2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput live H cap' charge sp ra r0 r1 r2 v head c)
    (N : OutNursery H (Gc.placedChannels cp s.world.chans.length) c)
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) (g : OCaml.LoopGeometry L P s c pl cp high)
    (placed : pl.φ (s.heap.alloc (.channel s.world.chans.length)).2 = some o.value.toNat)
    (heapS : s'.heap = (s.heap.alloc (.channel s.world.chans.length)).1)
    (chansS : s'.world.chans = s.world.chans ++ [ch]) :
    OCaml.LoopGeometry L P s' d pl (cp.put s.world.chans.length o.opening.record.toNat) high := by
  have block := o.block
  have low := N.low
  have highM := N.high
  have room := N.room
  have aligned := N.aligned
  have dom := h.domain
  have hE : Boot.WhileMinRuntime.domain + 928 ≤ Gc.minorRegion.lo := by decide
  have hDB : Layout.domainStateBytes = 928 := rfl
  have hY : Layout.off_young_ptr = 8 := rfl
  have hL : Layout.off_young_limit = 0 := rfl
  have hS : Layout.sym_Caml_state + 8 ≤ Boot.WhileMinRuntime.domain := by decide
  let D := (word c Layout.sym_Caml_state).toNat
  let Y := (runtimeFields c).youngPtr
  let log : List WEntry := [(D + Layout.off_young_ptr, 8, BitVec.ofNat 64 (Y - 24))]
  let c₁ : Config := { c with σ := { c.σ with mem := writeLog c.σ.mem log } }
  have mem₁ : c₁.σ.mem = writeLog c.σ.mem log := rfl
  have domOut : OutLRange log Layout.sym_Caml_state 8 := by
    simp only [log, OutLRange, and_true, D, dom]; omega
  have prims : Layout.sym_caml_prim_table + Layout.off_prim_contents + 8 ≤ Boot.WhileMinRuntime.domain := by decide
  have primsOut : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8 := by
    simp only [log, OutLRange, and_true, D, dom]; omega
  have headS : Layout.sym_caml_all_opened_channels + 8 ≤ Boot.WhileMinRuntime.domain := by decide
  have headOut : OutLRange log Layout.sym_caml_all_opened_channels 8 := by
    simp only [log, OutLRange, and_true, D, dom]; omega
  have chansOut : ∀ id ch' a, s.world.chans[id]? = some ch' → cp id = some a →
      OutLRange log a (chanOffBuff + ioBufferSize) := fun id ch' a hc hp => by
    have mem : a ∈ Gc.placedChannels cp s.world.chans.length :=
      Gc.mem_placedChannels.2 ⟨id, (List.getElem?_eq_some_iff.mp hc).1, hp⟩
    have r := N.recordsApart a mem
    unfold Gc.chanRecordBytes at r
    simp only [log, OutLRange, and_true, D, dom]; omega
  have dom₁ : word c₁ Layout.sym_Caml_state = word c Layout.sym_Caml_state := by
    unfold word; rw [mem₁]; exact bytesT_writeLog_out _ domOut
  have prims₁ : word c₁ (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) := by
    unfold word; rw [mem₁]; exact bytesT_writeLog_out _ primsOut
  have yw : word c₁ (D + Layout.off_young_ptr) = BitVec.ofNat 64 (Y - 24) := by
    show bytesT (writeLog c.σ.mem log) _ 8 = _
    exact OCaml.Vm.Gc.word_writeLog_at _ log 0 _ _ rfl trivial
  have lw : word c₁ (D + Layout.off_young_limit) = word c (D + Layout.off_young_limit) := by
    show bytesT (writeLog c.σ.mem log) _ 8 = _
    exact bytesT_writeLog_out _ (by simp only [log, OutLRange, and_true, D]; omega)
  have ptr₁ : (runtimeFields c₁).youngPtr = Y - 24 := by
    change (word c₁ ((word c₁ Layout.sym_Caml_state).toNat + Layout.off_young_ptr)).toNat = _
    rw [dom₁]
    change (word c₁ (D + Layout.off_young_ptr)).toNat = _
    rw [yw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := g.nursery.top; omega)]
  have lim₁ : (runtimeFields c₁).youngLimit = (runtimeFields c).youngLimit := by
    change (word c₁ ((word c₁ Layout.sym_Caml_state).toNat + Layout.off_young_limit)).toNat =
      (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_young_limit)).toNat
    rw [dom₁]
    change (word c₁ (D + Layout.off_young_limit)).toNat = (word c (D + Layout.off_young_limit)).toNat
    rw [lw]
  have reserve : NurseryReserve c log o.value.toNat (Obj.channel s.world.chans.length).wosize 2 :=
    { before := by show Y = _; omega
      size := Nat.le_refl _
      room := by simp only [Gc.minorRegion] at low; omega
      aligned := by omega
      capacity := by omega
      after := fun c' m => by
        refine ⟨?_, ?_⟩
        · have : (runtimeFields c').youngPtr = (runtimeFields c₁).youngPtr := by
            simp only [runtimeFields, domainWord, word, m, mem₁]
          rw [this, ptr₁]; omega
        · have : (runtimeFields c').youngLimit = (runtimeFields c₁).youngLimit := by
            simp only [runtimeFields, domainWord, word, m, mem₁]
          rw [this, lim₁] }
  let s₁ : St := { s with heap := (s.heap.alloc (.channel s.world.chans.length)).1 }
  have g₁ : OCaml.LoopGeometry L P s₁ c₁ pl cp high :=
    g.alloc_log placed reserve rfl rfl domOut primsOut chansOut headOut mem₁
  have new := open_out_placed (t := s₁) (c' := c₁) o heap h pins data g rfl rfl placed
    (by simp only [Gc.minorRegion] at low ⊢; omega) (by show o.value.toNat + 8 * 2 ≤ _; omega)
    dom₁ prims₁ (by rw [lim₁]; exact g.nursery.nurseryLow) (by rw [ptr₁]; omega)
  have primsD : word d (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) :=
    word_of_kept fun j hj => static_kept custom o h N (by simp [openStatics]) hj
  have listed : Gc.OpenChannelList d.σ.mem (o.opening.record.toNat :: Gc.placedChannels cp s.world.chans.length) :=
    Gc.OpenChannelsLinked.list heap.channels o.linked (o.opening.record.isLt) fun b hb => by
      apply bytesT_keep
      intro j hj
      exact record_kept custom o heap h N hb (by unfold Gc.chanOffNext; omega)
        (by unfold Gc.chanOffNext Gc.chanRecordBytes chanOffBuff ioBufferSize; omega)
        (fun _ => Or.inl (by unfold Gc.chanOffNext; omega))
  exact g₁.openChan new heapS chansS (by rw [o.domain, dom₁]) (by rw [primsD, prims₁])
    (by rw [o.youngLimit, lim₁]) (by rw [o.youngPtr, ptr₁]) listed

end OCaml.Vm.Sim
