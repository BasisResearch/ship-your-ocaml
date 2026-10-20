import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Gc.F1Heap

/-! The representation across a channel opening: the channel placement gains
the new record (`ChanPlace.put`), every old object and channel keeps its
layout, and the old list head's record changes only in its link words
(`next`, `prev`), which `ChanAt` does not read. -/
namespace OCaml.Vm.Primitives
open OCaml.Bytecode Vsa.Machine Vsa.Sim
set_option autoImplicit false

/-- The channel placement with channel `id` at record `a`. -/
def _root_.OCaml.Vm.ChanPlace.put (cp : ChanPlace) (id a : Nat) : ChanPlace :=
  fun i => if i = id then some a else cp i

theorem _root_.OCaml.Vm.ChanPlace.put_self (cp : ChanPlace) (id a : Nat) : cp.put id a id = some a := by
  simp [OCaml.Vm.ChanPlace.put]

theorem _root_.OCaml.Vm.ChanPlace.put_other (cp : ChanPlace) {id a i : Nat} (ne : i ≠ id) :
    cp.put id a i = cp i := by
  simp [OCaml.Vm.ChanPlace.put, ne]

/-- An object's layout reads the channel placement only at its own channel id. -/
theorem ObjAt.chanPlace {c : Config} {pl : Place} {cp cp' : ChanPlace} {a : Nat} {o : Obj}
    (h : ObjAt c pl cp a o) (same : ∀ j, o = .channel j → cp' j = cp j) : ObjAt c pl cp' a o := by
  cases o with
  | channel j =>
    obtain ⟨header, ops, place⟩ := h
    exact ⟨header, ops, by rw [same j rfl]; exact place⟩
  | _ => exact h

/-- **A channel record outside its link words**: `ChanAt` reads `fd`,
`offset`, `end`, `curr`, `max` (bytes 0–39), `flags` (68–71) and the buffer,
never `next` (48) or `prev` (56). -/
theorem channel_copied_links {c c' : Config} {a : Nat} {ch : Chan} (h : ChanAt c a ch)
    (front : Reloc.Copied c c' a a 48)
    (back : Reloc.Copied c c' (a + 64) (a + 64) (chanOffBuff - 64 + ch.buffer.length)) : ChanAt c' a ch := by
  let pl : Place := ⟨fun _ => none, 0, 0⟩
  have backAt (off n : Nat) (lo : 64 ≤ off) (hi : off + n ≤ chanOffBuff + ch.buffer.length) :
      ∀ j, j < n → byte c' (a + off + j) = byte c (a + off + j) := by
    intro j hj
    have e := back (off - 64 + j) (by omega)
    rwa [show a + 64 + (off - 64 + j) = a + off + j by omega] at e
  have img : (Reloc.chanEqv a ch).Img id pl 0 0 c c' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨h.cursorLe, h.bufferLe, h.aligned⟩, ?_⟩
    · exact Reloc.bytesT_congr (front.mono chanOffFd 4 (by simp only [chanOffFd]; omega))
    · exact Reloc.bytesT_congr (front.mono chanOffOffset 8 (by simp only [chanOffOffset]; omega))
    · exact Reloc.bytesT_congr (front.mono chanOffCurr 8 (by simp only [chanOffCurr]; omega))
    · exact Reloc.bytesT_congr (front.mono chanOffMax 8 (by simp only [chanOffMax]; omega))
    · exact Reloc.bytesT_congr (front.mono chanOffEnd 8 (by simp only [chanOffEnd]; omega))
    · exact Reloc.bytesT_congr (backAt chanOffFlags 4 (by simp only [chanOffFlags]; omega)
        (by simp only [chanOffFlags, chanOffBuff]; omega))
    · intro i b hb
      have hi := (List.getElem?_eq_some_iff.mp hb).1
      change byte c' (a + chanOffBuff + i) = byte c (a + chanOffBuff + i)
      have e := backAt chanOffBuff (i + 1) (by simp only [chanOffBuff]; omega) (by omega) i (by omega)
      exact e
    · exact Reloc.bytesT_congr (backAt chanOffFlags 4 (by simp only [chanOffFlags]; omega)
        (by simp only [chanOffFlags, chanOffBuff]; omega))
  exact (Reloc.chanEqv a ch).transport id pl 0 0 c c' h img

/-- **The world after `openChan`**: the old channels keep their records
(`kept`), the new one is represented at `rec`, and the console and the
object-ID counter are unchanged. -/
theorem WorldRepr.openChan {c d : Config} {cp : ChanPlace} {w : World} {rec : Nat} {ch : Chan}
    (h : WorldRepr c cp w)
    (output : Vsa.Machine.output d.σ = Vsa.Machine.output c.σ)
    (oo : word d Layout.sym_oo_last_id = word c Layout.sym_oo_last_id)
    (kept : ∀ id old a, w.chans[id]? = some old → cp id = some a → ChanAt d a old)
    (new : ChanAt d rec ch) :
    WorldRepr d (cp.put w.chans.length rec) {w with chans := w.chans ++ [ch]} := by
  refine ⟨by rw [output]; exact h.output, ?_, by rw [oo]; exact h.ooId⟩
  intro id old hc
  rcases Nat.lt_or_ge id w.chans.length with lt | ge
  · rw [List.getElem?_append_left lt] at hc
    obtain ⟨a, ha, _⟩ := h.chans id old hc
    exact ⟨a, by rw [ChanPlace.put_other cp (Nat.ne_of_lt lt)]; exact ha, kept id old a hc ha⟩
  · rw [List.getElem?_append_right ge] at hc
    rcases Nat.eq_or_lt_of_le ge with eq | gt
    · subst eq
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨rec, ChanPlace.put_self cp _ rec, new⟩
    · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; omega)] at hc
      cases hc

/-- **What a successful `openChan` says about the heap** (its guard): no
object names the new channel id. -/
theorem openChan_fresh {h h' : Heap} {w w' : World} {fd : Int} {isOut : Bool} {v : Val}
    (ok : openChan h w fd isOut = .ok v h' w') :
    ∀ l, h.get? l ≠ some (.channel w.chans.length) := by
  intro l hl
  unfold openChan at ok
  dsimp only at ok
  split at ok
  · cases ok
  have mem : Obj.channel w.chans.length ∈ h.objs := List.mem_of_getElem? hl
  have contains : h.objs.contains (.channel w.chans.length) = true := List.contains_iff_mem.mpr mem
  simp only [contains, ↓reduceIte] at ok
  cases ok

/-- **What a successful `openChan` says about the world** (its first guard):
fewer than `Gc.maxChannels` channels were open. -/
theorem openChan_bound {h h' : Heap} {w w' : World} {fd : Int} {isOut : Bool} {v : Val}
    (ok : openChan h w fd isOut = .ok v h' w') : w.chans.length < Gc.maxChannels := by
  have m : Gc.maxChannels = 64 := rfl
  rw [m]
  unfold openChan at ok
  dsimp only at ok
  split at ok
  · cases ok
  · omega

/-- The new id is apart from every channel object of the heap, so extending
the placement there keeps every old object's layout. -/
theorem ObjAt.openChan {c : Config} {pl : Place} {cp : ChanPlace} {a rec l : Nat} {o : Obj} {h : Heap}
    {n : Nat} (layout : ObjAt c pl cp a o) (fresh : ∀ l, h.get? l ≠ some (.channel n))
    (ho : h.get? l = some o) : ObjAt c pl (cp.put n rec) a o :=
  ObjAt.chanPlace layout fun j hj => by
    subst hj
    exact ChanPlace.put_other cp fun e => fresh l (e ▸ ho)

end OCaml.Vm.Primitives
