import OCaml.Programs.Generated.LazyForceCode
import OCaml.Bytecode.FwdObservations
import OCaml.Logic.Symbolic
import OCaml.Logic.CodeSlice

/-! Symbolic execution of the real CamlinternalLazy.force entry, extracted by
runbc --lean. Only the already-forced cases are relevant to forwarding; the
Lazy_tag branch invokes user code and is deliberately a separate obligation. -/
namespace OCaml.Programs.LazyForce
open OCaml.Bytecode

/-- The two constants read from the loaded Stdlib__Obj global. -/
structure ObjConstants (h : Heap) (globals obj : Val) : Prop where
  global : field? h globals objGlobal = some obj
  forward : field? h obj 9 = some (.int 250)
  lazy : field? h obj 5 = some (.int 246)

/-- Calling convention for force, with an arbitrary return continuation. -/
def entry (v a env retEnv : Val) (ret trap : Nat) (ex : BitVec 63)
    (rest : List Val) (h : Heap) (w : World) : St :=
  ⟨0, a, v :: .code ret :: retEnv :: .int ex :: rest, env, 0, trap, h, w⟩

def returned (v retEnv : Val) (ret trap : Nat) (ex : BitVec 63)
    (rest : List Val) (h : Heap) (w : World) : St :=
  ⟨ret, v, rest, retEnv, ex.toNat, trap, h, w⟩

/-- Read-only primitive equations, directly reducing the actual primitive dispatcher. -/
theorem tag_primitive (P : Prog) (v : Val) (h : Heap) (w : World) :
    prim P "caml_obj_tag" [v] h w =
      (if v.isInt then .ok (Val.ofInt 1000) h w else
       match tag? h v with | some t => .ok (Val.ofInt t) h w | none => .unsupported) := by
  rw [prim, if_neg (by decide +kernel), if_neg (by decide +kernel), if_pos (by decide +kernel)]
  simp only [primF3]
  split <;> simp_all
  split <;> simp_all

theorem forward_get (P : Prog) (h : Heap) (w : World) (l : Nat) (v : Val)
    (block : h.get? l = some (.block 250 [v])) :
    prim P "caml_array_unsafe_get" [.ptr l 0, .int 0] h w = .ok v h w := by
  have tag : tag? h (.ptr l 0) = some 250 := by simp [tag?, block, Obj.tag]
  have size : size? h (.ptr l 0) = some 1 := by simp [size?, block, Obj.wosize]
  have field : field? h (.ptr l 0) 0 = some v := by simp [field?, block]
  rw [prim, if_neg (by decide +kernel), if_pos (by decide +kernel)]
  delta primF2 primF2.match_13
  simp only [String.reduceEq, dite_false, dite_true,
    primF1Impl._sparseCasesOn_8, ints?._sparseCasesOn_1, putBlock._sparseCasesOn_1,
    size, tag]
  simp [doubleArrayTag, field]

/-- The extracted decoder; decoded_run_sound connects it to any pinned program. -/
def exec (P : Prog) := decodedK P (decodeAt code)

def tagged (v : Val) (tag : BitVec 63) (env retEnv : Val) (ret trap : Nat)
    (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World) : St :=
  ⟨5, .int tag, v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
    env, 0, trap, h, w⟩

def tested (pc : Nat) (v : Val) (tag : BitVec 63) (accu env retEnv : Val) (ret trap : Nat)
    (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World) : St :=
  ⟨pc, accu, .int tag :: v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
    env, 0, trap, h, w⟩

/-- The three argument moves followed by the non-allocating tag primitive. -/
theorem force_tag (P : Prog) (image : ForceCode P) (v a env retEnv : Val)
    (tag : BitVec 63) (ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (read : prim P "caml_obj_tag" [v] h w = .ok (.int tag) h w) :
    Run.iter (exec P) 4 (entry v a env retEnv ret trap ex rest h w) =
      .ok (tagged v tag env retEnv ret trap ex rest h w) := by
  change Run.iter (exec P) 1
    ⟨3, v, v :: v :: v :: .code ret :: retEnv :: .int ex :: rest, env, 0, trap, h, w⟩ = _
  rw [Run.iter_one]
  unfold exec decodedK
  change (match opt P.prims[316]? (fun nm => cCall P
      ⟨3, v, v :: v :: v :: .code ret :: retEnv :: .int ex :: rest, env, 0, trap, h, w⟩
      2 nm [v]) with
    | .next s => Except.ok s | r => Except.error r) = _
  rw [image.tagName]
  simp only [opt, cCall, read]
  rfl

/-- Read the Forward tag constant and select its branch (four instructions). -/
theorem force_forward_test (P : Prog) (obj v env retEnv : Val) (ret trap : Nat)
    (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (constants : ObjConstants h P.globals obj) :
    Run.iter (exec P) 4 (tagged v 250 env retEnv ret trap ex rest h w) =
      .ok (tested 12 v 250 (.int 1) env retEnv ret trap ex rest h w) := by
  change (match opt (field? h P.globals objGlobal) (fun ob =>
    opt (field? h ob 9) (fun x => Res.next
      ⟨8, x, .int 250 :: v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
        env, 0, trap, h, w⟩)) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 3 = _
  rw [constants.global]
  simp only [opt, constants.forward]
  rfl

/-- The payload read and return use the same heap and caller continuation. -/
theorem force_forward_return (P : Prog) (image : ForceCode P) (v env retEnv : Val)
    (l ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (saved : 0 ≤ ex.toInt)
    (block : h.get? l = some (.block 250 [v])) :
    Run.iter (exec P) 4
      (tested 12 (.ptr l 0) 250 (.int 1) env retEnv ret trap ex rest h w) =
      .ok (returned v retEnv ret trap ex rest h w) := by
  have get := forward_get P h w l v block
  change Run.iter (exec P) 2
    ⟨14, .ptr l 0, .int 0 :: .int 250 :: .ptr l 0 :: .ptr l 0 :: .ptr l 0 ::
      .code ret :: retEnv :: .int ex :: rest, env, 0, trap, h, w⟩ = _
  unfold Run.iter exec decodedK
  change (match opt P.prims[17]? (fun nm => cCall P
    ⟨14, .ptr l 0, .int 0 :: .int 250 :: .ptr l 0 :: .ptr l 0 :: .ptr l 0 ::
      .code ret :: retEnv :: .int ex :: rest, env, 0, trap, h, w⟩
    2 nm [.ptr l 0, .int 0]) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 1 = _
  rw [image.getName]
  simp only [opt, cCall, get]
  change Run.iter (exec P) 1
    ⟨16, v, .int 250 :: .ptr l 0 :: .ptr l 0 :: .ptr l 0 ::
      .code ret :: retEnv :: .int ex :: rest, env, 0, trap, h, w⟩ = _
  rw [Run.iter_one]
  change (match (if rest.length + 7 < 4 then Res.wrong else
    if ex.toInt < 0 then Res.unsupported else .next (returned v retEnv ret trap ex rest h w)) with
    | .next s => Except.ok s | r => Except.error r) = _
  rw [if_neg (by omega), if_neg (by omega)]

/-- The real stdlib Forward branch returns its payload in twelve instructions,
for any payload, surrounding heap, caller stack, environment and world. -/
theorem force_forward (P : Prog) (image : ForceCode P) (obj v a env retEnv : Val)
    (l ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (saved : 0 ≤ ex.toInt)
    (constants : ObjConstants h P.globals obj)
    (block : h.get? l = some (.block 250 [v])) :
    Run.iter (bcK P) 12 (entry (.ptr l 0) a env retEnv ret trap ex rest h w) =
      .ok (returned v retEnv ret trap ex rest h w) := by
  apply decoded_run_sound P (decodeAt code) image.decode
  have tag : prim P "caml_obj_tag" [.ptr l 0] h w = .ok (.int 250) h w := by
    rw [tag_primitive]
    simp [Val.isInt, tag?, block, Obj.tag, Val.ofInt]
  change Run.iter (exec P) (4 + (4 + 4)) _ = _
  rw [Run.iter_add, force_tag P image _ a env retEnv 250 ret trap ex rest h w tag]
  change Run.iter (exec P) (4 + 4) _ = _
  rw [Run.iter_add, force_forward_test P obj _ env retEnv ret trap ex rest h w constants]
  exact force_forward_return P image v env retEnv l ret trap ex rest h w saved block

/-- A non-Forward tag selects the ordinary-value test. -/
theorem force_value_test (P : Prog) (obj v env retEnv : Val) (tag : BitVec 63)
    (ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (constants : ObjConstants h P.globals obj) (different : tag ≠ 250) :
    Run.iter (exec P) 4 (tagged v tag env retEnv ret trap ex rest h w) =
      .ok (tested 18 v tag (.int 0) env retEnv ret trap ex rest h w) := by
  change (match opt (field? h P.globals objGlobal) (fun ob =>
    opt (field? h ob 9) (fun x => Res.next
      ⟨8, x, .int tag :: v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
        env, 0, trap, h, w⟩)) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 3 = _
  rw [constants.global]
  simp only [opt, constants.forward]
  change (match opt (physEq? (.int tag) (.int 250)) (fun e => Res.next
    ⟨10, Val.ofBool e, .int tag :: v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
      env, 0, trap, h, w⟩) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 1 = _
  have cmp : (Val.int tag == Val.int 250) = false := by
    exact beq_eq_false_iff_ne.mpr (fun eq => different (Val.int.inj eq))
  simp only [physEq?, cmp, opt]
  rfl

/-- A non-Lazy, non-Forward value is returned unchanged. -/
theorem force_value_return (P : Prog) (obj v env retEnv : Val) (tag : BitVec 63)
    (ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (saved : 0 ≤ ex.toInt)
    (constants : ObjConstants h P.globals obj) (different : tag ≠ 246) :
    Run.iter (exec P) 6 (tested 18 v tag (.int 0) env retEnv ret trap ex rest h w) =
      .ok (returned v retEnv ret trap ex rest h w) := by
  change (match opt (field? h P.globals objGlobal) (fun ob =>
    opt (field? h ob 5) (fun x => Res.next
      ⟨21, x, .int tag :: v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
        env, 0, trap, h, w⟩)) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 5 = _
  rw [constants.global]
  simp only [opt, constants.lazy]
  change (match opt (physEq? (.int tag) (.int 246)) (fun e => Res.next
    ⟨23, Val.ofBool (!e), .int tag :: v :: v :: v :: .code ret :: retEnv :: .int ex :: rest,
      env, 0, trap, h, w⟩) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 3 = _
  have cmp : (Val.int tag == Val.int 246) = false := by
    exact beq_eq_false_iff_ne.mpr (fun eq => different (Val.int.inj eq))
  simp only [physEq?, cmp, opt]
  change (match (if rest.length + 7 < 4 then Res.wrong else
    if ex.toInt < 0 then Res.unsupported else .next (returned v retEnv ret trap ex rest h w)) with
    | .next s => Except.ok s | r => Except.error r) >>= Run.iter (exec P) 0 = _
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

/-- The payload path reaches the same caller state as the Forward path. -/
theorem force_value (P : Prog) (image : ForceCode P) (obj v a env retEnv : Val)
    (tag : BitVec 63) (ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (saved : 0 ≤ ex.toInt)
    (constants : ObjConstants h P.globals obj)
    (read : prim P "caml_obj_tag" [v] h w = .ok (.int tag) h w)
    (notForward : tag ≠ 250) (notLazy : tag ≠ 246) :
    Run.iter (bcK P) 14 (entry v a env retEnv ret trap ex rest h w) =
      .ok (returned v retEnv ret trap ex rest h w) := by
  apply decoded_run_sound P (decodeAt code) image.decode
  change Run.iter (exec P) (4 + (4 + 6)) _ = _
  rw [Run.iter_add, force_tag P image v a env retEnv tag ret trap ex rest h w read]
  change Run.iter (exec P) (4 + 6) _ = _
  rw [Run.iter_add, force_value_test P obj v env retEnv tag ret trap ex rest h w constants notForward]
  exact force_value_return P obj v env retEnv tag ret trap ex rest h w saved constants notLazy

/-- Forward and payload calls have equal output/exit and divergence observations
for every caller continuation, by confluence after twelve versus fourteen steps.
The tag-reading premise is the actual primitive equation, not a run assumption. -/
theorem force_observations (P : Prog) (image : ForceCode P) (obj v a env retEnv : Val)
    (tag : BitVec 63) (l ret trap : Nat) (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (saved : 0 ≤ ex.toInt)
    (constants : ObjConstants h P.globals obj)
    (block : h.get? l = some (.block 250 [v]))
    (read : prim P "caml_obj_tag" [v] h w = .ok (.int tag) h w)
    (notForward : tag ≠ 250) (notLazy : tag ≠ 246) :
    FwdObservations P (entry (.ptr l 0) a env retEnv ret trap ex rest h w)
      (entry v a env retEnv ret trap ex rest h w) :=
  .of_common_result (force_forward P image obj v a env retEnv l ret trap ex rest h w saved constants block)
    (force_value P image obj v a env retEnv tag ret trap ex rest h w saved constants read notForward notLazy)

/-- The two force arguments differ by exactly one permitted contextual shortcut. -/
theorem force_argument_edit (v a env retEnv : Val) (l ret trap : Nat)
    (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (block : h.get? l = some (.block 250 [v])) (payload : ShortcutPayload h v) :
    FwdEdit (entry (.ptr l 0) a env retEnv ret trap ex rest h w)
      (entry v a env retEnv ret trap ex rest h w) :=
  .replace _ (.stack 0) l v block payload rfl

/-- Integer payloads need no abstract primitive premise: the real tag primitive
returns the immediate-value pseudo-tag 1000. -/
theorem force_integer_observations (P : Prog) (image : ForceCode P)
    (obj a env retEnv : Val) (n : BitVec 63) (l ret trap : Nat)
    (ex : BitVec 63) (rest : List Val) (h : Heap) (w : World)
    (saved : 0 ≤ ex.toInt)
    (constants : ObjConstants h P.globals obj)
    (block : h.get? l = some (.block 250 [.int n])) :
    FwdObservations P (entry (.ptr l 0) a env retEnv ret trap ex rest h w)
      (entry (.int n) a env retEnv ret trap ex rest h w) := by
  apply force_observations P image obj (.int n) a env retEnv 1000 l ret trap ex rest h w saved constants block
  · rw [tag_primitive]; rfl
  · decide
  · decide

end OCaml.Programs.LazyForce
