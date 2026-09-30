import OCaml.Logic.Symbolic

/-! Application summaries retain the full push/enter state, including extra
arguments, closure environment and caller frame. A caller never substitutes a
syntactic "return to next PC" for RETURN/GRAB's dynamic behaviour. -/
namespace OCaml.Bytecode

/-- A symbolic run and its named postcondition, shared by block and function
composition. The postcondition may describe a normal return or a caught raise. -/
structure SummaryResult (P : Prog) (s : St) (Post : St → Prop) where
  steps : Nat
  state : St
  run : Run.iter (bcK P) steps s = .ok state
  post : Post state

/-- A function summary is explicitly indexed by its application precondition.
In particular, under- and over-application require their own pre/post cases;
`extra`, the caller return frame and the heap are not erased by this API.
Generated blocks prove its run field, with recursive cases using `loop_rule`
or a well-founded rank. -/
structure ApplicationSummary (P : Prog) (entry : Nat)
    (Pre : St → Prop) (Post : St → St → Prop) : Prop where
  run : ∀ s, s.pc = entry → Pre s → Nonempty (SummaryResult P s (Post s))

/-- Splice a generated push/enter prefixRun with a function summary. The
callee's actual exit state is passed to the continuation, including partial
closures from GRAB and re-entry states from over-applied RETURN. -/
theorem call_summary {P : Prog} {entry n : Nat} {s callee : St}
    {Pre : St → Prop} {Post : St → St → Prop} {Done : St → Prop}
    (prefixRun : Run.iter (bcK P) n s = .ok callee)
    (summary : ApplicationSummary P entry Pre Post)
    (atEntry : callee.pc = entry) (pre : Pre callee)
    (continuation : ∀ result, Post callee result → Nonempty (SummaryResult P result Done)) :
    Nonempty (SummaryResult P s Done) := by
  obtain ⟨body⟩ := summary.run callee atEntry pre
  obtain ⟨tail⟩ := continuation body.state body.post
  exact ⟨⟨n + body.steps + tail.steps, tail.state,
    sym_seq (sym_seq prefixRun body.run) tail.run, tail.post⟩⟩

/-- A tail call needs no synthetic return frame or continuation. -/
theorem tail_summary {P : Prog} {entry n : Nat} {s callee : St}
    {Pre : St → Prop} {Post : St → St → Prop}
    (prefixRun : Run.iter (bcK P) n s = .ok callee)
    (summary : ApplicationSummary P entry Pre Post)
    (atEntry : callee.pc = entry) (pre : Pre callee) :
    Nonempty (SummaryResult P s (Post callee)) := by
  obtain ⟨body⟩ := summary.run callee atEntry pre
  exact ⟨⟨n + body.steps, body.state, sym_seq prefixRun body.run, body.post⟩⟩

end OCaml.Bytecode
