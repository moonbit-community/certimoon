// The integer assertions of the spec testsuite (spec_cases_test.mbt): each
// result is a theorem of the semantics, so they check the port's numeric
// layer and reduction rules against the reference results.

///|
test "the spec testsuite's integer assertions hold" {
  let failures = []
  for c in spec_cases {
    let (name, body, expected) = c
    let cfg = @wasm.config(body)
    let want = match expected {
      Some(v) => @wasm.computes_stmt(cfg, [v])
      None => @wasm.traps_stmt(cfg)
    }
    let got = @wasm.outcome(cfg) catch {
      e => {
        failures.push(name + ": " + e.to_string())
        continue
      }
    }
    if !@kernel.hyp(got).is_empty() || !@basics.aconv(@kernel.concl(got), want) {
      failures.push(name + ": got " + @term_syntax.print_term(@kernel.concl(got)))
    }
  }
  if !failures.is_empty() {
    fail("\{failures.length()} of \{spec_cases.length()} cases fail:\n" + failures.join("\n"))
  }
}

///|
test "the spec testsuite's loads at address 0 hold" {
  // address.wast's data, then zeros as far as the loads reach
  let bytes = Array::makei(40, i => if i < 26 { (b'a'.to_int() + i).to_byte() } else { b'\x00' })
  let st = @wasm.store(memory=bytes)
  let failures = []
  for c in spec_load_cases {
    let (name, body, expected) = c
    let cfg = @wasm.config(body, store=st.0, inst=st.1)
    let got = @wasm.outcome(cfg) catch {
      e => {
        failures.push(name + ": " + e.to_string())
        continue
      }
    }
    // computes(cfg, s, vs): loads leave the store as it is
    let want = @wasm.computes_stmt(cfg, [expected.unwrap()])
    if !@kernel.hyp(got).is_empty() || !@basics.aconv(@kernel.concl(got), want) {
      failures.push(name + ": got " + @term_syntax.print_term(@kernel.concl(got)))
    }
  }
  if !failures.is_empty() {
    fail("\{failures.length()} of \{spec_load_cases.length()} cases fail:\n" + failures.join("\n"))
  }
}
