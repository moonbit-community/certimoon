// Every line is JSON so the same commands support both development and timing.

///|
fn event(phase : String, ms : Double) -> Unit {
  let row : Json = { "phase": phase, "ms": @json.ToJson::to_json(ms) }
  println(row.stringify())
}

///|
fn elapsed(start : @bench.Timestamp) -> Double {
  @bench.monotonic_clock_end(start) / 1000.0
}

///|
fn run(args : Array[String]) -> Unit raise {
  guard args.length() >= 2 &&
    (args[1] == "verify" || args[1] == "list" || args[1] == "check") else {
    raise Failure(
      "usage: moon run cmd/tlsf -- [check LEMMA ... | verify | list]",
    )
  }
  let mode = args[1]
  let keep_going = mode == "check" &&
    args.length() >= 3 &&
    args[2] == "--keep-going"
  let names_start = if keep_going { 3 } else { 2 }
  if mode == "check" && args.length() <= names_start {
    raise Failure(
      "usage: tlsf check [--keep-going] NAME ... | check [--keep-going] --all",
    )
  }
  if (mode == "check" && args.length() < 3) ||
    (mode != "check" && args.length() != 2) {
    raise Failure(
      "usage: tlsf check NAME [NAME ...] | check --all | list | verify",
    )
  }
  let total = @bench.monotonic_clock_start()
  let start = @bench.monotonic_clock_start()
  @logic.load()
  event("checked_base", elapsed(start))
  if @env.get_env_var("WASMCERT_PROOF_TRACE") == Some("1") {
    @logic.set_trace(true)
  }
  let start = @bench.monotonic_clock_start()
  if mode == "verify" {
    @allocator.verify()
    event("full_tlsf_replay", elapsed(start))
    let row : Json = {
      "status": "VERIFIED",
      "declarations": @json.ToJson::to_json(@allocator.names().length()),
      "axioms": @json.ToJson::to_json(@kernel.axioms().length()),
    }
    println(row.stringify())
  } else {
    let until = if mode == "check" &&
      args.length() == names_start + 1 &&
      args[names_start] != "--all" {
      Some(args[names_start])
    } else {
      None
    }
    let plan = @allocator.prepare_checks(until~)
    event("tlsf_declarations", elapsed(start))
    @testkit.check_axioms()
    if mode == "list" {
      for name in plan.names() {
        let row : Json = {
          "name": name,
          "kind": @json.ToJson::to_json(plan.kind(name)),
          "location": @json.ToJson::to_json(plan.location(name)),
        }
        println(row.stringify())
      }
    } else {
      let selected = if args.length() == names_start + 1 &&
        args[names_start] == "--all" {
        plan.names()
      } else {
        args[names_start:].to_owned()
      }
      let mut failed = 0
      for name in selected {
        let start = @bench.monotonic_clock_start()
        let result = Some(plan.check(name)) catch {
          e => {
            @testkit.check_axioms()
            if !keep_going {
              raise e
            }
            let row : Json = {
              "status": "CONDITIONAL FAIL",
              "name": name,
              "error": e.to_string(),
            }
            println(row.stringify())
            failed += 1
            None
          }
        }
        guard result is Some(result) else { continue }
        let ms = elapsed(start)
        @testkit.check_axioms()
        let row : Json = {
          "status": "CONDITIONAL PASS",
          "name": result.name(),
          "ms": @json.ToJson::to_json(ms),
          "premises": @json.ToJson::to_json(result.premises()),
          "closed_implication": @json.ToJson::to_json(
            @kernel.hyp(result.theorem()).is_empty(),
          ),
        }
        println(row.stringify())
      }
      if failed > 0 {
        event("total", elapsed(total))
        @env.exit(1)
      }
    }
  }
  event("total", elapsed(total))
}

///|
fn main {
  run(@env.args()) catch {
    e => {
      let row : Json = { "status": "FAIL", "error": e.to_string() }
      println(row.stringify())
      @env.exit(1)
    }
  }
}
