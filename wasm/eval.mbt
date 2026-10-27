// A symbolic evaluator: runs a configuration (s, f, es) and proves every
// step from the reduction rules, so `run` gives
// reduce_trans((s, f, es), (s', f', es')) with es' values or [Trap].
//
// A step finds the redex (the first instruction after a prefix of
// values), instantiates the rule for it, proves the rule's side
// conditions by computation (rewriting with the port's definitions and
// evaluating word and numeral arithmetic), and puts the step back into its
// context: the values before it and the instructions after it (Lfilled
// with LBase), and each label around it (Lfilled with LRec). A br is
// matched with its label by depth.
//
// Covered: numeric instructions, references (ref.null, ref.is_null),
// unreachable, nop, drop, select, block, loop, if, br, br_if, br_table,
// local.get/set/tee, and traps. Calls, frames, globals, memory and tables
// are not: they raise "no rule for".

///|
/// The rules a step uses: (key, relation, position among the relation's
/// rules, text the rule must contain), the positions as in reduction.mbt
/// and store.mbt.
let step_rules : Array[(String, String, Int, Array[String])] = [
  ("unop", "reduce_simple", 0, ["Basic(Unop("]),
  ("binop_some", "reduce_simple", 1, ["Basic(Binop(", "SOME("]),
  ("binop_none", "reduce_simple", 2, ["Basic(Binop(", "NONE"]),
  ("testop", "reduce_simple", 3, ["Basic(Testop("]),
  ("relop", "reduce_simple", 4, ["Basic(Relop("]),
  ("cvt_some", "reduce_simple", 5, ["Convert", "SOME("]),
  ("cvt_none", "reduce_simple", 6, ["Convert", "NONE"]),
  ("reinterpret", "reduce_simple", 7, ["Reinterpret"]),
  ("ref_null", "reduce_simple", 8, ["Basic(Ref_null("]),
  ("is_null", "reduce_simple", 9, ["Ref_is_null", "wasm_bool(true)"]),
  ("not_null", "reduce_simple", 10, ["Ref_is_null", "wasm_bool(false)"]),
  ("unreachable", "reduce_simple", 20, ["Basic(Unreachable)"]),
  ("nop", "reduce_simple", 21, ["Basic(Nop)"]),
  ("drop", "reduce_simple", 22, ["Basic(Drop)"]),
  ("select_zero", "reduce_simple", 23, ["Basic(Select(", "[v_to_e(v2)]"]),
  ("select_nonzero", "reduce_simple", 24, ["Basic(Select(", "[v_to_e(v1)]"]),
  ("if_zero", "reduce_simple", 25, ["Basic(If(", "Block(tb, e2s)"]),
  ("if_nonzero", "reduce_simple", 26, ["Basic(If(", "Block(tb, e1s)"]),
  ("label_values", "reduce_simple", 27, ["[Label(", "MAP(v_to_e"]),
  ("label_trap", "reduce_simple", 28, ["[Label(", "[Trap])], [Trap]"]),
  ("br", "reduce_simple", 29, ["[Label(", "Basic(Br(i))"]),
  ("br_if_zero", "reduce_simple", 30, ["Basic(Br_if(", "NIL)"]),
  ("br_if_nonzero", "reduce_simple", 31, ["Basic(Br_if(", "[Basic(Br(i))]"]),
  ("br_table_in", "reduce_simple", 32, ["Basic(Br_table(", "EL(val(c), is_)"]),
  ("br_table_out", "reduce_simple", 33, ["Basic(Br_table(", "<= val("]),
  ("local_tee", "reduce_simple", 37, ["Basic(Local_tee("]),
  ("trap", "reduce_simple", 38, ["Lfilled(0, ", "[Trap])"]),
  ("lift", "reduce", 0, ["reduce_simple("]),
  ("local_get", "reduce", 8, ["Basic(Local_get("]),
  ("local_set", "reduce", 9, ["Basic(Local_set("]),
  ("block", "reduce", 36, ["Basic(Block("]),
  ("loop", "reduce", 37, ["Basic(Loop("]),
  ("context", "reduce", 38, ["Lfilled(k, lholed, es', "]),
  ("lbase", "Lfilled", 0, ["LBase("]),
  ("lrec", "Lfilled", 1, ["LRec("]),
  ("trans_refl", "reduce_trans", 0, ["reduce_trans("]),
  ("trans_step", "reduce_trans", 1, ["reduce("]),
]

///|
let rules : Map[String, @kernel.Thm] = Map([])

///|
let eval_rewrite : Ref[@equal.Conv?] = Ref::{ val: None }

///|
let list_rewrite : Ref[@equal.Conv?] = Ref::{ val: None }

///|
fn setup() -> Unit raise {
  if eval_rewrite.val is Some(_) {
    return
  }
  load()
  for r in step_rules {
    let (key, rel, i, marks) = r
    let all = @bool.conjuncts_rule(thm(rel + "_rules")).to_array()
    let th = all[i]
    let (_, body) = @basics.strip_forall(@kernel.concl(th))
    let text = @term_syntax.print_term(body)
    for m in marks {
      if !text.contains(m) {
        raise Failure("wasmcert/wasm eval: \{rel} rule \{i} is not \{key}: \{text}")
      }
    }
    rules[key] = th
  }
  // list structure: APPEND, MAP and v_to_e on written-out lists
  list_rewrite.val = Some(
    @equal.thenc(
      @simp.pure_rewrite_conv(
        @list.List([@lists.append(), @lists.map(), thm("v_to_e")]),
      ),
      @calc_num.num_reduce_conv,
    ),
  )
  let ths = def_thms.copy()
  for th in [
    @lists.append(),
    @lists.map(),
    @lists.length(),
    @lists.reverse(),
    @lists.el_cons(),
    @lists.hd(),
    @lists.tl(),
    @lists.not_cons_nil(),
    @lists.cons_11(),
    @ind_types.option_distinct(),
    @ind_types.option_inj(),
    @words.dimindex_8(),
    @words.dimindex_16(),
    @words.dimindex_32(),
    @words.dimindex_64(),
    @words.dimindex_128(),
  ] {
    ths.push(th)
  }
  // constructors a side condition compares
  for ty_name in ["einstr", "value", "v_num", "v_ref", "t_num", "t_ref", "valtype"] {
    ths.push(@ind_types.distinctness(ty_name)) catch {
      _ => ()
    }
    ths.push(@ind_types.injectivity(ty_name)) catch {
      _ => ()
    }
  }
  eval_rewrite.val = Some(@simp.rewrite_conv(@list.List(ths)))
}

///|
fn rule(key : String) -> @kernel.Thm raise {
  match rules.get(key) {
    Some(th) => th
    None => raise Failure("wasmcert/wasm eval: no rule " + key)
  }
}

///|
/// `t == t'`, `t'` the list structure of `t` written out.
fn list_conv(t : @kernel.Term) -> @kernel.Thm raise {
  match list_rewrite.val {
    Some(c) => c(t)
    None => raise Failure("wasmcert/wasm eval: not set up")
  }
}

///|
/// `t == t'`, `t'` the value of `t`: rewriting with the definitions and
/// evaluating word and numeral arithmetic until nothing changes.
fn eval_conv(t : @kernel.Term) -> @kernel.Thm raise {
  guard eval_rewrite.val is Some(rw) else {
    raise Failure("wasmcert/wasm eval: not set up")
  }
  let once = @equal.thenc(
    rw,
    @equal.thenc(@words.word_reduce_conv, @calc_num.num_reduce_conv),
  )
  let mut th = @kernel.refl(t)
  for _ in 0..<100 {
    let cur = @equal.rhs(@kernel.concl(th))
    let next = once(cur)
    if @basics.aconv(@equal.rhs(@kernel.concl(next)), cur) {
      return th
    }
    th = @kernel.trans(th, next)
  }
  raise Failure(
    "wasmcert/wasm eval: evaluating " + show_term(t) + " does not settle",
  )
}

///|
fn show_term(t : @kernel.Term) -> String {
  @term_syntax.print_term(t) catch {
    _ => (try @printer.string_of_term(t) catch { _ => "?" })
  }
}

///|
fn const_named(t : @kernel.Term) -> String {
  if @kernel.is_const(t) {
    (try @kernel.dest_const(t) catch { _ => ("", @kernel.bool_ty) }).0
  } else {
    ""
  }
}

///|
/// The head constant's name and the arguments.
fn head_args(t : @kernel.Term) -> (String, Array[@kernel.Term]) {
  let (h, args) = @basics.strip_comb(t)
  (const_named(h), args.to_array())
}

///|
fn app(f : String, args : Array[@kernel.Term]) -> @kernel.Term raise {
  @basics.list_mk_comb(tm(f), @list.List(args))
}

///|
fn einstr_list(items : ArrayView[@kernel.Term]) -> @kernel.Term raise {
  @lists.mk_list(@list.List(items.iter().collect()), ty("Einstr"))
}

///|
fn value_list(items : ArrayView[@kernel.Term]) -> @kernel.Term raise {
  @lists.mk_list(@list.List(items.iter().collect()), ty("Value"))
}

///|
fn numeral(n : Int) -> @kernel.Term raise {
  @nums.mk_small_numeral(n.to_int64())
}

///|
/// The value an instruction is (V_num, V_vec or V_ref), if it is one.
fn as_value(e : @kernel.Term) -> @kernel.Term? raise {
  match head_args(e) {
    ("Basic", [b]) =>
      match head_args(b) {
        ("EConstNum", [x]) => Some(app("V_num", [x]))
        ("EConstVec", [x]) => Some(app("V_vec", [x]))
        _ => None
      }
    ("Ref", [r]) => Some(app("V_ref", [r]))
    _ => None
  }
}

///|
/// The index of the first instruction that is not a value.
fn first_instr(items : Array[@kernel.Term]) -> Int? raise {
  for i, e in items {
    if as_value(e) is None {
      return Some(i)
    }
  }
  None
}

///|
fn values_of(items : ArrayView[@kernel.Term]) -> Array[@kernel.Term] raise {
  let out = []
  for e in items {
    out.push(as_value(e).unwrap())
  }
  out
}

///|
fn owned(items : ArrayView[@kernel.Term]) -> Array[@kernel.Term] {
  items.iter().collect()
}

///|
/// A final instruction list: values, or [Trap].
fn is_final(items : Array[@kernel.Term]) -> Bool raise {
  first_instr(items) is None ||
  (items.length() == 1 && head_args(items[0]).0 == "Trap")
}

///|
/// `rule` with its quantified variables instantiated by name.
fn inst(
  key : String,
  pairs : Array[(String, @kernel.Term)],
) -> @kernel.Thm raise {
  let th = rule(key)
  let (vars, _) = @basics.strip_forall(@kernel.concl(th))
  let names = []
  let tms = []
  for v in vars {
    let (name, _) = @kernel.dest_var(v)
    names.push(name)
    let mut t = v
    for p in pairs {
      if p.0 == name {
        t = p.1
      }
    }
    tms.push(t)
  }
  for p in pairs {
    if !names.contains(p.0) {
      raise Failure("wasmcert/wasm eval: rule \{key} has no variable \{p.0}")
    }
  }
  @bool.ispecl(@list.List(tms), th)
}

///|
/// `t`, proved from `given` or by computation.
fn prove_cond(t : @kernel.Term, given : Array[@kernel.Thm]) -> @kernel.Thm raise {
  for g in given {
    if @basics.aconv(@kernel.concl(g), t) {
      return g
    }
  }
  if @basics.is_conj(t) {
    let (a, b) = @basics.dest_conj(t)
    return @bool.conj(prove_cond(a, given), prove_cond(b, given))
  }
  let e = eval_conv(t)
  if const_named(@equal.rhs(@kernel.concl(e))) == "T" {
    @bool.eqt_elim(e)
  } else {
    raise Stuck(
      "cannot show " + show_term(t) + " (it computes to " +
      show_term(@equal.rhs(@kernel.concl(e))) +
      ")",
    )
  }
}

///|
/// A side condition does not hold, or a configuration cannot step.
priv suberror Stuck {
  Stuck(String)
}

///|
/// Rule `key`, instantiated, with its list structure written out and its
/// side conditions proved.
fn apply_rule(
  key : String,
  pairs : Array[(String, @kernel.Term)],
  given? : Array[@kernel.Thm] = [],
) -> @kernel.Thm raise {
  let th = @equal.conv_rule(list_conv, inst(key, pairs))
  let c = @kernel.concl(th)
  if @basics.is_imp(c) {
    @bool.mp(th, prove_cond(@basics.dest_imp(c).0, given))
  } else {
    th
  }
}

///|
/// The first of the rules whose side conditions hold.
fn first_rule(
  keys : Array[String],
  pairs : Array[(String, @kernel.Term)],
) -> @kernel.Thm raise {
  let mut last = ""
  for key in keys {
    try {
      return apply_rule(key, pairs)
    } catch {
      Stuck(msg) => last = msg
      e => raise e
    }
  }
  raise Stuck(last)
}

///|
/// `reduce(s, f, es, s', f', es')` from a reduce or reduce_simple step,
/// with es' computed.
fn as_reduce(
  th : @kernel.Thm,
  s : @kernel.Term,
  f : @kernel.Term,
) -> @kernel.Thm raise {
  let th = match head_args(@kernel.concl(th)) {
    ("reduce_simple", [e, e2]) =>
      apply_rule("lift", [("e", e), ("e'", e2), ("s", s), ("f", f)], given=[th])
    _ => th
  }
  // the result's instructions: the last argument
  @equal.conv_rule(@equal.rand_conv(eval_conv), th)
}

///|
/// `Lfilled(0, LBase(vals, rest), es, vals ++ es ++ rest)`.
fn lfilled_base(
  vals : Array[@kernel.Term],
  rest : @kernel.Term,
  es : @kernel.Term,
) -> @kernel.Thm raise {
  let vs = value_list(vals[:])
  let lb = app("LBase", [vs, rest])
  apply_rule("lbase", [("lholed", lb), ("vs", vs), ("es'", rest), ("es", es)], given=[
    @kernel.refl(lb),
  ])
}

///|
/// From `Lfilled(k, l, es, lk)`: `Lfilled(k + 1, LRec(vals, n, es0, l,
/// rest), es, vals ++ [Label(n, es0, lk)] ++ rest)`.
fn lfilled_rec(
  vals : Array[@kernel.Term],
  n : @kernel.Term,
  es0 : @kernel.Term,
  inner : @kernel.Thm,
  rest : @kernel.Term,
) -> @kernel.Thm raise {
  let (_, a) = head_args(@kernel.concl(inner))
  guard a is [k, l, es, lk] else { raise Failure("wasmcert/wasm eval: lfilled_rec") }
  let vs = value_list(vals[:])
  let lr = app("LRec", [vs, n, es0, l, rest])
  apply_rule(
    "lrec",
    [
      ("lholed", lr),
      ("vs", vs),
      ("n", n),
      ("es'", es0),
      ("l", l),
      ("es''", rest),
      ("k", k),
      ("es", es),
      ("lfilledk", lk),
    ],
    given=[@kernel.refl(lr), inner],
  )
}

///|
/// A step of `es` as a step of `es` inside a context with the same
/// Lfilled shape on both sides.
fn in_context(
  step : @kernel.Thm,
  build : (@kernel.Term) -> @kernel.Thm raise,
) -> @kernel.Thm raise {
  let (_, a) = head_args(@kernel.concl(step))
  guard a is [_, _, es, _, _, es2] else { raise Failure("wasmcert/wasm eval: in_context") }
  let lf1 = build(es)
  let lf2 = build(es2)
  @drule.match_mp(rule("context"))(@bool.conj(step, @bool.conj(lf1, lf2)))
}

///|
/// A step of the redex as a step of `pre ++ redex ++ rest`.
fn with_prefix(
  step : @kernel.Thm,
  pre : Array[@kernel.Term],
  rest : ArrayView[@kernel.Term],
) -> @kernel.Thm raise {
  if pre.is_empty() && rest.is_empty() {
    return step
  }
  let rest_t = einstr_list(rest)
  in_context(step, es => lfilled_base(pre, rest_t, es))
}

///|
/// A step of `es` as a step of `[Label(n, es0, es)]`.
fn in_label(
  step : @kernel.Thm,
  n : @kernel.Term,
  es0 : @kernel.Term,
) -> @kernel.Thm raise {
  let nil = einstr_list([][:])
  in_context(step, es => lfilled_rec([], n, es0, lfilled_base([], nil, es), nil))
}

///|
/// Where the next br of `items` is: Some((label index, labels around
/// it)), when the instruction to execute is a br.
fn find_br(items : Array[@kernel.Term]) -> (Int, Int)? raise {
  guard first_instr(items) is Some(pos) else { return None }
  match head_args(items[pos]) {
    ("Basic", [b]) =>
      match head_args(b) {
        ("Br", [i]) => Some((@nums.dest_small_numeral(i).to_int(), 0))
        _ => None
      }
    ("Label", [_, _, li]) => {
      let li_items = @basics.dest_list(li).to_array()
      if is_final(li_items) {
        None
      } else {
        match find_br(li_items) {
          Some((i, d)) => Some((i, d + 1))
          None => None
        }
      }
    }
    _ => None
  }
}

///|
/// For a br `depth` labels deep in `items`, taking `n` values:
/// (those values, Lfilled(depth, lholed, values ++ [br], items)).
fn br_context(
  items : Array[@kernel.Term],
  depth : Int,
  n : Int,
) -> (Array[@kernel.Term], @kernel.Thm) raise {
  let pos = first_instr(items).unwrap()
  let vals = values_of(items[:pos])
  let rest = einstr_list(items[pos + 1:])
  if depth == 0 {
    if vals.length() < n {
      raise Stuck("a br needs \{n} values and has \{vals.length()}")
    }
    let k = vals.length() - n
    let lf = lfilled_base(owned(vals[:k]), rest, einstr_list(items[k:pos + 1]))
    (owned(vals[k:]), lf)
  } else {
    guard head_args(items[pos]) is ("Label", [n2, es0, li]) else {
      raise Failure("wasmcert/wasm eval: br_context")
    }
    let (used, inner) = br_context(@basics.dest_list(li).to_array(), depth - 1, n)
    (used, lfilled_rec(vals, n2, es0, inner, rest))
  }
}

///|
priv enum StepResult {
  Final
  Stepped(@kernel.Thm)
  // the instruction to execute is a br to a label outside the list
  Escapes
}

///|
/// One step of (s, f, es).
fn step(
  s : @kernel.Term,
  f : @kernel.Term,
  es : @kernel.Term,
) -> StepResult raise {
  let items = @basics.dest_list(es).to_array()
  guard first_instr(items) is Some(pos) else { return Final }
  if is_final(items) {
    return Final
  }
  let x = items[pos]
  let vals = values_of(items[:pos])
  let rest = items[pos + 1:]
  match head_args(x) {
    ("Trap", []) => {
      // the trap ends everything around it
      let lf = lfilled_base(vals, einstr_list(rest), einstr_list([x][:]))
      let lholed = head_args(@kernel.concl(lf)).1[1]
      let th = apply_rule("trap", [("es", es), ("lholed", lholed)], given=[lf])
      Stepped(as_reduce(th, s, f))
    }
    ("Label", [n, es0, li]) => {
      let li_items = @basics.dest_list(li).to_array()
      let th = if first_instr(li_items) is None {
        let vs = value_list(values_of(li_items[:])[:])
        as_reduce(apply_rule("label_values", [("n", n), ("es", es0), ("vs", vs)]), s, f)
      } else if is_final(li_items) {
        as_reduce(apply_rule("label_trap", [("n", n), ("es", es0)]), s, f)
      } else {
        match find_br(li_items) {
          Some((i, d)) if i == d => {
            let (used, lf) = br_context(li_items, d, @nums.dest_small_numeral(n).to_int())
            let lholed = head_args(@kernel.concl(lf)).1[1]
            let rule_th = apply_rule(
              "br",
              [
                ("vs", value_list(used[:])),
                ("n", n),
                ("i", numeral(i)),
                ("lholed", lholed),
                ("LI", li),
                ("es", es0),
              ],
              given=[lf],
            )
            as_reduce(rule_th, s, f)
          }
          Some((i, d)) if i > d => return Escapes
          _ =>
            match step(s, f, li) {
              Stepped(inner) => in_label(inner, n, es0)
              Escapes => return Escapes
              Final => raise Failure("wasmcert/wasm eval: label body is final")
            }
        }
      }
      Stepped(with_prefix(th, vals, rest))
    }
    ("Basic", [b]) => {
      guard basic_step(s, f, b, vals) is Some((k, th)) else { return Escapes }
      Stepped(with_prefix(as_reduce(th, s, f), owned(vals[:vals.length() - k]), rest))
    }
    _ => raise Stuck("no rule for " + show_term(x))
  }
}

///|
/// The step of `b` with the values before it: (how many values it takes,
/// the step), or None for a br (its label is further out).
fn basic_step(
  s : @kernel.Term,
  f : @kernel.Term,
  b : @kernel.Term,
  vals : Array[@kernel.Term],
) -> (Int, @kernel.Thm)? raise {
  let (op_name, args) = head_args(b)
  // the k values before b
  fn take(k : Int) -> Array[@kernel.Term] raise {
    if vals.length() < k {
      raise Stuck("\{op_name} needs \{k} values and has \{vals.length()}")
    }
    owned(vals[vals.length() - k:])
  }
  // the number in V_num(c)
  fn num(v : @kernel.Term) -> @kernel.Term raise {
    match head_args(v) {
      ("V_num", [c]) => c
      _ => raise Stuck(op_name + " needs a number, not " + show_term(v))
    }
  }
  // the word in V_num(ConstInt32(n))
  fn i32(v : @kernel.Term) -> @kernel.Term raise {
    match head_args(num(v)) {
      ("ConstInt32", [n]) => n
      _ => raise Stuck(op_name + " needs an i32, not " + show_term(v))
    }
  }
  fn value(t : @kernel.Term) -> @kernel.Term raise {
    @equal.rhs(@kernel.concl(eval_conv(t)))
  }
  let r = match (op_name, args) {
    ("Unop", [t, op]) => {
      let v = take(1)
      (1, apply_rule("unop", [("v", num(v[0])), ("t", t), ("op", op)]))
    }
    ("Binop", [t, op]) => {
      let v = take(2)
      let (c1, c2) = (num(v[0]), num(v[1]))
      match head_args(value(app("app_binop", [op, c1, c2]))) {
        ("SOME", [c]) =>
          (2, apply_rule("binop_some", [("op", op), ("v1", c1), ("v2", c2), ("v", c), ("t", t)]))
        ("NONE", []) =>
          (2, apply_rule("binop_none", [("op", op), ("v1", c1), ("v2", c2), ("t", t)]))
        _ => raise Stuck("cannot compute " + show_term(b))
      }
    }
    ("Testop", [t, op]) => {
      let v = take(1)
      (1, apply_rule("testop", [("v", num(v[0])), ("t", t), ("op", op)]))
    }
    ("Relop", [t, op]) => {
      let v = take(2)
      (2, apply_rule("relop", [("v1", num(v[0])), ("v2", num(v[1])), ("t", t), ("op", op)]))
    }
    ("Cvtop", [t2, cv, t1, sat_sx]) => {
      let c = num(take(1)[0])
      let common = [("v", c), ("t1", t1), ("t2", t2)]
      if head_args(cv).0 == "Reinterpret" {
        (1, apply_rule("reinterpret", common))
      } else {
        match head_args(value(app("cvt", [t2, sat_sx, c]))) {
          ("SOME", [c2]) =>
            (1, apply_rule("cvt_some", common + [("sat_sx", sat_sx), ("v'", c2)]))
          ("NONE", []) => (1, apply_rule("cvt_none", common + [("sat_sx", sat_sx)]))
          _ => raise Stuck("cannot compute " + show_term(b))
        }
      }
    }
    ("Ref_null", [t]) => (0, apply_rule("ref_null", [("t", t)]))
    ("Ref_is_null", []) => {
      let v = take(1)[0]
      guard head_args(v) is ("V_ref", [r]) else {
        raise Stuck("ref.is_null needs a reference, not " + show_term(v))
      }
      (1, first_rule(["is_null", "not_null"], [("v_r", r)]))
    }
    ("Unreachable", []) => (0, apply_rule("unreachable", []))
    ("Nop", []) => (0, apply_rule("nop", []))
    ("Drop", []) => (1, apply_rule("drop", [("v", take(1)[0])]))
    ("Select", [t_tag]) => {
      let v = take(3)
      (
        3,
        first_rule(["select_zero", "select_nonzero"], [
          ("v1", v[0]),
          ("v2", v[1]),
          ("n", i32(v[2])),
          ("t_tag", t_tag),
        ]),
      )
    }
    ("If", [tb, e1s, e2s]) => {
      let n = i32(take(1)[0])
      (
        1,
        first_rule(["if_zero", "if_nonzero"], [
          ("n", n),
          ("tb", tb),
          ("e1s", e1s),
          ("e2s", e2s),
        ]),
      )
    }
    ("Br", [_]) => return None
    ("Br_if", [i]) =>
      (1, first_rule(["br_if_zero", "br_if_nonzero"], [("n", i32(take(1)[0])), ("i", i)]))
    ("Br_table", [is_, i]) =>
      (
        1,
        first_rule(["br_table_in", "br_table_out"], [
          ("c", i32(take(1)[0])),
          ("is_", is_),
          ("i", i),
        ]),
      )
    ("Block" | "Loop", [tb, body]) => {
      guard head_args(value(app("tb_tf", [app("f_inst", [f]), tb]))) is ("Tf", [t1s, t2s]) else {
        raise Stuck("cannot compute the type of " + show_term(b))
      }
      let n = @basics.dest_list(t1s).length()
      let m = @basics.dest_list(t2s).length()
      let key = if op_name == "Block" { "block" } else { "loop" }
      (
        n,
        apply_rule(key, [
          ("vs", value_list(take(n)[:])),
          ("n", numeral(n)),
          ("tb", tb),
          ("es", body),
          ("t1s", t1s),
          ("t2s", t2s),
          ("m", numeral(m)),
          ("s", s),
          ("f", f),
        ]),
      )
    }
    ("Local_get" | "Local_set", [j]) => {
      guard head_args(f) is ("Wframe", [locs, inst_t]) else {
        raise Stuck("locals need the frame written out, not " + show_term(f))
      }
      let ls = @basics.dest_list(locs).to_array()
      let jj = @nums.dest_small_numeral(j).to_int()
      if jj >= ls.length() {
        raise Stuck("no local \{jj}: the frame has \{ls.length()}")
      }
      let split = [
        ("vi", value_list(ls[:jj])),
        ("j", j),
        ("v", ls[jj]),
        ("vs", value_list(ls[jj + 1:])),
        ("s", s),
      ]
      if op_name == "Local_get" {
        (0, apply_rule("local_get", split + [("f", f)]))
      } else {
        (1, apply_rule("local_set", split + [("i", inst_t), ("v'", take(1)[0])]))
      }
    }
    ("Local_tee", [i]) => (1, apply_rule("local_tee", [("v", take(1)[0]), ("i", i)]))
    _ => raise Stuck("no rule for " + show_term(b))
  }
  Some(r)
}

///|
/// Runs the configuration `cfg` = (s, f, es) to a final state and proves
/// `reduce_trans(cfg, (s', f', es'))`, es' values or [Trap], step by step
/// from the reduction rules. The instruction list must be written out;
/// local.get/set need the frame written out (`Wframe([...], inst)`).
/// Raises if a step has no rule here (see the top of this file) or after
/// `max_steps` steps.
pub fn run(cfg : @kernel.Term, max_steps? : Int = 10000) -> @kernel.Thm raise {
  setup()
  // write out the list structure first, and restate the result for cfg
  let cfg_eq = list_conv(cfg)
  let mut cur = @equal.rhs(@kernel.concl(cfg_eq))
  let steps = []
  while true {
    if steps.length() >= max_steps {
      raise Failure("wasmcert/wasm run: no final state after \{max_steps} steps")
    }
    let (s, rest) = @pair.dest_pair(cur)
    let (f, es) = @pair.dest_pair(rest)
    let r = step(s, f, es) catch {
      Stuck(msg) =>
        raise Failure(
          "wasmcert/wasm run: stuck after \{steps.length()} steps: \{msg}",
        )
      e => raise e
    }
    match r {
      Final => break
      Escapes => raise Failure("wasmcert/wasm run: a br leaves every block")
      Stepped(th) => {
        steps.push(th)
        let a = head_args(@kernel.concl(th)).1
        cur = @pair.mk_pair((a[3], @pair.mk_pair((a[4], a[5]))))
      }
    }
  }
  let mut acc = apply_rule("trans_refl", [("c", cur)])
  for i = steps.length() - 1; i >= 0; i = i - 1 {
    acc = @drule.match_mp(rule("trans_step"))(@bool.conj(steps[i], acc))
  }
  // reduce_trans(cfg, final) from reduce_trans(cfg', final), cfg == cfg'
  let rt = @kernel.rator(@kernel.rator(@kernel.concl(acc)))
  @kernel.eq_mp(
    @equal.sym(@equal.ap_thm(@equal.ap_term(rt, cfg_eq), cur)),
    acc,
  )
}

///|
/// `computes(cfg, s', vs)` or `traps(cfg, s')`, from `run(cfg)`.
pub fn outcome(cfg : @kernel.Term, max_steps? : Int = 10000) -> @kernel.Thm raise {
  let th = run(cfg, max_steps~)
  let fin = @kernel.rand(@kernel.concl(th))
  let (s2, rest) = @pair.dest_pair(fin)
  let (f2, es2) = @pair.dest_pair(rest)
  let items = @basics.dest_list(es2).to_array()
  if first_instr(items) is None {
    // the value stack lists the top first
    let vs = values_of(items[:])
    vs.rev_in_place()
    let goal = app("computes", [cfg, s2, value_list(vs[:])])
    let defs = @list.List([thm("v_stack_to_es"), @lists.reverse(), @lists.append()])
    @tactics.prove(
      goal,
      @tactics.then_tac(
        @simp.pure_rewrite_tac(@list.List([thm("computes")])),
        @tactics.then_tac(
          @tactics.exists_tac(f2),
          @tactics.then_tac(
            @tactics.conv_tac(
              @equal.rand_conv(
                @equal.rand_conv(
                  @equal.rand_conv(
                    @equal.thenc(@simp.pure_rewrite_conv(defs), list_conv),
                  ),
                ),
              ),
            ),
            @tactics.accept_tac(th),
          ),
        ),
      ),
    )
  } else {
    @tactics.prove(
      app("traps", [cfg, s2]),
      @tactics.then_tac(
        @simp.pure_rewrite_tac(@list.List([thm("traps")])),
        @tactics.then_tac(@tactics.exists_tac(f2), @tactics.accept_tac(th)),
      ),
    )
  }
}
