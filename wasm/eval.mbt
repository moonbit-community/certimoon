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
// local.get/set/tee, global.get/set, call (of native functions), return,
// loads and stores (packed too), memory.size, memory.grow, memory.fill,
// memory.copy, call_indirect (through a table written out), and traps.
// Host functions, vector instructions and the table instructions are
// not: they raise "no rule for". memory.grow
// may fail in any state; the evaluator takes the step that grows when it
// can.
//
// Memory is a byte list, so loads and stores compute on it element by
// element: the evaluator suits small memories, written out (`store`). A
// grown memory's new bytes stay REPLICATE(n, 0) until something reads
// them.

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
  ("frame_values", "reduce_simple", 34, ["[Frame(", "MAP(v_to_e"]),
  ("frame_trap", "reduce_simple", 35, ["[Frame(", "[Trap])], [Trap]"]),
  ("return", "reduce_simple", 36, ["Basic(Return)"]),
  ("local_tee", "reduce_simple", 37, ["Basic(Local_tee("]),
  ("trap", "reduce_simple", 38, ["Lfilled(0, ", "[Trap])"]),
  ("lift", "reduce", 0, ["reduce_simple("]),
  ("call", "reduce", 1, ["Basic(Call("]),
  ("call_indirect", "reduce", 2, ["Basic(Call_indirect(", "[Invoke(i_cl)]"]),
  ("call_indirect_trap", "reduce", 3, ["Basic(Call_indirect(", "[Trap]"]),
  ("invoke", "reduce", 4, ["Func_native("]),
  ("local_get", "reduce", 8, ["Basic(Local_get("]),
  ("local_set", "reduce", 9, ["Basic(Local_set("]),
  ("global_get", "reduce", 10, ["Basic(Global_get("]),
  ("global_set", "reduce", 11, ["Basic(Global_set("]),
  ("load_some", "reduce", 12, ["Basic(Load(", "NONE", "wasm_deserialise_num"]),
  ("load_none", "reduce", 13, ["Basic(Load(", "NONE", "[Trap]"]),
  ("load_packed_some", "reduce", 14, ["load_packed(", "wasm_deserialise_num"]),
  ("load_packed_none", "reduce", 15, ["load_packed(", "[Trap]"]),
  ("store_some", "reduce", 16, ["Basic(Store(", "store(", "s_mems_update"]),
  ("store_none", "reduce", 17, ["Basic(Store(", "store(", "[Trap]"]),
  ("store_packed_some", "reduce", 18, ["store_packed(", "s_mems_update"]),
  ("store_packed_none", "reduce", 19, ["store_packed(", "[Trap]"]),
  ("memory_size", "reduce", 26, ["Basic(Memory_size)"]),
  ("memory_grow", "reduce", 27, ["Basic(Memory_grow)", "mem_grow("]),
  ("memory_grow_fail", "reduce", 28, ["Basic(Memory_grow)", "int32_minus_one"]),
  ("block", "reduce", 36, ["Basic(Block("]),
  ("loop", "reduce", 37, ["Basic(Loop("]),
  ("context", "reduce", 38, ["Lfilled(k, lholed, es', "]),
  ("frame_context", "reduce", 39, ["[Frame(", "f0"]),
  ("copy_trap", "reduce", 43, ["Basic(Memory_copy)", "[Trap]"]),
  ("copy_zero", "reduce", 44, ["Basic(Memory_copy)", "nn == 0", "NIL"]),
  ("copy_up", "reduce", 45, ["Basic(Memory_copy)", "ndest <= nsrc"]),
  ("copy_down", "reduce", 46, ["Basic(Memory_copy)", "ndest > nsrc"]),
  ("fill_trap", "reduce", 47, ["Basic(Memory_fill)", "[Trap]"]),
  ("fill_zero", "reduce", 48, ["Basic(Memory_fill)", "nn == 0", "NIL"]),
  ("fill_step", "reduce", 49, ["Basic(Memory_fill)", "Basic(Store("]),
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
/// The theorems `eval_rewrite` rewrites with (set up by `setup`).
let eval_thms : Array[@kernel.Thm] = []

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
        raise Failure("certimoon/wasm eval: \{rel} rule \{i} is not \{key}: \{text}")
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
    @lists.replicate(),
    @lists.length_replicate(),
    @lists.last(),
    @pair.pair_eq(),
    @words.dimindex_8(),
    @words.dimindex_16(),
    @words.dimindex_32(),
    @words.dimindex_64(),
    @words.dimindex_128(),
  ] {
    ths.push(th)
  }
  // constructors a side condition compares
  for ty_name in [
    "einstr", "value", "v_num", "v_ref", "t_num", "t_ref", "valtype", "tp_num", "sx",
    "mut", "cl", "tf", "limit_t", "tab_t", "global", "inst", "wstore", "wframe",
  ] {
    ths.push(@ind_types.distinctness(ty_name)) catch {
      _ => ()
    }
    ths.push(@ind_types.injectivity(ty_name)) catch {
      _ => ()
    }
  }
  for th in ths {
    eval_thms.push(th)
  }
  eval_rewrite.val = Some(rewrite_with(ths, suc_args))
}

///|
/// One rewrite at a time with `ths`, everywhere (as rewrite_conv), and
/// numeral and word arithmetic at each subterm, so a condition is decided
/// before the branches of its `if` grow; the definitions by SUC patterns
/// `suc` apply to numerals through suc_arg_conv.
fn rewrite_with(
  ths : Array[@kernel.Thm],
  suc : Array[(String, Int, Int)],
) -> @equal.Conv raise {
  let rewrite_step = @simp.general_rewrite_conv(
    true,
    c => c,
    @simp.basic_net(),
    @list.List(ths),
  )
  let step = @equal.first_conv(@list.List([
    rewrite_step,
    @equal.thenc(t => suc_arg_conv(t, suc), rewrite_step),
    // a branch an `if` does not take may divide by zero
    t => @calc_num.num_red_conv(t) catch { _ => raise Failure("num_red_conv") },
    t => @words.word_red_conv(t) catch { _ => raise Failure("word_red_conv") },
  ]))
  @equal.top_depth_conv(step)
}

///|
/// The definitions by SUC patterns: (name, number of arguments, the
/// argument with the pattern).
let suc_args : Array[(String, Int, Int)] = [
  ("take", 2, 0),
  ("drop", 2, 0),
  ("takefill", 3, 1),
  ("list_update", 3, 1),
  ("le_bytes", 2, 0),
  ("upt", 2, 1),
  ("REPLICATE", 2, 0),
]

///|
/// REPLICATE(n, x) is written out only for n up to this, so a grown
/// memory's new pages stay REPLICATE(65536 * k, 0).
let replicate_limit : Int64 = 64

///|
/// `f(.., n, ..) == f(.., SUC(n - 1), ..)` for a definition by SUC
/// patterns applied to a numeral n > 0.
fn suc_arg_conv(
  t : @kernel.Term,
  suc : Array[(String, Int, Int)],
) -> @kernel.Thm raise {
  let (name, args) = head_args(t)
  for e in suc {
    let (fname, arity, pos) = e
    if fname == name && args.length() == arity && @nums.is_numeral(args[pos]) {
      let n = @nums.dest_small_numeral(args[pos]) catch { _ => replicate_limit + 1 }
      if n > 0 && (name != "REPLICATE" || n <= replicate_limit) {
        let mut c = @equal.rand_conv(@calc_num.num_conv)
        for _ in 0..<(arity - 1 - pos) {
          c = @equal.rator_conv(c)
        }
        return c(t)
      }
    }
  }
  raise Failure("suc_arg_conv")
}

///|
fn rule(key : String) -> @kernel.Thm raise {
  match rules.get(key) {
    Some(th) => th
    None => raise Failure("certimoon/wasm eval: no rule " + key)
  }
}

///|
/// `t == t'`, `t'` the list structure of `t` written out.
fn list_conv(t : @kernel.Term) -> @kernel.Thm raise {
  match list_rewrite.val {
    Some(c) => c(t)
    None => raise Failure("certimoon/wasm eval: not set up")
  }
}

///|
/// `t == t'`, `t'` the value of `t`: rewriting with the definitions and
/// evaluating word and numeral arithmetic until nothing changes.
fn eval_conv(t : @kernel.Term) -> @kernel.Thm raise {
  guard eval_rewrite.val is Some(rw) else {
    raise Failure("certimoon/wasm eval: not set up")
  }
  settle(rw, t)
}

///|
/// A conversion that computes as the evaluator's side conditions do
/// (`eval_conv`): rewriting with the port's definitions and `defs`, and
/// evaluating word and numeral arithmetic, until nothing changes. `suc`
/// names the definitions among `defs` by SUC patterns, as (name, number
/// of arguments, the argument with the pattern), so that they apply to
/// numerals. For proving facts about written-out stores, such as a
/// theorem's hypotheses about a concrete one.
pub fn compute_conv(
  defs : Array[@kernel.Thm],
  suc? : Array[(String, Int, Int)] = [],
) -> @equal.Conv raise {
  setup()
  let rw = rewrite_with(eval_thms + defs, suc_args + suc)
  t => settle(rw, t)
}

///|
/// `t == t'`, rewriting with `rw` and computing arithmetic until nothing
/// changes.
fn settle(rw : @equal.Conv, t : @kernel.Term) -> @kernel.Thm raise {
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
    "certimoon/wasm eval: evaluating " + show_term(t) + " does not settle",
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
fn einstr_list(items : ArrayView[@kernel.Term]) -> @kernel.Term raise {
  @lists.mk_list(@list.List(items.iter().collect()), hol_type("einstr"))
}

///|
fn value_list(items : ArrayView[@kernel.Term]) -> @kernel.Term raise {
  @lists.mk_list(@list.List(items.iter().collect()), hol_type("value"))
}

///|
/// The value an instruction is (V_num, V_vec or V_ref), if it is one.
fn as_value(e : @kernel.Term) -> @kernel.Term? raise {
  match head_args(e) {
    ("Basic", [b]) =>
      match head_args(b) {
        ("EConstNum", [x]) => Some(call("V_num", [x]))
        ("EConstVec", [x]) => Some(call("V_vec", [x]))
        _ => None
      }
    ("Ref", [r]) => Some(call("V_ref", [r]))
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
      raise Failure("certimoon/wasm eval: rule \{key} has no variable \{p.0}")
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
  let th = inst(key, pairs)
  if !@basics.is_imp(@kernel.concl(th)) {
    return @equal.conv_rule(list_conv, th)
  }
  // the side conditions and the conclusion apart: numeral arithmetic on a
  // false side condition can turn the whole rule into T
  let th = @equal.conv_rule(
    @equal.thenc(
      @equal.rator_conv(@equal.rand_conv(list_conv)),
      @equal.rand_conv(list_conv),
    ),
    th,
  )
  @bool.mp(th, prove_cond(@basics.dest_imp(@kernel.concl(th)).0, given))
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
  // the result's instructions (the last argument), and its store (the
  // fourth) when the step changes it
  let th = @equal.conv_rule(@equal.rand_conv(eval_conv), th)
  let s2 = head_args(@kernel.concl(th)).1[3]
  if @basics.aconv(s2, s) {
    th
  } else {
    @equal.conv_rule(
      @equal.rator_conv(@equal.rator_conv(@equal.rand_conv(eval_conv))),
      th,
    )
  }
}

///|
/// `Lfilled(0, LBase(vals, rest), es, vals ++ es ++ rest)`.
fn lfilled_base(
  vals : Array[@kernel.Term],
  rest : @kernel.Term,
  es : @kernel.Term,
) -> @kernel.Thm raise {
  let vs = value_list(vals[:])
  let lb = call("LBase", [vs, rest])
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
  guard a is [k, l, es, lk] else { raise Failure("certimoon/wasm eval: lfilled_rec") }
  let vs = value_list(vals[:])
  let lr = call("LRec", [vs, n, es0, l, rest])
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
  guard a is [_, _, es, _, _, es2] else { raise Failure("certimoon/wasm eval: in_context") }
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
      raise Failure("certimoon/wasm eval: br_context")
    }
    let (used, inner) = br_context(@basics.dest_list(li).to_array(), depth - 1, n)
    (used, lfilled_rec(vals, n2, es0, inner, rest))
  }
}

///|
/// How many labels deep the next instruction of `items` is when it is a
/// return.
fn find_return(items : Array[@kernel.Term]) -> Int? raise {
  guard first_instr(items) is Some(pos) else { return None }
  match head_args(items[pos]) {
    ("Basic", [b]) => if head_args(b).0 == "Return" { Some(0) } else { None }
    ("Label", [_, _, li]) => {
      let li_items = @basics.dest_list(li).to_array()
      if is_final(li_items) {
        None
      } else {
        find_return(li_items).map(d => d + 1)
      }
    }
    _ => None
  }
}

///|
/// One step of `[Frame(n, f2, body)]` in (s, f).
fn frame_step(
  s : @kernel.Term,
  f : @kernel.Term,
  n : @kernel.Term,
  f2 : @kernel.Term,
  body : @kernel.Term,
) -> @kernel.Thm raise {
  let items = @basics.dest_list(body).to_array()
  if first_instr(items) is None {
    let vs = value_list(values_of(items[:])[:])
    return as_reduce(apply_rule("frame_values", [("n", n), ("f", f2), ("vs", vs)]), s, f)
  }
  if is_final(items) {
    return as_reduce(apply_rule("frame_trap", [("n", n), ("f", f2)]), s, f)
  }
  if find_return(items) is Some(d) {
    let (used, lf) = br_context(items, d, @nums.dest_small_numeral(n).to_int())
    let lholed = head_args(@kernel.concl(lf)).1[1]
    let th = apply_rule(
      "return",
      [
        ("vs", value_list(used[:])),
        ("n", n),
        ("j", small_num(d)),
        ("lholed", lholed),
        ("es", body),
        ("f", f2),
      ],
      given=[lf],
    )
    return as_reduce(th, s, f)
  }
  match step(s, f2, body) {
    Stepped(inner) => {
      let a = head_args(@kernel.concl(inner)).1
      apply_rule(
        "frame_context",
        [
          ("s", a[0]),
          ("f", a[1]),
          ("es", a[2]),
          ("s'", a[3]),
          ("f'", a[4]),
          ("es'", a[5]),
          ("f0", f),
          ("n", n),
        ],
        given=[inner],
      )
    }
    Escapes => raise Stuck("a br leaves the blocks of a function")
    Final => raise Failure("certimoon/wasm eval: frame body is final")
  }
}

///|
/// The step of `Invoke(i_cl)` with the values `vals` before it: (how many
/// values it takes, the step).
fn invoke_step(
  s : @kernel.Term,
  f : @kernel.Term,
  i_cl : @kernel.Term,
  vals : Array[@kernel.Term],
) -> (Int, @kernel.Thm) raise {
  let cl = @equal.rhs(
    @kernel.concl(eval_conv(@basics.list_mk_icomb("EL", @list.List([i_cl, call("s_funcs", [s])])))),
  )
  guard head_args(cl) is ("Func_native", [j, tf, ts, es]) else {
    raise Stuck("no rule for invoking " + show_term(cl))
  }
  guard head_args(tf) is ("Tf", [t1s, t2s]) else {
    raise Stuck("cannot compute the type of " + show_term(cl))
  }
  let n = @basics.dest_list(t1s).length()
  if vals.length() < n {
    raise Stuck("a call needs \{n} values and has \{vals.length()}")
  }
  let vcs = owned(vals[vals.length() - n:])
  guard head_args(@equal.rhs(@kernel.concl(eval_conv(call("n_zeros", [ts]))))) is ("SOME", [zs]) else {
    raise Stuck("cannot compute the locals of " + show_term(cl))
  }
  let ves = einstr_list(vcs.map(v => @equal.rhs(@kernel.concl(eval_conv(call("v_to_e", [v])))))[:])
  let th = apply_rule("invoke", [
    ("i_cl", i_cl),
    ("s", s),
    ("f", f),
    ("j", j),
    ("t1s", t1s),
    ("t2s", t2s),
    ("ts", ts),
    ("es", es),
    ("ves", ves),
    ("vcs", value_list(vcs[:])),
    ("n", small_num(n)),
    ("k", small_num(@basics.dest_list(ts).length())),
    ("m", small_num(@basics.dest_list(t2s).length())),
    ("zs", zs),
  ])
  (n, th)
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
                ("i", small_num(i)),
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
              Final => raise Failure("certimoon/wasm eval: label body is final")
            }
        }
      }
      Stepped(with_prefix(th, vals, rest))
    }
    ("Basic", [b]) => {
      guard basic_step(s, f, b, vals) is Some((k, th)) else { return Escapes }
      Stepped(with_prefix(as_reduce(th, s, f), owned(vals[:vals.length() - k]), rest))
    }
    ("Invoke", [i_cl]) => {
      let (k, th) = invoke_step(s, f, i_cl, vals)
      Stepped(with_prefix(as_reduce(th, s, f), owned(vals[:vals.length() - k]), rest))
    }
    ("Frame", [n, f2, body]) => Stepped(with_prefix(frame_step(s, f, n, f2, body), vals, rest))
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
      match head_args(value(call("app_binop", [op, c1, c2]))) {
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
        match head_args(value(call("cvt", [t2, sat_sx, c]))) {
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
      guard head_args(value(call("tb_tf", [call("f_inst", [f]), tb]))) is ("Tf", [t1s, t2s]) else {
        raise Stuck("cannot compute the type of " + show_term(b))
      }
      let n = @basics.dest_list(t1s).length()
      let m = @basics.dest_list(t2s).length()
      let key = if op_name == "Block" { "block" } else { "loop" }
      (
        n,
        apply_rule(key, [
          ("vs", value_list(take(n)[:])),
          ("n", small_num(n)),
          ("tb", tb),
          ("es", body),
          ("t1s", t1s),
          ("t2s", t2s),
          ("m", small_num(m)),
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
    // its frame is further out
    ("Return", []) => return None
    ("Call", [j]) => (0, apply_rule("call", [("s", s), ("f", f), ("j", j)]))
    ("Call_indirect", [ti, j]) => {
      let c = i32(take(1)[0])
      let i = value(call("f_inst", [f]))
      let common = [("s", s), ("f", f), ("i", i), ("ti", ti), ("c", c), ("j", j)]
      // the table's entry at c, and when it is a function, its type
      let val_c = @basics.mk_icomb(con("val"), c)
      let entry = value(call("stab", [s, i, ti, val_c]))
      let target = match head_args(entry) {
        ("SOME", [r]) =>
          match head_args(r) {
            ("ConstRefFunc", [a]) => Some(a)
            _ => None
          }
        _ => None
      }
      match target {
        Some(a) => {
          let tf = value(call("stypes", [i, j]))
          let el = @basics.mk_icomb(@basics.mk_icomb(con("EL"), a), call("s_funcs", [s]))
          let cl = value(call("cl_type", [el]))
          if @basics.aconv(tf, cl) {
            (1, apply_rule("call_indirect", common + [("i_cl", a), ("tf", tf)]))
          } else {
            (1, apply_rule("call_indirect_trap", common + [("i_cl", a)]))
          }
        }
        None => (1, apply_rule("call_indirect_trap", common + [("i_cl", small_num(0))]))
      }
    }
    ("Global_get", [j]) => (0, apply_rule("global_get", [("s", s), ("f", f), ("j", j)]))
    ("Global_set", [j]) => {
      let v = take(1)[0]
      let s2 = value(call("supdate_glob", [s, call("f_inst", [f]), j, v]))
      (1, apply_rule("global_set", [("s", s), ("f", f), ("j", j), ("v", v), ("s'", s2)]))
    }
    ("Load", [t, packed, a, off]) => {
      let k = i32(take(1)[0])
      let (j, m) = memory(s, f)
      let common = [("f", f), ("j", j), ("s", s), ("m", m), ("k", k), ("off", off), ("t", t), ("a", a)]
      let len = call("t_num_length", [t])
      let addr = @basics.mk_icomb(@basics.mk_mconst("val", @basics.mk_fun_ty(@kernel.type_of(k), hol_type("num"))), k)
      match head_args(packed) {
        ("NONE", []) =>
          match head_args(value(call("load", [m, addr, off, len]))) {
            ("SOME", [bs]) => (1, apply_rule("load_some", common + [("bs", bs)]))
            _ => (1, apply_rule("load_none", common))
          }
        ("SOME", [tp_sx]) => {
          let (tp, sx) = @pair.dest_pair(tp_sx)
          let lp = call("tp_num_length", [tp])
          let more = common + [("tp", tp), ("sx", sx)]
          match head_args(value(call("load_packed", [sx, m, addr, off, lp, len]))) {
            ("SOME", [bs]) => (1, apply_rule("load_packed_some", more + [("bs", bs)]))
            _ => (1, apply_rule("load_packed_none", more))
          }
        }
        _ => raise Stuck("cannot read " + show_term(b))
      }
    }
    ("Store", [t, packed, a, off]) => {
      let vs = take(2)
      let k = i32(vs[0])
      let v = num(vs[1])
      let (j, m) = memory(s, f)
      let common = [
        ("v", v),
        ("t", t),
        ("f", f),
        ("j", j),
        ("s", s),
        ("m", m),
        ("k", k),
        ("off", off),
        ("a", a),
      ]
      let addr = @basics.mk_icomb(@basics.mk_mconst("val", @basics.mk_fun_ty(@kernel.type_of(k), hol_type("num"))), k)
      let bits = call("bits_num", [v])
      let (op, len, extra, key) = match head_args(packed) {
        ("NONE", []) => ("store", call("t_num_length", [t]), [], "store")
        ("SOME", [tp]) => ("store_packed", call("tp_num_length", [tp]), [("tp", tp)], "store_packed")
        _ => raise Stuck("cannot read " + show_term(b))
      }
      match head_args(value(call(op, [m, addr, off, bits, len]))) {
        ("SOME", [mem2]) => (2, apply_rule(key + "_some", common + extra + [("mem'", mem2)]))
        _ => (2, apply_rule(key + "_none", common + extra))
      }
    }
    ("Memory_size", []) => {
      let (j, m) = memory(s, f)
      let n = value(call("mem_size", [m]))
      (0, apply_rule("memory_size", [("f", f), ("j", j), ("s", s), ("m", m), ("n", n)]))
    }
    ("Memory_grow", []) => {
      let c = i32(take(1)[0])
      let (j, m) = memory(s, f)
      let n = value(call("mem_size", [m]))
      let addr = @basics.mk_icomb(@basics.mk_mconst("val", @basics.mk_fun_ty(@kernel.type_of(c), hol_type("num"))), c)
      let common = [("f", f), ("j", j), ("s", s), ("m", m), ("n", n), ("c", c)]
      match head_args(value(call("mem_grow", [m, addr]))) {
        ("SOME", [mem2]) => (1, apply_rule("memory_grow", common + [("mem'", mem2)]))
        _ => (1, apply_rule("memory_grow_fail", common))
      }
    }
    ("Memory_copy" | "Memory_fill", []) => {
      let v = take(3)
      let (ma, m) = memory(s, f)
      let dest = i32(v[0])
      let n = i32(v[2])
      fn nat(w : @kernel.Term) -> @kernel.Term raise {
        value(@basics.mk_icomb(@basics.mk_mconst("val", @basics.mk_fun_ty(@kernel.type_of(w), hol_type("num"))), w))
      }
      let nn = nat(n)
      let common = [("f", f), ("ma", ma), ("s", s), ("m", m), ("dest", dest), ("ndest", nat(dest)), ("n", n), ("nn", nn)]
      let pred = if @nums.dest_small_numeral(nn) > 0L {
        [("nn_pred", small_num(@nums.dest_small_numeral(nn).to_int() - 1))]
      } else {
        []
      }
      if op_name == "Memory_copy" {
        let src = i32(v[1])
        let both = common + [("src", src), ("nsrc", nat(src))]
        (3, first_rule(["copy_trap", "copy_zero"], both) catch {
          Stuck(_) => first_rule(["copy_up", "copy_down"], both + pred)
          e => raise e
        })
      } else {
        let both = common + [("fv", i32(v[1]))]
        (3, first_rule(["fill_trap", "fill_zero"], both) catch {
          Stuck(_) => apply_rule("fill_step", both + pred)
          e => raise e
        })
      }
    }
    _ => raise Stuck("no rule for " + show_term(b))
  }
  Some(r)
}

///|
/// The current memory of (s, f): its index in the store and its value.
fn memory(s : @kernel.Term, f : @kernel.Term) -> (@kernel.Term, @kernel.Term) raise {
  let ind = @equal.rhs(@kernel.concl(eval_conv(call("smem_ind", [call("f_inst", [f])]))))
  guard head_args(ind) is ("SOME", [j]) else {
    raise Stuck("no memory: the instance's memories are " + show_term(ind))
  }
  let m = @equal.rhs(
    @kernel.concl(eval_conv(@basics.list_mk_icomb("EL", @list.List([j, call("s_mems", [s])])))),
  )
  (j, m)
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
      raise Failure("certimoon/wasm run: no final state after \{max_steps} steps")
    }
    let (s, rest) = @pair.dest_pair(cur)
    let (f, es) = @pair.dest_pair(rest)
    let r = step(s, f, es) catch {
      Stuck(msg) =>
        raise Failure(
          "certimoon/wasm run: stuck after \{steps.length()} steps: \{msg}",
        )
      e => raise e
    }
    match r {
      Final => break
      Escapes => raise Failure("certimoon/wasm run: a br leaves every block")
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
    let goal = call("computes", [cfg, s2, value_list(vs[:])])
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
      call("traps", [cfg, s2]),
      @tactics.then_tac(
        @simp.pure_rewrite_tac(@list.List([thm("traps")])),
        @tactics.then_tac(@tactics.exists_tac(f2), @tactics.accept_tac(th)),
      ),
    )
  }
}
