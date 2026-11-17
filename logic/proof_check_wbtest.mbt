///|
test "individual checks are lazy, reusable, conditional, and isolated" {
  let ran : Array[String] = []
  let before = names().length()
  let axioms = @kernel.axioms().length()
  let plan = collect_proofs("proof_check_fixture", fn() raise {
    let previous = declare_proof("check_previous", tm("T"), fn() raise {
      ran.push("previous")
      prove(tm("T"), @tactics.accept_tac(@bool.truth()))
    })
    ignore(
      declare_proof("check_target", tm("T"), fn() raise {
        ran.push("target")
        let th = prove(tm("T"), @tactics.accept_tac(previous))
        record("check_target", th)
        th
      }),
    )
    ignore(
      declare_proof("check_unused", tm("F"), () => abort("unselected proof ran")),
    )
  })
  assert_eq(ran.length(), 0)
  assert_eq(plan.names(), ["check_previous", "check_target", "check_unused"])
  for _ in 0..<2 {
    let result = plan.check("check_target")
    assert_eq(result.name(), "check_target")
    assert_eq(result.premises(), ["check_previous"])
    assert_true(@basics.aconv(result.statement(), tm("T")))
    assert_true(@kernel.hyp(result.theorem()).is_empty())
    assert_true(@basics.aconv(@kernel.concl(result.theorem()), tm("T → T")))
  }
  assert_eq(ran, ["target", "target"])
  assert_eq(names().length(), before)
  assert_eq(@kernel.axioms().length(), axioms)
  assert_true(!checking_proof())
  @testkit.check_axioms()
}

///|
test "individual checks reject self, future, and unrelated assumptions" {
  let future : Ref[@kernel.Thm?] = Ref::{ val: None, }
  let plan = collect_proofs("proof_check_bad", fn() raise {
    ignore(
      declare_proof("bad_self", tm("F"), fn() raise {
        @kernel.assume_rule(tm("F"))
      }),
    )
    ignore(declare_proof("bad_forward", tm("F"), () => future.val.unwrap()))
    future.val = Some(
      declare_proof("bad_later", tm("F"), () => abort("unused")),
    )
    ignore(
      declare_proof("bad_unrelated", tm("T"), fn() raise {
        @bool.add_assum(tm("(unapproved : Bool)"), @bool.truth())
      }),
    )
    ignore(declare_proof("bad_conclusion", tm("F"), () => @bool.truth()))
  })
  // bad_forward has an earlier F schema (bad_self), so use a separate catalog
  // below for the captured-future check. Here, ensure lookup itself forbids it.
  let ctx = proof_scope(plan, Some(1), None)
  for name in ["bad_forward", "bad_later"] {
    let message = try {
      ignore(ctx.lookup(name))
      ""
    } catch {
      e => e.to_string()
    }
    assert_true(message.contains("self/forward reference"))
  }
  for name in ["bad_self", "bad_unrelated", "bad_conclusion", "unknown"] {
    let message = try {
      ignore(plan.check(name))
      ""
    } catch {
      e => e.to_string()
    }
    assert_true(message != "", msg=name)
    assert_true(!checking_proof())
  }
  let captured = collect_proofs("proof_check_future", fn() raise {
    ignore(declare_proof("captured_target", tm("F"), () => future.val.unwrap()))
    future.val = Some(
      declare_proof("captured_later", tm("F"), () => abort("unused")),
    )
  })
  let message = try {
    ignore(captured.check("captured_target"))
    ""
  } catch {
    e => e.to_string()
  }
  assert_true(message.contains("unapproved premise"))
  @testkit.check_axioms()
}

///|
test "individual checks accept instantiated previous schemas" {
  let plan = collect_proofs("proof_check_inst", fn() raise {
    let previous = declare_proof("inst_previous", tm("(x : A) == x"), () => {
      abort("unused")
    })
    ignore(
      declare_proof("inst_target", tm("(y : Bool) == y"), fn() raise {
        let inst = @drule.term_match(
          @list.List([]),
          @kernel.concl(previous),
          tm("(y : Bool) == y"),
        )
        @drule.instantiate_all(inst, previous)
      }),
    )
  })
  let result = plan.check("inst_target")
  assert_eq(result.premises(), ["inst_previous"])
  assert_true(@kernel.hyp(result.theorem()).is_empty())
}

///|
test "failed collection restores context and duplicate declarations fail" {
  let message = try {
    ignore(
      collect_proofs("proof_check_duplicate", fn() raise {
        ignore(declare_proof("duplicate", tm("T"), () => @bool.truth()))
        ignore(declare_proof("duplicate", tm("T"), () => @bool.truth()))
      }),
    )
    ""
  } catch {
    e => e.to_string()
  }
  assert_true(message.contains("duplicate proof declaration"))
  assert_true(!checking_proof())
  let plan = collect_proofs("proof_check_after_failure", fn() raise {
    ignore(declare_proof("after_failure", tm("T"), () => @bool.truth()))
  })
  assert_eq(plan.check("after_failure").premises(), [])
}

///|
test "full declaration replay executes proofs and refuses hypotheses" {
  let ran = Ref::{ val: 0, }
  let previous = declare_proof("full_fixture_previous", tm("T"), fn() raise {
    ran.val = ran.val + 1
    prove(tm("T"), @tactics.accept_tac(@bool.truth()))
  })
  let target = declare_proof("full_fixture_target", tm("T"), fn() raise {
    ran.val = ran.val + 1
    prove(tm("T"), @tactics.accept_tac(previous))
  })
  assert_eq(ran.val, 2)
  assert_true(@kernel.hyp(target).is_empty())
  let message = try {
    ignore(
      declare_proof("full_fixture_bad", tm("F"), fn() raise {
        prove(tm("F"), @tactics.accept_tac(@kernel.assume_rule(tm("F"))))
      }),
    )
    ""
  } catch {
    e => e.to_string()
  }
  assert_true(message.contains("additional assumptions"))
  @testkit.check_axioms()
}

///|
test "single checks stop collecting at the selected statement" {
  let visited : Array[String] = []
  let plan = collect_proofs(
    "proof_check_prefix",
    fn() raise {
      visited.push("first")
      ignore(declare_proof("prefix_first", tm("T"), () => @bool.truth()))
      visited.push("selected")
      ignore(declare_proof("prefix_selected", tm("T"), () => @bool.truth()))
      visited.push("later")
      abort("collection continued past selected statement")
    },
    until=Some("prefix_selected"),
  )
  assert_eq(visited, ["first", "selected"])
  assert_eq(plan.names(), ["prefix_first", "prefix_selected"])
  assert_eq(plan.check("prefix_selected").premises(), [])
  assert_true(!checking_proof())
}

///|
test "conditional polymorphic premises work in rewrite and matching tactics" {
  let stmt = "∀ y : Bool, (P : (Bool) -> Bool)(y)"
  let implication = "∀ y : Bool, (P : (Bool) -> Bool)(y) → (Q : (Bool) -> Bool)(y)"
  let plan = collect_proofs("proof_check_polymorphic", fn() raise {
    let rule = declare_proof(
      "poly_rule",
      tm("∀ x : A, (P : (A) -> Bool)(x)"),
      () => abort("unused"),
    )
    ignore(
      declare_proof("poly_rewrite", tm(stmt), fn() raise {
        prove(tm(stmt), seq([@tactics.gen_tac, @simp.rewrite_tac(ths([rule]))]))
      }),
    )
    let mp = declare_proof(
      "poly_mp",
      tm("∀ x : A, (P : (A) -> Bool)(x) → (Q : (A) -> Bool)(x)"),
      () => abort("unused"),
    )
    ignore(
      declare_proof("poly_match", tm(implication), fn() raise {
        prove(
          tm(implication),
          seq([
            @tactics.gen_tac,
            @tactics.disch_tac,
            match_mp_tac(mp),
            @simp.asm_rewrite_tac(ths([])),
          ]),
        )
      }),
    )
  })
  assert_eq(plan.check("poly_rewrite").premises(), ["poly_rule"])
  assert_eq(plan.check("poly_match").premises(), ["poly_mp"])
}

///|
test "lazy proofs preserve inferred type variables by retaining their goal term" {
  let text = "∀ x : Num, word(x) == word(x)"
  let goal = tm(text)
  let plan = collect_proofs("proof_check_inferred_types", fn() raise {
    ignore(
      declare_proof("inferred_goal", goal, fn() raise {
        // Parsing the same text afresh allocates a different inferred word width.
        ignore(tm(text))
        prove(goal, seq([@tactics.gen_tac, @tactics.refl_tac]))
      }),
    )
  })
  let result = plan.check("inferred_goal")
  assert_true(
    @basics.aconv(result.statement(), @kernel.concl(result.theorem())),
  )
  assert_eq(result.premises(), [])
}
