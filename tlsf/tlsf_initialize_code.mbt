// The complete shipped initializer, including growth failure aborts.
// DATA_SECTION_END is linked as d; push is a native module index.

///|
fn define_tlsf_initialize_code() -> Unit raise {
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.tee 0
      #|i32.const 16
      #|i32.shr_u
      #|local.get 0
      #|i32.const 65535
      #|i32.and
      #|i32.const 67743
      #|i32.add
      #|i32.const 16
      #|i32.shr_u
      #|i32.add
      #|local.set 1
      #|memory.size
      #|local.tee 2
      #|i32.const 65536
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|local.get 2
      #|i32.gt_u
      #|if
      #|local.get 1
      #|local.get 2
      #|i32.sub
      #|memory.grow
      #|i32.const 4294967295
      #|i32.eq
      #|if
      #|unreachable
      #|end
      #|end
      #|local.get 0
      #|i32.const 2176
      #|i32.add
      #|local.tee 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|memory.size
      #|i32.const 16
      #|i32.shl
      #|local.get 0
      #|i32.sub
      #|i32.const 8
      #|i32.sub
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 3
      #|i32.and
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|call push
      #|drop
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_code", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.tee 0
      #|i32.const 16
      #|i32.shr_u
      #|local.get 0
      #|i32.const 65535
      #|i32.and
      #|i32.const 67743
      #|i32.add
      #|i32.const 16
      #|i32.shr_u
      #|i32.add
      #|local.set 1
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_arithmetic", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|memory.size
      #|local.tee 2
      #|i32.const 65536
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_check", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|local.get 2
      #|i32.gt_u
      #|if
      #|local.get 1
      #|local.get 2
      #|i32.sub
      #|memory.grow
      #|i32.const 4294967295
      #|i32.eq
      #|if
      #|unreachable
      #|end
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_grow", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 2176
      #|i32.add
      #|local.tee 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_mark", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|memory.size
      #|i32.const 16
      #|i32.shl
      #|local.get 0
      #|i32.sub
      #|i32.const 8
      #|i32.sub
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 3
      #|i32.and
      #|i32.or
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_size", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|call push
      #|drop
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_publish", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_top", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 2176
      #|i32.add
      #|local.tee 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|memory.size
      #|i32.const 16
      #|i32.shl
      #|local.get 0
      #|i32.sub
      #|i32.const 8
      #|i32.sub
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 3
      #|i32.and
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|call push
      #|drop
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_initialize_tail", show(code), params=[
        "(d : \{w32})",
        "(push : Num)",
      ]),
    )
  }
  ignore(
    program("tlsf_initialize_size_before", "[Local_get(0)]", params=[
      "(d : \{w32})",
      "(push : Num)",
    ]),
  )
  let wat =
    #|i32.const 16
    #|i32.shl
    #|local.get 0
    #|i32.sub
    #|i32.const 8
    #|i32.sub
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 3
    #|i32.and
    #|i32.or
    #|i32.store offset=0 align=2**2
  ignore(
    program("tlsf_initialize_size_after", show(@wasm.code_of_wat(wat)), params=[
      "(d : \{w32})",
      "(push : Num)",
    ]),
  )
}

///|
fn define_tlsf_initialize_control_code() -> Unit raise {
  let params = ["(d : \{w32})", "(push : Num)"]
  for
    (name, wat) in [
      ("tlsf_initialize_check_test", "local.tee 2\ni32.const 65536\ni32.gt_u"),
      ("tlsf_initialize_grow_test", "local.get 1\nlocal.get 2\ni32.gt_u"),
      ("tlsf_initialize_grow_amount", "local.get 1\nlocal.get 2\ni32.sub"),
      ("tlsf_initialize_guard_test", "i32.const 4294967295\ni32.eq"),
      (
        "tlsf_initialize_grow_yes", "local.get 1\nlocal.get 2\ni32.sub\nmemory.grow\ni32.const 4294967295\ni32.eq\nif\nunreachable\nend",
      ),
    ] {
    ignore(program(name, show(@wasm.code_of_wat(wat)), params~))
  }
}

///|
fn prove_tlsf_initialize_control_parts() -> Unit raise {
  let w = w32
  let rw = (xs : Array[@kernel.Thm]) => @simp.rewrite_tac(ths(xs))
  let abort_guard = "[If(Tbv(NONE),[Unreachable],NIL)]"
  let vars = "∀ d : \{w}, ∀ push : Num"
  let _ = lemma(
    "tlsf_initialize_check_parts",
    "\{vars}, tlsf_initialize_check(d,push) == APPEND([Memory_size],APPEND(tlsf_initialize_check_test(d,push),\{abort_guard}))",
    rw([
      thm("tlsf_initialize_check"),
      thm("tlsf_initialize_check_test"),
      @lists.append(),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_grow_yes_parts",
    "\{vars}, tlsf_initialize_grow_yes(d,push) == APPEND(tlsf_initialize_grow_amount(d,push),APPEND([Memory_grow],APPEND(tlsf_initialize_guard_test(d,push),\{abort_guard})))",
    rw([
      thm("tlsf_initialize_grow_yes"),
      thm("tlsf_initialize_grow_amount"),
      thm("tlsf_initialize_guard_test"),
      @lists.append(),
    ]),
  )
  let _ = lemma(
    "tlsf_initialize_grow_parts",
    "\{vars}, tlsf_initialize_grow(d,push) == APPEND(tlsf_initialize_grow_test(d,push),[If(Tbv(NONE),tlsf_initialize_grow_yes(d,push),NIL)])",
    rw([
      thm("tlsf_initialize_grow"),
      thm("tlsf_initialize_grow_test"),
      thm("tlsf_initialize_grow_yes"),
      @lists.append(),
    ]),
  )
}
