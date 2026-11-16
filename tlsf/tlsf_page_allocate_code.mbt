// Exact Page::allocate: one size argument, one result, five i32 locals.

///|
fn define_tlsf_page_allocate_code() -> Unit raise {
  {
    let wat =
      #|i32.const 1080
      #|call take_idx
      #|local.tee 1
      #|i32.eqz
      #|if
      #|i32.const 0
      #|return
      #|end
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.const 1056
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.div_u
      #|local.tee 5
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 28
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 32
      #|i32.add
      #|local.tee 2
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 4
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 4
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|i32.const 1
      #|local.set 3
      #|loop
      #|block
      #|block (result i32)
      #|local.get 3
      #|local.get 5
      #|i32.lt_u
      #|if
      #|local.get 1
      #|i32.const 32
      #|i32.add
      #|local.get 3
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.mul
      #|i32.add
      #|local.tee 4
      #|i32.const 4
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 4
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 8
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.get 4
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|local.set 2
      #|local.get 3
      #|i32.const 1
      #|i32.add
      #|br 1
      #|end
      #|br 1
      #|end
      #|local.set 3
      #|br 1
      #|end
      #|end
      #|local.get 1
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_code", show(code), params=["(take_idx : Num)"]),
    )
  }
  {
    let wat =
      #|i32.const 1080
      #|call take_idx
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_call", show(code), params=["(take_idx : Num)"]),
    )
  }
  {
    let wat =
      #|local.tee 1
      #|i32.eqz
      #|if
      #|i32.const 0
      #|return
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_guard", show(code), params=[
        "(take_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.const 1056
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.div_u
      #|local.tee 5
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 28
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 32
      #|i32.add
      #|local.tee 2
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 4
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 4
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|i32.const 1
      #|local.set 3
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_begin", show(code), params=[
        "(take_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|loop
      #|block
      #|block (result i32)
      #|local.get 3
      #|local.get 5
      #|i32.lt_u
      #|if
      #|local.get 1
      #|i32.const 32
      #|i32.add
      #|local.get 3
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.mul
      #|i32.add
      #|local.tee 4
      #|i32.const 4
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 4
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 8
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.get 4
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|local.set 2
      #|local.get 3
      #|i32.const 1
      #|i32.add
      #|br 1
      #|end
      #|br 1
      #|end
      #|local.set 3
      #|br 1
      #|end
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_loop", show(code), params=["(take_idx : Num)"]),
    )
  }
  {
    let wat =
      #|local.get 3
      #|local.get 5
      #|i32.lt_u
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_test", show(code), params=["(take_idx : Num)"]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 32
      #|i32.add
      #|local.get 3
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.mul
      #|i32.add
      #|local.tee 4
      #|i32.const 4
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 4
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 8
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.get 4
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|local.set 2
      #|local.get 3
      #|i32.const 1
      #|i32.add
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_page_allocate_step", show(code), params=["(take_idx : Num)"]),
    )
  }
  let wat =
    #|local.set 3
    #|br 1
  let code = @wasm.code_of_wat(wat)
  ignore(
    program("tlsf_page_allocate_next", show(code), params=["(take_idx : Num)"]),
  )
}

///|
fn define_tlsf_page_allocate_fill() -> Unit raise {
  let code = @equal.rhs(
    @kernel.concl(
      @simp.rewrite_conv(
        ths([
          thm("tlsf_page_allocate_begin"),
          thm("tlsf_page_allocate_loop"),
          @lists.append(),
        ]),
      )(
        tm(
          "APPEND(tlsf_page_allocate_begin((take_idx : Num)),APPEND(tlsf_page_allocate_loop(take_idx),[Local_get(1)]))",
        ),
      ),
    ),
  )
  ignore(
    program("tlsf_page_allocate_fill", show(code), params=["(take_idx : Num)"]),
  )
}
