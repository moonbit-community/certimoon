// The complete shipped Memory::ensure and its compositional boundaries.
// DATA_SECTION_END is linked as d; pop and push are actual module indices.

///|
fn define_tlsf_ensure_code() -> Unit raise {
  {
    let wat =
      #|i32.const 1
      #|i32.const 27
      #|local.get 0
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.tee 0
      #|i32.clz
      #|i32.sub
      #|i32.shl
      #|i32.const 1
      #|i32.sub
      #|local.tee 1
      #|local.get 0
      #|i32.add
      #|local.get 1
      #|i32.const 4294967295
      #|i32.xor
      #|i32.and
      #|local.set 1
      #|i32.const d
      #|local.tee 0
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 0
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|end
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
      #|if
      #|local.get 1
      #|i32.const 65543
      #|i32.add
      #|i32.const 16
      #|i32.shr_u
      #|memory.grow
      #|i32.const 4294967295
      #|i32.eq
      #|if
      #|i32.const 0
      #|return
      #|end
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|local.set 1
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 4
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|memory.size
      #|i32.const 16
      #|i32.shl
      #|local.get 1
      #|i32.sub
      #|i32.const 8
      #|i32.sub
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 3
      #|i32.and
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|call push
      #|drop
      #|else
      #|local.get 1
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.sub
      #|i32.const 65535
      #|i32.add
      #|i32.const 16
      #|i32.shr_u
      #|memory.grow
      #|i32.const 4294967295
      #|i32.eq
      #|if
      #|i32.const 0
      #|return
      #|end
      #|local.get 0
      #|call pop
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
      #|end
      #|i32.const 1
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_code", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.const 1
      #|i32.const 27
      #|local.get 0
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.tee 0
      #|i32.clz
      #|i32.sub
      #|i32.shl
      #|i32.const 1
      #|i32.sub
      #|local.tee 1
      #|local.get 0
      #|i32.add
      #|local.get 1
      #|i32.const 4294967295
      #|i32.xor
      #|i32.and
      #|local.set 1
      #|i32.const d
      #|local.tee 0
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 0
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|end
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_prefix", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 65543
      #|i32.add
      #|i32.const 16
      #|i32.shr_u
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_used_amount", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.sub
      #|i32.const 65535
      #|i32.add
      #|i32.const 16
      #|i32.shr_u
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_free_amount", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.const 4294967295
      #|i32.eq
      #|if
      #|i32.const 0
      #|return
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_guard", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|local.set 1
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 4
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|memory.size
      #|i32.const 16
      #|i32.shl
      #|local.get 1
      #|i32.sub
      #|i32.const 8
      #|i32.sub
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 3
      #|i32.and
      #|i32.or
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_used_write", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
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
      program("tlsf_ensure_free_write", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.const 1
      #|i32.const 27
      #|local.get 0
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.tee 0
      #|i32.clz
      #|i32.sub
      #|i32.shl
      #|i32.const 1
      #|i32.sub
      #|local.tee 1
      #|local.get 0
      #|i32.add
      #|local.get 1
      #|i32.const 4294967295
      #|i32.xor
      #|i32.and
      #|local.set 1
      #|i32.const d
      #|local.tee 0
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 0
      #|i32.const 16
      #|i32.shr_u
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_prefix_before_size", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|end
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_prefix_after_size", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|local.set 1
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 4
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_used_before_size", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|i32.const 16
      #|i32.shl
      #|local.get 1
      #|i32.sub
      #|i32.const 8
      #|i32.sub
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 3
      #|i32.and
      #|i32.or
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_used_after_size", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_ensure_free_before_size", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
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
  let code = @wasm.code_of_wat(wat)
  ignore(
    program("tlsf_ensure_free_after_size", show(code), params=[
      "(d : \{w32})",
      "(pop : Num)",
      "(push : Num)",
    ]),
  )
}
