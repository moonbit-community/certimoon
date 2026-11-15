// Complete shipped Memory::free. The argument is the Memory header,
// eight bytes before the client payload. pop/push are module indices.

///|
fn define_tlsf_free_code() -> Unit raise {
  {
    let wat =
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967294
      #|i32.and
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|if (result i32)
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
      #|else
      #|i32.const 1
      #|end
      #|i32.eqz
      #|if
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|call pop
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|end
      #|local.get 1
      #|local.set 0
      #|end
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if (result i32)
      #|i32.const 1
      #|else
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
      #|end
      #|i32.eqz
      #|if
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|call pop
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|end
      #|end
      #|local.get 0
      #|call push
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_code", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967294
      #|i32.and
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_clear", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|if (result i32)
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
      #|else
      #|i32.const 1
      #|end
      #|i32.eqz
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_prev_test", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|call pop
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_prev_pop", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|end
      #|local.get 1
      #|local.set 0
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_prev_write", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if (result i32)
      #|i32.const 1
      #|else
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
      #|end
      #|i32.eqz
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_next_test", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|call pop
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_next_pop", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_next_write", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|call pop
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|end
      #|local.get 1
      #|local.set 0
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_prev_body", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|call pop
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_next_body", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|if (result i32)
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.load offset=0 align=2**2
      #|i32.const 1
      #|i32.and
      #|else
      #|i32.const 1
      #|end
      #|i32.eqz
      #|if
      #|local.get 0
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|call pop
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 3
      #|i32.and
      #|local.get 2
      #|i32.const 4294967292
      #|i32.and
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 8
      #|i32.add
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 2
      #|i32.and
      #|if
      #|local.get 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967293
      #|i32.and
      #|i32.const 2
      #|i32.or
      #|i32.store offset=0 align=2**2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|else
      #|local.get 0
      #|local.get 0
      #|i32.load offset=0 align=2**2
      #|i32.const 4294967292
      #|i32.and
      #|i32.add
      #|i32.const 12
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|end
      #|local.get 1
      #|local.set 0
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_free_prev", show(code), params=[
        "(d : \{w32})",
        "(pop : Num)",
        "(push : Num)",
      ]),
    )
  }
  let wat =
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 2
    #|i32.and
    #|if (result i32)
    #|i32.const 1
    #|else
    #|local.get 0
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967292
    #|i32.and
    #|i32.add
    #|i32.const 8
    #|i32.add
    #|i32.load offset=0 align=2**2
    #|i32.const 1
    #|i32.and
    #|end
    #|i32.eqz
    #|if
    #|local.get 0
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967292
    #|i32.and
    #|i32.add
    #|i32.const 8
    #|i32.add
    #|local.tee 1
    #|call pop
    #|local.get 0
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|local.tee 2
    #|i32.const 3
    #|i32.and
    #|local.get 2
    #|i32.const 4294967292
    #|i32.and
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967292
    #|i32.and
    #|i32.add
    #|i32.const 8
    #|i32.add
    #|i32.or
    #|i32.store offset=0 align=2**2
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|i32.const 2
    #|i32.and
    #|if
    #|local.get 0
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967293
    #|i32.and
    #|i32.const 2
    #|i32.or
    #|i32.store offset=0 align=2**2
    #|i32.const d
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|i32.const 1908
    #|i32.add
    #|local.get 0
    #|i32.store offset=0 align=2**2
    #|else
    #|local.get 1
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967292
    #|i32.and
    #|i32.add
    #|i32.const 12
    #|i32.add
    #|local.get 0
    #|i32.store offset=0 align=2**2
    #|end
    #|end
  let code = @wasm.code_of_wat(wat)
  ignore(
    program("tlsf_free_next", show(code), params=[
      "(d : \{w32})",
      "(pop : Num)",
      "(push : Num)",
    ]),
  )
}
