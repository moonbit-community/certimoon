// Exact contiguous publication prefixes in the shipped malloc_no_grow.
// The following return instructions belong to the surrounding dispatch.

///|
fn define_tlsf_page_publish_code() -> Unit raise {
  {
    let wat =
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|local.set 4
      #|local.get 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 4
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 3
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 16
      #|i32.add
      #|local.get 0
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 1
    ignore(
      program("tlsf_page_publish_fresh_code", show(@wasm.code_of_wat(wat)), params=[
        "(d : \{w32})",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.tee 3
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 4
      #|local.get 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 4
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 3
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 16
      #|i32.add
      #|local.get 0
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 0
      #|local.get 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|if
      #|local.get 0
      #|i32.const 24
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|end
      #|local.get 1
      #|i32.const 8
      #|i32.add
    ignore(
      program("tlsf_page_publish_partial_code", show(@wasm.code_of_wat(wat)), params=[
        "(d : \{w32})",
      ]),
    )
  }
  let wat =
    #|local.get 0
    #|i32.const 20
    #|i32.add
    #|local.tee 3
    #|i32.load offset=0 align=2**2
    #|local.tee 1
  ignore(
    program("tlsf_page_publish_head_code", show(@wasm.code_of_wat(wat)), params=[
      "(d : \{w32})",
    ]),
  )
}
