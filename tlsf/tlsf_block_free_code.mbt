// Block::free and Page::free are inlined in the compiler’s public free.
// These are contiguous, unmodified fragments, retaining its three locals.

///|
fn define_tlsf_block_free_code() -> Unit raise {
  {
    let wat =
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.get 1
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|i32.const 20
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 16
      #|i32.add
      #|local.tee 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.const 1
      #|i32.sub
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|local.get 0
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.eq
      #|if (result i32)
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 2
      #|local.set 1
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 2
      #|i32.const 3
      #|i32.shl
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
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.const 1
      #|i32.eq
      #|if (result i32)
      #|local.get 0
      #|i32.const 24
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|if (result i32)
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 28
      #|i32.add
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const 0
      #|else
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.set 2
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const 0
      #|end
      #|drop
      #|local.get 0
      #|call free_idx
      #|else
      #|i32.const 0
      #|end
      #|end
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_code", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.get 1
      #|i32.const 4
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|i32.const 20
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 16
      #|i32.add
      #|local.tee 1
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.const 1
      #|i32.sub
      #|i32.store offset=0 align=2**2
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_release", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|local.get 0
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.eq
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_classify", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 2
      #|local.set 1
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|local.get 0
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 2
      #|i32.const 3
      #|i32.shl
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
      #|i32.const 0
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_publish", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 1
      #|i32.eq
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_last_test", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 24
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|if (result i32)
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 28
      #|i32.add
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const 0
      #|else
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.set 2
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const 0
      #|end
      #|drop
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_unlink", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 28
      #|i32.add
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const 0
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_unlink_prev", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.set 2
      #|local.get 0
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|local.get 1
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|if
      #|local.get 1
      #|i32.const 24
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|end
      #|i32.const 0
    let code = @wasm.code_of_wat(wat)
    ignore(
      program("tlsf_block_free_unlink_head", show(code), params=[
        "(d : \{w32})",
        "(free_idx : Num)",
      ]),
    )
  }
  let wat =
    #|local.get 0
    #|i32.const 24
    #|i32.add
    #|local.tee 1
    #|i32.load offset=0 align=2**2
    #|if (result i32)
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|local.tee 2
    #|i32.const 28
    #|i32.add
    #|local.get 0
    #|i32.const 28
    #|i32.add
    #|i32.load offset=0 align=2**2
    #|local.tee 1
    #|i32.store offset=0 align=2**2
    #|local.get 1
    #|if
    #|local.get 1
    #|i32.const 24
    #|i32.add
    #|local.get 2
    #|i32.store offset=0 align=2**2
    #|end
    #|i32.const 0
    #|else
    #|local.get 0
    #|i32.const 8
    #|i32.add
    #|i32.load offset=0 align=2**2
    #|i32.const 7
    #|i32.add
    #|i32.const 3
    #|i32.shr_u
    #|local.set 2
    #|local.get 0
    #|i32.const 28
    #|i32.add
    #|i32.load offset=0 align=2**2
    #|local.set 1
    #|i32.const d
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|local.get 2
    #|i32.const 3
    #|i32.shl
    #|i32.add
    #|i32.const 1916
    #|i32.add
    #|local.get 1
    #|i32.store offset=0 align=2**2
    #|local.get 1
    #|if
    #|local.get 1
    #|i32.const 24
    #|i32.add
    #|i32.const 0
    #|i32.store offset=0 align=2**2
    #|end
    #|i32.const 0
    #|end
    #|drop
    #|local.get 0
    #|call free_idx
  let code = @wasm.code_of_wat(wat)
  ignore(
    program("tlsf_block_free_reclaim", show(code), params=[
      "(d : \{w32})",
      "(free_idx : Num)",
    ]),
  )
}
