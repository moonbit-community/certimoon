// Contiguous pieces of the exact entry points, for compositional proofs.

///|
fn define_tlsf_malloc_parts() -> Unit raise {
  let ps = [
    "(d : \{w32})",
    "(initialize_idx : Num)",
    "(page_idx : Num)",
    "(take_idx : Num)",
    "(ensure_idx : Num)",
  ]
  {
    let wat =
      #|local.get 0
      #|i32.eqz
      #|if
      #|i32.const 0
      #|return
      #|end
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
      #|local.get 0
      #|i32.const 256
      #|i32.le_u
      #|if (result i32)
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|return
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
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
      #|return
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.tee 3
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
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
      #|return
      #|end
      #|end
      #|i32.const 4294967295
      #|else
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 0
      #|if (result i32)
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
      #|end
    ignore(
      program("tlsf_malloc_try_body", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|return
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
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
      #|return
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.tee 3
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
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
      #|return
      #|end
      #|end
      #|i32.const 4294967295
    ignore(
      program("tlsf_malloc_try_small", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 0
      #|if (result i32)
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
    ignore(
      program("tlsf_malloc_try_large", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
    ignore(
      program(
        "tlsf_malloc_try_fast_lookup",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
    ignore(
      program("tlsf_malloc_try_cached", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
    ignore(
      program(
        "tlsf_malloc_try_partial_lookup",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
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
      program(
        "tlsf_malloc_try_partial",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
    ignore(
      program(
        "tlsf_malloc_try_page_call",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
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
    ignore(
      program("tlsf_malloc_try_head", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
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
      program("tlsf_malloc_try_fresh", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
    ignore(
      program(
        "tlsf_malloc_try_ready_guard",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|i32.const 0
      #|local.get 0
      #|i32.eqz
      #|br_if 0
      #|drop
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
      #|local.get 0
      #|i32.const 256
      #|i32.le_u
      #|if (result i32)
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|local.set 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 3
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|br 2
      #|end
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
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
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|br 2
      #|end
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|call page_idx
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|if
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|local.tee 2
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|br 3
      #|end
      #|end
      #|i32.const 4294967295
      #|else
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 1
      #|if (result i32)
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
      #|end
    ignore(
      program("tlsf_malloc_first_body", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|local.set 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 3
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|br 2
      #|end
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
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
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|br 2
      #|end
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|call page_idx
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|if
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|local.tee 2
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|br 3
      #|end
      #|end
      #|i32.const 4294967295
    ignore(
      program(
        "tlsf_malloc_first_small",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 1
      #|if (result i32)
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
    ignore(
      program(
        "tlsf_malloc_first_large",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
    ignore(
      program(
        "tlsf_malloc_first_fast_lookup",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|local.set 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 3
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
    ignore(
      program(
        "tlsf_malloc_first_cached",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
    ignore(
      program(
        "tlsf_malloc_first_partial_lookup",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
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
      #|local.get 2
      #|i32.const 8
      #|i32.add
    ignore(
      program(
        "tlsf_malloc_first_partial",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|call page_idx
      #|local.tee 1
    ignore(
      program(
        "tlsf_malloc_first_page_call",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
    ignore(
      program("tlsf_malloc_first_head", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|local.tee 2
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 2
    ignore(
      program(
        "tlsf_malloc_first_fresh",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
    ignore(
      program(
        "tlsf_malloc_first_ready_guard",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|i32.const 0
      #|local.get 0
      #|i32.eqz
      #|br_if 0
      #|drop
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
      #|local.get 0
      #|i32.const 256
      #|i32.le_u
      #|if (result i32)
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|br 2
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
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
      #|br 2
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.tee 3
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
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
      #|br 3
      #|end
      #|end
      #|i32.const 4294967295
      #|else
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 0
      #|if (result i32)
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
      #|end
    ignore(
      program("tlsf_malloc_retry_body", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|br 2
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
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
      #|br 2
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.tee 3
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
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
      #|br 3
      #|end
      #|end
      #|i32.const 4294967295
    ignore(
      program(
        "tlsf_malloc_retry_small",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 0
      #|if (result i32)
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
    ignore(
      program(
        "tlsf_malloc_retry_large",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
    ignore(
      program(
        "tlsf_malloc_retry_fast_lookup",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
    ignore(
      program(
        "tlsf_malloc_retry_cached",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
    ignore(
      program(
        "tlsf_malloc_retry_partial_lookup",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
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
      program(
        "tlsf_malloc_retry_partial",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
    ignore(
      program(
        "tlsf_malloc_retry_page_call",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
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
    ignore(
      program("tlsf_malloc_retry_head", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
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
      program(
        "tlsf_malloc_retry_fresh",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
    ignore(
      program(
        "tlsf_malloc_retry_ready_guard",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|block (result i32)
      #|i32.const 0
      #|local.get 0
      #|i32.eqz
      #|br_if 0
      #|drop
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
      #|local.get 0
      #|i32.const 256
      #|i32.le_u
      #|if (result i32)
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|local.tee 1
      #|i32.load offset=0 align=2**2
      #|local.set 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 3
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|br 2
      #|end
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|i32.const 8
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 28
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.set 1
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
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
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|br 2
      #|end
      #|local.get 2
      #|i32.const 3
      #|i32.shl
      #|local.tee 3
      #|call page_idx
      #|local.tee 1
      #|if
      #|local.get 1
      #|i32.const 20
      #|i32.add
      #|local.tee 4
      #|i32.load offset=0 align=2**2
      #|local.tee 2
      #|if
      #|local.get 2
      #|i32.const 8
      #|i32.add
      #|local.tee 2
      #|i32.load offset=0 align=2**2
      #|local.set 5
      #|local.get 3
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|i32.add
      #|local.get 5
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 4
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 1
      #|i32.const 16
      #|i32.add
      #|local.get 1
      #|i32.const 12
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|i32.store offset=0 align=2**2
      #|local.get 2
      #|br 3
      #|end
      #|end
      #|i32.const 4294967295
      #|else
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 1
      #|if (result i32)
      #|local.get 1
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
      #|end
      #|end
    ignore(
      program(
        "tlsf_malloc_full_prefix",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|local.tee 1
      #|i32.const 4294967295
      #|i32.ne
      #|if
      #|local.get 1
      #|return
      #|end
      #|local.get 0
      #|i32.const 256
      #|i32.le_u
      #|if
      #|i32.const 1080
      #|call ensure_idx
      #|i32.eqz
      #|if
      #|unreachable
      #|end
      #|else
      #|local.get 0
      #|call ensure_idx
      #|i32.eqz
      #|if
      #|unreachable
      #|end
      #|end
    ignore(
      program(
        "tlsf_malloc_full_after_attempt",
        show(@wasm.code_of_wat(wat)),
        params=ps,
      ),
    )
  }
  {
    let wat =
      #|block (result i32)
      #|i32.const 0
      #|local.get 0
      #|i32.eqz
      #|br_if 0
      #|drop
      #|i32.const d
      #|local.tee 1
      #|i32.const 4294965088
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 1
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1908
      #|i32.add
      #|local.tee 1
      #|i32.const 16
      #|i32.shr_u
      #|memory.size
      #|i32.ge_u
      #|if (result i32)
      #|i32.const 0
      #|else
      #|local.get 1
      #|i32.load offset=0 align=2**2
      #|end
      #|i32.eqz
      #|if
      #|call initialize_idx
      #|end
      #|local.get 0
      #|i32.const 256
      #|i32.le_u
      #|if (result i32)
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 0
      #|i32.const 7
      #|i32.add
      #|i32.const 3
      #|i32.shr_u
      #|local.tee 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|local.tee 0
      #|i32.load offset=0 align=2**2
      #|local.set 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.const 1912
      #|i32.add
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|i32.add
      #|local.get 2
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|i32.const 0
      #|i32.store offset=0 align=2**2
      #|local.get 0
      #|br 2
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|i32.const d
      #|i32.const 15
      #|i32.add
      #|i32.const 4294967280
      #|i32.and
      #|i32.add
      #|i32.const 1916
      #|i32.add
      #|i32.load offset=0 align=2**2
      #|local.tee 0
      #|if
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
      #|br 2
      #|end
      #|local.get 1
      #|i32.const 3
      #|i32.shl
      #|local.tee 2
      #|call page_idx
      #|local.tee 0
      #|if
      #|local.get 0
      #|i32.const 20
      #|i32.add
      #|local.tee 3
      #|i32.load offset=0 align=2**2
      #|local.tee 1
      #|if
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
      #|br 3
      #|end
      #|end
      #|i32.const 4294967295
      #|else
      #|local.get 0
      #|i32.const 4160749568
      #|i32.gt_u
      #|if
      #|unreachable
      #|end
      #|local.get 0
      #|call take_idx
      #|local.tee 0
      #|if (result i32)
      #|local.get 0
      #|i32.const 8
      #|i32.add
      #|else
      #|i32.const 4294967295
      #|end
      #|end
      #|end
    ignore(
      program("tlsf_malloc_full_retry", show(@wasm.code_of_wat(wat)), params=ps),
    )
  }
  let wat =
    #|local.tee 0
    #|i32.const 4294967295
    #|i32.eq
    #|if (result i32)
    #|unreachable
    #|else
    #|local.get 0
    #|end
  ignore(
    program("tlsf_malloc_full_result", show(@wasm.code_of_wat(wat)), params=ps),
  )
}
