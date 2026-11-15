// The complete Memory::take shipped by the compiler, including both calls
// and its explicit successful return. Parameters name linked indices.

///|
fn define_tlsf_take_code() -> Unit raise {
  let wat =
    #|block (result i32)
    #|i32.const 31
    #|i32.const 1
    #|i32.const 27
    #|local.get 0
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|local.tee 3
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
    #|local.tee 0
    #|i32.clz
    #|i32.sub
    #|local.tee 1
    #|i32.const 4
    #|i32.sub
    #|local.set 2
    #|i32.const d
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|i32.load offset=0 align=2**2
    #|local.tee 4
    #|i32.const 1
    #|local.get 1
    #|i32.const 4
    #|i32.sub
    #|i32.shl
    #|i32.const 1
    #|i32.sub
    #|i32.const 4294967295
    #|i32.xor
    #|local.tee 1
    #|i32.and
    #|i32.ctz
    #|local.tee 5
    #|i32.const 32
    #|i32.ne
    #|if
    #|i32.const d
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|i32.const 4
    #|i32.add
    #|local.get 5
    #|i32.const 68
    #|i32.mul
    #|i32.add
    #|local.tee 5
    #|i32.load offset=0 align=2**2
    #|i32.const 1
    #|local.get 0
    #|local.get 2
    #|i32.shr_u
    #|i32.const 15
    #|i32.and
    #|i32.shl
    #|i32.const 1
    #|i32.sub
    #|i32.const 4294967295
    #|i32.xor
    #|i32.and
    #|i32.ctz
    #|local.tee 0
    #|i32.const 32
    #|i32.ne
    #|if
    #|local.get 5
    #|i32.const 4
    #|i32.add
    #|local.get 0
    #|i32.const 2
    #|i32.shl
    #|i32.add
    #|i32.load offset=0 align=2**2
    #|br 2
    #|else
    #|local.get 4
    #|local.get 1
    #|i32.const 1
    #|i32.shl
    #|i32.and
    #|i32.ctz
    #|local.tee 0
    #|i32.const 32
    #|i32.ne
    #|if
    #|i32.const d
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|i32.const 4
    #|i32.add
    #|local.get 0
    #|i32.const 68
    #|i32.mul
    #|i32.add
    #|local.tee 0
    #|i32.load offset=0 align=2**2
    #|i32.ctz
    #|local.tee 1
    #|i32.const 32
    #|i32.ne
    #|if
    #|local.get 0
    #|i32.const 4
    #|i32.add
    #|local.get 1
    #|i32.const 2
    #|i32.shl
    #|i32.add
    #|i32.load offset=0 align=2**2
    #|br 4
    #|end
    #|end
    #|end
    #|end
    #|i32.const 0
    #|end
    #|local.tee 0
    #|if
    #|local.get 0
    #|call pop
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967292
    #|i32.and
    #|local.tee 2
    #|local.get 3
    #|i32.const 264
    #|i32.add
    #|i32.gt_u
    #|if
    #|local.get 0
    #|local.get 2
    #|i32.add
    #|i32.const 8
    #|i32.add
    #|local.set 4
    #|local.get 3
    #|local.get 0
    #|i32.const 8
    #|i32.add
    #|i32.add
    #|local.tee 1
    #|local.get 2
    #|local.get 3
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
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967294
    #|i32.and
    #|i32.store offset=0 align=2**2
    #|local.get 1
    #|i32.const 4
    #|i32.add
    #|local.get 0
    #|i32.store offset=0 align=2**2
    #|local.get 1
    #|call push
    #|drop
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 2
    #|i32.and
    #|i32.const 0
    #|i32.ne
    #|local.tee 2
    #|if
    #|local.get 1
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967293
    #|i32.and
    #|i32.const 2
    #|i32.or
    #|i32.store offset=0 align=2**2
    #|else
    #|local.get 1
    #|local.get 1
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967293
    #|i32.and
    #|i32.store offset=0 align=2**2
    #|end
    #|local.get 2
    #|if
    #|local.get 0
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967293
    #|i32.and
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
    #|local.get 4
    #|i32.const 4
    #|i32.add
    #|local.get 1
    #|i32.store offset=0 align=2**2
    #|end
    #|local.get 0
    #|local.get 3
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 3
    #|i32.and
    #|i32.or
    #|i32.store offset=0 align=2**2
    #|end
    #|local.get 0
    #|local.get 0
    #|i32.load offset=0 align=2**2
    #|i32.const 4294967294
    #|i32.and
    #|i32.const 1
    #|i32.or
    #|i32.store offset=0 align=2**2
    #|local.get 0
    #|return
    #|end
    #|local.get 0
  let code = @wasm.code_of_wat(wat)
  ignore(
    program("tlsf_take_code", show(code), params=[
      "(d : \{w32})",
      "(pop : Num)",
      "(push : Num)",
    ]),
  )
}
