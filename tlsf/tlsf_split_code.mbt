// The shipped split guard, inlined split and final mark-used in Memory::take.
// Entry is immediately after pop; push is the module function index.

///|
fn define_tlsf_split_code() -> Unit raise {
  let wat =
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
  let code = @wasm.code_of_wat(wat)
  ignore(program("tlsf_split_code", show(code), params=["(d : \{w32})", "(push : Num)"]))
}
