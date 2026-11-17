// The exact public free body. All proof fragments are slices of this one
// transcription; the WAT checker compares the complete native function.

///|
fn define_tlsf_public_free_code() -> Unit raise {
  let wat =
    #|block
    #|i32.const d
    #|local.tee 1
    #|i32.const 4294965088
    #|i32.gt_u
    #|if
    #|unreachable
    #|end
    #|local.get 0
    #|local.get 1
    #|i32.const 15
    #|i32.add
    #|i32.const 4294967280
    #|i32.and
    #|i32.const 2184
    #|i32.add
    #|i32.lt_u
    #|br_if 0
    #|local.get 0
    #|i32.const 8
    #|i32.sub
    #|local.tee 1
    #|i32.load offset=0 align=2**2
    #|i32.const 4
    #|i32.and
    #|if (result i32)
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
    #|else
    #|local.get 1
    #|call free_idx
    #|end
    #|drop
    #|end
  let code = @wasm.code_of_wat(wat)
  let top = @basics.dest_list(code).head().unwrap()
  let body = args_of(top, "Block", 2).unwrap()[1]
  let instructions = @basics.dest_list(body).to_array()
  let mut cut = 0
  for i, instr in instructions {
    if head_name(instr) == "Br_if" {
      cut = i + 1
      break
    }
  }
  guard cut > 0 else { raise Failure("public free: missing guard branch") }
  let choose = instructions[instructions.length() - 2]
  let branch = args_of(choose, "If", 3).unwrap()
  let instr_type = @kernel.type_of(instructions[0])
  let list = (xs : Array[@kernel.Term]) => {
    @lists.mk_list(@list.List(xs), instr_type)
  }
  let params = ["(d : \{w32})", "(free_idx : Num)"]
  for
    (name, fragment) in [
      ("code", code),
      ("body", body),
      ("guard", list(instructions[:cut].to_owned())),
      ("read", list(instructions[cut:instructions.length() - 2].to_owned())),
      ("dispatch", list(instructions[cut:].to_owned())),
      ("large", branch[2]),
      ("choose", list([choose])),
    ] {
    ignore(program("tlsf_public_free_" + name, show(fragment), params~))
  }
}
