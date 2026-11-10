///|
test "code is printed as WebAssembly text, and reads back" {
  load()
  let code = @term_syntax.parse_term(
    "[Local_get(2), Local_get(1), Binop(T_i32, Binop_i(Sub)), EConstNum(ConstInt32(word(2))), Relop(T_i32, Relop_i(Lt(U))), If(Tbv(NONE), [Return], NIL), Block(Tbv(NONE), [Loop(Tbv(NONE), [Local_get(0), Load(T_i32, NONE, 2, 0), Local_set(6), Br_if(1), Br(0)])]), Local_get(0), Local_get(6), Store(T_i32, SOME(Tp_i8), 0, 4), Call(1), If(Tbv(SOME(T_num(T_i64))), [EConstNum(ConstInt64(word(7)))], [Load(T_i64, SOME((Tp_i32, S)), 2, 8)]), Testop(T_i32, Eqz), Unop(T_i32, Extend_s(Tp_i8)), Drop]",
  )
  inspect(
    wat_of_code(code),
    content=(
      #|local.get 2
      #|local.get 1
      #|i32.sub
      #|i32.const 2
      #|i32.lt_u
      #|if
      #|  return
      #|end
      #|block
      #|  loop
      #|    local.get 0
      #|    i32.load offset=0 align=2**2
      #|    local.set 6
      #|    br_if 1
      #|    br 0
      #|  end
      #|end
      #|local.get 0
      #|local.get 6
      #|i32.store8 offset=4 align=2**0
      #|call 1
      #|if (result i64)
      #|  i64.const 7
      #|else
      #|  i64.load32_s offset=8 align=2**2
      #|end
      #|i32.eqz
      #|i32.extend8_s
      #|drop
    ),
  )
}

///|
test "an instruction with no WebAssembly name here is kept in the term syntax" {
  load()
  let code = @term_syntax.parse_term("[Local_get(0), EConstNum(ConstInt32((x : Word[Tybit0[Tybit0[Tybit0[Tybit0[Tybit0[Unit]]]]]]))), Binop(T_f32, Binop_f(Addf)), Br_table([0, 1], 2)]")
  inspect(
    wat_of_code(code, indent="  "),
    content=(
      #|  local.get 0
      #|  i32.const x
      #|  hol Binop(T_f32, Binop_f(Addf))
      #|  hol Br_table([0, 1], 2)
    ),
  )
}
