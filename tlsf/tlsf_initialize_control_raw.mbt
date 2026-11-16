///|
fn prove_tlsf_initialize_control_raw() -> Unit raise {
  let w = w32
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let lc = "[(l0 : Value),\{i("req")},\{i("old")}]"
  let vars = "∀ d : \{w}, ∀ push : Num, ∀ l0 : Value, ∀ req : \{w}, ∀ old : \{w}, ∀ R : \{rty}"
  ignore(
    sym_prove(
      "tlsf_initialize_check_test_raw",
      "\{vars}, ∀ l2 : Value, sl_triple(st([\{i("old")}],[(l0 : Value),\{i("req")},(l2 : Value)],R),tlsf_initialize_check_test(d,push),st([\{i("wasm_bool(word_ugt((old : " + w + "),word(65536)))")}],\{lc},R))",
      [],
      [],
    ),
  )
  ignore(
    sym_prove(
      "tlsf_initialize_grow_test_raw",
      "\{vars}, sl_triple(st(NIL,\{lc},R),tlsf_initialize_grow_test(d,push),st([\{i("wasm_bool(word_ugt((req : " + w + "),(old : " + w + ")))")}],\{lc},R))",
      [],
      [],
    ),
  )
  ignore(
    sym_prove(
      "tlsf_initialize_grow_amount_raw",
      "\{vars}, sl_triple(st(NIL,\{lc},R),tlsf_initialize_grow_amount(d,push),st([\{i("word_sub((req : " + w + "),(old : " + w + "))")}],\{lc},R))",
      [],
      [],
    ),
  )
  ignore(
    sym_prove(
      "tlsf_initialize_guard_test_raw",
      "∀ d : \{w}, ∀ push : Num, ∀ lc : List[Value], ∀ ret : \{w}, ∀ R : \{rty}, sl_triple(st([\{i("ret")}],lc,R),tlsf_initialize_guard_test(d,push),st([\{i("wasm_bool((ret : " + w + ") == word(4294967295))")}],lc,R))",
      [],
      [],
    ),
  )
}
