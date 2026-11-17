///|
fn define_tlsf_malloc_full_parts() -> Unit raise {
  let ps = malloc_env_variables().map(x => "(" + x.0 + " : " + x.1 + ")")
  let early =
    #|local.tee 1
    #|i32.const 4294967295
    #|i32.ne
    #|if
    #|local.get 1
    #|return
    #|end
  ignore(
    program("tlsf_malloc_full_early", show(@wasm.code_of_wat(early)), params=ps),
  )
  let grow =
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
    program("tlsf_malloc_full_growth", show(@wasm.code_of_wat(grow)), params=ps),
  )
}
