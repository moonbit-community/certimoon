///|
fn malloc_original(v : String, n : String) -> String {
  if v == "first" {
    malloc_i(n)
  } else {
    "(original : Value)"
  }
}

///|
fn malloc_request_locals(
  v : String,
  n : String,
  l0 : String,
  l1 : String,
  l2 : String,
  l3 : String,
  l4 : String,
) -> String {
  let work = [if v == "first" { l0 } else { malloc_i(n) }, l1, l2, l3, l4]
  let s = malloc_locals(v, work)
  if v == "first" {
    s.replace(old="(original : Value)", new=malloc_i(n))
  } else {
    s
  }
}

///|
fn prove_tlsf_malloc_request_setup() -> Unit raise {
  let w = w32
  let n = "(n : " + w + ")"
  let c = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let k = "val(" + c + ")"
  let q = "DIV(val(" + n + ")+7,8)"
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let _ = lemma(
    "tlsf_malloc_request_setup",
    "∀ n : " +
    w +
    ", 0 < val(n) && val(n) <= 256 → " +
    k +
    " == " +
    q +
    " && " +
    k +
    " < 33 && 8 <= 8*" +
    k +
    " && 8*" +
    k +
    " <= 256 && val(n) <= 8*" +
    k +
    " && MOD(8*" +
    k +
    ",8) == 0 && word_jshl(" +
    c +
    ",word(3)) == word(8*" +
    k +
    ") && val((word(8*" +
    k +
    ") : " +
    w +
    ")) == 8*" +
    k +
    " && DIV(8*" +
    k +
    ",8) == " +
    k,
    seq([
      @tactics.gen_tac,
      @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
      g => {
        @tactics.strip_assume_tac(
          block_under(
            inst(thm("tlsf_malloc_small_round"), ["val(" + n + ")"]),
            g,
          ),
        )(g)
      },
      g => {
        @tactics.strip_assume_tac(
          block_under(inst(thm("tlsf_malloc_small_class_word"), [n]), g),
        )(g)
      },
      free_have(
        k + " == " + q,
        seq([
          arw([@words.val_word(), @words.dimindex_32()]),
          @tactics.conv_tac(@calc_num.num_reduce_conv),
          @tactics.match_mp_tac(@arith.mod_lt()),
          @int.asm_arith_tac,
        ]),
      ),
      free_have(
        "DIV(8*" + k + ",8) == " + k,
        seq([
          @tactics.match_mp_tac(
            inst(@arith.div_uniq(), ["8*" + k, "8", k, "0"]),
          ),
          @int.asm_arith_tac,
        ]),
      ),
      arw([]),
      @tactics.repeat_tac(@tactics.conj_tac),
      @tactics.first(
        @list.List([
          solve(@int.asm_arith_tac),
          solve(
            seq([
              @simp.rewrite_tac(ths([@words.val_word(), @words.dimindex_32()])),
              @tactics.conv_tac(@calc_num.num_reduce_conv),
              @tactics.match_mp_tac(@arith.mod_lt()),
              @int.asm_arith_tac,
            ]),
          ),
        ]),
      ),
    ]),
  )
}

///|
fn prove_tlsf_malloc_lookup_cases() -> Unit raise {
  let w = w32
  let lw = "List[" + w + "]"
  let a = block_model_args()
  let n = "(n : " + w + ")"
  let kw = "(kw : " + w + ")"
  let cls = "word_jushr(word_add(" + n + ",word(7)),word(3))"
  let b = "(b : " + w + ")"
  let bs = "(bs : " + lw + ")"
  let vars = malloc_publication_variables() +
    page_model_variables() +
    [
      ("n", w),
      ("kw", w),
      ("before", heap),
      ("fp", rty),
      ("l0", "Value"),
      ("l1", "Value"),
      ("l2", "Value"),
      ("l3", "Value"),
      ("l4", "Value"),
      ("b", w),
      ("bs", lw),
    ]
  let r = "tlsf_malloc_ro(" +
    (a + ["(before : " + heap + ")", "(fp : " + rty + ")"]).join(",") +
    ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  for v in malloc_variant_names() {
    for fast in [true, false] {
      let word = if fast { cls } else { kw }
      let prefix = if fast { "fast" } else { "partial" }
      let oldargs = malloc_publication_variables().map(x => {
          if x.0 == "original" {
            malloc_original(v, n)
          } else {
            "(" + x.0 + " : " + x.1 + ")"
          }
        }) +
        a +
        [
          n,
          kw,
          "(before : " + heap + ")",
          "(fp : " + rty + ")",
          "(l0 : Value)",
          "(l1 : Value)",
          "(l2 : Value)",
          "(l3 : Value)",
          "(l4 : Value)",
        ]
      let raw = inst(
        thm("tlsf_malloc_" + v + "_" + prefix + "_lookup_raw"),
        oldargs,
      )
      for cons in [false, true] {
        let hd = if cons { b } else { "(word(0) : " + w + ")" }
        let list = if cons {
          "CONS(" + b + "," + bs + ")"
        } else {
          "(NIL : " + lw + ")"
        }
        let cond = "val(" +
          a[0] +
          ") <= 4294965088 && val(" +
          word +
          ") < 33 && " +
          a[if fast { 13 } else { 14 }] +
          "(val(" +
          word +
          ")) == " +
          list
        let inlc = if fast {
          malloc_request_locals(
            v, n, "(l0 : Value)", "(l1 : Value)", "(l2 : Value)", "(l3 : Value)",
            "(l4 : Value)",
          )
        } else {
          malloc_locals(v, [
            "(l0 : Value)",
            malloc_i(kw),
            "(l2 : Value)",
            "(l3 : Value)",
            "(l4 : Value)",
          ])
        }
        let outlc = malloc_locals(v, [
          malloc_i(hd),
          malloc_i(word),
          if fast {
            "(l2 : Value)"
          } else {
            malloc_i("word(8*val(" + kw + "))")
          },
          "(l3 : Value)",
          "(l4 : Value)",
        ])
        let outlc = if v == "first" {
          outlc.replace(old="(original : Value)", new=malloc_i(n))
        } else {
          outlc
        }
        let inlc = if v == "first" {
          inlc.replace(old="(original : Value)", new=malloc_i(n))
        } else {
          inlc
        }
        let _ = lemma(
          "tlsf_malloc_" +
          v +
          "_" +
          prefix +
          "_" +
          (if cons { "cons" } else { "nil" }),
          page_quantify(vars) +
          cond +
          " → sl_triple(st(NIL," +
          inlc +
          "," +
          r +
          ")," +
          malloc_part(v, prefix + "_lookup") +
          ",st([" +
          malloc_i(hd) +
          "]," +
          outlc +
          "," +
          r +
          "))",
          seq([
            gen,
            @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
            if fast {
              @tactics.all_tac
            } else {
              g => {
                @tactics.assume_tac(
                  @simp.rewrite_rule(ths([@words.word_val()]))(
                    block_under(
                      inst(thm("tlsf_malloc_small_shift"), ["val(" + kw + ")"]),
                      g,
                    ),
                  ),
                )(g)
              }
            },
            g => {
              free_apply(
                @simp.rewrite_rule(
                  g.0.map(x => x.1) +
                  ths([
                    thm("tlsf_small_head"),
                    @lists.hd(),
                    @lists.not_cons_nil(),
                  ]),
                )(raw),
              )(g)
            },
          ]),
        )
      }
    }
  }
  let _ = arw
}
