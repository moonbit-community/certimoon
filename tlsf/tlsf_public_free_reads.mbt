// Read the dispatch tag from allocator-owned headers, leaving clients framed.

// Build a read-only cell view by selecting its exact owned points-to factor.

///|
fn public_free_read_tac(rws : Array[@kernel.Thm]) -> @tactics.Tactic raise {
  let ac = [
    thm("star_assoc"),
    thm("star_comm"),
    thm("star_left_comm"),
    thm("star_emp_hl"),
    thm("star_emp_hr"),
  ]
  let rules = rws + lift_rws() + [thm("has_i32")]
  seq([
    @tactics.repeat_tac(@tactics.gen_tac),
    @simp.rewrite_tac(ths(rules)),
    beta_goal(),
    @tactics.disch_then(th => @tactics.strip_assume_tac(th)),
    g => {
      let (_, body) = @basics.dest_exists(g.1)
      let wanted = args_of(body, "star", 3).unwrap()[0]
      let mut available : Array[@kernel.Term]? = None
      for (_, th) in g.0 {
        if args_of(@kernel.concl(th), "star", 3) is Some(parts) {
          let factors = malloc_star_factors(parts[0]) +
            malloc_star_factors(parts[1])
          if factors.any(t => @basics.aconv(t, wanted)) {
            available = Some(factors)
            break
          }
        }
      }
      guard available is Some(factors) else {
        raise Failure("public free: header cell not exposed: " + show(wanted))
      }
      let rest = small_star(
        factors.filter(t => !@basics.aconv(t, wanted)).map(show),
      )
      seq([
        @tactics.exists_tac(tm(rest)),
        @tactics.first_x_assum(th => {
          if head_name(@kernel.concl(th)) == "star" {
            @tactics.mp_tac(th)
          } else {
            @tactics.no_tac
          }
        }),
        @simp.asm_rewrite_tac(ths(ac)),
      ])(g)
    },
  ])
}

///|
fn prove_tlsf_public_free_reads() -> Unit raise {
  let w = w32
  let a = block_model_args()
  let m = "(m : " + w + ")"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let arw = (ts : Array[@kernel.Thm]) => @simp.asm_rewrite_tac(ths(ts))
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let _ = lemma(
    "tlsf_public_free_read_large",
    page_quantify(
      page_model_variables() + [("m", w), ("client", hprop), ("h", heap)],
    ) +
    "MEM(" +
    m +
    "," +
    a[3] +
    ") → (star(tlsf_allocator(" +
    a.join(",") +
    "),(client : " +
    hprop +
    "),(h : " +
    heap +
    ")) → has_i32(h,val(" +
    m +
    ")," +
    a[4] +
    "(" +
    m +
    ")))",
    () => {
      seq([
        gen,
        @tactics.disch_tac,
        @tactics.mp_tac(inst(thm("tlsf_small_member_split"), [m, a[3]])),
        arw([]),
        strip,
        subst_only("xs"),
        public_free_read_tac([
          thm("tlsf_allocator"),
          thm("tlsf_large"),
          thm("tlsf_chain"),
          thm("tlsf_regions_append"),
          thm("tlsf_regions"),
        ]),
      ])
    },
  )
}
