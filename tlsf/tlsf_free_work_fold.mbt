///|
fn prove_tlsf_free_work_fold() -> Unit raise {
  let w = w32
  let lw = "List[\{w}]"
  let ht = "(\{w}) -> \{w}"
  let bt = "(Num) -> (Num) -> \{lw}"
  let gen = @tactics.repeat_tac(@tactics.gen_tac)
  let strip = @tactics.disch_then(th => @tactics.strip_assume_tac(th))
  let i = (x : String) => "V_num(ConstInt32((\{x} : \{w})))"
  let xs = "APPEND((ys : \{lw}),CONS((m : \{w}),(zs : \{lw})))"
  let params = "(d : \{w}),(lim : Num),(m0 : \{w}),(xs0 : \{lw}),(hd0 : \{ht}),(fp : \{rty}),(left : Bool),(right : Bool)"
  let pending = "tlsf_free_pending((d : \{w}),(lim : Num),(top : \{w}),(ys : \{lw}),(m : \{w}),(zs : \{lw}),(hd : \{ht}),(fl : \{w}),(sb : (Num) -> \{w}),(bl : \{bt}))"
  let r = "(gs : List[Value]) => (ms : Num) => (h : \{heap}) => ms == (lim : Num) && star(\{pending},(fp : \{rty})(gs,ms),h)"
  let cond = "tlsf_free_geom((d : \{w}),(lim : Num),(top : \{w}),\{xs},(hd : \{ht}),(m : \{w})) && !tlsf_used(hd(m)) && tlsf_bins_match(\{xs},tlsf_mark(hd,m),(bl : \{bt})) && tlsf_free_covers((m0 : \{w}),(hd0 : \{ht}),m,hd) && tlsf_free_live((xs0 : \{lw}),hd0,m0,\{xs},hd) && (!(left : Bool) || tlsf_free_left((ys : \{lw}),hd)) && (!(right : Bool) || tlsf_free_right((zs : \{lw}),hd))"
  let vars = "∀ d : \{w}, ∀ lim : Num, ∀ m0 : \{w}, ∀ xs0 : \{lw}, ∀ hd0 : \{ht}, ∀ fp : \{rty}, ∀ left : Bool, ∀ right : Bool, ∀ top : \{w}, ∀ ys : \{lw}, ∀ m : \{w}, ∀ zs : \{lw}, ∀ hd : \{ht}, ∀ fl : \{w}, ∀ sb : (Num) -> \{w}, ∀ bl : \{bt}, ∀ l1 : Value, ∀ l2 : Value"
  let _ = lemma(
    "tlsf_free_work_fold",
    "\{vars}, \{cond} → (∀ vs : List[Value], ∀ lc : List[Value], ∀ gs : List[Value], ∀ ms : Num, ∀ h : \{heap}, st(NIL,[\{i("m")},(l1 : Value),(l2 : Value)],\{r})(vs,lc,gs,ms,h) → tlsf_free_work(\{params})(vs,lc,gs,ms,h))",
    seq([
      gen,
      strip,
      ent_tac([thm("tlsf_free_work")], [
        "(top : \{w})",
        "(ys : \{lw})",
        "(m : \{w})",
        "(zs : \{lw})",
        "(hd : \{ht})",
        "(fl : \{w})",
        "(sb : (Num) -> \{w})",
        "(bl : \{bt})",
        "(l1 : Value)",
        "(l2 : Value)",
      ]),
    ]),
  )
}
