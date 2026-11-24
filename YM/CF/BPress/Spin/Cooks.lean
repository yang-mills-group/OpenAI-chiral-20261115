import YM.CF.BPress.Spin.Entry
/-! Variation over path-family and types; stage prices not assuming existence of atlas to interpolate. Precompute sector costs at given range R. Need dependence on supplied derivatives in later use; not on how they were purchased. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Lattice SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Stride Quad Blank Paint Cellar Cellar.Pass Hole Pf Pf.Currency Pf.RealBook Pledge Fock
open scoped Hole Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker BigOperators
attribute [local instance] opCStarAlgebra
variable {N:Side}{D: Type}[TopologicalSpace D] {A B W:Pledge}{j w v n:ℕ}{d e ε r ρ q r' σ δ:ℝ}{width:Side}
structure Sight (F:Form N D) (U:D→ℝ→Paint (More N))(A:ℝ)(a:ℝ): Prop where
 taxes (i:D × PartH a)(o:Site (More N)) : ‖U i.1 i.2.val o‖≤A
 varies (X:Support (More N))(i:Site N)(p:node i∈X)(t v: D)(s:PartH a): ‖U t s.val (node i)-U v s.val (node i)‖ ≤ F.eval X t v -- uses Lip coefficient 1; can build eval itself scaled choose permit. 
 cont : Continuous (fun x:D × PartH a => U x.1 x.2.val)
namespace Sight
-- adapt Engine.stream_node to general rope on Form extension.
def pad (F:Form N D)(a:ℝ): Form N (D×PartH a):= { eval:=(Currency.rope a F.stage).eval,
                                                      pos:=(Currency.rope a F.stage).pos,
                                                      mono:=(Currency.rope a F.stage).includeV }
def price (A:ℝ):Pledge:=let b:=Follows A; (stream A).scales b
where Follows(A:ℝ):= max 1 A -- to satisfy: stream_node uses lift through Eval b passed, need morph up.
lemma value {x a:ℝ}{F:Form N D}{U:D→ℝ→Paint (More N)}(v:Sight F U x a): (price x).Costs (Currency.rope a F.stage) (fun i=> Paint.coupling (U i.1 i.2.val)):=by
 let K:=max 1 x; have hc:0≤ K:=zero_le_one.trans (le_max_left ..); let g:=pad F a
 let G: Form N (D×PartH a):= {eval:=fun i x y=> K*g.eval i x y,
                               pos:=fun i _ _=>mul_nonneg hc (g.pos ..),
                               mono:=fun h _ _=>mul_le_mul_of_nonneg_left (g.mono h ..) hc}
 have he : Form.Comes G (stream x) (fun i=>Paint.coupling (U i.1 i.2.val)):=by
    refine stream_node G (fun i:D × PartH a=>U i.1 i.2.val) (fun x=>v.taxes x) v.cont ?_; intro X l m o h; let y:= F.eval X l.1 m.1; have ht:0≤y:=F.pos ..; by_cases t:l.2=m.2
    · rw [← t]; refine (v.varies _ _ h l.1 m.1 l.2).trans ?_; change y≤K*(y+ if _ then 0 else 2); rw [if_pos t,add_zero]; exact le_mul_of_one_le_left ht (le_max_left ..)
    change ‖U _ _ _-U _ _ _‖≤K*(y+_); rw [if_neg t]; have hp:= (norm_sub_le (U l.1 l.2.val (node o)) (U m.1 m.2.val (node o))).trans (add_le_add ((v.taxes ..).trans (le_max_right 1 x)) ((v.taxes ..).trans (le_max_right 1 x))); change _ ≤ K+K at hp; nlinarith
 exact Costs.morph he id continuous_id rfl rfl hc fun _ _ _=> le_rfl -- stage exact
end Sight

structure GroupFields (F:Form N D)(U:D→OpenW N d)(x:D→ Support N) : Prop where
 V: Continuous U
 reads:∀(i:Support (More N))(a b), invitation i (U a).val (U b).val≤F.eval i a b
 S:∀i:Site N, IsClopen {a:D|i∈ x a}
 L:Hole.Bits F x
variable {D₀: Form N D}{U:D→OpenW N d}{X':D→ Support N}
def utere (U:D→OpenW N d)(j:ℕ)(M:Jill.Male): Raw D (Single N):=fun x=> spar j M (U x).val
lemma sees (X:GroupFields D₀ U X')(p:Shelf N d j A)(M:Jill.Male)(R:Aim N)(v:R.toll B.rate W.rate B.price W.price): D₀.Comes A (utere U j M) ∧ D₀.Comes (priceS A B W) (fun x=>Ts R (utere U j M x) (U x).val) ∧ ∀ u :Bool,D₀.Comes (stream 1) (fun x=> Lock (X' x) u):= ⟨Form.pulls (p.entries M) U X.V X.reads,Form.pulls (CostS M p R v) U X.V X.reads,fun _=>trackprice D₀ X.L X.S _⟩
structure ColorSex (F:Form N D)(U:D→ℝ→Paint (More N))(A:ℝ): Prop where
 line0:Sight F U A 0
 line1:Sight F U A 1
theorem gen (X:GroupFields D₀ U X')(p:Shelf N d j A)(M:Jill.Male)(R:Aim N)(v:R.toll B.rate W.rate B.price W.price)(C C':D→ℝ→Paint (More N))(H:ColorSex D₀ C σ)(J:ColorSex D₀ C' σ)(y:∀ x, Issued (Locks (X' x) true) (Locks (X' x) false) (utere U j M x) (Ts R (utere U j M x) (U x).val) (coupling ∘ C x) (coupling ∘ C' x) r ε) : RealBook.Stoke (fun x=> Locks (X' x) true) (fun x=> Locks (X' x) false) (utere U j M) (fun x=>Ts R (utere U j M x) (U x).val) (fun x=>coupling ∘ C x) (fun x=>coupling ∘ C' x) D₀.stage A (priceS A B W) (stream 1) (Sight.price σ) ε r quota:=by obtain ⟨b,f,q⟩:=sees X p M R v; exact ⟨y,D₀.full,b,f,q true,q false,H.line0.value,H.line1.value,J.line0.value,J.line1.value⟩ -- proof
end YM.CF.BPress.Spin
