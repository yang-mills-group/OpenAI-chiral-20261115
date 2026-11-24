import YM.CF.Laic.Inlets
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section
variable {n:Side}{ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{l:ι→Site n}{u:κ→Site n}{F G: Positions ι → Op κ}{A b c:ℝ}{k:ℕ}
structure HoldX (l:ι→ Site n)(u:κ→Site n)(F:Positions ι→Op κ)(A b:ℝ)(k:ℕ):Prop where
 glow: ContDiffAt ℝ ω F 0
 law: CableM l u u A k F 0 b
 funds:0<b
namespace HoldX
lemma lift(h:HoldX l u F A b k)(p:b ≤ c): HoldX l u F A c k:=⟨h.glow,h.law.books p,h.funds.trans_le p⟩
lemma drop(h:HoldX l u F A b k)(p:c≤ A): HoldX l u F c b k:=⟨h.glow,h.law.mild p h.funds.le,h.funds⟩
lemma opP(h:HoldX l u F A b k)(t:HoldX l u G A c k): HoldX l u (fun x=>F x+G x) A (b+c) k:=⟨h.glow.add t.glow,inkP (Nacre.tort.mp h.glow) (Nacre.tort.mp t.glow) h.law t.law,add_pos h.funds t.funds⟩
lemma minus(h:HoldX l u F A b k): HoldX l u (fun x=>-F x) A b k:=⟨h.glow.neg, inkN (Nacre.tort.mp h.glow) h.law,h.funds⟩
lemma times(h:HoldX l u F A b k)(p:HoldX l u G A c k)(t:0<A){Y:ℕ}(q:Multiplicity u Y):HoldX l u (fun x=>F x*G x) (slip k A) (2*(b*c*conductor k Y A)) k:=by
 let ht:=mul_pos (mul_pos h.funds p.funds) (conductor_pos k Y t); refine ⟨h.glow.mul p.glow,(wire_mul (Nacre.tort.mp h.glow) (Nacre.tort.mp p.glow) h.law p.law t h.funds p.funds q).books (le_of_eq (by ring)),?_⟩; linarith
lemma blank (v:0<A):HoldX l u (fun _=>1) A 1 k:=⟨contDiffAt_const,wire_one l u v,by norm_num⟩
lemma cold (v:0<A):HoldX l u (fun _=>0) A 1 k:=⟨contDiffAt_const,wire_zero l u v,by norm_num⟩
end HoldX
end
variable {n N: Side}{T:RG.StepData (More n) (More N)}{G:Ratio n N}{a b d:ℝ}{k:ℕ}
abbrev ReadY (F:Forest T.ratio)(T':Ratio n N)(U:Snap F→ Op (Iota T')) (a b:ℝ)(k:ℕ):Prop:= HoldX (clothH T F) (lookM T') U a b k
lemma skyK (a b:ℝ)(L:Side)(p:0<a)(t:0<b)(m k:ℕ) : ∃ d c:ℝ,0<d∧0<c∧∀ {n N: Side}{T:RG.StepData (More n) (More N)}(F:Forest T.ratio)(G:Ratio n N)(v:T.ratio=ratio G)(g:G.count=L)(h:Odd L.val),
 (∀ X:Toy m N, (∀ i,balance a X i≤b) → ReadY F G (fun y=>foot G (sumU (cavil X) (fine group F y))) d c k) ∧ ∀ (X:Toy m n), (∀ i,balance a X i≤b) → ReadY F G (fun y=>endorse G (sumU (cavil X) (outer group F y))) d c k:=by
 obtain ⟨x,z,H⟩:=hatch k; obtain ⟨u,c,s,e,D⟩:=savoy a x k m (2*L.val) p z -- tune
 refine ⟨u,b*c,s,mul_pos t e,fun F G v g h=>?_⟩
 obtain ⟨J,K⟩:= H F
 constructor
 · intro X hp; obtain ⟨he,hz⟩:= D (yon_F G F v g) (congrArg Prod.fst hats0) J X b t.le hp; refine ⟨Nacre.tort.mpr fun i j=> Nacre.tort.mp he _ _,frame_y G hz, mul_pos t e⟩ -- F norm
 intro X hp; obtain ⟨he,hz⟩:= D (yon_O G F v g) (congrArg Prod.snd hats0) K X b t.le hp; refine ⟨?_,order_y G (g.symm ▸ h) s (mul_pos t e|>.le) ?_,mul_pos t e⟩; refine Nacre.tort.mpr fun i j=>?_; unfold endorse extendK; simp only [Matrix.of_apply]; split; exact Nacre.tort.mp he _ _; exact contDiffAt_const
 -- can't rewrite T.ratio at all D. address F dprop. transport
 rw [←v]; exact hz
-- generic transition
lemma pivM(a b:ℝ)(k Y:ℕ)(p:0<a)(q:0<b):∃ d c:ℝ,0<d∧d≤a∧0<c ∧∀ {n:Side}{ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{l:ι→Site n}{u:κ→Site n}{T K S B P:Positions ι→Op κ},Multiplicity u Y→ HoldX l u S a b k→HoldX l u K a b k→ HoldX l u T a b k→HoldX l u B a b k→ HoldX l u P a b k→ S 0=0→ HoldX l u (fun x=> traitP (B x) (K x) (T x) (capT (P x) (S x))) d c k:=by
 -- capA (P S), BKT, gas, inverse, trait
 let f:= slip k a; let g:=slip k f; let s:=slip k g
 have hf:0<f:=slip_pos k p; have hg:0<g:=slip_pos k hf; have hs:0<s:=slip_pos k hg; let F:=2*((1+b)*b*conductor k Y a); let B:=2*(b*b*conductor k Y a); let R:=2*(F*b*conductor k Y f); let G:=2*(b*B*conductor k Y f); let T:=2*(G*R*conductor k Y g)
 have hA:f ≤ a:=slip_le k p.le; have hB:g≤ f:=slip_le k hf.le; have hy:s≤g:=slip_le k hg.le; have hc:=conductor_pos k Y p; have hc1:=conductor_pos k Y hf; have hc2:=conductor_pos k Y hg; have hF:0<F:=by unfold F; positivity
 have hR:0<R:=by unfold R; positivity
 have hT :0<T:=by unfold T G B; positivity
 obtain ⟨d,r,u,e,x,H⟩:=ventB hs hT k Y
 let D:= slip k d; let w:= slip k D; let z:= slip k w; have hv := slip_pos k u; have hw:=slip_pos k hv; let P:=2*(b*(1+R)*conductor k Y d); let T':=2*(r*b*conductor k Y d); let C':=2*((1+b)*P*conductor k Y D)
 have hx:= conductor_pos k Y u; have hh:=conductor_pos k Y hv; have he:=conductor_pos k Y hw
 let Q:=2*(C'*T'*conductor k Y w); have hq:0<Q:=by unfold Q C' T' P; positivity
 have hd:d≤g:= e.trans hy; have ht:d≤a:=hd.trans (hB.trans hA); have hn:D≤d:=slip_le k u.le; have hk:w≤D:=slip_le k hv.le
 refine ⟨z,Q, slip_pos k hw,(slip_le k hw.le).trans (hk.trans (hn.trans ht)),hq,?_⟩
 intro n ι κ _ _ _ l t T K S B' P' hm HS HK HT HB HP h0
 have hpB:HoldX l t (fun x=>capT (P' x) (S x)) g R k:=(((HoldX.blank p).opP HP.minus).times HS p hm |>.times (HP.drop hA) hf hm) -- one-sub definitional?
 let T1 x:=capT (P' x) (S x); have hp:HoldX l t (fun x=>bentT (K x) (B' x) (T x) (T1 x)) s _ k:= ((HK.drop hA).times (HB.times HT p hm) hf hm).times hpB hg hm
 let W x:=1+bentT (K x) (B' x) (T x) (T1 x); have hr:bentT (K 0) (B' 0) (T 0) (T1 0)=0:=by unfold T1 capT bentT; rw [h0,mul_zero,zero_mul,mul_zero]
 have hx:HoldX l t (fun x=>(W x)⁻¹) d r k:=by
    have ht:ContDiffAt ℝ ω W 0:= contDiffAt_const.add hp.glow
    refine ⟨(inv_p (show IsUnit (W 0) by simp [W,hr])).comp _ ht,?_,x⟩
    have hv:= H hm hp.glow hr hp.law; simpa only [W] using hv
 exact (((((HoldX.blank p).opP HB.minus).drop (hn.trans ht)).times ((HT.drop ht).times ((HoldX.blank u).opP (hpB.drop hd)) u hm) hv hm).times ((hx.times (HK.drop ht) u hm).drop hk) hw hm)
end YM.CF.Laic
