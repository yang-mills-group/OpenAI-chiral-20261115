import YM.CF.Neige.Glen
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange
variable {q:Chi}{θ D U r' ε m:ℝ}
abbrev neo(T:Tube G S)(x:ℝ)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(V:Config G c):=musk x V T k A F
abbrev acc(T:Tube G S)(x:ℝ)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(q:Chi)(D:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ):=punt∘bankX T x A F k q D Y l
lemma outer_p (T:Teller G)(P:Patch)(p:P.Branches T.bind G)(n:ℕ): ∃ θ C:ℝ,0<θ ∧0<C ∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(U:Tube G S)(A:Stores S)(F:Forest S.ratio)(V:Config G c), Cert P T S U x → A.flags=RG.flags (temp x) V→∀(k:S.Choices),PriceW (emptyA U x k A F ∘ Vmove x V) (perZ U x k A F ∘ Vmove x V) n 0 C (C*Real.exp (-θ*↑(radiusB x/60))):=by
 obtain ⟨a,d,v,C,m,ha,hd,hv,hC,hm,h⟩:=stampX n G T P p
 let D:= FreeResolvent.TestD.room d (C+1) (min m 1) n; let V:=priceFiber P G D; let η:=min m 1
 have hP:FreeResolvent.TestD.Price d (C+1) η D 1 V 1 n:=⟨lt_min hm zero_lt_one,by positivity,hd,rfl,le_rfl,(priceFiber_pos ..).le,zero_le_one,le_rfl⟩
 have hz:=hP.pos; let θ:=↑(n+1:ℕ)*D
 let X:= V*FreeResolvent.TestD.meter n n (C+1) 1 (FreeResolvent.TestD.rise V η); let Z:= Jet.composeCost n (activation G n 0 D * FreeResolvent.tagPrice 1 n (C+1) X) 1; let S:=2^n*(Jet.composeCost n (activation G n 0 d*C) 1+1)*Jet.composeCost n (activation G n 0 D*X) 1
 let Q:=max 1 (max S Z); have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 refine ⟨θ,Q,by unfold θ; positivity,lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
 filter_upwards [h,ht.eventually (ge_mem_nhds zero_lt_one),Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x H ht hp c f X' U A F W hx he k
 obtain ⟨hy,h',_,_⟩:= H X' U hx.got hx.size hx.funds.1 A F k W he 0 (by simpa using ha.le); simp only [field_zero] at hy
 have hR:(FreeResolvent.native c).Volume (front (G:=G) A F (x:=x)) D V:=by unfold V; rw [← hx.got]; exact (fiber_volume X' G hz A F x).1
 apply (cap_tag (k:=k) (T:=U) (V:=W) h' hy hm hd hp ht hC.le hP hR).cheaper (show S ≤  Q from (le_max_left ..).trans (le_max_right ..))
 apply le_trans (le_of_eq (show _= Z*Real.exp (-θ*↑(radiusB x/60)) from ?_)) (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (by positivity)); unfold Z θ X composeCost; rw [neg_mul]; ring
abbrev tipPay (v x:ℝ):ℝ:= Real.exp (-v*↑(radiusB x/60))
lemma tip_s {v:ℝ}(h:0<v):Tendsto (tipPay v) atTop (𝓝 0):= by
 have he:Tendsto (fun x:ℝ=>radiusB x/60) atTop atTop:= tendsto_atTop.mpr (fun i => (Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)).mono fun x hx=> by omega)
 exact Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.comp he).const_mul_atTop_of_neg (neg_lt_zero.mpr h))
structure Mem (n:ℕ) (T:Tube G S)(x θ C t s U:ℝ) (F:Forest S.ratio)(A:Stores S)(k:S.Choices)(V:Config G c)(l:ℕ)(q:Chi)(D:ℝ)(Y:LinkArray G (Frozen A x F)):Prop where
 center:PriceW (emptyA T x k A F ∘ Vmove x V) (perZ T x k A F ∘ Vmove x V) n 0 C (C*tipPay θ x)
 core: PriceW (neo T x k A F ∘ Vmove x V) (simplest (neo T x k A F ∘ Vmove x V)) n 0 t t
 modes: PriceW (acc T x k A F q D Y l ∘ Vmove x V) (simplest (acc T x k A F q D Y l ∘ Vmove x V)) n 0 s s
 vertex:IsUnit (layX T x A F k q D Y l V).det
 safe: ‖paintO ((layX T x A F k q D Y l V)⁻¹)‖  ≤ U
lemma sash(hr:Loom n x U V T F A Y k q D l)(hp:ShardIncome n x v C m T A F V k)(h:C*tipPay v x ≤ 1/2)(he:U*lamp x ≤ 1/2)(ht:U*lamp x^3 ≤ 1/2) {C':ℝ}(hf:PriceW (emptyA T x k A F ∘ Vmove x V) (perZ T x k A F∘ Vmove x V) n 0 C' (C'*tipPay θ x)) :
 Mem n T x θ C' (C*tipPay v x) (U*lamp x) (2*U*U) F A k V l q D Y:=by
 let z:=layX T x A F k q D Y l V; let X:=majorX T x A F k q D Y l V
 have hM: Vmove x V 0=V :=by simp [Vmove]
 have h₁:‖paintO (perturb z X)‖ ≤ 1/2:=by
    apply le_trans _ ht; unfold z X; nth_rw 1 2 [← hM]; exact hr.errorX.value -- tune
 have h₂:‖paintO z.transpose‖  ≤  U:=by unfold z; rw [← hM]; exact hr.back.value
 have h₃:‖paintO X‖ ≤ U:=by unfold X; rw [← hM]; exact hr.major.value
 have hv:=unitInv z X h₁ h₂ h₃; exact ⟨hf,up_p hp.trouble h,up_p hr.lump he,hv.1,hv.2⟩
lemma jumpW(K:Teller G)(P:Patch)(n l:ℕ)(hn:2  ≤  n)(hl:l  ≤ 18)(p:P.Branches K.bind G)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1)):
 ∃ θ C m v Q D:ℝ,0<θ∧0<C ∧0< m∧ 0<v∧0<Q∧∀ᶠ x:ℝ in atTop, C*tipPay θ x<1 ∧ Q*tipPay v x<1∧ D*lamp x<1∧∀{c f:Side}(S:StepData c f)(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(V:Config G c),Cert P K S T x → A.flags=RG.flags (temp x) V → sizedP G P K S T F→∀(k:S.Choices), ShardIncome n x v Q m T A F V k ∧ ∀(q:Chi)(d:ℝ)(Y: LinkArray G (Frozen A x F)), Loom n x D V T F A Y k q d l∧ Mem n T x θ C (Q*tipPay v x) (D*lamp x) (2*D*D) F A k V l q d Y:=by
 obtain ⟨m,v,Q,D,hm,hv,hQ,h⟩:=metricsU K P n l hn hl p W; obtain ⟨θ,C,hθ,hC,h'⟩:=outer_p K P p n
 have hv' := (tip_s hv).const_mul Q; have hθ' := (tip_s hθ).const_mul C; have hx:= lamp_s.const_mul D; have ht':= (lamp_s.pow 3).const_mul D; rw [mul_zero] at hv' hθ' hx; rw [zero_pow (by norm_num),mul_zero] at ht'; have he : (0:ℝ)<1/2:= by norm_num
 refine ⟨θ,C,m,v,Q,D,hθ,hC,hm,hv,hQ,?_⟩
 filter_upwards [h,h',hv'.eventually (ge_mem_nhds he),hθ'.eventually (gt_mem_nhds zero_lt_one),hx.eventually (ge_mem_nhds he),ht'.eventually (ge_mem_nhds he)] with x hx he' ha hu hl' hQ'
 refine ⟨hu,lt_of_le_of_lt ha (by norm_num),lt_of_le_of_lt hl' (by norm_num),?_⟩
 intro c f S T A F V H he hs k; obtain ⟨hc,Hh⟩:= hx S T H A F V he hs k
 exact ⟨hc,fun q d Y=>⟨Hh q d Y,sash (Hh q d Y) hc ha hl' hQ' (he' S T A F V H he k)⟩⟩
end YM.CF.Neige
