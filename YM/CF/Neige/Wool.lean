import YM.CF.Neige.Crux
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
open LocalJet
abbrev lamp(x:ℝ):ℝ:= ((radiusB x:ℝ)^9)*temp x
lemma lamp_s : Tendsto lamp atTop (𝓝 0):= Work.E09.radiusB_temp _
section 
variable (T:Tube G S)(x:ℝ)(A:Stores S)(F:Forest S.ratio)(k:S.Choices)
abbrev bedX (V:Config G c):= bark x V T k A F
abbrev baseX(V:Config G c):= Rows.gram T x V k (shots S x) A F
variable(q:Chi)(D:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(V:Config G c)
abbrev majorX:= hessN T x V k A F q D Y l
abbrev bankX:= perturb (bedX T x A F k V) (majorX T x A F k q D Y l V)
abbrev layX := white (bedX T x A F k V) (majorX T x A F k q D Y l V)
abbrev fareX := legacy (bedX T x A F k V) (majorX T x A F k q D Y l V)
abbrev cashX := perturb (layX T x A F k q D Y l V) (baseX T x A F k V)
end
variable {q:Chi}{D d' M a' r' m ε:ℝ}
structure ShardIncome (n:ℕ)(x v C m:ℝ)(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(V:Config G c)(k:S.Choices):Prop where
 kernel : Protected n (baseX T x A F k ∘ Vmove x V) 0 C
 soil : FreeResolvent.Gap (baseX T x A F k V) m
 rootX: Protected n (bedX T x A F k ∘ Vmove x V) 0 C
 rootT: Protected n (fun y=>(bedX T x A F k (Vmove x V y)).transpose) 0 C
 trouble: Protected n (fun y=>musk x (Vmove x V y) T k A F) 0 (C*Real.exp (-v*↑(radiusB x /60)))
lemma bear (K:Teller G)(P:Patch)(n:ℕ)(ht:P.Branches K.bind G):∃ m v C:ℝ,0< m ∧0<v∧0<C∧∀ᶠ x:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S),Cert P K S T x→∀ (A:Stores S)(F:Forest S.ratio)(V:Config G c), A.flags=RG.flags (temp x) V →∀ k:S.Choices, ShardIncome n x v C m T A F V k:=by
 obtain ⟨a,d,v,C,m,ha,hd,hv,hC,hm,h⟩:=stampX n G K P ht
 let X:= composeCost n (activation G n 0 d*C) 1; let Q:=max 1 X; have hQ:0<Q:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
 have hp:Tendsto temp atTop (𝓝 0):= by simpa using (Work.E09.radiusB_temp 0)
 refine ⟨m,v,Q,hm,hv,hQ,?_⟩; filter_upwards [h,hp.eventually (ge_mem_nhds zero_lt_one)] with x hx hp c f S T hT A F V hu k
 obtain ⟨hg,hU,hB,H⟩:=hx S T hT.got hT.size hT.funds.1 A F k V hu 0 (by simpa using ha.le); simp only [field_zero] at hg
 let p:= front (G:=G) (x:=x) A F; let E:= Real.exp (-v*↑(radiusB x/60))
 have h:= (warp_h p hU hd hC.le hp (g:= baseX T x A F k)).mono (show X ≤ Q from le_max_right ..)
 have hk := (warp_h p hB hd hC.le hp (g:=bedX T x A F k)).mono (show X ≤ Q from le_max_right ..)
 have ht := (warp_h p hB.transpose hd hC.le hp (g:=fun y=>(bedX T x A F k y).transpose)).mono (show X ≤ Q from le_max_right ..)
 refine ⟨h,hg,hk,ht,(warp_h p H hd (mul_nonneg hC.le (Real.exp_pos _).le) hp (g:=fun y=>musk x y T k A F)).mono ?_⟩
 change _ ≤  Q*E; apply le_trans (le_of_eq (show _=X*E from by unfold X E composeCost; ring)); exact mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le
lemma hand_r(hr:1000  ≤ radiusB x)(B:ℝ)(h:B≥0)(hc:0 ≤ C): chips S (radiusB x)*Fintype.card G.ColorIndex*(B*tideF C x) ≤  ( (Fintype.card (Site S.patch.L):ℝ)*(3^4*Fintype.card Axis)*Fintype.card G.ColorIndex*(B*C))*lamp x:=by
 let R:ℝ:= radiusB x; have he:1 ≤ R:=by unfold R; exact_mod_cast (show 1 ≤ radiusB x by omega)
 have hp: grain (radiusB x) ≤ 3^4*R^4:=by
    have h0:=pow_le_pow_left₀ (show 0 ≤ R+R+1 by positivity) (show R+R+1 ≤ 3*R by linarith) 4
    rw [mul_pow] at h0; unfold R at *; unfold grain; push_cast; exact h0
 have hw:0 ≤ tideF C x:=mul_nonneg hc (mul_nonneg (by positivity) (Work.E04.temp_nonneg _))
 unfold chips; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) (by positivity)) (Nat.cast_nonneg _)) (mul_nonneg h hw)).trans_eq
 unfold R tideF lamp blockF; ring
end YM.CF.Neige
