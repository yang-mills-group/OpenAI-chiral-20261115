import YM.CF.Char.Jaspe
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows Gauges Push
variable {n:ℕ}
def shirt(G:Gauge)(K:Teller G)(P:Patch)(x C s:ℝ)(n l:ℕ):Prop:= 0<s ∧ temp x ≤ s ∧ 0<C ∧∀{c f:Side}(S:StepData c f)(T:Tube G S)(A:Stores S)(F:Forest S.ratio), Cert P K S T x→ sizedP G P K S T F→ ∀(V: Config G c), A.flags=RG.flags (temp x) V → ∀ k:S.Choices, ∀(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F)), PatchReads.Ready T x ∧ Allows n (fun y=>cot T x (Vmove x V y) k A F q d Y l) 0 (C*s^2)∧ ∀ i j,Allows n (fun y=> driftN T x (Vmove x V y) k A F q d Y l i j) 0 (C*s)
lemma shipped (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n l:ℕ)(hn:2 ≤ n)(hl:l ≤ 18)(W: Uniform.Before G K.top.width K.top.paths K.j K.bind (n+1+1)): ∃ C s,0<s∧ ∀ᶠ x in atTop,shirt G K P x C (tideF s x) n l:=by
 obtain ⟨b,t,hb,ht,h⟩:=tender n l hn P K p W; obtain ⟨a,u,ha,hu,hp⟩:=famed K P p n l hn W; obtain ⟨B,hB,hv⟩:=terrain G n (by omega)
 let G' := Fintype.card G.ColorIndex; let C:= Push.Uniform.shade G * Jet.composeCost n b (1/2); let D:ℝ:=G'*(G'*Jet.composeCost n a (1/2)); let z:=max (max C D) 1; have hz:0<z:=zero_lt_one.trans_le (le_max_right ..)
 refine ⟨z,B,hB,?_⟩
 filter_upwards [h,hp,hv,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,(tide_s B).eventually (ge_mem_nhds (lt_min ht hu)), PatchReads.reserve K P] with x h hP hZ hx hk hw
 obtain ⟨hg,hg',hΨ⟩:=hZ; let s:=tideF B x
 refine ⟨hg,hg',hz,?_⟩
 intro c f S T A F H Hc V he k q d Y
 have hθ:=hw S T H.got H.size H.funds.1; obtain ⟨X,X',ht',ht''⟩:= H.funds.1.feeds; rw [← H.funds.1.high] at ht'
 refine ⟨hθ,allows_pi (mul_nonneg hz.le (sq_nonneg _)) ?_,?_⟩
 · rintro ⟨i,j⟩; by_cases hi: green x S A i.val.val
   · obtain ⟨R,k',⟨hl₀,Hh⟩,hr⟩:=hΨ S V F A (front A F (i,j)) (groundF (i,j) hi) he H.size
     have hK : ‖R 0‖ < 1:=hl₀.trans_lt (by norm_num)
     refine (cept (T:=T) hθ ht' l hl hi (hr Y k) Hh (h S T F H Hc s hg hg' (hk.trans (min_le_left ..)) k q d 1 (R 0) hK) j).mono ?_
     change _  ≤  z*s^2; apply le_trans (show _ = C*s^2 from ?_).le (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_left ..)) (sq_nonneg _)); unfold C Jet.composeCost; ring
   simp_rw [cot,Pi.sub_apply,liftN,if_neg hi,sub_self]; exact allows_const _ (by rw [norm_zero]; positivity)
 rintro ⟨i,ii⟩ ⟨j,jj⟩; by_cases hm:meeting S x i.val.val j.val.val
 · by_cases hi:green x S A i.val.val ∧ green x S A j.val.val
   · obtain ⟨R,k',⟨hl₀,Hh⟩,hr⟩:=hΨ S V F A (front A F (i,ii)) (groundF (i,ii) hi.1) he H.size
     have hK : ‖R 0‖<1:=hl₀.trans_lt (by norm_num)
     apply (costPew ii jj hθ ht' l hl (hr Y k) Hh hm hi.1 hi.2 (hP S T F H Hc s hg hg' (hk.trans (min_le_right ..)) k q d 1 _ hK)).mono
     change (G':ℝ)*(G'*composeCost n (a*s) (1/2))  ≤ z*s
     apply le_trans (show _ = D*s from ?_).le (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_left ..)) hg.le); unfold D Jet.composeCost; ring
   simp_rw [driftN,Matrix.sub_apply,hessN,Matrix.of_apply,if_neg hi,sub_self]; exact allows_const _ (by rw [norm_zero]; positivity)
 let g(i: Directions G c):=Vmove x V i
 simp_rw [driftN, Matrix.sub_apply, hessN_off hθ (show (j,jj) ∉ panels (x:=x) A F (i,ii) from hm) hx, gram_off hθ (show (j,jj) ∉ panels (x:=x) A F (i,ii) from hm) hx,sub_self]; exact allows_const _ (by rw [norm_zero]; positivity)
end YM.CF.Char
