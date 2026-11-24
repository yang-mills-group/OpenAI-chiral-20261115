import YM.CF.Souk.Chart
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort MeasureTheory AnalyticBridge.RelativeLogdet
open Next.SectorChange PatchReads Next.SectorChange.Wisps Summit
variable {q:Chi}{k:S.Choices}{M:ℝ}
section shelf
variable (T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(a:ℝ)(l:ℕ)
-- defined *all* V. no claim off island
def tallyX(y:Config G c):ℝ:=
 let A:= bareStores S;
 -(1/2:ℝ)*(∑ i∈Finset.range 3,pulseX (emptyA T x k A F y) (perZ T x k A F y) i)+(1/2:ℝ)*(∑ i∈Finset.range 3,pulseX (neo T x k A F y) (fun _=>1) i)+∑ i∈Finset.range 3,pulseX (acc T x k A F q a 1 l y) (fun _=>1) i
end shelf
-- uses pricing ground gap, Shard.
private lemma barter {A T' B C:ShelfQ τ}(h:B=A*(1+T'))(hp:IsUnit B.det)(he:IsUnit C.det)(L:ShelfQ τ)(hs:1+L=A.transpose*C*A): Real.log B.det=(1/2)*Real.log (1+L).det-(1/2)*Real.log C.det+Real.log (1+T').det:=by
 have hh:=hp.ne_zero; rw [h,det_mul,mul_ne_zero_iff] at hh; rw [h,Matrix.det_mul, Real.log_mul hh.1 hh.2,hs,Matrix.det_mul, Matrix.det_mul, Real.log_mul _ hh.1,Matrix.det_transpose,Real.log_mul hh.1 he.ne_zero]; ring; rw [Matrix.det_transpose]; exact mul_ne_zero hh.1 he.ne_zero
set_option maxHeartbeats 450000 in
lemma charm {b H m:ℝ}(hr:Ready T x)(hR:1000 ≤radiusB x) (hp:ShardIncome 3 x b V m T (bareStores S) F (1:Config G c) k) (hQ:Loom 3 x Q (1:Config G c) T F (bareStores S) 1 k q M l) (h:Mem 3 T x t C (V*tipPay b x) (Q*lamp x) H F (bareStores S) k (1:Config G c) l q M 1)(hc:0 ≤C)(hv:tipPay t x ≤ lamp x)(hu:tipPay b x ≤ lamp x)(ht:composeCost 2 (C*lamp x) (Uniform.shade G) ≤1/2)(hk:composeCost 2 (V*lamp x) (Uniform.shade G) ≤1/2)(hB:composeCost 2 (Q*lamp x) (Uniform.shade G) ≤1/2)(hd:lamp x ≤1)(j:Fin 2→Primary c G):
 let A:Mast G c→ Config G c:=fun y=>facadeX G (temp x• y); let L:=μ₁ T F x k q M (temp x) l; let D(y:Mast G c):= Real.log (L y).det-tallyX T x F k q M l (A y); let E:= raised G S.patch.L ((l+52)*radiusB x); let B(x):= Jet.composeCost 2 x (Uniform.shade G); let K(y):=40000*E*(B y)*(B (y*lamp x))^3
 ContDiffAt ℝ 2 D 0 ∧ |Uniform.entry D 0 j| ≤ K C+K V+K Q:=by
 intro P L Z E B W
 let A:=bareStores S; let F':= emptyA T x k A F; let L₀:= perZ T x k A F; let b':= acc T x k A F q M 1 l; let m':= neo T x k A F
 let G'(f:Config G c→ShelfQ (Taq F x G))(p:Config G c→ℝ→ShelfQ (Taq F x G))(R:ℝ):Prop:=ContDiffAt ℝ 2 (lastT (f∘P) (p∘P) 3) 0∧|Uniform.entry (lastT (f∘P) (p∘P) 3) 0 j| ≤ W R
 let one(y:Config G c)(t:ℝ): ShelfQ (Taq F x G):=1; let J:=pageX (G:=G) F x; let D:=Vmove x (1:Config G c); have hw(y:Mast G c): P y=D (hull G c y):=by unfold P facadeX; rw [map_smul]
 have hV:0≤V:=hp.rootX.nonneg; have hπ:0≤ Q:=hQ.link.nonneg
 let R₀:=radiusB x; let K':= (l+51)*R₀; let Y₀:LinkArray G (Frozen A x F):=1
 have hSum{f:Config G c→ShelfQ (Taq F x G)}{p:Config G c→ℝ→ShelfQ (Taq F x G)}{R N v U} (hB:Protected 3 (f∘D) 0 U)(ht: PriceW (f∘D) (p∘D) 3 0 N v) (hh: N ≤ R)(hk:v ≤ R*lamp x)(hx: B (R*lamp x) ≤1/2)(he:∀ V₀ V', Sample k V₀ Y₀ K' (f V₀) k V' Y₀ (f V')∧∀ u,Sample k V₀ Y₀ K' (p V₀ u) k V' Y₀ (p V' u))(hL:∀ V,Names (f V) R₀):G' f p R:=by
    let X:=ht; have hg : PriceW (f∘D) (p∘D) 2 0 N v:=⟨fun i h=>(ht.pre i h).of_le (by norm_num),fun i h=>(ht.St i h).of_le (by norm_num),fun i h=>(ht.Tag i h).of_le (by norm_num),ht.heart,fun i hi=>⟨((ht.paid i hi).1).order (by decide), ((ht.paid i hi).2).order (by decide)⟩⟩
    exact transfer_t (l:=(l+52)*radiusB x) hr K' (hB.order (by decide)) (hg.cheaper hh hk) he hL hx j (by unfold K' R₀; simp_rw [Nat.add_mul]; omega)
 have hj :Protected 3 (F'∘D) 0 (V+1):=subsid hp.kernel (show Protected 3 (fun _=> (1:ShelfQ (Taq F x G))) (0:Directions G c) 1 from allows_const _ (by rw [paint_one]; exact ContinuousLinearMap.norm_id_le))
 obtain ⟨hc,hN⟩:= hSum (p:=L₀) hj h.center le_rfl (mul_le_mul_of_nonneg_left hv hc) ht (fun V V'=>⟨((basic_sr hr hR).less stone_s).more (by unfold K' R₀; simp_rw [Nat.add_mul]; omega), fun u=>(perPt u hr hR).more (by unfold K' R₀; simp_rw [Nat.add_mul]; omega)⟩) (fun i=> ((basic_n hr hR).less (lanes_one _)).under (by unfold R₀; omega))
 have hX: Protected 3 (m'∘D) 0 (V*tipPay b x):= hp.trouble; have hMM:PriceW (m'∘D) (one∘D) 3 0 (V*tipPay b x) (V*tipPay b x) := h.core -- shadow
 obtain ⟨hP,hL⟩:= hSum hX hMM (mul_le_of_le_one_right hV (hu.trans hd)) (mul_le_mul_of_nonneg_left hu hV) hk (fun _ _=>⟨(neo_pt hr hR).more (by unfold K' R₀; simp_rw [Nat.add_mul]; omega),fun _=> stone_s⟩) (fun _=> neoN hr hR)
 have hD:Protected 3 (b'∘D) 0 (Q*lamp x):= hQ.lump
 obtain ⟨hm,hY⟩:=hSum (p:=one) hD (N:=Q*lamp x) (v:=Q*lamp x) (by exact h.modes) (mul_le_of_le_one_right hπ hd) le_rfl hB (fun _ _=> ⟨(accPt hr hR).more (by unfold K' R₀; simp_rw [Nat.add_mul]; omega),fun _=> stone_s⟩) (fun _=> accN hr hR)
 let X₁:=lastT (F'∘P) (L₀ ∘ P) 3; let X₂:=lastT (m'∘P) (one ∘ P) 3; let X₃:=lastT (b'∘P) (one ∘ P) 3; let R(y):=(1/2:ℝ)*X₂ y-(1/2:ℝ)* X₁ y+ X₃ y
 have hF: Z=ᶠ[𝓝 0] R:=by
    let U:= layX T x A F k q M 1 l; let V' :=U ∘P
    have hξ: L= lathe x (temp x) F U:= rfl; have hp': ContinuousAt (fun y=>(L y).det) 0:= Loops.det_contDiff.continuous.continuousAt.comp (f:=L) ((steep (X:=L) (can_tags hQ.link)).continuousAt)
    have hΛ(y:Mast G c): (L y).det=(V' y).det:=Matrix.det_submatrix_equiv_self ..
    have hV : (L 0).det≠0:=by rw [hΛ]; unfold V'; rw [Function.comp_apply,hw,map_zero]; rw [show D 0= (1:Config G c) by simp [D,Vmove]]; exact h.vertex.ne_zero -- tune
    have hχ:ContinuousAt (fun y:Mast G c=>(1+F' (P y)).det) 0:=by
       let f:= fun y: Directions G c=>1+F' (D y); have h:ContinuousAt f 0:=continuousAt_const.add (transX hj).continuousAt
       have hh: ContinuousAt f (hull G c 0):= (map_zero (hull G c)).symm ▸ h; apply ContinuousAt.congr (Loops.det_contDiff.continuous.continuousAt.comp (f:=f ∘ hull G c) (hh.comp (hull G c).continuous.continuousAt)) ?_
       filter_upwards with i; rw [hw]; rfl
    have hZ:(1+ F' (P 0)).det ≠ 0:=by
       rw [hw,map_zero]; have hh:= h.center.heart 1 (by simp [Isle,interval]); rw [edgeM,AnalyticNext.ConnectedActivity.ResolventVolume.graph,one_smul] at hh; exact hh.ne_zero
    filter_upwards [hχ.eventually (isOpen_ne.mem_nhds hZ), hp'.eventually (isOpen_ne.mem_nhds hV)] with y ha hb -- tune
    change (1+ F' (P y)).det≠0 at ha; change (L y).det≠0 at hb; unfold Z R X₁ X₂ X₃ tallyX lastT; dsimp only [Function.comp_apply]
    rw [hΛ] at hb ⊢; let T':=b' (P y); let K:= bedX T x A F k (P y); let X:=1+F' (P y)
    have hk: V' y=K*(1+T'):=rfl; have hp :1+ (neo T x k A F (P y))=K.transpose*X*K:=by
       rw [show X=baseX T x A F k (P y) from add_sub_cancel ..]; exact add_sub_cancel ..
    rw [barter hk (isUnit_iff_ne_zero.mpr hb) (show IsUnit X.det from isUnit_iff_ne_zero.mpr ha) (m' (P y)) hp] -- tune
    unfold T' X b' m' F' one L₀ A acc; simp only [Function.comp_apply]; ring -- tune
 have hs(x:ℝ)(hX:|x|≤1){Z:Mast G c→ℝ}{v:ℝ}(hz:ContDiffAt ℝ 2 Z 0)(he:|Uniform.entry Z 0 j| ≤ v): |Uniform.entry (fun y=>x*Z y) 0 j| ≤ v:=by
    erw [show Uniform.entry _ _ _= x*Uniform.entry Z 0 j from hiccup Z x j (hz.of_le (by norm_num)),abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hX).trans he
 let s:ℝ:=1/2; have he:ContDiffAt ℝ 2 R 0:= ((hP.const_smul s).sub (hc.const_smul s)).add hm; refine ⟨he.congr_of_eventuallyEq hF,?_⟩
 have hp' : |Uniform.entry R 0 j|≤ W C+W V+W Q:=by
    -- factor each
    let P₀(y):= (-1:ℝ)*X₃ y; let Z:=s • X₂ - s • X₁; rw [show R= Z-P₀ from funext fun y=>by change s*_ - s* _+_= (s*_-s*_)-(-1:ℝ)*X₃ y; ring, add_comm (W C)]; apply collect ((hP.const_smul s).sub (hc.const_smul s)) (hm.const_smul (-1:ℝ)) _ (collect (X:=s • X₂) (Y:=s • X₁) (hP.const_smul s) (hc.const_smul s) _ (hs s (by unfold s; norm_num) hP hL) (hs s (by unfold s; norm_num) hc hN)) (hs (-1:ℝ) (by norm_num) hm hY)
 unfold Uniform.entry; rw [(hF.iteratedFDeriv ℝ 2).eq_of_nhds]; exact hp'
end YM.CF.Souk
