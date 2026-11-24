/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Souk.Corn
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Glowing
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
open Planned.JetPort Finset
lemma yo{i j:Primary c G}(Y : In G c→L[ℝ] In G c→L[ℝ] ℝ)(h : ∀ p q, ∀ σ τ, Further.PhysicalPeriodLimitF933.Glowing.unitSize (G:=G) σ→ Further.PhysicalPeriodLimitF933.Glowing.unitSize (G:=G) τ →|Y (wave p σ) (wave q τ)|≤ C): |Y (tint G _ (bolt i)) (tint G _ (bolt j))| ≤ C:=by -- ambiguity
 let S:= Fintype.card (Site c); have hS:0<(S:ℝ):=by unfold S; positivity
 rw [← Further.PhysicalPeriodLimitF933.Glowing.cash,← Further.PhysicalPeriodLimitF933.Glowing.cash]; simp only [map_sum,map_smul,_root_.sum_apply, _root_.smul_apply,smul_eq_mul,← Finset.mul_sum, abs_mul]; let b:=(S:ℝ)⁻¹; rw [Finset.sum_comm]; rw [abs_of_pos (inv_pos.mpr (show 0<(Fintype.card (Site c):ℝ) by positivity))] -- tune
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_trans ((abs_sum_le_sum_abs ..).trans (sum_le_sum fun _ _=>abs_sum_le_sum_abs ..)) (Finset.sum_le_sum (fun _ _=> Finset.sum_le_sum (fun _ _=> h _ _ _ _ (Further.PhysicalPeriodLimitF933.Glowing.orig _ _) (Further.PhysicalPeriodLimitF933.Glowing.orig _ _))))) (show 0 ≤ b from by positivity)) (show 0 ≤ b from by positivity)).trans_eq
 simp only [sum_const,card_univ,nsmul_eq_mul]; change b*(b*((S:ℝ)*((S:ℝ)*C)))=_; unfold b; field_simp
section
variable {p:ChartRatio G}{k:S.Choices}
lemma bearerX {b d Θ H:ℝ}{z} (h: FiniteBound F T.up T.down T.high T.low b p z Θ d H) (v:Fin 2→Primary c G):
 let U:=fun u:Mast G c=> thermal F k T.high T.up z p (tint G _ u)-draft b T.down T.low (tint G _ u)
 ContDiffAt ℝ ω U 0 ∧ |Uniform.entry U 0 v| ≤ (Fintype.card (Site c):ℝ)*Θ*H*Real.exp (-d*c.val):=by
 intro U; let f:=thermal F k T.high T.up z p; let g (x:fieldDir G c 1):=draft b T.down T.low x; let V:= f-g; let L:= (tint G (Body 1 c)).toContinuousLinearMap
 have hV:ContDiffAt ℝ ω V (L 0):=by rw [map_zero]; exact (h.born k).sub h.classicalResult
 change ContDiffAt ℝ ω (V∘ L) _ ∧ _; refine ⟨hV.comp 0 L.contDiff.contDiffAt,?_⟩; change |Uniform.entry (V ∘ L) 0 v|≤ _; unfold Uniform.entry; rw [Uniform.iter_lin_at (hV.of_le le_top),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply]
 let M:=fderiv ℝ (fderiv ℝ V) 0; refine yo (i:=v 0) (j:=v 1) M fun p q x y hx hy => ?_; have hm: M (wave p x) (wave q y)=iteratedFDeriv ℝ 2 V 0 ![wave p x,wave q y]:=by rw [iteratedFDeriv_two_apply]; rfl
 rw [hm]; change |_| ≤ _; unfold V; rw [iteratedFDeriv_sub_apply ((h.born k).of_le le_top) (h.classicalResult.of_le le_top), _root_.sub_apply]; exact h.wave_price k p q _ _ hx hy
variable {R:PathData G}{q:Clip}
def safeD (R:PathData G)(m:ℕ): PathData G:={ grainA R m with loop:= Vol.batch R.loop m}
def gateY(p:ChartRatio G)(T:Tube G S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(q:Chi)(a:ℝ)(l:ℕ)(y:Mast G c):=inLoop (safeD T.up (Stores.till x)).loop F (flute F (sol S T k x F l) 1 y)- Real.log (μ₁ T F x k q a 1 l y).det- addH F p (flute F (sol S T k x F l) 1 y) -- plus sign check! thermal true includes +.5; K log opposite, correct
lemma thermalFold {p:ChartRatio G}{s:ℝ}{z}:
 let P:=Uniform.station z; let A:=flute F P s
 (fun y:Mast G c=>thermal F k T.high T.up z p (tint G _ (s•y)))= (inLoop T.up.loop F ∘ A)+ fun y=> (1/2)* Real.log (ξ T F k s z y).det- addH F p (A y):=by
 intro P A; ext t; let U:=tint G _ (s•t); let Z:=z U; have hp: Uniform.paint F G (A t)= (U,Z):=by
    unfold A flute Uniform.curve P Uniform.station; rw [Uniform.paint_meet]; dsimp only [Function.comp_apply]; rw [(tint G _).apply_symm_apply]
 have he :addH F p (A t)=Real.log (∏ i:F.Free,p.J (Z i)):=by unfold addH; congrm Real.log (Finset.prod _ ?_); funext i; change p.J ((Uniform.paint F G (A t)).2 i)=_; rw [hp]
 change _= inLoop _ F _+ _; dsimp only; rw [he]; have hv: inLoop T.up.loop F (A t)= Precision.loop T.up (lifting F (represent U) Z):=by
    unfold inLoop Uniform.signedFine Uniform.fine Uniform.outer; rw [hp]; rfl
 rw [hv]; unfold thermal; unfold U Z ξ Planned.JetPort.inside; abel
lemma yew {X Y:Fish ι→ℝ}(hX:ContDiffAt ℝ 2 X 0)(hY:ContDiffAt ℝ 2 Y 0)(q: Fin 2→ι): |Uniform.entry (X-Y) 0 q|=|Uniform.entry X 0 q-Uniform.entry Y 0 q|:=by unfold Uniform.entry; rw [iteratedFDeriv_sub_apply (hX.of_le (by norm_num)) (hY.of_le (by norm_num))]; rfl
lemma collect {X Y:Fish ι→ℝ}(hX:ContDiffAt ℝ 2 X 0)(hY:ContDiffAt ℝ 2 Y 0)(q: Fin 2→ι)(hx: |Uniform.entry X 0 q| ≤ A)(hy:|Uniform.entry Y 0 q| ≤ Q): |Uniform.entry (X-Y) 0 q| ≤ A+Q:= by rw [yew hX hY]; exact (abs_sub ..).trans (add_le_add hx hy)
lemma hiccup(f:Fish ι→ℝ)(g:ℝ)(q:Fin 2→ι)(h:ContDiffAt ℝ (2:ℕ) f 0):Uniform.entry (fun y=>g • f y) 0 q=g*Uniform.entry f 0 q:=by unfold Uniform.entry; rw [show (fun y=> g • f y)=g • f from rfl,iteratedFDeriv_const_smul_apply h]; rfl
set_option maxHeartbeats 700000 in
lemma tale {z} (k:S.Choices)(q:Chi)(a s:ℝ)(p:ChartRatio G) (h:PathData.Bounds T.up T.high K.top.width K.top.paths Q) (hs:Uniform.PaintSupply G 2 t) {C₀:ℝ} (hv:FloorZ (addH F p) C₀) (hr:0≤ C₀)(hg:GoodsR F (sol S T k x F l) (Uniform.station z) s A D) (hc:0 ≤ A)(hD:0 ≤ D)(hd:D ≤ 1)(hu:Protected 2 (μ₁ T F x k q a s l) 0 C)
 (hζ:Jewel (fun y=> perturb (μ₁ T F x k q a s l y) (ξ T F k s z y)) 0 r V)(hp:r≤1/2)(hξ:ContDiffAt ℝ 2 (ξ T F k s z) 0)(j:Fin 2→Primary c G):
 let M:=Newt.fareX G 2 2 t K.top.width S.patch.L; let N:= Newt.fareX G 2 2 t (K.top.width/2) S.patch.L; let R:=tollE K.top.width (Stores.till x)
 let u:=fun y:Mast G c=> gateY p T F x k q a l (s•y)-thermal F k T.high T.up z p (tint G _ (s•y))
 ContDiffAt ℝ 2 u 0 ∧ |Uniform.entry u 0 j| ≤ (D*(Q*M)+ 2*D*((A+1)*(Q*M)) + (A*(R*Q*N)+ A*(A*(R*Q*N))))+(D*C₀+2*D*((A+1)*C₀)+6*V):=by
 intro M N R u
 let Z:=μ₁ T F x k q a s l; let X:=ξ T F k s z; let Y(y:Mast G c):= perturb (Z y) (X y); let W(y:Mast G c):= 1+Y y; let f:= sol S T k x F l; let m:=flute F f s; let P':=flute F (Uniform.station z) s
 let L(y:Mast G c):= Real.log (W y).det
 have hW y: W y=(Z y).transpose * X y * Z y:= add_sub_cancel ..
 obtain ⟨hq,hb,hV⟩:= (hζ.logM hp 1 (by decide) j)
 let B:= T.up.loop; let B':= (safeD T.up (Stores.till x)).loop; let B₀:=haste (Stores.till x) B; let O:= inLoop B' F; let W':= inLoop B F; let E:= inLoop B₀ F; let N':=addH F p
 obtain ⟨hx,hG,hY,hA,hP⟩:= hg
 change m 0=0 at hx; change P' 0=0 at hG
 let w:ℕ:= Stores.till x
 have hm :0 ≤ Q:=(tsum_nonneg h.two.1).trans h.two.2.2
 have h_o:FloorZ O (Q*M):= alum _ _ (Vol.barn h.two _) h.width hs; have he:FloorZ E (R*Q*N):= alum _ _ (pastA _ h.width h.two _) (half_pos h.width) hs
 have hd y(hy:(W y).det≠0): Real.log (Z y).det=L y/2-(1/2)*Real.log (X y).det:=by
    rw [hW,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,mul_ne_zero_iff, mul_ne_zero_iff] at hy
    unfold L; rw [hW, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,Real.log_mul (mul_ne_zero hy.1.1 hy.1.2) hy.2,Real.log_mul hy.1.1 hy.1.2]; ring
 let D':=O ∘ m - O ∘ P'; let E':=N' ∘ m-N' ∘ P'; let T':=E ∘ P'; let Y'(x:Mast G c):=(1/2:ℝ) • L x
 have hh: u=ᶠ[𝓝 0] ((D'-T')-(E'+Y')):=by
    have hm: ContDiffAt ℝ 2 W 0:= contDiffAt_const.add (show ContDiffAt ℝ 2 Y 0 by simpa using steep hζ.upper) -- shadow he
    have hp : ContinuousAt (fun i=>(W i).det) 0:= (Loops.det_contDiff.continuous.continuousAt).comp (f:=W) hm.continuousAt
    filter_upwards [hp.eventually (isOpen_ne.mem_nhds (show (W 0).det≠0 from hq.ne_zero))] with y hh
    change u y=_
    have hv:thermal F k T.high T.up z p (tint G _ (s•y))= W' (P' y)+((1/2)*Real.log (X y).det-addH F p (P' y)):=congr_fun thermalFold y
    unfold u gateY; rw [hv]; rw [show μ₁ T F x k q a 1 l (s • y)=Z y from by unfold μ₁ Z; rw [one_smul],show flute F _ 1 (s • y)=m y from by unfold flute m; rw [one_smul]]; change O (m y)-Real.log (Z y).det- N' (m y)-_= (O _-_ - T' y)-(N' _- N' _+Y' y); rw [hd y hh,show T' y=W' (P' y)-O (P' y) from (congr_fun (short_ix F _ h.two h.width w) _).symm]; unfold Y'; rw [smul_eq_mul]; unfold N' Function.comp; ring -- tune
 have hxM:∀ i:Primary c G,costU (Uniform.entry m 0 (fun _ : Fin 1=>i)) ≤ A+1 ∧ costU (Uniform.entry P' 0 (fun _ : Fin 1=>i)) ≤ A+1:=by
    intro i; let q:Fin 1→Primary c G:=fun _=>i; obtain ⟨hp,he⟩:=hP 0 (by decide) q; refine ⟨?_, hp.trans (by linarith only)⟩
    let a:=Uniform.entry P' 0 q; let b:=Uniform.entry (m-P') 0 q; rw [show Uniform.entry m _ _=a+b from ?_]
    · refine le_trans (b:=costU a+costU b) ?_ (add_le_add hp (he.trans (by assumption))); unfold costU; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=> abs_add_le ..
    unfold a b Uniform.entry; rw [iteratedFDeriv_sub_apply (f:=m) (g:=P') (show ContDiffAt ℝ (1:ℕ) m 0 from hY.of_le (by norm_num)) (hA.of_le (by norm_num))]; rw [_root_.sub_apply, add_sub_cancel]; try rfl
 have hz f C (hc:FloorZ (τ:=Uniform.Joint F G) f C)(ht:0≤C) : ContDiffAt ℝ 2 (f∘m-f∘P') 0∧|Uniform.entry (f∘m-f∘P') 0 j| ≤ D*C+2*D*((A+1)*C):=by
    have va: ContDiffAt ℝ 2 (f∘m) 0:= (hx.symm ▸ hc.stiff : ContDiffAt ℝ 2 f (m 0)).comp 0 hY; have vb:ContDiffAt ℝ 2 (f∘P') 0:= (hG.symm ▸ hc.stiff : ContDiffAt ℝ 2 f (P' 0)).comp 0 hA
    rw [yew va vb]; exact ⟨va.sub vb, roll_E hc hx hG hY hA ht hxM (fun i hi j=> (hP i hi j).2) j⟩
 have hN(v:ℝ)(hv:0<v):0 ≤Newt.fareX G 2 2 t v S.patch.L:= mul_nonneg (Uniform.atomCost_nn hs hv _) (Uniform.count_pos (half_pos (Uniform.width_positive hv 2 S.patch.L))).le
 obtain ⟨hB,hB'⟩:=hz O _ h_o (mul_nonneg hm (hN _ h.width)); obtain ⟨hK,hS⟩:= hz N' C₀ hv hr
 have hU: ContDiffAt ℝ 2 T' 0:= (hG.symm ▸ he.stiff : ContDiffAt ℝ 2 E (P' 0)).comp 0 hA; have ht:=rise he hG hA (mul_nonneg (mul_nonneg (Real.exp_pos _).le hm) (hN _ (half_pos h.width))) hc (fun i hi j=> (hP i hi j).1) j
 have hv :ContDiffAt ℝ 2 Y' 0:=hb.const_smul (1/2:ℝ); have hV' : |Uniform.entry Y' 0 j| ≤ 6* V :=by
    let u:=Uniform.entry L 0 j; have he: Uniform.entry Y' 0 j=(1/2:ℝ)*u:=hiccup L _ _ (hb.of_le (by norm_num))
    rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤ 1/2)]; exact (mul_le_of_le_one_left (abs_nonneg _) (by norm_num)).trans hV
 refine ⟨((hB.sub hU).sub (hK.add hv)).congr_of_eventuallyEq hh,?_⟩
 have hm: |Uniform.entry (E'+Y') 0 j| ≤ _:= show _≤D*C₀+2*D*((A+1)*C₀)+6*V from by unfold Uniform.entry; erw [iteratedFDeriv_add_apply (f:=E') (g:=Y') (hK.of_le (by norm_num)) (hv.of_le (by norm_num))]; apply (abs_add_le ..).trans; exact add_le_add hS hV'
 unfold Uniform.entry; rw [(hh.iteratedFDeriv ℝ 2).eq_of_nhds]; exact collect (X:=D'-T') (hB.sub hU) (hK.add hv) j (collect hB hU j hB' ht) hm -- tune
end
end YM.CF.Souk
