import YM.CF.Souk.Ivoire
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
section price
variable {A:Fish ι→ShelfQ τ}{P:Fish ι→ℝ→ShelfQ τ}{x:Fish ι}{M:ℝ}
lemma dizzy(h:PriceW A P 2 x C t)(hA:ContDiffAt ℝ 2 A x)(hp:0 ≤ C)(hM:0 ≤ M)(ht:t≤1/2)(v:Fin 2→ι) (hv:∀ u∈Isle,Vital (fun i:Fish ι=>keystone A P i u) x C (M*C)∧Vital (fun i:Fish ι=>tea_r (A i) (P i) u) x t (M*t)): ContDiffAt ℝ 2 (lastT A P 3) x∧ |Uniform.entry (lastT A P 3) x v| ≤ 40000*M*C*t^3:=by
 let X(z:Fish ι ×ℝ):= petX (A z.1) (P z.1) 3 z.2
 obtain ⟨hX,he⟩:= petals h hp ht (hA.of_le (by norm_num)) 3
 have ht':0 ≤ t:=(h.paid 0 ⟨le_rfl,zero_le_one⟩).2.nonneg
 refine ⟨(hX.writes.of_le (by norm_num)).congr_of_eventuallyEq he,?_⟩; unfold Uniform.entry; rw [(he.iteratedFDeriv ℝ 2).eq_of_nhds]; apply lib_b v hX _ (by positivity)
 intro s hs; obtain ⟨hS,hQ⟩:=hv s hs; let f(y):=tea_r (A y) (P y) s; let K(y:Fish ι):= keystone A P y s; let Q(y: Fish ι):= K y*(f y*f y*f y)*(1-f y)⁻¹
 have htR:= hS.lit ((hQ.lit hQ).lit hQ); have hB:= htR.lit (tyLower hQ ht) -- name
 rw [show (fun y: Fish ι=>X (y,s))=(fun y=>(Q y).trace) from ?_]
 · apply (TraceAt (X:=Q) hB v).trans; have he:0 ≤ M*C*t^3:=by positivity
   have hz: (20*(M*t)) * (4*C*(4*(4*t*t)*t)) ≤ (20*M)*(4*C*(4*(4*t*t)*t)):=by gcongr; exact mul_le_of_le_one_right hM (by linarith)
   linarith -- polynomial
 ext y; change (K y*(f y)^3*(1-f y)⁻¹).trace=(Q y).trace; rw [show f y ^ 3=f y*f y*f y from by rw [← pow_two]; exact pow_succ ..]
end price
variable {q:Chi}{k:S.Choices}{M:ℝ}
abbrev Taq (F:Forest S.ratio)(x:ℝ)(G: Gauge):= Rows.In x (bareStores S) F (G:=G)
lemma port_pow [DecidableEq ι](H:Neige.Shelf τ)(V:ι≃τ)(i:ℕ): (H.submatrix V V)^i=(H^i).submatrix V V:=by induction i with
 | zero=> rw [pow_zero,pow_zero,Matrix.submatrix_one_equiv];
 | succ i ih=> rw [pow_succ,pow_succ, ih,Matrix.submatrix_mul_equiv]
lemma p_trace(H:Neige.Shelf τ)(V:ι≃τ): (H.submatrix V V).trace=H.trace:=V.sum_comp H.diag
section shell
variable {W:Config G c→ ShelfQ (Taq F x G)}{P':Config G c→ℝ→ ShelfQ (Taq F x G)}
lemma tanaka (h: PriceW (W∘Vmove x (1:Config G c)) (P'∘Vmove x (1:Config G c)) n 0 C t)(hp:Protected n (W∘Vmove x (1:Config G c)) 0 D):
 let K(y:Mast G c)(z:ℝ):= lathe x (temp x) F (fun y=> P' y z) y; let A:=lathe x (temp x) F W
 PriceW A K n 0 (composeCost n C (Uniform.shade G)) (composeCost n t (Uniform.shade G)):=by
 intro P A; let E:= pageX (G:=G) F x; let B(y:Mast G c):=facadeX G (temp x • y); let Q:= hull G c
 have he(y:Mast G c): Vmove x (1:Config G c) (Q y)= B y:=by unfold B facadeX; rw [map_smul]
 have hv: Arc (uncurry P) n 0:=by
    let L:ShelfQ (Taq F x G) →L[ℝ] ShelfQ (Key F G):=LinearMap.toContinuousLinearMap { toFun:= fun x=> x.submatrix E E,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
    let q':=uncurry (P'∘Vmove x (1:Config G c)); let X(y:Mast G c×ℝ):= (Q y.1,y.2); have hh(y:Mast G c×ℝ): P y.1 y.2=L (q' (X y)):=by change _=(P' (Vmove x 1 (Q y.1)) _).submatrix E E; rw [he]
    intro s hs; have H(X':ℝ): X (0,X')=(0,X'):=by simp [X]
    have hX:ContDiffAt ℝ n X (0,s):=((Q.contDiff.contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst).prodMk contDiffAt_snd)
    exact (L.contDiff.contDiffAt.comp _ ((show ContDiffAt ℝ n q' (X (0,s)) from (H s).symm ▸ h.pre s hs).comp (f:=X) (0,s) hX)).congr_of_eventuallyEq (Eventually.of_forall hh)
 have hA:ContDiffAt ℝ n A 0:= steep (can_tags hp); obtain ⟨ha,hT⟩:=arcW hA hv
 have hz(y:Mast G c)(t): edgeM (A y) t=(edgeM (W (B y)) t).submatrix E E:=by unfold edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph; rw [submatrix_add,Pi.add_apply,Pi.add_apply,submatrix_one_equiv,submatrix_smul]; rfl
 refine ⟨hv,ha,hT,fun u hu=> ?_,fun u hu=>?_⟩
 · rw [hz,Matrix.det_submatrix_equiv_self,← he,map_zero]; exact h.heart u hu
 obtain ⟨h₁,h₂⟩:=h.paid u hu; constructor
 · apply (can_tags (X:=fun y=> W y*P' y u) h₁).germ; filter_upwards with y; apply congrArg paintO; unfold keystone lathe P A; rw [Matrix.submatrix_mul_equiv] -- orientation
 apply (can_tags (X:=fun y=>tea_r (W y) (P' y) u) h₂).germ; filter_upwards with y; apply congrArg paintO; unfold tea_r; rw [hz]; unfold lathe B P; rw [Matrix.submatrix_mul_equiv]; rw [submatrix_sub,Pi.sub_apply, Pi.sub_apply,submatrix_one_equiv] -- tune
lemma transfer_t (hr:Ready T x)(K':ℕ)(hA:Protected 2 (W∘Vmove x (1:Config G c)) 0 D)(h: PriceW (W∘Vmove x (1:Config G c)) (P'∘Vmove x (1:Config G c)) 2 0 C t)
 (hu:∀ V V':Config G c, Sample k V 1 K' (W V) k V' 1 (W V') ∧∀ t:ℝ,Sample k V 1 K' (P' V t) k V' 1 (P' V' t)) (hp:∀ V:Config G c, Names (W V) i)
 (he:composeCost 2 t (Uniform.shade G) ≤ 1/2)(v:Fin 2→Primary c G)(hb:K'+i≤l):
 let A:=fun y:Mast G c=>facadeX G (temp x • y); let X:= lastT (W∘A) (P'∘A) 3
 ContDiffAt ℝ 2 X 0 ∧ |Uniform.entry X 0 v| ≤ 40000*(raised G S.patch.L l)*(composeCost 2 C (Uniform.shade G))*(composeCost 2 t (Uniform.shade G))^3:=by
 intro A X; let U:=lathe x (temp x) F W; let P(y:Mast G c)(z:ℝ):= lathe x (temp x) F (fun y=>P' y z) y; let L(u):= composeCost 2 u (Uniform.shade G); have hP:PriceW U P 2 0 (L C) (L t):= tanaka h hA
 obtain ⟨h₁,h₂⟩:=hP.paid 0 ⟨le_rfl,zero_le_one⟩
 let J:= pageX (G:=G) F x; let M:=raised G S.patch.L l; have hm:0 ≤ M:=by unfold M raised; positivity
 have hz(u:ℝ)(y:Mast G c):keystone U P y u=lathe x (temp x) F (fun y=> W y*P' y u) y ∧ tea_r (U y) (P y) u= lathe x (temp x) F (fun z=>tea_r (W z) (P' z) u) y:=by
    unfold keystone U P tea_r; refine ⟨?_,?_⟩
    · unfold lathe; rw [submatrix_mul_equiv]
    unfold lathe; unfold edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph; rw [← show (1+u • W (A y)).submatrix J J=1+ u • (U y) from ?_,submatrix_mul_equiv]; rw [Matrix.submatrix_sub,Pi.sub_apply,Pi.sub_apply,Matrix.submatrix_one_equiv]
    rw [Matrix.submatrix_add,Pi.add_apply,Pi.add_apply,Matrix.submatrix_one_equiv,Matrix.submatrix_smul]; rfl
 have heq: X=lastT U P 3:=by
    ext1 y; unfold X lastT; dsimp only [Function.comp_apply]
    rw [← det_submatrix_equiv_self J (1+W (A y)),Matrix.submatrix_add,Pi.add_apply,Pi.add_apply,Matrix.submatrix_one_equiv]; congrm _ - ?_; refine Finset.sum_congr rfl fun i _=>?_; apply setIntegral_congr_fun measurableSet_Icc; intro u hu; dsimp only [grind]; rw [show U y * P y u= _ from (hz u y).1, (hz u y).2]
    change Matrix.trace (W (A y)*P' (A y) u * _^i)= Matrix.trace ((W (A y)*P' (A y) u).submatrix J J * ((tea_r (W (A y)) (P' (A y)) u).submatrix J J)^i); rw [port_pow _ J, submatrix_mul_equiv]; exact (p_trace _ J).symm
 rw [heq]; apply dizzy hP (by simpa using (steep (can_tags hA))) h₁.nonneg hm he
 intro u Hu; obtain ⟨hv,hZ⟩:= hP.paid u Hu
 have hh:=funext fun y=> (hz u y).1; have hp₂:=funext fun y=> (hz u y).2; rw [hh] at hv; rw [hp₂] at hZ; rw [hh,hp₂]
 refine ⟨⟨by simpa using (steep hv),hv.value,mul_nonneg hm hv.nonneg,fun i hi j=>typed_Note (scaleS hv (by omega) j) (tileBill hr (k:=k) (X:=fun y=> W y*P' y u) (s:=temp x) ?_ (hv.order (by omega)) j)⟩,⟨by simpa using steep hZ,hZ.value,mul_nonneg hm hZ.nonneg,fun i hi j=> typed_Note (scaleS hZ (by omega) j) (tileBill hr (k:=k) (X:=fun z=>tea_r (W z) (P' z) u) (s:=temp x) ?_ (hZ.order (by omega)) j)⟩⟩
 · intro y z; exact tile_mul (hu _ _).1 ((hu _ _).2 u) (hp _) (hp _) (by omega)
 intro y z; exact stone_s.less (tile_mul (stone_s.plus ((hu _ _).1.scaling u)) ((hu _ _).2 u) ((lanes_one _).plus ((hp _).scaling u)) ((lanes_one _).plus ((hp _).scaling u)) (by omega))
end shell
end YM.CF.Souk
