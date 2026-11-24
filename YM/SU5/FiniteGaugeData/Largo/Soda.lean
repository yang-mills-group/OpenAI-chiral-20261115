import YM.SU5.FiniteGaugeData.Largo.Vers
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat
open scoped Topology BigOperators Pointwise
variable (o:Rim)(p:Slab o)(r:ℝ) {K : Side}
-- helper geometry. Read time `last(3)`. Pin real slab, order mentor.
section
abbrev full {X:Type*} (o:Tang→X) (t:X) : Axis→X:= Fin.snoc o t
private lemma full_snoc {X:Type*}(o:Tang→X)(t:X):full o t= ![o 0,o 1,o 2,t]:=by funext i; fin_cases i <;> rfl
lemma foldBig {m:Type*} [AddCommMonoid m] (f:Axis→m): ∑ i,f i = (∑ i:Tang,f i.castSucc)+ f 3:= by rw [Fin.sum_univ_castSucc]; rfl
lemma foldBigP {m:Type*} [CommMonoid m] (f:Axis→m): ∏ i,f i = (∏ i:Tang,f i.castSucc)* f 3:= by rw [Fin.prod_univ_castSucc]; rfl
lemma full_last {X:Type*}(o:Tang→X)(t:X): full o t 3=t:=rfl
lemma full_before {X:Type*}(o:Tang→X)(t:X)(i:Tang): full o t i.castSucc=o i:=by unfold full; simp
-- use pi4 equiv often
abbrev back {X:Type*}(q:Axis→X):Tang→X:=fun i=> q i.castSucc
def meet {X:Type*} : (Tang→X)×X ≃ Four X where
 toFun a:= full a.1 a.2
 invFun q:= (back q,q 3)
 left_inv a:= Prod.ext (funext (fun i=> full_before a.1 a.2 i)) rfl
 right_inv q:= by funext i; fin_cases i <;> rfl
lemma full_back {X:Type*}(q:Axis→X): full (back q) (q 3)=q:= meet.right_inv _
abbrev floorPin (o:Rim)(z:ℝ):Momentum:= tmap (full o z)
lemma reelG : Continuous (fun x:Rim×ℝ=> floorPin x.1 x.2):=by apply continuous_pi; intro i; fin_cases i <;> simp_rw [floorPin, tmap, full_snoc] <;> fun_prop
local notation "F"=> floorPin o r
abbrev blendC (j:Cover): Four ℝ:= fun i=>scar ((full o r) i) (j i)
lemma tone_pin (j:Cover): floorPin o r+reciprocal j=tmap (blendC o r j):=by funext i; unfold floorPin reciprocal blendC; simp only [tmap, Pi.add_apply,scar,τ,ofReal_add,ofReal_mul,ofReal_ofNat,ofReal_intCast]
include p
lemma never_pin (j:Cover): pass (F+reciprocal j)≠0:=by
 simp_rw [tone_pin,pass,tmap]; norm_cast; let V:=blendC o r j; have he:V 0≠0:=abs_pos.mp (zero_lt_one.trans_le (origin_price (o 0) (j 0) (p _).1 (p _).2)); exact (lt_of_lt_of_le (sq_pos_of_ne_zero he) (Finset.single_le_sum (a:=0) (fun k _=>sq_nonneg (V k)) (mem_univ _))).ne'
lemma town_quote {x:ℝ}(p':|x|≤ Real.pi) : floorPin o x∈baseCube:=by
 refine ⟨tmap_physical _,fun i=>?_⟩; change |((tmap _) _).re|≤_; unfold tmap; rw [Complex.ofReal_re]; have hv(i:Tang):|o i| ≤ Real.pi:=by have he:=p i; rw [abs_le]; constructor <;> linarith [Real.pi_gt_three]; -- tune
 exact Fin.lastCases (motive:=fun i=>|full o x i| ≤ Real.pi) p' (fun i=> (full_before o x i).symm ▸ hv i) i
lemma moanHeight: melody (floorPin o r) 3= hymn o r:=by
 rw [melody, ← Equiv.tsum_eq meet,onActual o p]; refine tsum_congr ?_; intro i; simp_rw [tone_pin]; let o':=o; let q:=bush o i.1; let r':=scar r i.2; let W:= blendC o r (meet i); let f:=tmap W; have hp: ∑ a:Axis,(W a)^2=q^2+r'^2:=by rw [foldBig,bush_sphere]; simp only [W,blendC,full_before, meet, Equiv.coe_fn_mk,full_last, r']
 change leer f^8 * ((2:ℂ)* _ / pass f)=_; have h0:pass f=(q^2+r'^2:ℝ):=by unfold pass f tmap; exact_mod_cast hp; -- tune
 rw [h0]; unfold leer keyL; dsimp only;
 have hx(i:Axis): hsinc (f i / 2)=Real.sinc (W i/2):=by rw [show f i/2= ((W i/2:ℝ):ℂ) from (by push_cast; rfl), h_real]
 simp_rw [hx]; change (∏ i:Axis, ((Real.sinc (W i/2):ℝ):ℂ))^8 * (2 * ((r':ℝ):ℂ) / ((q^2+r'^2:ℝ):ℂ))=_; norm_cast; rw [←prod_pow,foldBigP]; unfold W blendC; simp only [meet, Equiv.coe_fn_mk,full_before,full_last]; unfold r' q floam; ring
end
section
-- A generic sequential pricing lemma (interfaces for dense accumulation when mass parameter & stride-of-phase vary independently).
variable {D X:Type*}[TopologicalSpace D][FirstCountableTopology D][MetricSpace X]{Q:Set D}
variable {F:ℕ→D→X}{L:D→ X}
open Classical in
lemma sweep_area (p:∀ x∈ Q,∀ d:ℕ→ℕ, Tendsto d atTop atTop→∀ s:ℕ→ D,(∀ᶠ i:ℕ in atTop,s i ∈ Q)→ Tendsto s atTop (𝓝 x)→ Tendsto (fun i=>F (d i) (s i)) atTop (𝓝 (L x))): ContinuousOn L Q:=by
 -- continuity suffices at each sequence x from Q. choose approximates d_i. not necessarily lower indices measurable.
 intro x w; apply Filter.tendsto_iff_seq_tendsto.2; intro s d
 let t:=p x w; have h :∀ᶠ i:ℕ in atTop,s i∈Q:= d.eventually self_mem_nhdsWithin; let z(i:ℕ):=Real.exp (-(i:ℝ)); have hv(i:ℕ): ∃ q:ℕ, i≤ q ∧ (s i∈Q→ dist (F q (s i)) (L (s i))≤ z i):= by
    by_cases h:s i∈ Q; · obtain ⟨q,k,v⟩:= (((p (s i) h id tendsto_id _ (Eventually.of_forall fun _=>h) tendsto_const_nhds).eventually (closedBall_mem_nhds _ (Real.exp_pos _))).and (eventually_ge_atTop i)).exists; exact ⟨q,v,fun _=> Metric.mem_closedBall.mp k⟩
    exact ⟨i,le_rfl,fun a=>(h a).elim⟩
 choose u c C using hv; have ht:Tendsto z atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
 let H:= p x w u (tendsto_atTop_mono c tendsto_id) s h (tendsto_nhds_of_tendsto_nhdsWithin d)
 apply Metric.tendsto_nhds.mpr; intro ε p; filter_upwards [ht.eventually (ge_mem_nhds (half_pos p)),H.eventually (ball_mem_nhds _ (half_pos p)),h] with i t Z f; have hx:=C i f; rw [dist_comm] at hx; change dist (L _) _<_; have hp:=mem_ball.mp Z; exact lt_of_le_of_lt (dist_triangle (L (s i)) (F (u i) (s i)) (L x)) (by linarith)
end
abbrev Foyer := {x:Rim×ℝ| Slab x.1 ∧ |x.2| ≤ Real.pi}
lemma inSession(a:Axis): ContinuousOn (fun y:Rim×ℝ=> melody (floorPin y.1 y.2) a) Foyer:= by
 let f(i:ℕ):Side:=⟨2*i+1,by omega⟩; apply sweep_area (F:=fun i y=> mixL 4 (f i) (floorPin y.1 y.2) a); intro x hx d p s h g
 apply harmony (M:=fun i=> f (d i)) (fun j=> ⟨_,rfl⟩) _ (reelG.continuousAt.tendsto.comp g) (fun i=> never_pin x.1 hx.1 x.2 i) _ (h.mono (fun i c=> town_quote _ c.1 c.2)); exact (show Tendsto (fun i=>(f i).val) atTop atTop from StrictMono.tendsto_atTop (strictMono_nat_of_lt_succ (by intro i; change 2*i+1 < _; simp [f]))).comp p -- tune
end YM.CF.Window.Largo
