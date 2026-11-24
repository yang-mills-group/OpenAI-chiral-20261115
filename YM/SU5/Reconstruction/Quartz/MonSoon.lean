import YM.SU5.Reconstruction.Quartz.CascadeGate
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval ComplexOrder
open CrossedFrame Clasp Picket Lens Ravin BridgeClub Anvil ConePrice Sail
variable {a b:Axis}(p:b≠a) {H E K:Hilbert}(S:OS.Semigroup H a)(C:Clasp K H E)(B X Y W:H.Op)(γ s:ℝ)
local notation "Q"=>path a b
variable (N:ℝ)(x y:H) (d:ℝ≥0) (Z:ℂ→ H.Op)
local notation "XP"=> afterP (b:=b) S B x y
local notation "YP"=> beforeP (b:=b) S B x y
local notation "ξ"=> rateTime (b:=b) S B
local notation "c₁"=> (ceilingCost d)
local notation "H₁" i:max=> DivYield (b:=b) S B x y d Z i
local notation "co" i:max=> sightParam i
local notation "Dℝ"=> Ravin.D
open Complex
-- corner orientation of the other frame (negative s). Notice B/W demand a Full for Price usage only in Integrals, not in bottom CP internal purchase.
structure Powered : Prop where
 floor (s:ℝ): Z s= ascend (-s) C X
 ceil (s:ℝ): Z ((s:ℂ)+(κ:ℂ)*Complex.I)= ascend (-s) C W
 bound (z:ℂ)(p:z∈ Dℝ): ‖Z z‖≤ N
 wot(x y:H) : ContinuousOn (fun z=>inner ℂ x (Z z y)) Dℝ
 polar (x y:H): DifferentiableOn ℂ (fun z=> inner ℂ x (Z z y)) Dw
variable (h:Powered C X W N Z)
include h
lemma symphonic(n:ℕ): ContinuousOn (H₁ (co n)) Dℝ ∧ DifferentiableOn ℂ (H₁ (co n)) Dw:= by
 obtain ⟨M,v⟩:=Power d; let bB:= blue B x y N; have h0:(0:ℂ)∈ Dℝ:= ⟨⟨by norm_num,by norm_num⟩,⟨le_rfl,potential.le⟩⟩ -- tune
 have k:0≤N:= (norm_nonneg _).trans (h.bound 0 h0); have c0:0≤bB:=blue_back B x y k; have C0:0< co n:=by unfold sightParam; positivity
 have L:= cucumber (co n) M bB (crossprice d) (fun z=> XP (Z z)) C0 (crossprice_analytic (d:ℝ)) v c0 (fun z h=> (afterCont ..).aestronglyMeasurable) (fun z l=> blueL (b:=b) S B x y (Z z) (h.bound z l)) (fun v:Du=> h.wot x ((ξ) v y)) (fun v:Du=> h.polar x ((ξ) v y)) -- defeq after
 let u(z:ℂ):=Largo 0; have hy(z:ℂ)(v: Du): YP (Z z) v=inner ℂ (((ξ) v).adjoint x) (Z z y):= (ContinuousLinearMap.adjoint_inner_left ((ξ) v) (Z z y) x).symm
 have f:= cucumber (co n) 0 bB u (fun z v=> inner ℂ (((ξ) v).adjoint x) (Z z y)) C0 (differentiable_const _) (fun z t=> by simp [u,Forge,Eddy,Largo,pressure]) c0 ?_ (fun z p v=> (by rw [←hy]; exact blueR S B x y (Z z) (h.bound z p) v)) (fun v:Du=> h.wot _ y) (fun v:Du=> h.polar _ y)
 · simp_rw [← hy] at f; exact ⟨L.1.sub f.1, L.2.sub f.2⟩
 intro z k; simp_rw [← hy]; exact (beforeCont (b:=b) S B x y _).aestronglyMeasurable
lemma down_budget (n:ℕ)(z:ℂ)(q:z∈Dℝ) : ‖(H₁ (co n)) z‖≤ (2*Real.pi * blue B x y N)*Real.exp (sightParam n * ceilingCost d*z.im):= by
 let d':ℝ:= d; let i:=co n; have hi:0< i:=by unfold i sightParam; positivity
 let K₁:= blue B x y N; have hm:= h.bound z q; let k:=blue_back B x y ((norm_nonneg _).trans hm)
 apply (norm_sub_le ..).trans; have hL:= vat_score i (crossprice d' z) hi (XP (Z z)) _ k (afterCont ..|>.aestronglyMeasurable) (blueL S B x y _ hm); have hP:= (vat_score i (Largo 0) hi (YP (Z z)) _ k (beforeCont ..|>.aestronglyMeasurable) (blueR S B x y _ hm)).2
 apply le_trans (add_le_add hL.2 hP); let W₁:= i* ceilingCost d'*z.im; let C':= Real.pi*K₁; have hc:0≤C':=mul_nonneg (Real.pi_pos.le) k
 change C'* _+C'*_≤2*Real.pi*K₁*Real.exp W₁
 rw [show 2*Real.pi*K₁*Real.exp W₁=C'*Real.exp W₁+C'*Real.exp W₁ from (by unfold C'; ring)]; apply add_le_add <;> gcongr C'*Real.exp ?_
 · unfold W₁; exact (mul_le_mul_of_nonneg_left (wind z d' q) hi.le).trans_eq (mul_assoc ..).symm
 simp only[pressure,Eddy,Largo,Prod.fst_zero,Prod.snd_zero, ofReal_zero,zero_im, zero_pow (by norm_num : (2:ℕ)≠0),add_zero,mul_zero]; exact mul_nonneg (mul_nonneg hi.le (zero_le_one.trans (ceiling_ok ..))) (q.2.1)
noncomputable def cloud (s:ℝ):ℂ:= Real.pi • (afterP (b:=b) S B x y (ascend (-s) C X) (turning_shift d s) - beforeP (b:=b) S B x y (ascend (-s) C X) 0)
local notation "P₁"=> cloud (b:=b) S C B X x y d
omit h in
lemma clouds : Continuous (cloud (b:=b) S C B X x y d):= by
 unfold cloud; let f(s:ℝ):ℂ:= (XP (ascend (-s) C X) (turning_shift d s)- YP (ascend (-s) C X) 0); refine Continuous.const_smul (show Continuous f from ?_) Real.pi; unfold f; unfold afterP beforeP; simp_rw[mul_apply_eq_comp]; apply Continuous.sub
 · apply continuous_const.inner (ascentWalk C X (fun x:ℝ=>-x) continuous_id.neg _ _); apply rateAccess S B _ continuous_const _; unfold turning_shift; fun_prop
 apply continuous_const.inner (((ξ) 0).continuous.comp (ascentWalk C X (fun x:ℝ=>-x) continuous_id.neg _ continuous_const))
lemma gentle (s:ℝ): Tendsto (fun n=> (H₁ (co n)) s) atTop (𝓝 (P₁ s)):= by
 let v:=ascend (-s) C X; unfold DivYield; simp_rw [Powered.floor h s, price_rail]
 have hc:0≤‖v‖:=norm_nonneg _; unfold cloud; rw [smul_sub]; apply (festival (F:=XP v) _ _ (afterCont ..) (blueL S B x y _ le_rfl)).sub (festival (F:=YP v) _ _ (beforeCont ..) (blueR S B x y _ le_rfl)) -- F arg count tune syntax
variable {M:Set H.Op} (L:∀s:ℝ,∀ v:E4, boost C s * trans S v= trans S (Picket.move a b s v)* boost C s) (c:ℝ≥0) (v: Worth (b:=b) S C B (scud (d:ℝ) (6*ceilingCost d)) M)(w : Voices S (M:=M) W d c)
local notation "γ'"=> 6*ceilingCost d
include p L c v w
lemma kaleidoscope : ∃ C':ℝ, Ravin.Studies (fun n=> (H₁ (co n))) C' (ceilingCost d) := by
 let M':= 2*Real.pi*blue B x y N; let s':= capital (blue B x y (c:ℝ)) (d:ℝ) γ'; let C':= max M' s'
 have t:(0:ℂ)∈Dℝ:= ⟨⟨by norm_num,by norm_num⟩,⟨le_rfl,potential.le⟩⟩
 refine ⟨C',ceiling_ok d,(le_trans (?_ : 0≤ M') (le_max_left ..)), (fun i=>(symphonic (b:=b) S C B X W N x y d Z h i).1), (fun i=>(symphonic (b:=b) S C B X W N x y d Z h i).2),fun n z t=>?_,fun n z q e=>?_⟩
 · exact mul_nonneg (by positivity) (blue_back B x y ((norm_nonneg _).trans (h.bound 0 t)))
 · exact (down_budget (b:=b) S C B X W N x y d Z h n z t).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
 let s:=z.re
 have hp: z=(s:ℂ)+(κ:ℂ)*Complex.I:= Complex.ext (by simp[s]) (by simp only[add_im,mul_I_im,ofReal_im,ofReal_re,zero_add]; exact e)
 rw[hp]; unfold DivYield; rw [h.ceil]; apply le_trans (inCap p S C B W γ' s x y (L (-s)) d c v w (abs_le.mpr q.1) _ (by unfold sightParam;positivity)); exact mul_le_mul_of_nonneg_right (le_max_right ..) (go (sightParam n) _) -- powers order verify
where go (d t:ℝ) :0≤ surge d t:= (Real.exp_pos _).le
lemma basement : X * parcelUp S ((d:ℝ) • basis b) B= B *X:= by
 ext1 y; apply ext_inner_left ℂ; intro x
 obtain ⟨A,hA⟩:= kaleidoscope p S C B X W N x y d Z h L c v w
 have k:= Ravin.prize hA (gentle (b:=b) S C B X W N x y d Z h) (clouds ..)
 unfold cloud at k; rw [smul_eq_zero_iff_right Real.pi_pos.ne',sub_eq_zero] at k
 unfold beforeP afterP rateTime at k; rw [path0,parcel_zero,show path a b (turning_shift (↑d:ℝ) 0)=(d:ℝ) • basis b from ?_] at k; simpa only [neg_zero,ascend,boost_first,one_mul,star_one,mul_one] using k
 simp [path,turning_shift]; -- tune
end YM.Quartz.Waltz
