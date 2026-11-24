import SatinPP.Lining
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid
open OS.Semigroup.Balloon SatinNucleus
-- retreat
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ(j)" => P.advocate 3 x j -- unused
local notation "G" j:max=> P.ManyF j (P.advocate 3 x j)
local notation "κ" j:max=> P.wealth j (P.advocate 3 x j)
local notation "U" j:max=> P.cartage j (P.advocate 3 x j)
local notation "H" j:max=> P.seasons j (P.advocate 3 x j)
local notation "E" j:max=> (H j).E
variable (f r n:ℕ) (v:ℕ→ℕ)(u:StrictMono v)(a: ℕ→ (ℕ×ℕ)→ℝ)(Q:ℕ → Coalition) {P₀:ℕ→P.Apron}
local notation "a'" => fun i:ℕ=> a i (f,r)
variable (W:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
local notation "C" k:max=> P.basePlay x f k
local notation "Ψ" k:max=> P.meshPose k (P.runP f k 1 0)
local notation "A!"=> P.invoiceV x f r r 1
local notation "B!" i:max=> P.invoiceV x f r (v i) (( (a') i:ℝ):ℂ)
local notation "Φ"=> P.flightCap f
local notation "Z"=> (fun _:Axis=> P.flightCap f)
-- CP10 provenance compare on moved clock
local notation "r★" i:max => ((P.rewardK f r:ℂ) * ( ((a') i:ℝ):ℂ)) -- syntax needs (a')
local notation "X'" i:max => (U 3) Z ((r★ i) • P.beam 3 x (C (v i)) Φ)
private lemma contractionE (S:Hilbert)(c:S.Op)(p:‖c‖≤ 1)(x y:S): dist (c x) (c y)≤ dist x y:=by rw [dist_eq_norm,← map_sub,dist_eq_norm]; exact (c.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) p)
local notation "T" q:max=> fun i=>P.pleading x f r i (q i) v a' u
include u
set_option linter.unusedSectionVars false in
private lemma limiting_ball {b:ℝ}(t:f≤ r)(h:P.reached f r)(p:∀ᶠ i in atTop,r≤ v i)(e:0<b)(R:∀ᶠ i in atTop, dist (B! i) A! ≤ b/16): ∀ᶠ i:ℕ in atTop, dist (X' i) A! ≤ b:=by
 let Y(i):= Ψ (v i); let Z₀:= Z
 let W:= U 3; let S:= H 3
 let f'(i:ℕ):= ((Φ)-Y i 3).toNNReal; have hu:Tendsto Y atTop (𝓝 Z):=P.offer_approaches f|>.comp u.tendsto_atTop
 have hx:Tendsto (fun i=>Z₀-Y i) atTop (𝓝 0):=by simpa only [Z₀,sub_self] using (tendsto_const_nhds (x:=Z)).sub hu
 let S₁:=fun x:ℝ≥0 × Vantage=> W x.2 (S.E x.1 A!); have hw:Tendsto f' atTop (𝓝 0):=by
    have he:= (tendsto_const_nhds (x:=Φ)).sub ((tendsto_pi_nhds.mp hu) 3)
    have hc:= (continuous_real_toNNReal.tendsto _).comp he
    change Tendsto f' atTop (𝓝 ((Φ)-(Φ)).toNNReal) at hc; simpa only [sub_self,Real.toNNReal_zero] using hc
 have he: Tendsto (fun i=> S₁ (f' i,Z₀-Y i)) atTop (𝓝 A!):=by
    have ht:(S₁) (0,0)= A!:= by unfold S₁ S W; dsimp only; rw [(H 3).eZero,P.cart_zero]; rfl
    have ht':Continuous S₁:= P.caravan 3 (P.advocate 3 x 3) Prod.snd _ continuous_snd ((S.continuousE A!).comp continuous_fst) -- tune
    exact (ht'.tendsto' _ _ ht).comp (hw.prodMk_nhds hx)
 filter_upwards [Metric.tendsto_nhds.mp he _ (show 0<b/2 from half_pos e), p, R] with i t' z z'
 refine le_trans (dist_triangle _ (S₁ (f' i,Z₀-Y i)) _) ?_; have hb: dist (X' i) (S₁ (f' i,Z₀-Y i)) ≤ b/16:= by
    rw [P.moves_invoice x f r v a t h z] -- u not used?
    exact (contractionE (G 3) (W (Z₀-Y i)) (P.cart_pay ..) _ _).trans ((contractionE (G 3) (S.E (f' i)) (S.shrinks _) _ _).trans z')
 linarith only [t',hb,e]
-- close and lift. cost at mean
omit u in
private lemma allied {X₁:Hilbert}(G': Coalition)(T': X₁)(Y:ℕ→ X₁) (b:ℝ)(p:∀ i∈G'.voters,dist (Y i) T'≤ b) : dist (∑ i∈ G'.voters,(G'.w i:ℂ) • Y i) T' ≤ b:=by
 letI := InnerProductSpace.rclikeToReal ℂ X₁
 exact (convex_closedBall T' b).sum_mem G'.signed G'.pledges p -- instance order

variable (g s:ℕ)
abbrev booth(i:ℕ) := P.rewardK f r * a i (f,r)
local notation "R0" i:max => P.booth g s a i
local notation "R1" i:max => P.booth f r a i
structure Offering(δ:ℝ):Prop where
 down:f ≤ r
 paid:P.reached f r
 loan:∀ᶠ i in atTop,dist (B! i) A! ≤ δ/16
 tint:P.Synchrony g f
 share:∃ b:ℝ,∃ c:ℕ→ℝ,Tendsto c atTop (𝓝 b) ∧ ∀ᶠ i:ℕ in atTop,R0 i=c i*(R1 i)
local notation "T0"=> fun i=>P.pleading x g s i (Q i) v (fun i=>a i (g,s)) u
local notation "X0" i:max=>(U 3) Z ((R0 i:ℂ) • P.beam 3 x (P.basePlay x g (v i)) Φ)
omit u in
private lemma jacket_eq {A B:P.Apron}(a:A.s=B.s)(b:A.u=B.u)(c:A.F=B.F)(d:A.S=B.S): A=B:=by
 cases A;cases B; cases a;cases b;cases c;cases d;rfl
lemma springs_ball {δ:ℝ}(t:P.Offering x f r v a g s δ)(e:0<δ)
  (m:Radiates P x T0 W): ∃ b:ℝ, dist ((U 3) Z ((κ 3) (W 3 [] Φ))) ((b:ℂ) • A!) ≤ δ*|b| := by
 obtain ⟨b,c,l,h⟩:= t.share
 refine ⟨b,le_of_forall_pos_le_add ?_⟩
 intro ε ε'
 have hu:= limiting_ball P x f r v u a t.down t.paid (u.tendsto_atTop.eventually_ge_atTop r) e t.loan
 have z:∀ᶠ i in atTop,dist (X0 i) ((b:ℂ) • A!) ≤ δ*|b|+ε:= by
    let R:=fun i=>δ*|c i|+|c i-b| *‖A!‖
    have ht:Tendsto R atTop (𝓝 (δ*|b|)):= by
       simpa only [sub_self,abs_zero,zero_mul,add_zero] using (l.abs.const_mul δ).add ((l.sub_const b).abs.mul_const ‖A!‖)
    filter_upwards [h,u.tendsto_atTop.eventually t.tint,hu,ht.eventually (gt_mem_nhds (lt_add_of_pos_right (δ*|b|) ε'))] with i B tint M R'
    have ee:X0 i=(c i:ℂ) • (X' i):=by
       have eh:P.basePlay x g (v i)= C (v i):=jacket_eq P rfl rfl (congrArg (P.centeredQ x _) tint) (congrArg frameOne tint)
       rw [B,Complex.ofReal_mul,mul_smul,map_smul,eh];unfold booth;rw [Complex.ofReal_mul]
    rw [ee]
    refine (dist_triangle _ ((c i:ℂ) • A!) _).trans (le_trans ?_ R'.le)
    rw [dist_eq_norm,dist_eq_norm,←smul_sub,←sub_smul, norm_smul, norm_smul, Complex.norm_real,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    rw [dist_eq_norm] at M
    unfold R;rw [mul_comm δ];exact add_le_add_left (mul_le_mul_of_nonneg_left M (abs_nonneg _)) _
 let T₀:=T0
 let Y(i:ℕ):= P.beam 3 x ((T₀ i).pivot P []) (Φ)
 let QX:= (U 3) Z; have ht:Tendsto (fun i=>QX (Y i)) atTop (𝓝 (QX ((κ 3) (W 3 [] Φ)))):= (QX.continuous.tendsto _).comp (m.port 3 [] (P.flight_pos f) tendsto_const_nhds)
 refine le_of_tendsto (ht.dist (tendsto_const_nhds (x:= ((b:ℂ) • A!)))) ?_
 obtain ⟨b',hp⟩:= eventually_atTop.mp z
 filter_upwards [(m.slender 3).eventually (gt_mem_nhds (P.flight_pos f)),eventually_ge_atTop b'] with i v0 p'
 have hw:QX (Y i)= ∑ k∈ (Q i).voters,((Q i).w k:ℂ) • X0 (i+k):=by
    unfold Y; rw [P.beam_bank, P.pleading_p x 3 g s i _ v u _ _ _ ((P.pleading_w ..).symm.le.trans (le_of_lt v0)),map_sum,map_sum]
    refine sum_congr rfl fun k _=>?_
    rw [Apron.pivot_nil]; unfold QX; simp only [P.beam_bank,map_smul,Complex.ofReal_mul,mul_smul,booth]
 change dist (QX (Y i)) _ ≤ _; rw [hw]; exact allied (X₁:= G 3) (Q i) _ (fun k=>X0 (i+k)) _ fun k _=> hp (i+k) (by omega)

local notation "V☆" t:max=> (κ 3) (W 3 [] t)
def Pennant:Prop:=∀t:ℝ,t>0→ V☆ t ≠0 
omit u in lemma medal {j k:ℕ}
  (w:∀ t:ℝ,t>0→LinearIndependent ℂ (fun i:SatinJets.Seven=>P.epochW x j k i (V☆ t))):P.Pennant x W :=
 fun t h r=> LinearIndependent.ne_zero 0 (w t h) (by rw [r];unfold epochW;rw [map_zero])
lemma recoups {δ:ℝ}(t:P.Offering x (P.pointEra r) r v a g s δ)
  (e:0<δ)(m:Radiates P x T0 W)(w:P.Pennant x W):
  P.CandleLoan x W r δ:=by
 obtain ⟨b,h⟩:=P.springs_ball x _ _ v u a Q W _ _ t e m
 refine ⟨b,fun z=>w (P.lengthP r) (P.lengthP_pos r) ?_,h⟩
 rw [z,Complex.ofReal_zero,zero_smul,abs_zero,mul_zero,dist_zero_right,P.cart_norm] at h
 exact norm_le_zero_iff.mp h

