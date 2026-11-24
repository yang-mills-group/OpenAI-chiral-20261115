import YM.SU5.May.LunarEpoch
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding May.Lunar
open Push.SectorMeasure
open Advance.Depths
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (m t s R:ℕ) (P:Ramp)
open May.TorqueBeam Therapies Advance.Whorl FloeRoom
open PhaseChoice
local notation "σ" m:max=> (((Y.ir m).val):ℝ)
local notation "D" i:max=> flowK Y i
local notation "T" i:max=> turnUp Y i
local notation "Pμ" i:max => precisionAt Λ (turnUp Y i)
abbrev gaze := May.Lunar.age
variable (x:Cover)(r:ℝ≥0)(W:Finset Cover)
lemma g_p (r':ℕ)(i:Axis): gaze x i=precisionAt Λ r'* (location Λ r' (nodeC x) i):=by
 have hx:0<precisionAt Λ r':= Tapestry.positiveScale ..; unfold gaze location; rw [nodePrint, age_at]; field_simp; ring
variable (h:0<r) (u: PhaseChoice.SupportedPhysically Λ l s W (Acres P r))
local notation "Wμ" i:max=> volumeAround Λ l (T i - s) W
private lemma earth_b : 1 ≤ bindingC Λ:=by have he:=half_bill; have hv: (1:ℝ) ≤ Λ.block.val:=by exact_mod_cast (show 1 ≤ Λ.block.val from Λ.block.property)
                                           unfold bindingC; nlinarith only [he,hv]
include h u
lemma stint : ∀ᶠ m in atTop,∀ a:ℕ,T m=s+a→∀ x:Cover,nodeC x∈ volumeAround Λ l a W→Legible P (𝗠 m (T m)) x∧‖gaze x‖ ≤hazySize (D m) (𝗠 m (T m)):= by
 obtain ⟨B,H0,w⟩:= PhaseChoice.canBound Λ l s W
 let YG:= zenithL Y; let τ:ℝ:= halfer*r; have hc:0<τ:= mul_pos halfLegal (NNReal.coe_pos.mpr h); let ht:= (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (flow_grows Y)
 filter_upwards [ht.eventually_ge_atTop 10, ((tendsto_pow_atTop (show (10:ℕ)≠0 from (by decide))).comp ht).eventually_ge_atTop (2*B), (YG.const_mul_atTop hc).eventually_gt_atTop (20:ℝ)] with m hm1 hm2 hi a g x X; let n:= T m; let y:Axis→ℝ:= location Λ (T m) (nodeC x); have hy(i:Axis): gaze x i=(Pμ m)*y i:= g_p x _ i; have hs:(r:ℝ) < landN P y:= (by unfold y; rw [g]; exact (show (r:ℝ)< landN P (location Λ (s+a) (nodeC x)) from (u.persists a).contains X))
 have hB(i:Axis): |y i| ≤ B:= (by unfold y; rw [g]; exact (w.persists a).contains X i); let L:ℝ:= Pμ m; let D':ℝ:= (D m); let N:ℝ:= rimB (𝗠 m n); let ρ:ℝ:= σ m; have hℓ:0<L:= Tapestry.positiveScale _ _
 have hV:0<N:= rimH _; have h1:(10:ℝ) ≤ D':=hm1; have h2:2*B ≤ D'^10:=hm2; have H':0<D':=(show (0:ℝ)<10 by norm_num).trans_le h1; have hZ:‖gaze x‖≤ hazySize (D m) (𝗠 m (T m)):=by
    obtain ⟨i,hx⟩:= ArchiveK.one_arm (gaze x); refine hx.trans ?_; rw [hy,abs_mul, abs_of_nonneg hℓ.le]; unfold hazySize; apply (le_div_iff₀ (show 0< D'^10 from (by positivity))).2; change 2*(L*|y i|)*_ ≤ N; refine le_trans (mul_le_mul_of_nonneg_right (show 2*(L*|y i|) ≤ L*(2*B) from (by nlinarith only [mul_le_mul_of_nonneg_left (hB i) hℓ.le])) (show 0≤D'^10 from (by positivity))) ?_
    have hv:D'^20 ≤ρ:= earth_m Y m; rw [mul_assoc L]; refine le_trans (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right h2 (show 0≤ D'^10 from (by positivity))).trans (le_trans (le_of_eq (b:=D'^20) (by ring)) hv)) hℓ.le) ?_; rw [show N=bindingC Λ*ρ*L from ocean_l ..,mul_comm _ L]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by unfold ρ; positivity) earth_b) hℓ.le -- rw mul_comm _ L may rewrite y side.
 refine ⟨⟨?_,?_⟩, hZ⟩; · unfold faceN; rw [chopped,hy,hy]; change (r:ℝ) < y P.a+y P.b at hs; apply lt_trans (show 20 <τ*L from hi); unfold τ; exact lt_of_le_of_lt (le_of_eq (show _=halfer*(L*(r:ℝ)) from (by ring))) (mul_lt_mul_of_pos_left (show L*(r:ℝ) < L*(y P.a)+L*(y P.b) from ((mul_lt_mul_of_pos_left hs hℓ).trans_eq (mul_add ..))) halfLegal) -- mul_right_comm formula likely wrong
 change lengthT P (gaze x)< N /8; apply lt_of_le_of_lt ((le_abs_self _).trans ((show |lengthT P (gaze x)| ≤ _ from abs_real_inner_le_norm ..).trans (show ‖tilted P‖ * ‖gaze x‖ ≤ hazySize (D m) (𝗠 m (T m)) from (by rw [rulerL P,one_mul]; exact hZ)))) -- probe
 change N/D'^10 < N/8; apply div_lt_div_of_pos_left hV (by norm_num) (_); exact lt_of_lt_of_le ((show (8:ℝ)<10 by norm_num).trans_le h1) (by nth_rw 1 [←pow_one D']; exact pow_le_pow_right₀ (by linarith) (by decide : (1:ℕ) ≤10))
omit h u
lemma horizonT(m s:ℕ): Tendsto (fun t:ℕ=>(freshBook Y m t s).M.val) atTop atTop:= by
 let f(i:ℕ):= (freshBook Y m i s).M
 have hg:1<Λ.R.L.val:=by have he:= Λ.R.coarse; omega
 have hf: Tendsto (fun t:ℕ=>Λ.R.L.val^t) atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt hg
 refine tendsto_atTop.mpr fun R=>?_ ; obtain ⟨d,p⟩:=(hf.eventually_ge_atTop R.val).exists
 filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+d)] with v g
 have he(j i:ℕ)(h:i+j ≤ Y.uv v): Λ.R.L.val^j ≤ (freshBook Y m v i).M.val.val:=by
    induction j generalizing i with | zero=> exact (freshBook Y m v i).M.val.property| succ j ih=> have hp:(freshBook Y m v i).M=upMale Λ.R.L Λ.R.odd_side (freshBook Y m v (i+1)).M:= ((projectA Y m v).last.pass i (by omega)).grown; rw [hp,pow_succ']; exact Nat.mul_le_mul_left Λ.R.L.val (ih (i+1) (by omega))
 exact p.trans (he _ _ g)
include u h
lemma wagesK : able Y s P level W:=by
 have H:= (flow_grows Y).eventually (rebased (K:=atTop (α:=ℕ)) P);
 filter_upwards [stint Y s P r W h u,H,fundsReb Y P] with m p j Q a β; have v:rimB (𝗠 m (s+a))=rimB (𝗠 m (T m)):=by rw [β]
 let f(i:ℕ):= (freshBook Y m i (s+a)).M
 filter_upwards [ j (𝗠 m (s+a)) (volumeAround Λ l a W) (v.symm ▸ Q.1) (v.symm ▸ Q.2.1) (Vale.val_e ..) (by intro x y; exact (β ▸ p a β x y)) f (horizonT Y m (s+a))] with i x; intro b y z p; rw [Λ.kJ]; apply le_trans ?_ (x b y z p); apply neg_le_neg; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); unfold gentle; rw [mul_comm (tuition ..)]; exact mul_le_mul_of_nonneg_left Q.2.2 (by positivity)
omit u
lemma Atlas : YieldPlate Y P r:= fun s W q=> ⟨level,level_p,wagesK Y s P r W h q⟩
#print axioms Atlas
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
