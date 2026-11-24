import Anomaly.Gab.Travel
/-!
 Price room OVER the K survival on normal unit charges. Reserve includes Gap minted costs,
 scale exponent > m and close to m+1. Deployment uses $D$ when gap algorithm with 
 chord $γ$, and can use arbitrary finite but pre-appointment cumulative costs after
 D. Also can pay implantation using any pre-stage.Flints.
 -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2 ε T:ℝ}{z:ℂ}
namespace SketchA
variable {u f δ q b a P:ℝ}
variable (g:0<q)
variable {Z F:ArcΦ × ℂ}
local notation "Zs"=> pκ.winA H
local notation "κρ"=> κprobe mintR L H (A*Q) w z
local notation "Lν"=> ((L.val:ℝ)⁻¹)
variable (Y':Bleak pκ L v0 v1 v2 A) (M:Melon L X Y z H Q A w)
variable (U:Markup L X Y z H Q A w K C v0 v1 v2 Z.1 F.1 Z.2 F.2) (h:pκ.winA H Z=0)(Hq:Q ≤ 2*q)
abbrev billGap (A C K:ℝ):= 2*far_C A*(|C| + paceY*|K|)
lemma gapV (A C K:ℝ): 0≤billGap A C K:=by unfold billGap; have ht:0 ≤ paceY:=zero_le_one.trans paceY_paid; exact mul_nonneg (mul_nonneg zero_le_two (far_ge _)) (by positivity) -- syntax tune
include Y' M h g U Hq
lemma reroute : let v:= ((q:ℂ)⁻¹) • pκ.winA H F;
   |K*κprobe mintR L H (A*Q) w z Z.1| ≤ billGap A C K * (((L.val:ℝ)⁻¹)^(m+1))*q ∧ ‖v‖ ≤ billGap A C K* (((L.val:ℝ)⁻¹)^(m+1)) ∧ (q:ℂ) • v=pκ.winA H F :=by
 intro v; let E':= Lν^(m+1); let r:= 2* far_C A; have hp:=far_ge A; have p:=Y' X Y z H Q w K C M Z.1 _ Z.2 F.2 U (show pκ.space _ Z.1=0 from congrArg Prod.fst h)
 have he: |κρ Z.1|≤ r*E'*q:=(p.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Hq (by positivity)) hp)).trans_eq (by unfold r E'; ring)
 have hv:‖pκ.space H F.1‖≤ paceY*(|K| *(r*E'*q)):= (pκ.pace ..).trans (Markup.pay_Y M U he)
 have h':0 ≤ paceY:=zero_le_one.trans paceY_paid
 have hu:0 ≤ r:=mul_nonneg zero_le_two hp; have x:0 ≤ E':=by unfold E'; positivity
 let T:= billGap A C K
 have hB :paceY*(|K| *(r*E'*q)) ≤ T * E'*q:=by unfold T billGap; change _≤ r* (|C|+paceY* |K|) * E' * q; nlinarith only [mul_nonneg hu (mul_nonneg (abs_nonneg C) (mul_nonneg x g.le))] -- unfold order
 refine ⟨?_,?_,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr g.ne') _⟩
 · rw [abs_mul]; apply le_trans (mul_le_mul_of_nonneg_left he (abs_nonneg K)); exact (le_mul_of_one_le_left (by positivity) paceY_paid).trans hB
 unfold v; rw [norm_smul,norm_inv,Complex.norm_real, Real.norm_of_nonneg g.le,Prod.norm_def]; apply le_trans (mul_le_mul_of_nonneg_left (max_le (hv.trans hB) ?_) (inv_nonneg.mpr g.le)) 
 · rw [show _ =_ from (show q⁻¹ * (T * E'*q)= T * E' from by field_simp)]
 have ht:= Markup.offset_pay M U he; rw [show Z.2=0 from congrArg Prod.snd h,sub_zero] at ht; refine ht.trans ?_; unfold T billGap; change _≤ r* (|C|+paceY* |K|) * E' * q; nlinarith only [mul_nonneg hu (mul_nonneg (mul_nonneg h' (abs_nonneg K)) (mul_nonneg x g.le))]
omit Y' M h g U Hq
-- d-member lower & lam tied
abbrev tiny :ℝ := (10:ℝ)⁻¹ ^ 20
abbrev γMuse (k:ℕ):ℝ:= k+(9/10:ℝ)
abbrev L_Muse (k:ℕ):ℝ:= k+(4/5:ℝ)
abbrev Raise_L (k:ℕ)(L:Side):ℝ:= (L.val:ℝ)^γMuse k
lemma γrise (k:ℕ)(U v:ℝ)(p:0<v) : Next_L (fun L=>let R:=Raise_L k L; R * (U *((L.val:ℝ)⁻¹)^(k+1)) ≤ v):=by
 let e:ℝ:=(k+1:ℕ)-γMuse k; have he:0<e:=by unfold e γMuse; push_cast; linarith
 let q:=tendsto_rpow_atTop he; obtain ⟨t,p'⟩:= (eventually_atTop.mp ((q.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (eventually_ge_atTop (U/v)))) -- tuple wrong tune
 filter_upwards [eventually_ge_atTop t] with n u L h; have hf:0 < (L.val:ℝ):=by positivity
 let a:ℝ:=L.val
 intro R
 have hv:a^γMuse k / a^(k+1:ℕ)= (a^e)⁻¹:=by rw [←Real.rpow_natCast,←Real.rpow_sub hf,←Real.rpow_neg hf.le,show γMuse k-(↑(k+1):ℝ)=-e from (by unfold e; ring)]
 have hp:= show U/v ≤ a^e from p' _ (le_trans u h)
 refine le_trans (Eq.le (show _=U/(a^e) from ?_)) ?_
 · rw [div_eq_mul_inv U,←hv]; change _*(U * a⁻¹^(k+1))=_; rw [inv_pow]; ring
 apply (div_le_iff₀ (Real.rpow_pos_of_pos hf e)).2; exact ((div_le_iff₀ p).mp hp).trans_eq (mul_comm ..)
lemma grows_E(k:ℕ)(U:ℝ) : Next_L (fun L=> U*(L.val:ℝ)^k ≤ (L.val:ℝ)^((k:ℝ)+tiny)):=by
 have hp:0 < tiny:=pow_pos (by positivity) _
 obtain ⟨t,p⟩:=eventually_atTop.mp (((tendsto_rpow_atTop hp).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (eventually_ge_atTop U)); filter_upwards [eventually_ge_atTop t] with n h L u
 rw [Real.rpow_add (by positivity),Real.rpow_natCast,mul_comm U]; exact mul_le_mul_of_nonneg_left (p _ (le_trans h u)) (by positivity)
end SketchA
end YM.CF.Py
