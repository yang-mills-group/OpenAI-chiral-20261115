import YM.CF.Wray.Kite
import YM.CF.Wray.Frost
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Iva Eire Font
variable (F:Pilot)(v:Stake.Isle)(w:Hos S n)
local notation "ζ"=>radiusB x
local notation "L_"=> R.L
local notation "C₀"=> Single (mid N B)
-- core prices.activation. net exp can pay also any PP pressure by renormalizing Pose.Bore.Se
variable {σ:ℝ}(Q₀:Pail.Payment R σ)(Z:Pluck R)
open Pail
local notation "v_"=> Scales.g G5
-- Pare Core at every requested power before µ. SAT measure, amplitude can grow Lento absorbed.
lemma invertC(P:Side):Lento fun x=> (Scales.g G5 P x)⁻¹:=by
 apply (Lento.yearB P).mono; let g(x):=Scales.g G5 P x
 filter_upwards [(year G5 P).eventually_ge_atTop 1, (minute G5 P).eventually (ge_mem_nhds zero_lt_one)] with x t v; let u:=y G5 P x; have hp:0< u:= zero_lt_one.trans_le t; have hv:0<g x:=Scales.gauge G5 P hp; have ht:u*g x^2=1:= yg2 G5 P hp
 change |(g x)⁻¹| ≤ |u|; rw [abs_of_pos (inv_pos.mpr hv),abs_of_pos hp, inv_le_iff_one_le_mul₀ hv]; change g x ≤ 1 at v; nlinarith only [ht,hv,hp,v,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left v hv.le) hp.le]
lemma upJ(k:ℕ)(F:Pilot)(K:Patch):sizeK K.L k fun x=> Real.exp (-eventB K F x/4):=by
 let Z':=K.L; let g(x):= (Scales.g G5 K.L x)^k; have hv:0< F.penalty/(64*4):= div_pos F.earn (by norm_num) -- unfold? remove
 refine ⟨0,?_⟩; filter_upwards [loomH ((invertC K.L).power k) _ hv K.L,(year G5 K.L).eventually_gt_atTop 0] with x h t
 let U:=eventB K F x/4; have hh:Real.exp U ≥ (g x)⁻¹:=by rw [show U=scaleM G5 K.L (F.penalty/(64*4)) x from (by unfold U eventB scaleM; ring)]; unfold g; rw [← inv_pow]; exact (le_abs_self _).trans h -- inv_pow orientation
 rw [abs_of_pos (Real.exp_pos _),neg_div,Real.exp_neg,pow_zero,mul_one]; exact (inv_anti₀ (inv_pos.mpr (pow_pos (Scales.gauge _ _ t) k)) hh).trans_eq (inv_inv _)
local notation "nK"=> l*radiusB x
lemma bore_s{Y:ℝ→ℝ}(h:BoreP Y)(a:ℝ)(p:0 < a):∃ n:ℕ,∀ j:ℕ,n≤ j→∀ᶠ x in atTop,|Y x|≤ a*(plow x)^j:=by
 obtain ⟨K,m,c,p'⟩:=h.pace; have ht:Tendsto plow atTop atTop:= tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto) -- tune Scales.b
 refine ⟨m+1,fun j l=>?_⟩; filter_upwards [p', (ht.const_mul_atTop p).eventually_ge_atTop K] with x hx hp; have hw:1≤ plow x:=Scales.size x; apply hx.trans; apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw l) p.le); rw [pow_succ]; exact (mul_le_mul_of_nonneg_right hp (pow_nonneg (by linarith) _)).trans_eq (by ring)
lemma bornP(P:Patch)(k:ℕ) :BoreP fun x=> (spanI P (k*radiusB x):ℝ):=by unfold spanI; push_cast; let h:= (BoreP.still (k:ℝ)).grip BoreP.radius_c; exact (((((h.join h).join (BoreP.still _)).self _).grip (BoreP.still _)).join (BoreP.still _))
abbrev boothX(R:Patch)(l:ℕ)(x:ℝ):= let N:=l*radiusB x; Fintype.card Axis *R.L.val^4*(N+3+(N+3)+1)^4
lemma boost(k:ℕ)(P:Patch):BoreP fun x=>(boothX P k x:ℝ):=by
 unfold boothX; push_cast; let h:= ((BoreP.still (k:ℝ)).grip BoreP.radius_c).join (BoreP.still 3); exact (BoreP.still _).grip ((((h.join h).join (BoreP.still _)).self _))
lemma snapped(k:ℕ)(L:Patch)(l:ℕ)(a C:ℝ)(h:0<a)(p:0<C){K:ℝ→ℝ}(hp:Lento K) :∃ n:ℕ,∀ j:ℕ,n≤ j→ sizeK L.L k (fun x=> K x * bloom (luceL L j x) (l*radiusB x) (luceL L j x) a C L):=by
 let F(x):= spanI L (l*radiusB x); let U(x):= Real.log C*(boothX L l x:ℝ); let f(x):= Real.exp (U x); have hu:Lento f:= (((BoreP.still _).grip (boost l L):BoreP U).lento_w.mono (Eventually.of_forall fun i=> by rw [show abs (f i)=Real.exp (U i) from abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; exact Real.exp_monotone (le_abs_self _)))
 let G(x):=Scales.g G5 L.L x; obtain ⟨D,m,z,v⟩:= (hp.times ((invertC L.L).power k)).times hu
 obtain ⟨r,hv⟩:= bore_s ((((BoreP.still D).grip (BoreP.relB.self m)).grip (bornP L l))) a h
 refine ⟨r,fun j w=>⟨0,?_⟩⟩; filter_upwards [(year G5 L.L).eventually_gt_atTop 0,hv j w,v] with x hY hx hu
 let n':= l*radiusB x; let c:= (Scales.g G5 L.L x)^k; have hc:0<c:=pow_pos (Scales.gauge _ _ hY) k; let u:= luceL L j x; have ht:1 ≤ u:=one_le_pow₀ (Scales.size x); have hz:0<(F x:ℝ):=Nat.cast_pos.mpr (by unfold F spanI; omega)
 let t:= a*u^2/(F x:ℝ); have he:D*plow x^m≤ t:= (le_div_iff₀ hz).mpr (((le_abs_self _).trans hx).trans (mul_le_mul_of_nonneg_left (le_self_pow₀ ht (by omega)) (le_of_lt (by assumption)))) -- h shadow 0<a still? rename
 change |K x*bloom u n' u a C L|≤ _; have hb:bloom u n' u a C L=Real.exp (-t)*f x:=by
    unfold bloom; congr 1; · simp only [t,F,n',neg_mul, neg_div]
    unfold f U; rw [mul_comm (Real.log C),Real.exp_nat_mul,Real.exp_log p] -- tune
 rw [hb,Real.exp_neg, pow_zero,mul_one]; have hU: |K x| *c⁻¹*f x ≤ Real.exp t:= by
    have h':∀ x:ℝ, (G x)⁻¹^k=(G x^k)⁻¹:= fun x=> inv_pow ..
    change |K x*((G x)⁻¹^k)* f x|≤ _ at hu; rw [h' x, abs_mul,abs_mul,abs_of_pos (inv_pos.mpr hc),abs_of_pos (Real.exp_pos _)] at hu; exact hu.trans (Real.exp_monotone he)
 change _≤ c; rw [abs_mul,abs_of_pos (mul_pos (inv_pos.mpr (Real.exp_pos _)) (Real.exp_pos _)), mul_comm (_⁻¹),← mul_assoc,← div_eq_mul_inv]; refine (div_le_iff₀ (Real.exp_pos _)).mpr ?_; calc
     _= c*(|K x| *c⁻¹*f x):=by field_simp; rfl
     _≤ _:= mul_le_mul_of_nonneg_left hU hc.le
end YM.CF.Wray
