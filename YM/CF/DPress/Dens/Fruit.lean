import YM.CF.DPress.Dens.Pear
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Cap Graph Window Mint Period
namespace Quant
local notation "Hx"=> hat R.L x
variable (Z: Lore M B R A.μ)
open BPress Fixed
local notation "Vm"=> cell M B R.L i
local notation "U_A"=> Λ.w (hat R.L x i)
section
lemma meal {N:Side}(X: Pane N→ FC (Single N))(b d :ℝ) (h:∀ i, ‖X i‖≤ b)(F:Orbit N→Phys N)(g:∀ i, ‖F i‖≤ d) : ‖Fixed.functional F X‖ ≤ b*d:=by
 have he(v:Orbit N): ‖integrand X F v‖ ≤ b*d:=by
    let p:= (tickB N); have ht:‖mateK N‖=1:=p.2; let H:=norm_inner_le_norm (𝕜:=ℂ) (mateK N) (acts (X v.1) (F v)); rw [ht,one_mul] at H; refine H.trans ((Graph.spentS _ _ _).trans (mul_le_mul (h _) (g _) (norm_nonneg _) ((norm_nonneg _).trans (h 1))))
 change ‖∫ x, BPress.integrand X F x ∂city _‖≤_; simpa [measureReal_def] using norm_integral_le_of_norm_le_const (μ:=city N) (f:=integrand X F) (Eventually.of_forall he) -- maybe open.measure simp
open scoped YM.CF.BPress
lemma func_sub {d:ℝ}{N:Side}(X: Pane N→ FC (Single N))(P Q:Orbit N→Phys N)(p:Integrable P (city _))(q:Integrable Q (city _))(h: Measurable X)(t:∀ i, ‖X i‖≤ d) : Fixed.functional P X-Fixed.functional Q X=Fixed.functional (P-Q) X:=by
 have he(f:Orbit N→Phys N)(p: Integrable f (city N)): Integrable (integrand X f) (city _):=by
    let g:= fun z : FC (Single N) × Phys N => beamZ N (acts z.1 z.2); let S: Orbit N→ FC (Single N)× Phys N:=fun i=> (X i.1,f i); have ht:Continuous g:= continuous_const.inner ((acts_cont.comp continuous_fst).clm_apply continuous_snd); have W: AEStronglyMeasurable S (city N):= ((h.comp measurable_fst).aestronglyMeasurable).prodMk p.1; refine Integrable.mono' (g:= fun i=> d*‖f i‖) (p.norm.const_mul d) (show AEStronglyMeasurable (g ∘ S) (city _) from ht.comp_aestronglyMeasurable W) (Eventually.of_forall fun i=>?_ ); have hx:= norm_inner_le_norm (𝕜:=ℂ) (mateK N) (acts (X i.1) (f i)); rw [(tickB N).2,one_mul] at hx; exact hx.trans ((Graph.spentS _ _ _).trans (mul_le_mul_of_nonneg_right (t _) (norm_nonneg _)))
 change (∫ i, BPress.integrand X P i ∂city _) - (∫ i, integrand X Q i ∂city _)=_; rw [←integral_sub (he _ p) (he _ q)]; apply integral_congr_ae (Eventually.of_forall _); intro i; change _=inner ℂ _ (acts _ (P i-Q i)); rw [map_sub,inner_sub_right]; rfl
end
variable {Y:StarPS n} {Yc:VestM M B R} (p: LedgerL D Z Y Yc) (t:i≤ n)
include p t
-- exposed.Thin.Area.Amount expression exponent. Proof.M. Universe `$norm_then`, χ fit error.
lemma budget_ret (W: Pane (cell M B R.L i)→FC (Single (cell M B R.L i)))(c:ℝ)(v:∀ i,‖W i‖ ≤ c):‖BPress.reading U (D.vint Y Yc i) (F.Y i) W‖ ≤ c*Real.exp (CHeight (Δ:=Δ) i (Tew.tiny R (hat R.L x i))*((More (cell M B R.L i)).val:ℝ)^4):= meal W c _ v (recX U _ _) (true_trace D Z p t)
open scoped YM.CF.BPress
lemma charge (W: Pane (cell M B R.L i)→FC (Single (cell M B R.L i))) (e:ℝ)(X:LogH (cell M B R.L i))(u: Measurable W)(h:∀ i, ‖W i‖≤ e)(v:Born (i:=i) (k:=k) D X Yc) : ‖reading U (render D i X (D.b_T Y i)) (F.Y i) W-reading U (vint D Y Yc i) (F.Y i) W‖ ≤ e*(CostP (Λ:=Λ) (Δ:=Δ) M i * μx Λ x k i) :=by
 let A:= render D i X (D.b_T Y i); let Y' := vint D Y Yc i; let μA:= recX U A (F.Y i); let μY:= recX U Y' (F.Y i); have hp:Integrable μA (city _):=by apply Integrable.smul (f:=denZ A U _) (c:=Complex.exp (-A.v)) (?_:Integrable _ (city _)); exact Env.integrableX (Quant.envelope D X _ v.leg.1.toAccountY) _ -- tune .param
 have ht:Integrable μY (city _):=by apply Integrable.smul (c:=Complex.exp (-Y'.v)) (?_:Integrable (denZ _ U _) (city _)); exact Env.integrableX (Envelope D Z p t) _ -- 
 change ‖Fixed.functional μA W-Fixed.functional μY W‖≤_; rw [func_sub W μA μY hp ht u h]; exact meal W _ _ h (μA-μY) (densityD D Z p t v)
include D
omit p t
-- error UV Tendsto along k-depth explicitly.
lemma cap_Ω : Tendsto (fun k:ℕ=> μx Λ x k i) atTop (𝓝 0):=by
 let η:= ηD (A:=A); have hp:0 < η:= Thrift.ηpos; have he:η<1:= Λ.he.trans_lt (by norm_num); have hk:Tendsto (fun k:ℕ=>k-i) atTop atTop:= tendsto_atTop.mpr fun b=> (eventually_ge_atTop (b+i)).mono fun i k=>by omega
 apply squeeze_zero' (Eventually.of_forall fun k=> (D.positiveμ k i).le) (g:=fun k:ℕ=>η^(k-i)*(U_A/4)) ?_ ?_; · apply (eventually_ge_atTop i).mono; intro k v; exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (F.wealth v) (by norm_num)) (pow_nonneg hp.le _)
 simpa only [zero_mul, Function.comp_apply] using (((tendsto_pow_atTop_nhds_zero_of_lt_one hp.le he).comp hk).mul_const (Λ.w (hat R.L x i)/4))
lemma poster (a:ℕ): Tendsto (fun n:ℕ=> μx Λ x (n-a) i) atTop (𝓝 0):= Tendsto.comp (cap_Ω D) (tendsto_atTop.mpr fun b=> (eventually_ge_atTop (b+a)).mono fun n p=> by omega)
end Quant
end Crib
end FitD
end YM.CF.Py.Kay
