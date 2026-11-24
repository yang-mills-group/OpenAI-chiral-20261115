import YM.CF.Continuum.BeamTilt
import YM.CF.Continuum.ChartTilt
import YM.CF.Continuum.PastureCoe

/-!
# Localize and pay; mixed gauge observable x matter stencil

Whole-box angles from Billhead are not enough: divide by cost of yield region. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter Metric Finset NormedSpace Cube SU Mint Mint.Roe Lattice RG Wilson Laurent Peaks Spire Brace Vault Dial Paige Pressure
open Rush Tulip Gall Graph Phase Fock Lat Flare Emu Skye Scree MeasureTheory Nacre Laic Girt Pastry Nova Branch Analysis
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
set_option quotPrecheck false

variable (F:GlowLeg)
variable {m B N:Side}{a b c w η r k z t t₀ μ x D L d K R s' E C y v vA u C' vB tQ tL tB r₀ C₀:ℝ}{J:Side}{j n n₀:ℕ}{O:Odd J.val}{Y:Pricing j J O (Thread j)}{P:Grasp Y B d}{hp:Pearl P}
variable (Q:Pic.Span hp K b v C' z s' n)(A:GramM (mid m B))(X:Loom (mid m B))(p:SkinT A X d)
variable (s:Site (mid m B))
local notation "Λ" => (mid m B)
local notation "nζ" => (mid m B).val
lemma compass_weight (H:Phys N)(S:Evaluation N)(i:Orbit N) : readLinear (compass N x*S) i H=reflectible N x i.1 • oneField i.1 H S:=by
 change inner ℂ (mateK N) (acts ((((reflectible N x i.1):ℂ) • (1:FC (Single N)))*S i.1) H)=_; rw [Algebra.smul_mul_assoc, one_mul,act_smul,inner_smul_right]; rfl
lemma tilt_uniform (U V: Bkg (More N))(x:Phys N)(s:Site N): oneField U x (glowRead F s)=oneField V x (glowRead F s):=by unfold oneField; rw [no_link F s U V]
def comparedToTilt (s:Site (mid m B)) (t₀:ℝ) (P': Grasp Y B d):= yieldAngle A t₀ • oneField (N:=mid m B) 1 (changeM (m:=m) P' (Kea.tax (needles Λ)) A.J.M) (glowRead F s)
def normalizedTilt (P':Grasp Y B d)(t₀:ℝ)(A:GramM (mid m B)) := yieldAngle A t₀ • Kea.AMP m P' (needles Λ) A.J.M
lemma tilt_start : comparedToTilt none A s t₀ P=normalizedTilt P t₀ A:=by unfold comparedToTilt; change _ • oneField 1 _ 1= _; rw [oneField_vac]; rfl

def inPocket (n:ℝ)(X y k C t K:ℝ) := X*y*rateLeg k+C*n^10*t*rateLeg (K*n) -- coarse/fine cost
open Sods
variable (W: Ledger R u η r C A)(H: Port Q k y C₀ tQ r₀ n₀)(g:C₀≤R)(h1:1 ≤ R)(ht: A.p.threshold≤r₀) (hw:0<w)(hw':w≤ A.funds.linear)(vK:0<vA)(ℓ:n₀≤(mid m B).val)
variable (dL:A.path.Bounds A.funds μ D L)(kL:0 ≤ A.beta) (hQ:pittance (mid m B) vA C≤1)(h:0≤ r)(hC:0≤ C) (ha:0<t)(t₁:t≤1)(hx:(mid m B).val^10*t≤v)(hx':(mid m B).val^10*t ≤ tQ)(fU:∀ U:Pane (mid m B), flags A.p.threshold U=∅→0<reflectible (mid m B) t₀ U→∃ F:Cart (More (mid m B)),lawnK (gauge F U) (Kea.tax (needles (mid m B))) t)(hV:∀ U:Pane (mid m B),flags A.p.threshold U=∅→HelpP U vA r)
local notation "C_u" => (Real.exp (flagBill Λ u η C-kinetic (More Λ) A.p D L A.beta w))
local notation "wT" => (compass Λ t₀)
local notation "Fζ"=>glowRead F s
local notation "TΛ" => recX P A X -- mention x
local notation "Ω"=> oneField (N:=Λ) 1 (changeM (m:=m) P (Kea.tax (needles Λ)) A.J.M) Fζ
local notation "ζΩ"=> Kea.angel m P A.J.M
local notation "ζD"=> (fun i:Orbit (mid m B)=> Graph.dim A i * reflectible Λ t₀ i.1)
local notation "rate"=> inPocket (mid m B).val (baton Λ u vA C k) y k C' t K
include Q A p h hC ha t₁ hx hx' fU hV ℓ W H g ht hw hw' h1 hQ vK kL dL
lemma pays_geometry (h0:0<t₀)(U:Orbit (mid m B)): ‖readLinear (wT * Fζ) U (recX P A X U) - (ζD U) • (Ω)‖ ≤ ζD U*(rate *ζΩ) + 45*C_u := by
 let n:=Λ; have t':0≤ reflectible n t₀ U.1:= reflectible_up ..; let f:=reflectible n t₀ U.1; have hX :0≤ (45:ℝ)*C_u:= by positivity
 rw [compass_weight]; by_cases d:f=0
 · change ‖f • _-(Graph.dim _ _*f) • _‖≤Graph.dim _ _*f*_+ _; -- tune grammar
   simpa only [d,mul_zero,zero_mul,zero_smul,sub_zero,norm_zero,zero_add] using hX
 let Y:=oneField U.1 (TΛ U) Fζ; let A':=Graph.beam A P X U; let V:= wT; let r':= rate; let rΩ:= Ω; have hd:0<f:= lt_of_le_of_ne t' (Ne.symm d); have hm:f≤1:=reflectible_cost h0 _; let sY:= past A U.1; have hsY:0 ≤ sY:= (Real.exp_pos _).le
 let c:=oneField U.1 A' Fζ; have h_Y:Y=sY • c:=by unfold Y; rw [porch,RCLike.real_smul_eq_coe_smul (K:=ℂ),oneField_scalar]; rfl
 change ‖f • Y - ((Graph.dim _ _)*f) • rΩ‖≤ (Graph.dim _ _)*f * (r'*ζΩ)+_
 rw [h_Y,smul_smul]; by_cases h:U∈Lace A -- fix T to U prevent shadow h
 · have hU:flags A.p.threshold U.1=∅:=h; rw [show Graph.dim A U=sY from (by unfold Graph.dim; rw [Set.indicator_of_mem h]),mul_comm sY, ←smul_sub,norm_smul]; rw [Real.norm_of_nonneg (mul_nonneg hd.le hsY)]; apply le_trans ?_ (le_add_of_nonneg_right hX); apply mul_le_mul_of_nonneg_left _ (mul_nonneg hd.le hsY)
   obtain ⟨G,Hf⟩:= fU U.1 hU hd; have v:= H.wear m ℓ U.1 A.J.M (needles Λ) _ _ (spiral _ (needlesSlow Λ)) ha t₁ hx' Hf
   have hxU:flags r₀ U.1=∅:=by
      rw [←subset_empty,←hU]; intro i q; obtain ⟨z,p,v'⟩:= (flags_spec ..).mp q; exact (flags_spec ..).mpr ⟨z,p, lt_of_le_of_lt ht v'⟩
   have hl := tilt_beam F Q A X p (H.site.trans ℓ) U W h h1 ‹0 ≤ r› vK.le (hV _ hU) hC hQ s H.sap.le H.lark.le v (fun i=>(H.draw _ ℓ U.1 hxU _ i).weigh g H.sap.le)
   let t':=oneField U.1 (changeM (m:=m) P U.1 A.J.M) Fζ; have hp:‖t'-rΩ‖ ≤ C'*nζ^10*t*ζΩ* rateLeg (K*nζ):=by unfold rΩ; rw [tilt_uniform F 1 U.1]; exact tilt_cost F Q A (H.site.trans ℓ) U ha t₁ hx G Hf s -- syntax
   exact ((show ‖c-rΩ‖ ≤ ‖c-t'‖+ ‖t'-rΩ‖ from (by simpa only [dist_eq_norm] using dist_triangle c t' rΩ)).trans (add_le_add hl hp)).trans_eq (by unfold r' inPocket; ring)
 rw [Graph.dim,Set.indicator_of_notMem h,zero_mul,zero_mul,zero_smul,sub_zero,norm_smul,zero_add,Real.norm_of_nonneg (mul_nonneg hd.le hsY)]; let Z':=flagBill Λ u η C; let Y':=kinetic (More Λ) A.p D L A.beta w; have hx:‖c‖≤ 45*Real.exp Z':=by
    obtain ⟨v,k,T⟩:=p.wave; let X_p:= cab A P X U; have hl : ‖A'‖ ≤ Real.exp Z':=(spentS _ _ X_p).trans (by rw [show ‖X_p‖= _ from (show ‖X_p‖=1 from (sea_g (Q.plan m (H.site.trans ℓ)).1 _ (T.paid U) _).2),mul_one]; exact extensive_mile W _ ‹0≤r› h1 hC ((P.broadness _ (Q.plan m (H.site.trans ℓ)).1 A.J.M).projection _ (T.paid U)))
    apply (norm_inner_le_norm ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_left hl (by norm_num)); rw [(tickB Λ).2,one_mul]; exact (spentS _ _ A').trans (mul_le_mul_of_nonneg_right (glowRead_cost F s _) (norm_nonneg _)) -- tune order
 have ht':sY ≤ Real.exp (-Y'):= Real.exp_le_exp.mpr (neg_le_neg (fullH dL A.p _ hw.le hw' kL h)); exact (mul_le_mul ((mul_le_of_le_one_left hsY hm).trans ht') hx (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by change _=45*Real.exp (Z'-Y'); rw [sub_eq_add_neg,Real.exp_add]; ring)
-- relative denominator cost. Using actual persisted E.v cancellation as in Square.relative
lemma harvest (h0:0<t₀): ‖moment (recX P A X) (wT * Fζ) - comparedToTilt F A s t₀ P‖ ≤ yieldAngle A t₀*(rate *ζΩ) +45*C_u := by
 have hxᵥ : Integrable (fun i=> Graph.dim A i*reflectible Λ t₀ i.1) (city (mid m B)) ∧ (∫ i, Graph.dim A i*reflectible Λ t₀ i.1∂city Λ)=yieldAngle A t₀:=by
    simp_rw [weight_is]; let f(i:Pane Λ):=priorWeight A i*reflectible Λ t₀ i; have hi:Integrable f (prior group (More Λ)):= ((env_priorWeight A dL).integrable _).mul_bdd (targetC Λ t₀).aestronglyMeasurable (c:=1) (Eventually.of_forall fun i=>(Real.norm_of_nonneg (reflectible_up ..)).trans_le (reflectible_cost h0 i)); apply And.intro _ (usesPrior f hi)
    have he := measurePreserving_fst («μ»:=prior group (More Λ)) («ν»:=depot Λ); exact Integrable.comp_measurable (g:=f) (μ:=city Λ) ((show (city Λ).map Prod.fst=_ from he.map_eq) ▸ hi) measurable_fst
 obtain ⟨v,k',T⟩:=p.wave; have z:=Girt.sailW A (bonB W dL) hp Q.stmt Q.eP Q.p _ X T (Q.plan m (H.site.trans ℓ)).1; have he: Integrable (denZ A P X) (city Λ):=Integrable.of_bound z.meas.aestronglyMeasurable _ (Eventually.of_forall z.cost.choose_spec); have hu:= ((show Integrable (recX P A X) (city Λ) from he.smul (Complex.exp (-A.v))))
 let f:= ζD; let wω:= Ω; let gq:=wT*Fζ; have t' : Integrable (fun i=>readLinear gq i (TΛ i)) (city Λ):= integrable_read hu gq ((mem_allObs ..).mp (fits_all (product_region (compass_local t₀) (glowRead_local F s)))).1; let t'x:= t'.sub (hxᵥ.1.smul_const wω); have pA:=hxᵥ.1.mul_const (rate * ζΩ); unfold moment comparedToTilt; rw [←hxᵥ.2,←integral_smul_const]; rw [←integral_sub t' (hxᵥ.1.smul_const (Ω)),←integral_mul_const]; refine (norm_integral_le_integral_norm _).trans ((integral_mono t'x.norm (pA.add (integrable_const (45*C_u))) (pays_geometry F Q A X p s W H g h1 ht hw hw' vK ℓ dL kL hQ h hC ha t₁ hx hx' fU hV h0)).trans_eq ?_)
 simp only [Pi.add_apply]; rw [integral_add pA (integrable_const _),integral_const, probReal_univ,one_smul]
end YM.CF.Window
