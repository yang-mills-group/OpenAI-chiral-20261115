import YM.SU5.WakeInvestment.Comparator
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

open Lamour.Bridge Celeste Clock Hookah
open Cliplet
open Window Buffered.Afterglow.Tower Ballad SitSpin
open Signal.Interval (separationCost)
variable {H:Real.exp 1≤ P.x} {χ d d':ℝ}
variable {I:Type*} [Fintype I] (u:I→Lead.Clan) (G:List I)(x:I→ Cover)(w:I→Twah.DirSpin)(R:ℕ)

variable {E A v:ℝ} {φ μ π κ:ℕ→ℕ} {E' : ℕ→ Buffered.Family (tent Y H) →ℂ}{X:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
variable {D₀:ℕ→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
open Lifted
open YM.Stationary (Gaia)
open Onyx SpinReceipt
abbrev Appoint (P:Preparation)(A:ℝ)(x:ℕ→ Cover)(y:Gaia): Prop := Tendsto (fun s:ℕ=>gaugeRise P s A (x s)) atTop (𝓝 y)
variable {φx:ℕ→ I→ Cover} {y:I→Gaia}
local notation "η_" P:max s:max => sPow P s A
local notation "R_" P:max s:max => zoomR P A s
lemma atOrigin (P:Preparation)(p:0<A) : Tendsto (fun s:ℕ=> gaugeRise P s A 0) atTop (𝓝 0) :=by
 let x : Gaia:= WithLp.toLp 2 (fun _ : Axis=> (1:ℝ)); let f:= (sPower_pay P p); have hp:= (tendsto_inv_atTop_zero.comp f).smul_const x; rw [zero_smul] at hp; apply hp.congr; intro s; ext i; change ((η_ P s)⁻¹ * 1)= ((nodeC 0 i:ℤ):ℝ)/(η_ P s); simp [nodeC,one_div]
lemma zeroSpin(s:ℕ)(P:Preparation): riseX (zoomR P A s) 0=0:=by ext i; change ((0:Cover) i:ℝ)/_ = 0; simp
lemma appoint_as (P:Preparation)(p:0<A)(x:ℕ→ Cover)(y:Gaia) : Appoint P A x y ↔ Tendsto (fun s:ℕ=> riseX (zoomR P A s) (x s)) atTop (𝓝 y):=by
 let Z(s):=gaugeRise P s A (x s); let z(s):=gaugeRise P s A 0; let t(s):=riseX (zoomR P A s) (x s); let q:=frayR P A; have hp(s):t s=q s • (Z s-z s):=by have hx:=delta_w (A:=A) s P (x s) 0; rw [zeroSpin,sub_zero] at hx; exact hx
 have hq:= fray_lift P p; have he:=atOrigin P p
 constructor
 · intro a
   have hx:= hq.smul ((show Tendsto Z atTop (𝓝 y) from a).sub he); rw [sub_zero,one_smul] at hx; exact hx.congr fun s=> (hp s).symm
 intro a; have ht:= ((hq.inv₀ one_ne_zero).smul a).add he; rw [inv_one,one_smul,add_zero] at ht; apply ht.congr; intro s; change (q s)⁻¹ • t s+z s=Z s; rw [hp,inv_smul_smul₀ (fray_p ..|>.ne'), sub_add_cancel]
lemma present_layout {P:Preparation}(p:0<A)(h:∀ i,Appoint P A (fun s=> φx s i) (y i)) (u:∀ i j, y i=y j →∀ᶠ s:ℕ in atTop, φx s i=φx s j): ∃ (B:ℕ) (d:ℝ),0<d ∧ ∀ᶠ s:ℕ in atTop,Twah.Spill (SitSpin.rest (φx s) w) B d (zoomR P A s):=by
 classical
 let J:= Twah.Cellz I; let Y(s:ℕ):I→Twah:= SitSpin.rest (φx s) w; let T (s:ℕ):= Twah.nearPoints (R_ P s) (Y s); let F:J→Gaia:= y ∘ Prod.fst; have hu(i:J): Tendsto (fun s:ℕ=> T s i) atTop (𝓝 (F i)):=by unfold T Y; simp_rw [spin_oasis]; exact (appoint_as P p _ (y i.1)).mp (h _)
 have ht(s:ℕ)(i:J):Twah.sitesX (Y s) i= φx s i.1:=by cases h:i.2<;> simp only [Twah.sitesX,Twah.oasis,h,↓reduceIte]; all_goals rfl
 obtain ⟨B,hB⟩:= (Filter.eventually_all.mpr (show ∀ i:J, ∀ᶠ B:ℕ in atTop, ‖F i‖<(B:ℝ) from fun i=> tendsto_natCast_atTop_atTop.eventually_gt_atTop _)).exists
 have he (i j:J) : ∀ᶠ d:ℝ in 𝓝[>] (0:ℝ), F i≠F j→ d< dist (F i) (F j):=by
    by_cases v:F i=F j; · exact Eventually.of_forall fun _ h=>False.elim (h v)
    exact eventually_nhdsWithin_of_eventually_nhds ((gt_mem_nhds (dist_pos.mpr v)).mono fun i h _=> h)
 obtain ⟨d,v,h'⟩:= ((show ∀ᶠ x:ℝ in 𝓝[>] 0,0<x from self_mem_nhdsWithin).and (Filter.eventually_all.mpr (fun i:J=> Filter.eventually_all.mpr (he i)))).exists; refine ⟨B,d,v,?_⟩
 have hy(i j:J):∀ᶠ s:ℕ in atTop,Twah.sitesX (Y s) i≠Twah.sitesX (Y s) j → d≤ dist (T s i) (T s j):=by
    by_cases e:F i=F j; · filter_upwards [u i.1 j.1 e] with s h t; exact False.elim (t (by rw [ht,ht,h]))
    filter_upwards [((hu i).dist (hu j)).eventually (le_mem_nhds (h' i j e))] with s g t; exact g
 have hk(i:J): ∀ᶠ s:ℕ in atTop, dist (T s i) 0 ≤ B:=by simp_rw [dist_zero_right]; exact (hu i).norm.eventually (ge_mem_nhds (hB i))
 exact (Filter.eventually_all.mpr hk).and (Filter.eventually_all.mpr (fun i:J=> Filter.eventually_all.mpr (hy i))) -- defeq orientation dist Gaia

lemma kernelPositions (P:Preparation)(p:0<A)(h:∀ i,Appoint P A (fun s=> φx s i) (y i))(t:∀ i j, y i=y j →∀ᶠ s:ℕ in atTop, φx s i=φx s j): Tendsto (fun s:ℕ=>wakeSum ((gaugeRise P s A) ∘ (φx s)) G u w) atTop (𝓝 (wakeSum y G u w)):=by
 let Y(s:ℕ)(i:I):=SitSpin.rest (φx s) w i; let y': Twah.Cellz I→ Gaia:=y ∘ Prod.fst
 have hu: Twah.riseUp Y (zoomR P A) y':=fun i=>by unfold Y; change Tendsto (fun s:ℕ=> Twah.nearPoints (zoomR P A s) (SitSpin.rest (φx s) w) i) _ _; simp_rw [spin_oasis]; exact (appoint_as P p _ _).mp (h i.1) -- need p
 have hp: Twah.plateau Y y' :=by
    intro i j q; filter_upwards [t i.1 j.1 q] with s r; have he(i:Twah.Cellz I): Twah.crumbs Y s i=φx s i.1:=by obtain ⟨i,b⟩:=i; cases b<;> rfl
    rw [he,he,r]
 let c:ℕ→ℂ:=fun s=> (frayR P A s:ℂ)^3 / 2; have hv:Tendsto (fun s=>c s^G.length) atTop (𝓝 ((1/2:ℂ)^G.length)):= by
    have hF := (Complex.continuous_ofReal.continuousAt.tendsto.comp (fray_lift P p)).pow 3; unfold c; simpa using (hF.div_const 2).pow G.length
 have hf:= hv.mul (Twah.witnessFlows u Y G (zoomR P A) y' w hu hp); apply hf.congr; intro s; exact (calibrated ..).symm
variable (V:Universal Y H φ μ X E') (Q:Coherent (i:=φ) (k:=μ) (E:=E') Y H D₀ π κ)
include V Q
lemma revenue_limit (J:Investment P E v)(L_:Dispatchers P)(K:Meritorious P) (p:0<A)(h:∀ i,Appoint P A (fun s=> φx s i) (y i))(t:∀ i j, y i=y j →∀ᶠ s:ℕ in atTop, φx s i=φx s j):
    Tendsto (fun s:ℕ=> E' s (insideJar P (tent Y H) u G (φx s) w A s)) atTop (𝓝 (wakeSum y G u w)):=by
 let f(s:ℕ):= E' s (insideJar P (tent Y H) u G (φx s) w A s); let Z(s:ℕ):= wakeSum ((gaugeRise P s A)∘φx s) G u w
 obtain ⟨B,d,u',hx⟩:=present_layout w p h t
 have ht: Tendsto (fun s=> f s-Z s) atTop (𝓝 0):= by
    rw [tendsto_zero_iff_norm_tendsto_zero]; apply Metric.tendsto_nhds.mpr; intro ε e; filter_upwards [pill_uniform Y u G w V Q J L_ K p (half_pos e) u' B,hx] with s a v; change dist (‖f s - Z s‖) 0 < _; rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]; exact lt_of_le_of_lt (a _ v) (half_lt_self e)
 have he:= ht.add (kernelPositions u G w P p h t); rw [zero_add] at he; exact he.congr fun s=> sub_add_cancel (f s) (Z s)
#print axioms revenue_limit
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
