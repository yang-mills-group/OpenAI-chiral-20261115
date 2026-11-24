import YM.SU5.FiniteGaugeData.Reliance.Figure
import YM.CF.Vp929.Stage.Institute
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Sour Stockpile Test TestW QuiltB Lor Lilt Rill Haro
variable {Wk b0 b1 b2 b3 Aχ Γχ Bv r:ℝ}{n₀ n₁:ℕ} (s: Major V Wk b0 b1 b2 b3 Aχ Γχ n₀) {pW:WindV K.j 2}{X F:ℝ→ℝ}
local notation "κB"=> budS R Wk Pay pW.C
local notation "κS"=> wrc R Wk Pay pW.C h
local notation "Qβ"=> χPost K R Pay pW.C Wk Aχ Γχ
local notation "Qφ"=> χPrice K R Pay pW.C Wk Aχ Γχ
local notation "Qs" x:max => couponY K R s.k Aχ Γχ (Qφ x) x
variable (u:Outlook D c X F pW ag Cg Bv n₁)
variable (l:lobe (2*catap Wk) h (γ₀ HI b0 (Tenant.quota^2*b1) (Tenant.quota^2*b2) 0 h) HI)(hO:J.roomX ≤ b3)
variable (fx:FitB R.L.val K s.k Aχ Γχ Pay pW.C Wk)
local notation "κg"=> sprayM D.pilot R ag

variable {ψ₁ ψ₂ θ₁ θ₂ ξ ξ' Λr g₁ g₀ μp:ℝ} {N0:ℕ}{cs:stationary D c x ag Cg g₁ Bv n₁}{o:Pitching w D x}(Z0:Cellar N0 o p p' c (allF R.L x) ag Cg)(T:Weather cs Z0 pW g₀)
local notation "ε"=> (dleaf R.L x/1000)
local notation "εs"=> (εp R Pay pW.C x)
local notation "km"=> 2*((ηA R c x g₁ (κg x) h Pay g₀ (epoch x) K Γχ (κB x))+(Qs x))
local notation "κτ"=> SelfCert (epoch x) b0 b1 b2 (κS x) 0 Wk g₁ g₀ (κg x) pW D x c
local notation "EqΥ"=> (BudgetPoint.mass)
local notation "Ux"=> (κS x)
local notation "ξx"=> rainX R 2 x
include s D
include u hO l fx
lemma globalPrices : ∃ C:ℝ→ℝ, CapLaw R C ((strictEscrow V D.localPrice).choose+|D.I.pay|+1) ∧ sizeK R.L 2 (wrc R Wk Pay pW.C h)∧ ∀ᶠ x in atTop,∀ N:ℕ,(D.size+200+(n₀+1)+Test.perimeter R.L.val) ≤ N → Funded (wrc R Wk Pay pW.C h x) (|Qβ x|) (C x) x N J q h:=by
 obtain ⟨ψ,θ,α,ζ,ξ,φ,hθ,hξ,v,w⟩:= moodPaid s u l
 let m_(x:ℝ):= Qs x; have he':Chill_v m_:= chill_Y s.k s
 obtain ⟨μ,t,pκ⟩:= thaw s u hθ hξ (w.mono fun _ i=> i.fee) he';
 let d:=(strictEscrow V D.localPrice).choose+|D.I.pay|; have hp:0<d:=lt_of_lt_of_le (strictEscrow V D.localPrice).choose_spec.1 (le_add_of_nonneg_right (abs_nonneg _)); have Dd:=(strictEscrow V D.localPrice).choose_spec.2 D c
 let Cc(t:ℝ):= reachμ K R Aχ Γχ (ξ t) (capCost R t d) t (κB t)
 have ht₀: Tendsto (fun i:ℝ=> houseP (epoch i) K Aχ Γχ (κB i)) atTop (𝓝 0):=((Chill_a (R:=R) (C':=pW.C) (Pay:=Pay) s.k s).2.low (k:=1) (by omega)).spine -- pW binder instead R C'? tune
 have h_θ: sizeK R.L 1 ξ:= hθ
 have ht₁: Tendsto (fun i:ℝ=> rateΓ (epoch i) (ξ i) Sour.wΨ) atTop (𝓝 0):= by
   let U:= zeST HI ξ; let p:= (YM.CF.Py.fee_Q HI ξ h_θ).spine; let Q:= (show Tendsto U atTop (𝓝 0) from p)
   have ht:Tendsto (fun x=> (1-U x)⁻¹) atTop (𝓝 1):= by simpa only [sub_zero,inv_one] using ((tendsto_const_nhds (x:=(1:ℝ))).sub Q |>.inv₀ (show (1:ℝ)-0≠0 by norm_num))
   simp_rw [rateΓ, pow_zero,mul_one]; exact (show Tendsto (fun x=> ξ x*(1-U x)⁻¹) atTop (𝓝 0) from by simpa only [zero_mul] using h_θ.spine.mul ht) -- `apply` weird
 have hCap:CapLaw R Cc (d+1):=by
   refine ⟨by linarith,?_⟩
   let V:ℝ:=(R.L.val:ℝ)^4; filter_upwards [(ht₁.add ht₀).eventually (ge_mem_nhds (show 0+0<V by rw [add_zero]; unfold V; positivity))] with x p
   have he: Cc x ≤ V + capCost R x d := add_le_add_left (show rateΓ (epoch x) (ξ x) Sour.wΨ+houseP (epoch x) K Aχ Γχ (κB x) ≤ V from p) _ -- p type t, add_left !!! b argument check
   exact he.trans_eq (by unfold capCost V; ring)
 refine ⟨Cc,hCap,v,?_⟩
 filter_upwards [w, u.forwards, pκ, adhere s.k s D.high fx, Dd,(tenor_Q (1/1000) _ t (by norm_num)),staple (c:=c) (ag:=ag) (Cg:=Cg) (D:=D) s hO] with x w uX g Q e j s₀
 intro N n0; refine ⟨w.due.radius,fun m n l p p' h w' => ?_⟩
 obtain ⟨M,v⟩:= uX; obtain ⟨o,b,v'⟩:= v N (by omega) m n l p p' w'; obtain ⟨x',C,H⟩:= s₀ N (by omega) m n l p p' o b; obtain ⟨Y⟩:= H (κS x) w.due.radius
 obtain ⟨q,he⟩:=Q; apply assemble (ξ:=α x) (Aχ:=Aχ) (Γχ:=Γχ) s b v' (by omega) x' C w Y g.1 (e m n l o p p' ag Cg (X x) Bv _ _ b M pW _ v') _ q he; rw [g.2]; apply j.trans_eq; ring
omit u
open Sour
lemma appoint_with_cap :∃ R0 δ C:ℝ→ℝ,CapLaw R C ((strictEscrow V D.localPrice).choose+|D.I.pay|+1) ∧ ∀ (N0:ℕ), D.size+200+(n₀+1)+Test.perimeter R.L.val ≤ N0 → Appointed J q R0 δ C h N0:=by
 obtain ⟨a,b,n,x,g,v⟩:= Frame_exists
 obtain ⟨c,p,χπ,u,k⟩:= Weather.focus_exists (D:=D) v g pW 0
 obtain ⟨C,cap,p,hg⟩:= globalPrices s u l hO fx
 let δ(i:ℝ):= |χPost K R Pay pW.C Wk Aχ Γχ i|; have hP:Chill_v δ:=χ_tame s.k s; have hx:∀ᶠ x:ℝ in atTop,0≤δ x:= Eventually.of_forall fun _=>abs_nonneg _
 refine ⟨wrc R Wk Pay pW.C h,δ,C,cap,fun N0 z=> ?_⟩; have ht:= hg.mono (fun i p=> p _ z); obtain ⟨P,y,H,H'⟩:= supplyΛ ht hP hx; obtain ⟨y',u,q⟩:= ((SplitFlag.buy_retag V U W J h s.direct).and (eventually_ge_atTop y)).exists
 refine ⟨⟨P,y',?_,u N0,cutMono H' q le_rfl le_rfl⟩,hP,hx,p⟩; exact ⟨fun m n w x p p' u v=> H.provides _ _ _ _ _ _ (q.trans u) v, fun m n w x z p p' u' v' ht hs=> H.compare _ _ _ _ _ _ _ _ _ (q.trans ht) (q.trans hs)⟩
end Focus
end Pitching
end YM.CF.Py.Rate


#print axioms YM.CF.Py.Rate.Pitching.Focus.appoint_with_cap
