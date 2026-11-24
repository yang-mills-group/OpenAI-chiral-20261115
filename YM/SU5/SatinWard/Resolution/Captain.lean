import YM.SU5.SatinWard.Resolution.Castle
import YM.SU5.SatinWard.Resolution.TunicW
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
variable {s:ℕ}(a b' c d:ℝ)
open BProof Pressure
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
local notation "K'"=> P.calibration
local notation "τ" s:max=> Pressure.temp (hat P.par.R.L P.par.x s)
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open Quire LampsQ LitCurrent Surplus Next.Rank Next.Rank.Spindle PSE
local notation "Δ★"=> P.run
local notation "H★"=> P.large
local notation "Lp"=> lapQ P.run
local notation "U'S" => WCash Δ★ s
open CasaF Ceremo Preparation.Tabletop
local notation "Y"=> P.run
local notation "ρ" v:max=> P.thresholdF v
local notation "X" v:max=> hat P.par.R.L P.par.x v
local notation "ts" v:max=> Pressure.temp (X v)
local notation "Ψ" v:max=> Real.sqrt (β v)
local notation "Ω" v:max=> (absol Δ★ v (Ψ v))
local notation "RR"=> Quire.grain
noncomputable abbrev dear (β:ℕ→ℝ) (p:P.Test)(v:ℕ) := (absol P.run v (Real.sqrt (β v)):ℂ) • p
abbrev bornPub(b C H A φ:ℝ)(j f0:ℕ)(χ:Chamber.Division)(η:Type)[Fintype η](s:ℕ)(x:Cover)(σ:ℕ→ℕ)(U:P.Test):Prop:=∃ Z F g,Tendsto g atTop atTop ∧ Ceremo P η s j f0 b C φ H A χ (σ ∘g) Z F∧ Z none x=U.val
variable (D H' A φ:ℝ) (g:P.NightCop)(x:Cover)(j f0:ℕ)(η:Type)[Fintype η]
private lemma cuedConst {P: Spine}{S:Finset Cover}{p:Family P.calibration}(v:InTest P.calibration true S false p) : BQueue S (fun i:ℕ=> p) p:=by
 obtain ⟨c,a⟩:=Journey.valuation P.run P.large v; refine BQueue.stay v (C:=c+1) ?_ (fun i u=>(a i u).trans (by linarith)); linarith only [show 0≤c from pay_nonneg (F:=p) a]
private lemma remane {n:ℕ→ℕ} {P:Spine}{S:Finset Cover}{x: ℕ→ Family P.calibration} {p:Family P.calibration}(a:BQueue S x p)(h:Tendsto n atTop atTop): BQueue S (x∘n) p:=by
 obtain ⟨f,t,⟨c,u,v,w⟩,g⟩:=a; exact ⟨fun _=> f _,t,⟨c,u,v,h.eventually w⟩,fun e p=> h.eventually (g e p) ⟩ -- prop tuple check grouping
include T g
lemma fortress (p:0<a)(r:ℕ)(χ:Chamber.Division) {h:ℝ}: ∃ E:ℝ, D ≤ E ∧0 < E∧ ∀ᶠ s:ℕ in atTop,∀ U:P.Test,0< lapQ P.run s→bornPub a h H' A φ j f0 χ η s x σ U → ∃ V m, Curie P.run s j χ E V m ∧
   ∀S:Finset Cover, pareQ (P.thresholdF s) (nodeC x) ⊆ S → WidthBudget S (budgetWidth (X s) r) →
    let Zβ:= Real.sqrt (β s); let X':=RR P.run V (nodeC x); ∀ (i:Axis)(z:P.Spectrum0 i),‖P.singleState i s z (dear β U s)-X'.issues (β s) (W s) Zβ‖≤ wane (X s) ∧
      ∀ (y:Tab ledgerDeck)(j:ticket S 1 (X s) 2 y), Tab.holds P.calibration Zβ y→ y.terms ≤ E → ‖P.singleState i s z ((dear β U s)*P.art (y.cookP Zβ P.calibration) (aux_test (y.thermal j Zβ))) -(mulT X' y).issues (β s) (W s) Zβ‖ ≤ wane (X s):=by
 let F:=T.purse.born; let O:=T.order.tendsto_atTop; obtain ⟨E,u,hE,w⟩:= Quire.gaff P.run P.large p χ x F.shearPos F.mail D φ j (b:=h); refine ⟨E,u,hE,?_⟩
 filter_upwards [(turnover P.par).eventually_ge_atTop 1,w, SlopeCharge.polish P r,SlopeCharge.banking P g 4 1 T zero_lt_one le_rfl] with s ht w gB gC U v h₀
 obtain ⟨Z,F',p₀,wp,C₁,u'⟩:=h₀; obtain ⟨Φ,G,M,v',m,o⟩:=C₁.anchor
 let pY:=Ceremo.earnedZ P η C₁; let t:=Ψ s; let DD:=dear β U s; let K0:=nodeC x
 let r₂:=σ ∘ p₀; let era:=P.nomadic ∘ r₂; let ere:=P.engine ∘ r₂; let r':= (Ω s:ℂ); let A(i:ℕ):= r' • G i none x
 have y': |t| ≤ Moon.fabric (Ω s):=Picker.permit P.run P.law P.history T.order.tendsto_atTop T.path_permanent s ht
 obtain ⟨f,rh⟩:= Picker.kings P.run P.law P.history T.order.tendsto_atTop T.path_permanent s; have hr':Tendsto r₂ atTop atTop:= O.comp wp
 let S0:=pareQ (ρ s) (nodeC x); have J₀:BQueue S0 A DD.val:=by
    have hS:pavilion (nodeC x) (hourBound Y s) ⊆ S0:= inclPav (nodeC x) _ (ρ s + petalD) (by unfold hourBound; unfold petalD; change (ρ s)+12 ≤_; omega)
    change BQueue S0 A (r' • U.val); rw [←u']; exact cueMono (cue_scale (m.bills none x) (fun _=>r') r' tendsto_const_nhds) hS
 let S(i:WCash P.run s):= RR P.run i (nodeC x); let Ψ'(i:ℕ):=Z none x
 let C (S:Finset Cover)(x:ℕ)(F:Buffered.Family P.calibration)(y:Tab (Sheds (ρ s) × Sheds (ρ s))):= AffordInk Y 4 1 s (era x) (ere x) P.large S F (Chip Y t (era x) (ere x) s y (f (p₀ x)))
 let C' (W:Finset Cover)(v:ℕ)(x:WCash Y s)(y:Tab ledgerDeck):= AffordInk Y 4 1 s (era v) (ere v) P.large W (A v*y.cookP t P.calibration) (Chip Y t (era v) (ere v) s (mulT (S x) y) (f (p₀ v)))
 let J (W: Finset Cover)(v:ℕ)(x: WCash Y s):= C W v (A v) (S x)∧ ∀ y:Tab ledgerDeck,ticket W 1 (X s) 2 y → Tab.holds P.calibration t y → y.terms ≤ E → C' W v x y
 let B(v:ℕ)(x: WCash Y s × ℂ):= Curie P.run s j χ E x.1 x.2 ∧ ∀W: Finset Cover, S0 ⊆ W→ J W v x.1
 have hw:∀ᶠ v in atTop,∃ ζ,B v ζ:=by
    filter_upwards [ (P.stockGo.comp hr').eventually w, wp.eventually rh] with i z ν; obtain ⟨b,d,Kx⟩:= (o i)
    obtain ⟨c,XB,hz,q⟩:= z (ere i) b.2.le d (Φ i); refine ⟨(c,XB),hz,fun W h=>?_⟩
    obtain ⟨e,p⟩:=q (Real.sqrt (β s)) y' (A i) W (InTest.mono (J₀.whereTo i) h) h (by refine Eq.trans (b:= (exhibit Y P.large s ((P.nomadic∘r₂) i)) (r' • G i none x)) rfl ?_; rw [map_smul]; apply Eq.trans _ (absolute_earn Y (Φ i) χ d x b.2.le v t).symm; exact congrArg (r' • ·) (m.learns x i none)) (f (p₀ i)) ν.2
    exact ⟨e,fun y s t u=> p _ s u t⟩
 obtain ⟨g,hq⟩:= eventually_atTop.mp hw; let n:=fun i:ℕ=> g+i; choose C'₀ cx using fun i:ℕ=> hq (n i) (by unfold n; omega)
 let f1:StrictMono n:=fun i j h=>by unfold n; omega
 obtain ⟨⟨z,m⟩,vX,xB,pX,m'⟩:= castle_sub (Eventually.of_forall fun i=> (cx i).1)
 let κ:=n∘vX; have hk:StrictMono κ:= f1.comp xB
 let w₀:=p₀ ∘ κ; have hθ:Tendsto w₀ atTop atTop:=wp.comp hk.tendsto_atTop
 let F'₀(i:ℕ):= (C'₀ (vX i)).1; have hx0(i:Sheds (ρ s) × Sheds (ρ s)) : Tendsto (fun k=>(S (F'₀ k)).tax i) atTop (𝓝 ((S z).tax i)) := ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp pX.fst_nhds i.1) i.2).mul_const _)
 let κf(J:Type)(a:Tab J): Prop:=True
 refine ⟨z,m,m',?_⟩; intro W u W' βx A' i k; obtain ⟨w,y,B,Jw,F⟩:=gB W W'; let E₁:= gC (σ∘w₀) (O.comp hθ); let q(i):= P.nomadic ((σ ∘ w₀) i); let t'(i):= P.engine ((σ ∘ w₀) i); let p₁:= A ∘ κ; have hp:BQueue W p₁ DD.val:=cueMono (remane J₀ hk.tendsto_atTop) u
 let a' := chip_city (s:=s) T f ht hθ (I:=Sheds (ρ s) × Sheds (ρ s)) (Z:=S ∘ F'₀) (φ:=fun _=> ⟨rfl,rfl⟩) hx0 rh t
 constructor
 · apply E₁ W (A ∘ κ) DD (fun i=> Chip P.run t (q i) (t' i) s (S (F'₀ i)) (f (w₀ i))) _ _ _ _ Jw B F i k; exact ⟨a',hp,Eventually.of_forall fun i=> ((cx (vX i)).2 W u).1⟩
 intro Yf HH H H'; let D':=mulT A' Yf; let D:=P.art (Yf.cookP t P.calibration) (aux_test (Yf.thermal HH t)); let Ψk(u):= (mulT (S (F'₀ u)) Yf)
 refine E₁ W (fun i=>p₁ i * D.val) (DD*D) (fun i=> Chip Y t (q i) (t' i) s (Ψk i) (f (w₀ i))) _ _ _ ⟨chip_city T f ht hθ (Z:=Ψk) (V:=D') (fun _=>⟨rfl,rfl⟩) (fun i=> (hx0 i.1).mul_const _) rh t,?_,Eventually.of_forall (fun i=> ((cx (vX i)).2 W u).2 Yf HH H H')⟩ Jw B F i k
 have u':BQueue (W∪W) _ _:=hp.multiply (cuedConst (P:=P) (Yf.thermal HH t)); rw [union_self] at u'; exact u'
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
