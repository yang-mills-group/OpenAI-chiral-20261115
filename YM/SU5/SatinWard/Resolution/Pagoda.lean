import YM.SU5.SatinWard.Resolution.Sarissa
import YM.SU5.SatinWard.Resolution.Captain
import YM.SU5.SatinWard.Resolution.Duette
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
abbrev bornJade(b C H A φ:ℝ)(j f0:ℕ)(χ:Chamber.Division)(η:Type)[Fintype η](s:ℕ)(x:Cover)(σ:ℕ→ℕ)(j0:Axis)(U:P.Test):Prop:=∃ Z F g,Tendsto g atTop atTop ∧ Ceremo P η s j f0 b C φ H A χ (σ ∘g) Z F∧ Z (some j0) x=U.val
variable (D H' A φ:ℝ) (g:P.NightCop)(x:Cover)(j f0:ℕ)(η:Type)[Fintype η]
private lemma cuedJade {P: Spine}{S:Finset Cover}{p:Family P.calibration}(v:InTest P.calibration true S false p) : BQueue S (fun i:ℕ=> p) p:=by
 obtain ⟨c,a⟩:=Journey.valuation P.run P.large v; refine BQueue.stay v (C:=c+1) ?_ (fun i u=>(a i u).trans (by linarith)); linarith only [show 0≤c from pay_nonneg (F:=p) a]
private lemma remaneJade {n:ℕ→ℕ} {P:Spine}{S:Finset Cover}{x: ℕ→ Family P.calibration} {p:Family P.calibration}(a:BQueue S x p)(h:Tendsto n atTop atTop): BQueue S (x∘n) p:=by
 obtain ⟨f,t,⟨c,u,v,w⟩,g⟩:=a; exact ⟨fun _=> f _,t,⟨c,u,v,h.eventually w⟩,fun e p=> h.eventually (g e p) ⟩ -- prop tuple check grouping
open LitCurrent AuroraX LampD
section
-- variant reduced to height-coherent plateau
attribute [local irreducible] bandWidthD
variable {Z:ℕ→ BeamLeaf P.run s}{z:BeamLeaf P.run s}{D:ℝ}{u:ℕ}{L:Chamber.Division}{j':Axis} (p:Tendsto Z atTop (𝓝 z)) (m:∀ᶠ i in atTop, LanternLease P.run s u L j' (Z i) D)
include m
local notation "B"=> P.thresholdF s
include p in
lemma citizen_r : LanternLease P.run s u L j' z D:=by
 let x:=D; have hx : Tendsto (fun i=> dietTotal B (Z i)) atTop (𝓝 (dietTotal B z)):= ((recordContinuity B).2.tendsto _).comp p; exact ⟨le_of_tendsto hx (m.mono fun i u=>u.scaleBill), nutrition_under _ _ _ p (m.mono fun i u=> u.crestWind),le_of_tendsto (((recordContinuity B).1.tendsto _).comp p|>.sub_const _|>.norm) (m.mono fun i u=>u.value)⟩
lemma citizen_sub : ∃ z':BeamLeaf P.run s,∃ c:ℕ→ℕ, StrictMono c∧ Tendsto (Z ∘ c) atTop (𝓝 z')∧ LanternLease P.run s u L j' z' D:=by
 have hx:∀ᶠ i in atTop,Z i∈ Metric.closedBall 0 D:=m.mono fun i h=> mem_closedBall.mpr ((dist_zero_right _).trans_le ((nutrition _ _).trans h.scaleBill))
 obtain ⟨m',u⟩:=eventually_atTop.mp hx; let g:=fun m:ℕ=> m'+m; let A:StrictMono g:=fun i j p=>by unfold g; omega
 obtain ⟨a,u,b,H,ht⟩:= (isCompact_closedBall (0: BeamLeaf P.run s) D).tendsto_subseq (x:=Z ∘ g) (fun i=> u (g i) (by unfold g; omega)); exact ⟨a,g∘b,A.comp H,ht,citizen_r (Z:=Z ∘ (g ∘ b)) ht ((A.comp H).tendsto_atTop.eventually m)⟩
end
attribute [local irreducible] bandWidthD
noncomputable abbrev keenJ(P:Spine)(v:ℕ)(U:P.Test):= canonLease P.run v • U
include T g
lemma jadeStone (j0:Axis)(u0:0<j)(p:0<a)(r:ℕ)(χ:Chamber.Division) {h:ℝ}: ∃ E:ℝ, D ≤ E ∧0 < E∧ ∀ᶠ s:ℕ in atTop,∀ U:P.Test,0< lapQ P.run s→bornJade a h H' A φ j f0 χ η s x σ j0 U → ∃ V, LanternLease P.run s j χ j0 V E ∧
   ∀S:Finset Cover, bandWidthD (P.thresholdF s) x ⊆ S → WidthBudget S (budgetWidth (X s) r) →
    let Zβ:= Real.sqrt (β s); let X':=LampD.headlight (P.thresholdF s) V x; ∀ (i:Axis)(z:P.Spectrum0 i),‖P.singleState i s z (keenJ P s U)-X'.issues (β s) (W s) Zβ‖≤ wane (X s) ∧
      ∀ (y:Tab principalKid)(j:ticket S 1 (X s) 2 y), Tab.holds P.calibration Zβ y→ y.terms ≤ E → ‖P.singleState i s z ((keenJ P s U)*P.art (y.cookP Zβ P.calibration) (aux_test (y.thermal j Zβ))) -(mulT X' y).issues (β s) (W s) Zβ‖ ≤ wane (X s):=by
 let F:=T.purse.born; let O:=T.order.tendsto_atTop; obtain ⟨E,u,hE,w⟩:= Quire.bright_tune P.run P.large principalKid p χ x F.shearPos F.mail D φ j u0 j0 h; refine ⟨E,u,hE,?_⟩
 filter_upwards [(turnover P.par).eventually_ge_atTop 1,w, SlopeCharge.polish P r,SlopeCharge.banking P g 4 1 T zero_lt_one le_rfl] with s ht w gB gC U v h₀
 obtain ⟨Z,F',p₀,wp,C₁,u'⟩:=h₀; obtain ⟨Φ,G,M,v',m,o⟩:=C₁.anchor
 let pY:=Ceremo.earnedZ P η C₁; let t:=Ψ s; let DD:=keenJ P s U; let K0:=nodeC x
 let r₂:=σ ∘ p₀; let era:=P.nomadic ∘ r₂; let ere:=P.engine ∘ r₂; let r':= canonLease Y s; let A(i:ℕ):= r' • G i (some j0) x
 have y': |t| ≤ Moon.fabric (Ω s):=Picker.permit P.run P.law P.history T.order.tendsto_atTop T.path_permanent s ht
 obtain ⟨f,rh⟩:= Picker.kings P.run P.law P.history T.order.tendsto_atTop T.path_permanent s; have hr':Tendsto r₂ atTop atTop:= O.comp wp
 let S0:=bandWidthD (ρ s) x; have J₀:BQueue S0 A DD.val:=by
    have hS:pavilion (nodeC x) (hourBound Y s) ⊆ S0:=by unfold S0 bandWidthD; exact inclPav (nodeC x) (hourBound Y s) (4*(ρ s) + petalD) (by unfold hourBound; unfold petalD; change (ρ s)+12 ≤_; omega)
    change BQueue S0 A (r' • U.val); rw [←u']; exact cueMono (cue_scale (m.bills (some j0) x) (fun _=>r') r' tendsto_const_nhds) hS
 let S(i:BeamLeaf P.run s):= LampD.headlight (ρ s) i x; let Ψ'(i:ℕ):=Z (some j0) x
 let C (S:Finset Cover)(x:ℕ)(F:Buffered.Family P.calibration)(y:Tab (NeedleCab (ρ s))):= AffordInk Y 4 1 s (era x) (ere x) P.large S F (Chip Y t (era x) (ere x) s y (f (p₀ x)))
 let C' (W:Finset Cover)(v:ℕ)(x:BeamLeaf P.run s)(y:Tab principalKid):= AffordInk Y 4 1 s (era v) (ere v) P.large W (A v*y.cookP t P.calibration) (Chip Y t (era v) (ere v) s (mulT (S x) y) (f (p₀ v)))
 let J (W: Finset Cover)(v:ℕ)(x: BeamLeaf P.run s):= C W v (A v) (S x)∧ ∀ y:Tab principalKid,ticket W 1 (X s) 2 y → Tab.holds P.calibration t y → y.terms ≤ E → C' W v x y
 let B(v:ℕ)(x: BeamLeaf P.run s):= LanternLease P.run s j χ j0 x E ∧ ∀W: Finset Cover, S0 ⊆ W→ J W v x
 have hw:∀ᶠ v in atTop,∃ ζ,B v ζ:=by
    filter_upwards [ (P.stockGo.comp hr').eventually w, wp.eventually rh] with i z ν; obtain ⟨b,d,Kx⟩:= (o i)
    obtain ⟨c,hz,q⟩:= z (ere i) b.2.le d (Φ i); refine ⟨c,hz,fun W h=>?_⟩
    obtain ⟨e,p⟩:=q (Real.sqrt (β s)) y' (A i) W (InTest.mono (J₀.whereTo i) h) h (by refine Eq.trans (b:= (exhibit Y P.large s ((P.nomadic∘r₂) i)) (r' • G i (some j0) x)) rfl ?_; rw [map_smul]; apply Eq.trans _ (tenorReceipt Y (Φ i) χ d x b.2.le j0 v).symm; exact congrArg (r' • ·) (m.learns x i (some j0))) (f (p₀ i)) ν.2
    exact ⟨e,fun y s t u=> p _ s u t⟩
 obtain ⟨g,hq⟩:= eventually_atTop.mp hw; let n:=fun i:ℕ=> g+i; choose C'₀ cx using fun i:ℕ=> hq (n i) (by unfold n; omega)
 let f1:StrictMono n:=fun i j h=>by unfold n; omega
 obtain ⟨z,vX,xB,pX,m'⟩:= citizen_sub (Eventually.of_forall fun i=> (cx i).1)
 let κ:=n∘vX; have hk:StrictMono κ:= f1.comp xB
 let w₀:=p₀ ∘ κ; have hθ:Tendsto w₀ atTop atTop:=wp.comp hk.tendsto_atTop
 let F'₀(i:ℕ):= (C'₀ (vX i)); have hx0(i: NeedleCab (ρ s)): Tendsto (fun k=>(S (F'₀ k)).tax i) atTop (𝓝 ((S z).tax i)) := by cases i; exact pX.fst_nhds; next i => exact tendsto_pi_nhds.mp pX.snd_nhds i
 let κf(J:Type)(a:Tab J): Prop:=True
 refine ⟨z,m',?_⟩; intro W u W' βx A' i k; obtain ⟨w,y,B,Jw,F⟩:=gB W W'; let E₁:= gC (σ∘w₀) (O.comp hθ); let q(i):= P.nomadic ((σ ∘ w₀) i); let t'(i):= P.engine ((σ ∘ w₀) i); let p₁:= A ∘ κ; have hp:BQueue W p₁ DD.val:=cueMono (remaneJade J₀ hk.tendsto_atTop) u
 let a' := chip_city (s:=s) T f ht hθ (I:=NeedleCab (ρ s)) (Z:=S ∘ F'₀) (φ:=fun _=> ⟨rfl,rfl⟩) hx0 rh t
 constructor
 · apply E₁ W (A ∘ κ) DD (fun i=> Chip P.run t (q i) (t' i) s (S (F'₀ i)) (f (w₀ i))) _ _ _ _ Jw B F i k; exact ⟨a',hp,Eventually.of_forall fun i=> ((cx (vX i)).2 W u).1⟩
 intro Yf HH H H'; let D':=mulT A' Yf; let D:=P.art (Yf.cookP t P.calibration) (aux_test (Yf.thermal HH t)); let Ψk(u):= (mulT (S (F'₀ u)) Yf)
 refine E₁ W (fun i=>p₁ i * D.val) (DD*D) (fun i=> Chip Y t (q i) (t' i) s (Ψk i) (f (w₀ i))) _ _ _ ⟨chip_city T f ht hθ (Z:=Ψk) (V:=D') (fun _=>⟨rfl,rfl⟩) (fun i=> (hx0 i.1).mul_const _) rh t,?_,Eventually.of_forall (fun i=> ((cx (vX i)).2 W u).2 Yf HH H H')⟩ Jw B F i k
 have u':BQueue (W∪W) _ _:=hp.multiply (cuedJade (P:=P) (Yf.thermal HH t)); rw [union_self] at u'; exact u'
#print axioms jadeStone
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
