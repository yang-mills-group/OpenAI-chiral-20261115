import YM.LocalFieldBounds.Motif.Season

/-!
# One election. Variation on seekingRoad from Harbinger and ranks through Season.
Permit carrying a purchase all the way from minister's grants into the LocalFieldBounds Programme.
Doesn't require Carriage in purchasing! No weakening/modification of the `Programme` (`Rank` etc.).
-/
section
-- rebook with explicit demands for these new step estimates. Extends ..WakeInvestment.Reappoint,WakeRoad.Marigold
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace Spine
universe u
open Ione Vow Swell
open _root_.Zephyr.Chern
-- keep all interfaces of W even through h/location elevations. Need a correlated request to regulator. No re-election.
open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers CF.Papyrus.Franc.Loaves

-- more prerequisites at election, retain every extra Preparation law solicited
def commissions (Φ : Preparation→Prop) :Prop:= ∀ X:TintDemand,∀ NLeaf:ℕ, CommissionVector (fun p=> Φ p∧ (TintRateCommercial NLeaf X p ∧ (Solstitial p∧Fountain p)) ∧ Meritorious p ∧ 15 ∣ p.R.L.val ∧ p.R.L.val %16 =1 ∧ 8 ∣ p.M.val)
lemma seekingRoad_plus {Φ : Preparation→Prop}(sponsor : commissions Φ) (X:TintDemand)(m:ℕ) (Q:Supplier)(μ ε:ℝ)(p₁:0<ε):∃ (n:ℕ)(P:Spine)(K:P.Register)(E:ℝ), Φ P.par ∧ Squall.{u} n m X P K E∧ (2+(m:ℝ))*strive_E 6<n ∧ uniform P K Q μ ε ∧ (P.par.R.L.val%16=1 ∧ 15∣P.par.R.L.val) ∧ ∃ b C, BornGrants P.par b C :=by
 have purchase(n:ℕ):CommissionVector (fun p =>
      ((TintRateCommercial n (crayon X) p ∧ Solstitial p) ∧ Meritorious p ∧
        15 ∣ p.R.L.val ∧ p.R.L.val % 16 = 1 ∧ 8 ∣ p.M.val) ∧ (Φ p ∧ Fountain p ∧ p.R.L.val%16=1 ∧ 15∣p.R.L.val)) := by
    constructor; intro e' ε he Q; obtain ⟨P, ℓ, Z, Y, p', u', t', r, c, A, ⟨hpΦ,h⟩, X', L', G', B', J⟩ :=
      (sponsor (crayon X) n).purchased e' ε he Q
    exact ⟨P, ℓ, Z, Y, p', u', t', r, c, A,⟨⟨⟨h.1.1,h.1.2.1⟩,h.2⟩, hpΦ,h.1.2.2,h.2.2.2.1,h.2.2.1 ⟩, X', L', G', B', J⟩
 obtain ⟨P,K,E,n,u,p,⟨hΦ,v,t,h⟩,Kx,A,y⟩:= reappointed_zest X (fun p=>Φ p∧Fountain p∧ p.R.L.val%16=1∧ 15∣ p.R.L.val) purchase m Q μ ε p₁
 refine ⟨n,P,K,E,hΦ,⟨A,v,p,PureForce.CakeL.endowment P A.lit.season v,?_,?_⟩,u,Kx,⟨t,h⟩,y⟩
 · intro A₀ ha b v u₀ w₀ J _ f hf B L Z l; exact achet (P:=P) (V:=K) (p:=ha) (a:=b) (b:=v) (u:=u₀) (w:=w₀) A f hf B L Z l
 intro I hI
 obtain ⟨v, hv⟩ := A.investment
 exact Jewel.onPermit (Y := P.run) (U := P.law) (Q := P.history) hv A.dispatch A.rocky.merit hI


end Spine
namespace SatinWard
open Spine Resolving Resolving.CrossMoment SlopeCharge
open Papal Papal.Moon Papal.Moon.Horizons
open Papal.SkyTax
open Papal.Moon.Moonlit -- location?
open SwitchC
open Preparation.Tabletop QuadClock ShapeLab
universe u
open Spine Ione Vow Swell Pitching.Focus
open _root_.Zephyr.Chern
open Preparation.Yoke EmberWind Jewel Ballad
open SpinReceipt Shuttle Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open YM.WakeFields YM.Stationary
open CF.Onyx CF.Gingham.Ruff Spine.Gingham.VoyageB
open Spine.Gingham Spine.Gingham.Diary Dial Pressure Stationary Regis.Circuit
open Preparation.Yoke.ArborJet
lemma provide_along_plus {Φ : Preparation→Prop}(sponsor : commissions Φ) (Υ extra: TintDemand)(m:ℕ)(Q:Supplier)(ε' β₀:ℝ)(hw:0<ε')(τ:ℝ)(u0:ΛcrestF τ) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ) (w : ℕ) (f : ℕ → ℕ) (β : ℕ → ℝ), Φ P.par ∧
      (2+(m:ℝ))*Ione.strive_E 6<w∧
      Squall.{u} w m (billUp τ Υ extra) P K E ∧ uniform P K Q β₀ ε' ∧
      (P.par.R.L.val%16=1 ∧ 15∣P.par.R.L.val) ∧ (∃ T Pay C Γ W V F U, Spine.FinanceLeaf (pushGarden Υ) (paidUp τ extra) m P T Pay C Γ W V F U w ∧
         StageBooking P T Pay C Γ W V F U m (study τ P extra T Pay C Γ) τ
       ) ∧ StrictMono f ∧ Tuned P f β ∧ ReflectedGaugeLower P β ∧ SignedDenominator P ∧
      (∃ b C t r, CouncilGrant P K b C t f r β ∧ PublicKernel P f r ∧
        ∀ (J:Type)[DecidableEq J] (q:ℕ)(rate:ℝ)(I:ℕ), 0<rate→ rate≤1→
        ∀ᶠ s:ℕ in atTop,∀ (T:Finset Cover)(A:SwitchC.Tab J)(j:SwitchC.ticket T rate (hat P.par.R.L P.par.x s) q A), ∀y:ℝ, |y| ≤ Moon.fabric (hat P.par.R.L P.par.x s) → A.terms ≤ Moon.voucher (hat P.par.R.L P.par.x s) → SwitchC.Tab.holds P.calibration y A → WidthBudget T (budgetWidth (hat P.par.R.L P.par.x s) I) →
         let V:=A.cookP y P.calibration
         ∀ (i:Axis)(z:P.Spectrum0 i), ‖P.singleState i s z (P.art V (aux_test (A.thermal j _)))- (A.issues (β s) (r s) y)‖ ≤ wane (hat P.par.R.L P.par.x s))∧
      (∀ (y : Cover) (n : ℕ) (b : ℝ), NewPier P P.jump128 y n b) ∧
      ∀ A : ℝ, 0 < A → ∃ (sites : ℕ → Fin 4 → Cover) (h : ℕ → ℕ),
        (∀ i, Appoint P.par A (fun s => sites s i) (spot4 i)) ∧ StrictMono h ∧
        ∀ U : P.Spectrum0 3 → Prop, (∀ᵐ x ∂ P.pillars 3, U x) →
          ∃ x, U x ∧ SelectedReadouts.{u} P K A β f h sites x:=by
  -- crest chosen
  obtain ⟨w,P,K,E,hΦ,squall,ev,HQ,M,b,C0,F⟩:= Spine.seekingRoad_plus.{u} sponsor (billUp τ Υ extra) m Q β₀ ε' hw
  obtain ⟨T,p,x,U,W,a0,F0,V,y⟩:=chartered (pushGarden Υ) (paidUp τ extra) m P w K E squall ev
  obtain ⟨a, c, μ, l, r, F, land, g, β, δ, hδ, C, X,
    q, hq, hg, pooled, _, typed, lower, _⟩ := GramSignal.reBunya squall -- F shadow fix
  let f₀ := r ∘ g
  obtain ⟨t,e⟩:= Spine.gardner squall ‹BornGrants P.par b C0›
  obtain ⟨u,W₀,β',k,k',k₀⟩:= e f₀ (land.grew.comp hg); let f:=f₀∘u
  have h:=pooled.sub P.run k
  have tuned : Tuned P f β := h
  have p₀:β=β':=funext fun s=> tendsto_nhds_unique (h.received s) (k'.path_permanent.mass s)
  subst β'; have gauge : ReflectedGaugeLower P β :=
    ⟨F, δ, q, hδ, hq, typed, lower.mono fun _ hs => hs.1⟩
  refine ⟨P, K, E, w, f, β, hΦ,ev, squall, HQ, M, ⟨T,p,x,U,W,a0,F0,V,y,Ticketing.paperRoom P K τ E p x U T W a0 F0 V w m Υ extra u0 squall y⟩, (land.grew.comp hg).comp k, tuned, gauge, denominatorOn P squall.ledger, ⟨b,C0,t,W₀,k', k₀, fun J _ q rate I v w'=> SlopeCharge.university P squall.ledger.rocky.night q rate k' v w' I⟩,
    fun y n b => Spine.pier_now P K E m squall.ledger _ P.jump_pos y n b, ?_⟩
  intro A positive
  have chooseSite (y : Gaia) : ∃ t : ℕ → Cover, Appoint P.par A t y :=
    ⟨_, (P.announces 1 (by decide) positive (0 : Cover) y).1⟩
  choose T appointed using fun i => chooseSite (spot4 i)
  let sites := fun (s:ℕ) (i:Fin 4) => T i s
  obtain ⟨h, strict, select⟩ := selectReadouts P squall.ledger squall.keep squall.path
    A positive f β tuned sites appointed
  exact ⟨sites, h, appointed, strict, select⟩

#print axioms provide_along_plus
end SatinWard
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
end
section
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace SatinWard
open Spine Resolving Resolving.CrossMoment SlopeCharge
open Papal Papal.Moon Papal.Moon.Horizons
open Papal.SkyTax
open Papal.Moon.Moonlit -- location?
open SwitchC
open Preparation.Tabletop QuadClock ShapeLab
universe u
open Spine Ione Vow Swell Pitching.Focus
open _root_.Zephyr.Chern
open Preparation.Yoke EmberWind Jewel Ballad
open SpinReceipt Shuttle Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open YM.WakeFields YM.Stationary
open CF.Onyx CF.Gingham.Ruff Spine.Gingham.VoyageB
open Spine.Gingham Spine.Gingham.Diary Dial Pressure Stationary Regis.Circuit
open Preparation.Yoke.ArborJet

namespace Installment
open Aria Casting Preparation Tabletop ShapeLab ResolutionFrame

open Spine.Fame Spine.Fame.Regulator Spine.Fame.PSE Spine.MarbleFace
theorem rank_program_at_plus {Φ : Preparation→Prop}(sponsor : commissions Φ) (Υ extra: TintDemand)(m:ℕ)(Q:Supplier)(ε' β₀:ℝ)(hw:0<ε')(τ:ℝ)(u0:ΛcrestF τ)(η:Type)[Fintype η][DecidableEq η](μ:Fintype.card (Announcement Wage4 η) ≤ m):
    let Y:= buyPSE τ Υ extra
    ∃ (P : Spine) (K : P.Register) (E : ℝ) (w : ℕ) (f : ℕ → ℕ) (β : ℕ → ℝ), Φ P.par ∧
      (2+(m:ℝ))*Ione.strive_E 6<w∧
      Squall.{u} w m (billUp τ Y extra) P K E ∧ uniform P K Q β₀ ε' ∧
      P.par.R.L.val %16=1 ∧ 64 ≤ P.par.R.L.val ∧ 15∣P.par.R.L.val∧
      (∃ T Pay C Γ W V F U, Spine.FinanceLeaf (pushGarden Y) (paidUp τ extra) m P T Pay C Γ W V F U w ∧
         StageBooking P T Pay C Γ W V F U m (study τ P extra T Pay C Γ) τ ∧
         ∀ᶠ s:ℕ in atTop, Piano P s (yardF cloverFrame) (assets (Asteroid P.par.K T Pay C Γ)) (study τ P extra T Pay C Γ) η f
       ) ∧ StrictMono f ∧ Tuned P f β ∧ ReflectedGaugeLower P β ∧ SignedDenominator P ∧
      (∃ b C t r, CouncilGrant P K b C t f r β ∧ PublicKernel P f r ∧
        ∀ (J:Type)[DecidableEq J] (q:ℕ)(rate:ℝ)(I:ℕ), 0<rate→ rate≤1→
        ∀ᶠ s:ℕ in atTop,∀ (T:Finset Cover)(A:SwitchC.Tab J)(j:SwitchC.ticket T rate (hat P.par.R.L P.par.x s) q A), ∀y:ℝ, |y| ≤ Moon.fabric (hat P.par.R.L P.par.x s) → A.terms ≤ Moon.voucher (hat P.par.R.L P.par.x s) → SwitchC.Tab.holds P.calibration y A → WidthBudget T (budgetWidth (hat P.par.R.L P.par.x s) I) →
         let V:=A.cookP y P.calibration
         ∀ (i:Axis)(z:P.Spectrum0 i), ‖P.singleState i s z (P.art V (aux_test (A.thermal j _)))- (A.issues (β s) (r s) y)‖ ≤ wane (hat P.par.R.L P.par.x s))∧
      (∀ (y : Cover) (n : ℕ) (b : ℝ), NewPier P P.jump128 y n b) ∧
      ∀ A : ℝ, 0 < A → ∃ (sites : ℕ → Fin 4 → Cover) (h : ℕ → ℕ),
        (∀ i, Appoint P.par A (fun s => sites s i) (spot4 i)) ∧ StrictMono h ∧
        ∀ U : P.Spectrum0 3 → Prop, (∀ᵐ x ∂ P.pillars 3, U x) →
          ∃ x, U x ∧ SelectedReadouts.{u} P K A β f h sites x:=by
 intro Y; obtain ⟨P,K,E,w,f,β,hΦ,h,c,HQ,⟨L,hL⟩,⟨T,Pay,C,Γ,W,V,F,U,y,q⟩,hp,A⟩:= provide_along_plus.{u} sponsor Y extra m Q ε' β₀ hw τ u0; let T':=play_piano Υ extra P Pay C Γ T W V F U f τ η μ hp.tendsto_atTop L y q; exact ⟨P,K,E,w,f,β,hΦ,h,c,HQ,L,T'.1,hL,⟨T,Pay,C,Γ,W,V,F,U,y,q,T'.2⟩,hp,A⟩
#print axioms rank_program_at_plus

end Installment
end SatinWard
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
end
section
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace SatinWard
open Spine Resolving Resolving.CrossMoment SlopeCharge
open Papal Papal.Moon Papal.Moon.Horizons
open Papal.SkyTax
open Papal.Moon.Moonlit -- location?
open SwitchC
open Preparation.Tabletop QuadClock ShapeLab
universe u
open Spine Ione Vow Swell Pitching.Focus
open _root_.Zephyr.Chern
open Preparation.Yoke EmberWind Jewel Ballad
open SpinReceipt Shuttle Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open YM.WakeFields YM.Stationary
open CF.Onyx CF.Gingham.Ruff Spine.Gingham.VoyageB
open Spine.Gingham Spine.Gingham.Diary Dial Pressure Stationary Regis.Circuit
open Preparation.Yoke.ArborJet

namespace Installment
open Aria Casting Preparation Tabletop ShapeLab ResolutionFrame

open Spine.Fame Spine.Fame.Regulator Spine.Fame.PSE Spine.MarbleFace
open CasaF Spine.Fame.Regulator.Internal
open LitCurrent LitCurrent.Chamber
open Harmonic

open Spine.Fame.Regulator.Internal.Dovetail.Freeport Polaris
open LitCurrent.AuroraX Imperial Lighthouse SoulField
open _root_.GarnetAct.Cut
/-! CP-I election. Packs full membership in E/W regulator. All this still along ONE Leader proposal
 and one direction calibration.Normalization.Fe. Preserve earlier polls.has permission to require
 further conull properties of the encounter with x. Full W unpadding NOT in this.
 -/
variable {m n:ℕ} {ℓ b d:ℝ} (P:Spine) (η:Type)[Fintype η][Nonempty η] {C H A a₀ b₀ a₁ b₁ φ φ':ℝ}{f0:ℕ}{f:ℕ→ℕ}{R:P.Register}
variable {T: Hove.Grant P.par.K.j 2}{x:ℝ} {β t':ℕ→ℝ} {p:ℕ→ HorizonLens→ HorizonLens→ ℝ}
local notation "dρ"=> P.par.block.val
local notation "JPop"=> P.Spectrum0 3
variable (U:P.NightCop)(M:P.par.R.L.val%16=1)(Lh:64 ≤ P.par.R.L.val) (pH:Tendsto f atTop atTop)
variable (T₁:CouncilGrant P R ℓ C t' f p β) (H':PublicKernel P f p)
variable (W:HeartClock P f0 H A a₀ b₀ φ P.jump128 M f η)(e:Melodic P η A f0 f) (P₁:ChargeRes P η A H f0 P.jump128)(Tξ:Resonant P η A H f0 P.jump128)
variable {X Y:TintDemand} {Fee cBoost Γ:ℝ}(V F' Z W':ℝ→ℝ) (χd:ℝ) [DecidableEq η]{E:ℝ}(Q:P.Register)(μ:Fintype.card (Announcement Wage4 η) ≤ m)(s:Fintype.card (Announcement Wage3 η) ≤ m)
variable (X' Z': TintDemand)(Q':Supplier)(HW1:Fintype.card (Announcement Wage4 η) ≤ m)(HW2:Fintype.card (Announcement Wage3 η) ≤ m)
local notation "xΠ" t:max=> wardRate t X' Z'
-- Pose.
include HW1 HW2
set_option maxHeartbeats 750000 in
theorem treaty_plus {Φ : Preparation→Prop}(sponsor : commissions Φ) (ε' β₀:ℝ)(hw:0<ε') :
    ∃ τ:ℝ,1 ≤ τ ∧ ΛcrestF τ ∧ ∃ (P : Spine) (K : P.Register) (E : ℝ) (w : ℕ) (f : ℕ → ℕ) (β : ℕ → ℝ), ∃ M:P.par.R.L.val%16=1,∃ Costs:Squall.{u} w m (billUp τ (wardRate τ X' Z') Z') P K E,∃ ht : StrictMono f, Φ P.par∧
      ((2+(m:ℝ))*Ione.strive_E 6<w∧ uniform P K Q' β₀ ε' ∧ 64 ≤ P.par.R.L.val ∧ 15∣ P.par.R.L.val) ∧
      (∃ T Pay C Γ W V F U, Spine.FinanceLeaf (pushGarden (wardRate τ X' Z')) (paidUp τ Z') m P T Pay C Γ W V F U w ∧
         StageBooking P T Pay C Γ W V F U m (study τ P Z' T Pay C Γ) τ ∧
         ∀ᶠ s:ℕ in atTop,January P η Costs.ledger.rocky.night M ht.tendsto_atTop (study τ P Z' T Pay C Γ) (assets (Asteroid P.par.K T Pay C Γ)) β s
       ) ∧ Tuned P f β ∧ ReflectedGaugeLower P β ∧ SignedDenominator P ∧ (∃ b C t r,CouncilGrant P K b C t f r β ∧ PublicKernel P f r):=by
 obtain ⟨τ,h,uτ⟩:= crest_early; obtain ⟨P,K,E,w,f,β,hΦ,wf,tW,u,P0,H0,p0,p,ht,uB,q,vB,ch,_,_⟩:= rank_program_at_plus.{u} sponsor (buoyL τ X' Z') Z' m Q' ε' β₀ hw τ uτ η HW1
 obtain ⟨T,Pay,C,mM,W,V,F,U,t',v,h'⟩:=p; obtain ⟨b,x,g,qz,i,G,_⟩:=ch; let he:= entitled P η P0 H0 ht.tendsto_atTop i G W V F U τ K HW1 HW2 t' v tW
 exact ⟨τ,h,uτ,P,K,E,w,f,β,P0,tW,ht,hΦ,⟨wf,u,H0,p0⟩,⟨T,Pay,C,mM,W,V,F,U,t',v,he⟩,uB,q,vB,⟨b,x,g,qz,i,G⟩⟩ -- u shadow? u = Register? conflict r choose rename
#print axioms treaty_plus
end Installment
end SatinWard
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
end
section
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.LocalFieldBounds.Motif
open Filter Function Set Metric MeasureTheory 
open scoped Topology ComplexOrder InnerProductSpace NNReal Classical
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
open CF.QuadClock.ShapeLab SoulField SatinWard.Installment
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open Polaris.Rampart _root_.GarnetAct.Cut
open Set MeasureTheory
open _root_.YM.SatinWFixed Andesite Carton _root_.YM.Boundary Probe
open CF.Py.Rate.LocalLimit Preparation
open CF.Buffered.Afterglow.Tower
open Preparation.Tabletop CasaF.Signboard
open CF.Py.Rate.LocalLimit.Preparation.Yoke
open CF.Ione.Clock CF.Moto CF.LitCurrent AuroraX Verdance Lattice
open CF.QuadClock.SignSlot
open Chili
open YM.WakeFields CF
open Papal.Moon
open SatinWard
universe u

open Resolving ResolutionFrame

/- avoid giant early elaboration reductions -/
attribute [local irreducible] Spine.Register
variable (X Z:TintDemand)(Q:Supplier)(m:ℕ)(η:Type)[Fintype η][Nonempty η]
theorem programme_plus [DecidableEq η]
    (sK:Fintype.card (Announcement Wage4 η) ≤ m)
    (sJ:Fintype.card (Announcement Wage3 η) ≤ m)
    (ε' target:ℝ) (w:0<ε')
    {Φ : Preparation → Prop} (sponsor : Spine.commissions Φ) :
    ∃ y : Programme.{u} X Z Q m η ε' target, Φ y.P.par := by
  obtain ⟨τ,i,j,P,K,E,n,f,β,M,c,ht,hΦ,
     ⟨h₁,k,h₂,h₃⟩,⟨T,Pay,C,Γ,W,V,F,Z',p,r,b⟩,v,g,t,u⟩ :=
        Installment.treaty_plus.{u} η X Z Q sK sJ sponsor ε' target w
  refine ⟨⟨w,sK,sJ,τ,⟨i,j⟩,P,K,E,n,f,β,M,⟨h₂,h₃⟩,c,ht,h₁,k,v,
     ⟨g,t⟩,u,T,Pay,C,Γ,W,V,F,Z',p,r,?_⟩,hΦ⟩
  obtain ⟨a,d,s,y,k,z⟩ := u
  exact b.mono fun i h=>january_debut P M _ _ h₂ k z h
#print axioms programme_plus

end YM.LocalFieldBounds.Motif
end
end
