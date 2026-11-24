import YM.SU5.Exchange.Election
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration

universe u

/-- One base tuple with the stronger promises of both imports. -/
def JointTuple (P : Spine) (K : P.Register) (x : P.Spectrum0 3) : Prop :=
 ∃ (c r : ℕ → ℕ) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron)
    (n : ℕ → ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
    (g h : ℕ) (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3))
    (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ∧
    P.Garrison x c r A n ∧ PlanetaryG.{u} P A ∧ (∀ y:P.Spectrum0 3,P.Guest y c r A n) ∧
    (∃ p:CapBacked P x A c r n w, P.OverM4 x c r F U A n w V Y Z p) ∧
    ∃ (M:M4Furnish P K c r x R i₀ F U A n w V g h X Y Z)
      (_:M4Velvet P x A c r n) (e:P.ThinVelour x A c r n w),
      M.AtSpindle e ∧ M.Contrasts e ∧ Sconces P K c r

open Regis.Head Regis.Head.Brecht
/-- The joint purchase, in a form allowing it to be conjoined with
 further pre-election estimates or additional a.e. qualifications. -/
theorem reside (P : Spine) (K : P.Register)
  (e : uniform P K blankSupplier 1 1) (ro : P.Roster)
  (s : P.NightCop) (t : Odd P.par.R.L.val) {A C : ℝ} (a : Chronicle P.run A)
  (H : ∀ᶠ i : ℕ in atTop, ∀ᶠ j : ℕ in atTop, ∀ k : ℕ,
    (P.run.voyage j).kick ≤ k → i ≤ P.run.uv k → Yoke.ShelterCost C P.run i j k)
  (good : P.Spectrum0 3 → Prop) (hg : ∀ᵐ x ∂ P.pillars 3, good x) :
   ∃ x : P.Spectrum0 3, good x ∧ JointTuple.{u} P K x := by
 obtain ⟨c,r,m,p,p',b,β,u'⟩ := P.electedTogether K e s t H a id 1 zero_lt_one
 obtain ⟨i,_,hi⟩ := u'.exists
 obtain ⟨x,R,gx,prep,v,A',w,V⟩ := hi good hg
 obtain ⟨A₀,W,showG,hW,pW,fund,pla,vv⟩ :=
   sameCamera.{u} P x K R c r (P.pointEra i) i A' v s t
    ((P.treasury_plot A C H a).mono fun s p=> p (s+1) (by omega) (s+1) le_rfl)
    β prep w V
 obtain ⟨n,X,hX,gr⟩ := P.conjunctionSeam x c r A₀ prep.setup (Heavier.loose P p) p'
 obtain ⟨i₀,m',F,U,Y,Z,M⟩ :=
   (P.packages_rows x K R c r _ _ e prep.setup A₀ W showG hW pW n X).exists
 let G : Garrison P x c r A₀ n := ⟨fund, gr x, p⟩
 have A1 := P.sold_lockup x K c r R i₀ F U A₀ n m' W _ _ X Y Z M G
 have A2 := (RegistrationAgreement.sameM4Tuple P K c r x R i₀ F U A₀ n m' W _ _ X Y Z).mp M
 let L : M4Velvet P x A₀ c r n := ⟨vv, hX⟩
 let q := L.thin m' X prep.setup
 exact ⟨x, gx, c, r, R, i₀, F, U, A₀, n, m', W, _, _, X, Y, Z, M, G, pla, gr,
   ⟨_, A1⟩, A2, L, q, A2.reunion q, A2.foil L, ⟨e, ro, s, m, p'⟩⟩

/-- No remaining physical or compatibility hypotheses for purchasing M8 and Wadding.
 The interaction goal doesn't follow just by using the raw products here. -/
theorem planetaryWadding :
    ∃ (P : Spine) (K : P.Register) (x : P.Spectrum0 3), JointTuple.{u} P K x := by
 obtain ⟨n,i,P,K,Q,r,v,_,_,_,tq,U,G,⟨C,p',c,D⟩,⟨A,y,q⟩,_⟩ :=
   partridge (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one id
 obtain ⟨x,_,hx⟩ := reside.{u} P K Q r v ⟨P.par.R.L.val/2,by omega⟩ y D
    (fun _=>True) (Eventually.of_forall fun _=>trivial)
 exact ⟨P,K,x,hx⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
