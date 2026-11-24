import Zephyr.Bed
import YM.SU5.Interaction.Partnership
import YM.SU5.Exchange.Visa.Moon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Buffered Buffered.Afterglow Buffered.Afterglow.Tower Buffered.Afterglow.Tower.VacuumSelection
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

open Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld

open Pitching.Focus
universe u
open Regis.Head Regis.Head.Brecht

abbrev May (D:TintDemand)(l:ℕ) (P:Preparation) : Prop :=
 TintRateCommercial l (crayon D) P ∧ Solstitial P ∧ 8∣P.M.val
lemma richMay (D:TintDemand)(l:ℕ) :
 CommissionVector (fun P=> May D l P ∧ training D l P):=by
 constructor; intro x y t s
 obtain ⟨P,q,Z,T,d,f,g,h,j,k,⟨⟨W,Y⟩,A,B,C,E⟩,r⟩ := (ministerSeasons (crayon D) l).purchased x y t s
 refine ⟨P,q,Z,T,d,f,g,h,j,k,⟨⟨W,Y,E⟩,?_,A,B,C⟩,r⟩
 obtain ⟨Pay,kC,u,Tξ,a,b,c,d,e,f,g,h,v⟩:=W.fromCrew
 exact ⟨Pay,kC,u,Tξ,a,b,c,d,e,f,g,h,RateCover.includes _ _ _ v⟩

structure Stakes (Mc:ℕ) (P:VacuumSelection.Spine) : Prop where
 first : FirstLease P
 post  : Post124 P.run
 eight : 8∣P.par.M.val
 pressure :
    ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧
     (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,
        (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)
     ∧ ∃ A:ℝ, Chronicle P.run A ∧
       (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v),
           EarnedClockPlot P C A f r v e u)
 rate  : RateStamp P.run
 visa  : Compass_sol P.run
 sprig : _root_.Zephyr.Chern.SprigFee P
 radius : ∃ (Pay kc G : ℝ)(Tξ:Hove.Grant P.par.K.j 2)(n:ℕ),
      Sweepcraft P.run Tξ Pay kc G n Mc
      -- For client coordination all the other credentials on the *same*
      -- fees, through a chosen pre-L demand: see Hippodrome.

open Ione
/-- Joint M8 / Velour purchase, pre-L tint demand, radius and
calendar funding, post-election a.e. client. See Partnership for the
full tuple. All of these are simultaneous. -/
theorem hippodrome
 (D:TintDemand)(n Mc:ℕ) (h: ((max Mc 2:ℕ):ℝ)*strive_E 6≤ (n:ℝ))
 (d:ℝ) (hd:0<d)(hd':d≤1)
 (T:Supplier)(b:ℝ)(hb:1≤b):
 ∃ (P:VacuumSelection.Spine) (K:P.Register)(c r:ℕ→ℕ),
    May D n P.par ∧ training D n P.par ∧
    uniform P K T b d ∧ Stakes Mc P ∧
  ∀ R₀ : P.Spectrum0 3 → Prop, (∀ᵐ x ∂ P.pillars 3, R₀ x) →
   ∃ (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    R₀ x ∧ Partnership.{u} P K c r x R i₀ F U A n w V g h X Y Z := by
 have hz:0 ≤ strive_E 6:=by unfold strive_E Jet.composeCost; positivity
 have wn:2*strive_E 6≤ (n:ℝ):=(mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_right Mc 2)) hz).trans h
 obtain ⟨P,K,c,r,w,t,l,u,v,z⟩:= interview.{u} D n _ (richMay D n) wn d hd hd' T b hb
 refine ⟨P,K,c,r,w,l,t,?_,z⟩
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,B⟩:= z (fun _=>True) (Eventually.of_forall fun _=>trivial)

 have E:=B.sconces
 obtain ⟨g,m,t,H⟩ :=l
 have A : FirstLease P:= ⟨E.roster,⟨_,_,g⟩,E.night,t,H,m,u⟩
 obtain ⟨Pay,k0,g0,S,x,y,a,f,_,b,c,_,R⟩:=w.1.fromCrew
 refine ⟨A,A.post,w.2.2,v,EarningsRate.atMask P.run R.stepRate E.roster.prepared,
    visa_onPath P.run E.roster.prepared w.2.1, _root_.Zephyr.Chern.SprigFee.paid P,Pay,k0,g0,S,n,
    bandRadius P.run ((R.includes _ _ _).staysOn ?_ ?_ x y f a b c Mc ?_) E.roster.prepared⟩
 · rw [P.par.kJ]; exact ⟨2,rfl⟩
 · exact P.par.kJ.ge
 · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left Mc 2) hz).trans h
