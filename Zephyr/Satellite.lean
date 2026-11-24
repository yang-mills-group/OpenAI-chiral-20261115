
import SU5SatinFieldRegistrationsNovember7
import Zephyr.LitPost

/-! The planetary election with (124), same tuple.
`Garrison` etc as for M8; Velour *base*, not claiming
the additional Velour qualifications here. Further demands can be put
in at many prices even before the election (as in Heavier itself);
nothing says they come free. -/

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
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld

open Regis.Head Regis.Head.Brecht
universe u


structure FirstLease (P: Spine): Prop where
 roster: P.Roster
 tint: ∃ (n:ℕ) (c:TintDemand), TintCommercial n c P.par
 night: P.NightCop
 side: 15 ∣ P.par.R.L.val
 phase: P.par.R.L.val % 16 = 1
 merits: Meritorious P.par
 orders: Yoke.Dispatchers P.par

lemma FirstLease.post {P:Spine}(s:FirstLease P) : Post124 P.run:= by
 obtain ⟨n,c,x⟩:=s.tint
 obtain ⟨Pay,k,Γ,t,_,_,_,_,_,_,_,_,lit⟩:= x.fromCrew
 exact Preparation.postpaid P.run lit s.roster.prepared


open SatinRegistration

theorem satellite_order (B_:TintDemand)(Y:Supplier)(t₁ t₂:ℝ)(hp:0<t₂)(f:ℕ→ℕ):
   ∃ (N:ℕ)(P:Spine) (K:P.Register)(c r:ℕ→ℕ),
     f ≤ r ∧ uniform P K Y t₁ t₂ ∧ FirstLease P ∧
     TintCommercial N (crayon B_) P.par ∧ Post124 P.run ∧
     ∀ (Ω:P.Spectrum0 3→Prop), (∀ᵐ x∂P.pillars 3,Ω x)→
      ∃ (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    Ω x ∧
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ∧ P.Garrison x c r A n ∧ PlanetaryG.{u} P A ∧ (∀ x:P.Spectrum0 3,P.Guest x c r A n) ∧ ∃ p:CapBacked P x A c r n w, P.OverM4 x c r F U A n w V Y Z p := by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G',C,ec,q,H',A,a,season,c,r,h,Θ,b,β,ρ'⟩:= heavier_century B_ Y t₁ t₂ hp 1 zero_lt_one f
 have hs:FirstLease P:= ⟨π₀,⟨n,_,h1⟩,h0,h3,h4,h2,G'⟩
 refine ⟨n,P,K,c,r,h,e,hs,h1,hs.post,?_⟩
 intro Ω hΩ
 obtain ⟨s,_,t⟩:=ρ'.exists
 obtain ⟨x,R,xΩ,p,v,a',q',S'⟩:=t Ω hΩ
 obtain ⟨X,V,qX,pX,hX,B',Be⟩:= gala_camera.{u} P x K R c r _ _ a' v h0 ⟨P.par.R.L.val/2,by omega⟩ ((P.treasury_plot A C H' a).mono fun s p=> p (s+1) (by omega) (s+1) le_rfl) β p q' S'
 obtain ⟨N,f',hW⟩:= P.seam_everyone x c r X p.setup (Heavier.loose P Θ); obtain ⟨i₀,w,F,U,Y,Z,z⟩:= (P.packages_rows x K R c r _ _ e p.setup X V qX pX hX N f').exists
 let t':Garrison P x c r X N:=⟨B', hW x, Θ⟩; let ht:= P.lockup_law x K c r R i₀ F U X N w V _ _ f' Y Z z t'; have hd:P.OverM4 x c r F U X N w V Y Z ht:=P.sold_lockup x K c r R i₀ F U X N w V _ _ f' Y Z z t'; exact ⟨x,R,i₀,F,U,X,N,w,V,P.pointEra s,s,f',Y,Z,xΩ,z,t',Be,hW,ht,hd⟩


#print axioms satellite_order

open RegistrationAgreement
/-- On the same planetary tuple and hence on the base Velour
tuple, (124) on the source arrays. -/
theorem planet_with_124 :
    ∃ (P:Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    id ≤ r ∧ uniform P K (fun _ _ _ _ _ _ _ _ _ _ _ _ => 0) 1 1 ∧
    FirstLease P ∧ Post124 P.run ∧
    M4Furnish P K c r x R i₀ F U A n w V g h X Y Z ∧
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ∧ P.Garrison x c r A n ∧ PlanetaryG.{u} P A ∧ (∀ x:P.Spectrum0 3,P.Guest x c r A n) ∧ ∃ p:CapBacked P x A c r n w, P.OverM4 x c r F U A n w V Y Z p := by
 obtain ⟨_,P,K,c,r,hr,b,s,_,H,u⟩ := satellite_order.{u}
    (fun _ _ _ _ _ _=>0) (fun _ _ _ _ _ _ _ _ _ _ _ _ =>0) 1 1 zero_lt_one id
 obtain ⟨x,R,i,F,U,A,n,w,V,g,h,X,Y,Z,_,q,p⟩ :=
   u (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 exact ⟨P,K,c,r,x,R,i,F,U,A,n,w,V,g,h,X,Y,Z,hr,b,s,H,
    (sameM4Tuple P K c r x R i F U A n w V g h X Y Z).mp q,q,p⟩

#check @planet_with_124
#print axioms planet_with_124
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
