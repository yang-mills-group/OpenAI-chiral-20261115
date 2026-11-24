import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.M7
import YM.SU5.Registration.Affine.SolarShop
import YM.SU5.Registration.Affine.Egret
/-!
 # M8: Partial local registration & ground compression
 See the construction notes
 Uses the same enrollment in extending the (116) calculation (in any observer axis) to
 the continuum point words, with generic Euclidean pose budgets.
 Establish all needed operator estimates for this step for gauge cinema & advance on W.
 Does NOT here assert relativistic covariance or that it solves the thin limit outreach of interaction.
-/
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
variable (P : Spine) (x : P.Spectrum0 3)
universe u
variable {I:Type u}(L:List I) (K:P.Register)
variable (A:ℕ→P.Apron)(a:Axis)(Y:I→P.Swatch)
local notation "S"=>P.seasons a (P.advocate 3 x a)
open Swatch
lemma all_axes_gauge (p:PlanetaryG.{u} P A)(f:I→ List Axis)(g:∀ i,Y i=ordinary (fun k=>(A k).pivot P (f i)))(v:I→ Vantage)(t:LightsCross a L v)(u:StarCluster L v) : (∃ V':∀ i x,(Y i).WPermit x a,P.Passport a L Y V' v) :=by
 let V' (i:I):= (p.purchase a (f i)).2; have w:∀ i x,(Y i).WPermit x a:= fun i x=> (g i).symm ▸ V' i x
 exact ⟨w,p.reads a f Y w L v g t u⟩
open Regis.Head Regis.Head.Brecht
theorem planetary_sunlit : ∃ (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    id ≤ r ∧ uniform P K (fun _ _ _ _ _ _ _ _ _ _ _ _ => 0) 1 1 ∧
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ∧ P.Garrison x c r A n ∧ PlanetaryG.{u} P A ∧ (∀ x:P.Spectrum0 3,P.Guest x c r A n) ∧ ∃ p:CapBacked P x A c r n w, P.OverM4 x c r F U A n w V Y Z p := by
 -- See M6, using stronger Future generation here.
 let Y:Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G',C,ec,q,H',A,a,season,c,r,h,Θ,b,β,ρ'⟩:= heavier_century (fun _ _ _ _ _ _=>0) Y 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨s,_,t⟩:=ρ'.exists
 obtain ⟨x,R,_,p,v,a',q',S'⟩:=t (fun _=>True) (Eventually.of_forall fun _=>True.intro)
 obtain ⟨X,V,qX,pX,hX,B',Be⟩:= gala_camera.{u} P x K R c r _ _ a' v h0 ⟨P.par.R.L.val/2,by omega⟩ ((P.treasury_plot A C H' a).mono fun s p=> p (s+1) (by omega) (s+1) le_rfl) β p q' S'
 obtain ⟨N,f',hW⟩:= P.seam_everyone x c r X p.setup (Heavier.loose P Θ); obtain ⟨i₀,w,F,U,Y,Z,z⟩:= (P.packages_rows x K R c r _ _ e p.setup X V qX pX hX N f').exists
 let t':Garrison P x c r X N:=⟨B', hW x, Θ⟩; let ht:= P.lockup_law x K c r R i₀ F U X N w V _ _ f' Y Z z t'; have hd:P.OverM4 x c r F U X N w V Y Z ht:=P.sold_lockup x K c r R i₀ F U X N w V _ _ f' Y Z z t'; exact ⟨P,K,c,r,x,R,i₀,F,U,X,N,w,V,P.pointEra s,s,f',Y,Z,h,e,z,t',Be,hW,ht,hd⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.M4Tuple
#print axioms Spine.all_axes_gauge
#print axioms Spine.PlanetaryG
#print axioms Spine.planetary_sunlit
