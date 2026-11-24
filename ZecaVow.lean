import ZecaTeam
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
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six
namespace Spine

variable {P:Spine}{x:P.Spectrum0 3}{A b C:ℝ}{f s:ℕ}
lemma ScoutAnthem.sky {v:ℕ→ℕ}{a:ℕ→ℕ × ℕ → ℝ}
     (h:ScoutAnthem P x A C f s b v a)(g:f<s):
  ∃ (u:ℕ→ℕ)(y:ℕ→ℕ × ℕ→ℝ), ScoutAnthem P x A C f s b u y ∧
              Skyways P f s A C (P.rewardK f s) u y:=by
 obtain ⟨R,t⟩:=h.station
 let h0:Engaged P f s A C v a:=⟨g,t.fast,fun i=>⟨t.up i,t.cruise i⟩⟩
 obtain ⟨el,p,m⟩:=P.raise_skyways h0 (P.rewardK f s)
 have e:=p.tendsto_atTop
 refine ⟨_,_,⟨⟨R,t.fast.comp p,fun i=>t.up _, fun i=>t.cruise _,t.price,
             fun i=>t.main _,fun i=>e.eventually (t.extra i)⟩,?_⟩,m⟩
 intro j l z pos
 obtain ⟨B,q⟩:=h.earns j l z pos
 exact ⟨B,e.eventually q⟩

variable {c r:ℕ→ℕ}{K:P.Register}{R:P.Ellis 3 x}

def Vow(P:Spine)(x:P.Spectrum0 3)(f s:ℕ)(A C b:ℝ)(Y:ℕ→P.Apron)
    (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)):Prop :=
 (∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition),
     ScoutAnthem P x A C f s b v a ∧ Skyways P f s A C (P.rewardK f s) v a∧
     Y=P.cinema x f s v a q u) ∧
 GalaxyShow P x f s Y V ∧ Afterimage P x Y

lemma sky_voyage (t:CruisePreparation P A C b K c r f s x R)
       {v:ℕ→ℕ}{a:ℕ→ℕ × ℕ→ℝ}
       (h:ScoutAnthem P x A C f s b v a)
       (β:0<b)(k:P.NightCop):
   ∃ Y V, Vow P x f s A C b Y V:=by
 obtain ⟨v,a,V,hp⟩:=h.sky t.station.2.1
 obtain ⟨x',u⟩:= V.station
 obtain ⟨q,W,T⟩:= P.radiated x v u.fast a f s V
 refine ⟨P.cinema x f s v a q u.fast,W,⟨v,a,u.fast,q,V,hp,rfl⟩,
    ?_,P.sky_cinema x f s v u.fast a q hp k⟩

 exact ⟨T,fun i=> P.pleading_b ..,fun i=> P.pleading_g ..,fun x z=> Spine.freemen P _ f s v u.fast a q W V t.station.2.1.le t.station.1 β T t.opera x z,fun j l k u v a b t g p=>P.scenic_right x j R T T l k t g (sub_pos.mpr p),fun j l k u v a b t g p=>P.scenic_left x j R T T l k t g (sub_pos.mpr p)⟩
end Spine

lemma elected_sky (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ Y V, Vow P x (P.pointEra s) s A C b Y V:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_century X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,d,t,v,a,V⟩:= p.2 F h
 exact ⟨x,R,d,t,sky_voyage t V β h0⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.elected_sky
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.elected_sky

