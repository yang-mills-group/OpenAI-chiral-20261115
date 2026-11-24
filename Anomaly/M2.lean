import Anomaly.M1
import Anomaly.Rack.Certify
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
open Ione Vow Swell Sour BScale _root_.Zephyr.Chern
set_option maxHeartbeats 800000

structure PlanetPins (P:Spine) :Prop where
  prepays (m:ℕ)(w:1 ≤ m)(k0:ℕ):∃ a b δ:ℝ,∃ F D X Z Y T:ℝ→ℝ,
    0<a∧0<b∧0<δ ∧ Chill_v F∧ Chill_v D∧ Quench P.par.R X∧ Quench P.par.R Z∧ Quench P.par.R Y∧ Quench P.par.R T∧
    ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s<P.run.uv k→
      let N:=P.par.Ctor (P.run.ir i) s; let p:=(RootBook P.run i k s).p; let K:=(P.run.voyage i).CapeT s; let Λ:=hat P.par.R.L P.par.x s; ∃ (J J':Axis→ SOp N) (G U:SOp N),
        PostPins P.run s i k m a b (F Λ) (D Λ) (X Λ) (Z Λ) (Y Λ) (T Λ) k0 J J' G U∧
          let f := traceMeter p K 0 G ∘ (Zephyr.Chern.petals (Zephyr.Chern.stream N)); Bud f∧ δ < (bud f 2).re

variable {P: Spine}{x:P.Spectrum0 3} {K:P.Register}{n:ℕ}

lemma PlanetPins.enrollment (s: Orbital P K n) : PlanetPins P:=by
  obtain ⟨p,k,g,T,t,v⟩:=s.more; let L:=P.par.R
  refine ⟨fun m w k0=>?_⟩
  obtain ⟨a,b,F,D,u,h,p',k',d⟩:=weighAll P.run s.roster.prepared s.compass s.reg m
  obtain ⟨δ,p,H⟩:=aperture_field P (SprigFee.paid _) a b u m w
  let C:=fun i=>D i * pinpr P.par.R.L i
  have hz:Quench P.par.R C:= productQuench (npl_chill k')
  obtain ⟨X,U,hU,V⟩:= benchEarn P.run v k0 F C (npl_chill p') hz
  obtain ⟨_,g_,_,_,_⟩:= wakePrice k0 U _ hU; obtain ⟨_,_,g1,g2,_⟩:= wakePrice k0 C _ hz
  refine ⟨a,b,δ,F,D,winL k0 C U,wakeK k0 U,putTip 2 C,putTip 3 C,u,h,p,npl_chill p',npl_chill k',win_P _ k0 _ _ hz hU,g_,g1,g2,?_⟩
  filter_upwards [V,d,H,(Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop 20] with s U d H R
  filter_upwards [U,d] with i U d k t _ _ _ _
  obtain ⟨J,J',G,W,X⟩:=d k t
  exact ⟨J,J',G,W,ReadyBench.certify P.run k0 X (U k t) t ((p_meters P.run i k s t).1.symm ▸ R),H i k t _ _ _ _ _ _ X⟩

/-- CP2 public: application paying the Mark & linear and multi-root costs
in the Aperture calculation. `PostPins` keeps at any licensed layout
for the Ward test the actual stamped leads, their aperture weights and
also the holomorphic (multiple/nopol) Key perturbations at this level.
See Quill.marked for exact use (and Quill.tender normalized signed reading
on kicked appearances of this P tape). This is not proof of the later
outputs (Cap approximants, interaction, etc.). -/
theorem currentQuill (Mc:ℕ) : ∃ (P : Spine)(K : P.Register)(x : P.Spectrum0 3),
  Orbital P K Mc ∧ JointTuple.{u} P K x∧ SprigFee P ∧ AperturePin P ∧ PlanetPins P := by
 obtain ⟨P,K,x,Z,A,T,Λ⟩:= currentFirstBuys.{u} Mc
 exact ⟨P,K,x,Z,A,T,Λ,PlanetPins.enrollment Z⟩

#print axioms currentQuill
#print axioms Preparation.Quill.tender
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
