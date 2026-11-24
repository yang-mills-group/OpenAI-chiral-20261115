import Gingham.Livery
import Gingham.Banquette
/-! # One strict appointment cost: common history, resolution,
appointment, width index (can vary between arms) and inspector,
across all the charges of a ranked reading. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ


open SatinRegistration
variable {ι:Type}[Fintype ι][DecidableEq ι]

open Diary 
variable (L M:ι→Hook P x)(a:Weave)
abbrev ReadyToGo (s:ℕ)(u v:ι→ℕ):Prop :=
   ∀i j,Height P x (L i) (M j) (u i) (v j) s
abbrev Seven (s:ℕ)(u v:ι→ℕ)(δ:ℝ) :=
 ∀i j, InBuoy a P x (L i) (M j) (u i) (v j) s ∧
    Topaz (GridEu a P x (L i) (M j) (u i) (v j) s) (AudEu a P x (L i) (M j)) δ

variable (s:ℕ)(u v:ι→ℕ)(δ:ℝ)
local notation "A" i:max=>BlotAt a P x (L i) (u i) s
local notation "B" j:max=>WellAt a P x (M j) (v j) s

lemma sharp_party (N:ℝ) (b:Seven P x L M a s u v δ):
    ∃ t, s ≤ t ∧ ∃ r:P.Test, Lodgment P t N r ∧
       ∀i j,SharpBill a P x s t (L i) (M j) (u i) (v j) δ r:=by
   let f:ι → ι→ Option Bool→ P.Test:=fun i j e=>match e with
    | none=> (A i)*(B j)
    | some true=> A i
    | some false=> B j

   let T:=ι × ι × Option Bool
   let k(i j:ι)(z:T→ℂ):=lever (fun t=>z (i,j,t))
   have h(i j:ι):Continuous (k i j):=(continuous_apply _).prodMk
          ((continuous_apply _).prodMk (continuous_apply _))
   let U:Set (T→ℂ):={z| ∀i j,Topaz (k i j z) (AudEu a P x (L i) (M j)) δ}
   have o:IsOpen U:=by
    refine isOpen_iff_mem_nhds.mpr fun z y=>?_
    show ∀ᶠ z' in 𝓝 z, ∀i j,Topaz (k i j z') _ _
    exact eventually_all.mpr fun i=>eventually_all.mpr fun j=>
       (h i j|>.continuousAt).preimage_mem_nhds (likelier _ _ (y i j))
   obtain ⟨t,v',w,K,H⟩:=after_knives P x s
         (fun t:T=>f t.1 t.2.1 t.2.2) o (fun i j=>(b i j).2) N
   refine ⟨t,v',w,K,fun i j=>?_⟩
   have S:=covered_sharp a P x s t (L i) (M j) (u i) (v j) (b i j).1 v'
   refine ⟨S,H.mono fun r e=>⟨e.1,e.2.1,?_⟩⟩
   unfold SharpEu
   rw [← S.product]
   exact e.2.2 i j


structure CourtLedger (δ:ℝ):Prop where
   force:Force P x L M a δ
   any_use :
    ∃N,RadiusAudit a N ∧
     ∃ n:ℕ,∀(s:ℕ)(u v:ι→ℕ), n  ≤ s→(∀i,n ≤ u i)→(∀j,n ≤ v j)→
      ReadyToGo P x L M s u v →
      Seven P x L M a s u v δ ∧
      ∃ t, s ≤ t ∧ ∃r:P.Test,Lodgment P t (N+1) r ∧
       (∀i j,SharpBill a P x s t (L i) (M j) (u i) (v j) δ r) ∧
       ∀ᶠ k in atTop,∃ q,∀i j, Served a P x t r k q (N+1) (L i) (M j) s (u i) (v j) δ

theorem force_election [Nonempty ι](h:Force P x L M a δ):
       CourtLedger P x L M a δ:=by
   obtain ⟨N,p⟩:=encloses a
   choose w k using h.el
   let m:ℕ:= (Finset.univ:(Finset (ι × ι))).sup (fun i=>w i.1 i.2)
   refine ⟨h,N,p,m,?_⟩
   intro s u v h1 h2 h3 q
   have b:Seven P x L M a s u v δ:=by
      intro i j
      have d:w i j ≤ m:=Finset.le_sup (f:=fun i:ι×ι=>w i.1 i.2)
        (Finset.mem_univ (i,j))
      exact k i j _ _ _ (d.trans (h2 i)) (d.trans (h3 j)) (d.trans h1) (q i j)


   obtain ⟨t,v',r,g,j⟩:=sharp_party P x L M a s u v δ (N+1) b
   refine ⟨b,t,v',r,g,j,?_⟩
   have w:∀ᶠ k in atTop,∀i j,∃q,Served a P x t r k q (N+1)
       (L i) (M j) s (u i) (v j) δ:=eventually_all.mpr fun i=>eventually_all.mpr fun l=>
        banquet a P x t r (L i) (M l) s (u i) (v l) δ N p g (j i l)
   refine w.mono ?_
   intro k w
   let i:=Classical.arbitrary ι
   exact ⟨(w i i).choose,fun i j=>(w i j).choose_spec⟩

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
