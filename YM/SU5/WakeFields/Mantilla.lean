import SU5SatinWakePhysicalGramNovember8
import YM.SU5.WakeFields.PierWindows

/-!
# Birth board on the very Wake investment at these w-stencils

All stamps retained, *two* ℝ→ℝ estimates (including birth Wage). Applies to ANY
interleaved σ of Current marks in that statement, including at their actual camera poses.
The spacetime reconstruction problem is not solved by this CP. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     InnerProductSpace NNReal ENNReal Classical
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
universe uᵣ
open Ione Vow
open _root_.Zephyr.Chern LitCurrent
open Roots Mew
open Vow.TreasuryFog Vow.TreasuryFog.Furrow
open scoped YM.CF.Mew

variable (P: Spine)
-- requires with its compass (ℒ.G.Prices). MC.
structure NewPier (r:ℕ)(x:Cover)(t:ℕ)(w:ℝ) : Prop where
   reach : ∃ a b v c:ℝ,∃ W:ℝ→ℝ, 0 < a∧ 0 < b∧ 0 < v ∧ 0 < c ∧ BPress.NPL (matA P.run r a b v w) ∧ BPress.NPL (matB P.run r a b v w)∧ BPress.NPL W ∧
    ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, s<P.run.uv k→ let Y:=P.run; let U:= RootBook P.run i k s; let ℒ:=(P.run.voyage i).CapeT s; let α:=age P.run i s; let x':=hat P.par.R.L P.par.x s
       MaskPoint Y r s i k a b ∧ ∃ (E:StampMark P r s i k a v) (M: Site α→ Sour.Bag α),
        Stakes (compassLine E x ℒ U.p (U.p.B/10)) c ∧
        (∀ u: Site α, Booked P.run w E u (M u) (matA P.run r a b v w x') (matB P.run r a b v w x'*pinpr P.par.R.L x')) ∧
        ∀ (I:Type) [LinearOrder I][Fintype I](o:I→Site α)(τ:Ids α) (Λu:ℕ),1≤Λu→Force_M U.p.B (Cube.node∘o) t→∃ K, Armed Y (k:=k) (i:=i) (s:=s) o τ (M ∘ o) (fun i=> truePaper Y w E (o i)) t Λu (W x' * pinpr P.par.R.L x') K ∧∀ (L:List I), L.length≤ Λu → ψS (Cube.node∘o) L →
           (L.map o).Pairwise (fun j j'=>Disjoint (Preparation.purchased P.run (k:=k) (i:=i) (s:=s) j) (Preparation.purchased P.run (k:=k) (i:=i) (s:=s) j')) ∧ ∀ (S: Support (More α)) (F':Mark α), AtSupport false S F' → (∀ j∈L.map o,Disjoint S (Preparation.purchased P.run (i:=i) (k:=k) (s:=s) j)) → (P.run.voyage i).kick≤k → let A:=berthPaper (s:=s) (i:=i) (k:=k) Y o L τ K Λu F'; let V:=partitionZ U P.par.U ℒ; Integrable A (city α) ∧ V≠0 ∧ Journey.compass Y i k s (F'*(L.map o|>.map (cloth Y w E)).prod)=(∫ i,A i∂city α)/V

lemma pier_now (K:P.Register)(A:ℝ)(Mc:ℕ)(p:PreparedInvestment P K A Mc)
 (r:ℕ)(h:0<r)(x: Cover)(t:ℕ)(w:ℝ) : NewPier P r x t w:=by
 let p':= p.lit; let W := P.scheduleLease p'.roster p'.payment p'.season p'.rate r h x
 obtain ⟨a,b,v,c,ha,hb,hv,hc,g,M⟩:= W.eventual
 let Y:=P.run; let F:=matA Y r a b v w; let G:=matB Y r a b v w
 obtain ⟨Pay,kp,Γ,Tξ,u,H⟩:=p.lit.support; obtain ⟨V,hV,R⟩:= pillarStage Y H t F G (g w).1 (g w).2
 constructor
 refine ⟨a,b,v,c,V,ha,hb,hv,hc,(g w).1,(g w).2,hV,?_⟩
 filter_upwards [M,R,(Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop 10] with s p hs h
 filter_upwards [hs] with i h' k K Y' U l α x'
 let Np:=(U).p; let tx:=pinpr P.par.R.L x'; obtain ⟨ζ,E,X,Yκ⟩:=p i k K; obtain ⟨M0,Z,vκ⟩:= Yκ w
 refine ⟨ζ,E,M0,X,Z,?_⟩
 intro I _ _ o τ u hu t
 obtain ⟨J,hR⟩:= ofWorldBorn (a:=F x') (b:=G x') Y (k:=k) (i:=i) (s:=s) o τ (V x'*tx) (h' k K) t u hu (fun j=> truePaper Y w E (o j)) (M0 ∘ o) (fun i=> (Z (o i)).nest)
 refine ⟨J,hR,?_⟩
 intro L tl q; have he:= pierGap (k:=k) (i:=i) (s:=s) Y o L t (ζ.B0.symm ▸ h) q
 refine ⟨he,?_⟩; intro S F' pF pH e; exact pierCompass Y w E M0 Z o L τ J hR F' pF tl q he pH K e

theorem cpEarth (A:TintDemand)(Mc:ℕ) : ∃ (P : Spine) (K:P.Register) (E:ℝ),
   PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧ QualifiedWakeReadout.{uᵣ} P K ∧ PhysicalWakeGram P ∧
   ∀ (x:Cover) (t:ℕ) (w:ℝ), NewPier P P.jump128 x t w:=by
 obtain ⟨P,K,E,v,h,q,G⟩:= Spine.wakeElectionWithPhysicalGram.{uᵣ} A Mc
 exact ⟨P,K,E,v,h,q,G,fun x t w=> pier_now P K E Mc v _ P.jump_pos x t w⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.cpEarth
