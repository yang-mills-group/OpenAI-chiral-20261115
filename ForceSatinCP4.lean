import SU5SatinProgressNovember7B
import ForceSatin.Pigment
import ForceSatin.Parterre
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

structure PublicKernel (P:Spine) (S:ℕ→ℕ) (W:ℕ→HorizonLens→HorizonLens→ℝ) :Prop where
 arrow (s:ℕ):∃ A:ℕ, CompassChar (fun i=> Papal.count P.run s (ΦWork P (S (A+i)))) (fun i=>(Papal.gram P.run s (ΦWork P (S (A+i))) (ζWork P (S (A+i)))).J.M)
 Wick (L:List Bite) : zTariff L= Emu.runes WickP L
 pigment (i j:PlaqAxes)(k l:SU.group.ColorIndex)(s)(x y:Cover): (↑(W s ((x,i),k) ((y,j),l)):ℂ)= (sch (G:=SU.group) k l:ℂ)*wObj (W s) i j (x-y)
 W_price(i j:PlaqAxes)(m:List Cover): ∃ C:ℝ,0<C∧∀ s x, x≠0→ ‖muJet m (wObj (W s) i j) x-muJet m (specter i j ∘ scape) x‖ ≤ C/rally x^(5+m.length)
 W_particle(x y:Bite) : y.hand=false → x.hand=true → x.spin∉plusHalf → y.spin∈plusHalf → let Q:=if x.cost=y.cost then tradeW x.spin y.spin (x.root-y.root) else 0; WickP y x=Q ∧ WickP x y=-Q
 W_like(x y:Bite):x.hand=y.hand→ WickP x y=0
 W_theta(i j:SpinIdx)(m:List Cover) : i∉plusHalf → j∈plusHalf → ∃ C:ℝ,0<C ∧ ∀ (x:Cover), x≠0→ ‖muJet m (tradeW i j) x-muJet m (CF.Papyrus.Franc.SatinForce.Flash i j ∘ scape) x‖ ≤ C/rally x^(4+m.length) -- units here WA matter spacings, no 1/4 on any leg

lemma makePub {P:Spine}{K:P.Register}{b C:ℝ}{t:ℕ→ℝ}{S:ℕ→ℕ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}(H:CouncilGrant P K b C t S W β): PublicKernel P S W:=by
 let h:= H.order.tendsto_atTop; let F:=H.path_permanent
 obtain ⟨k,T⟩:= sagaChar P.run P.law P.history h F 0
 exact ⟨sagaChar P.run P.law P.history h F,T.opus,fun i j k l s x y=> lagoon P.run P.law P.history h F s i j x y k l,worx P.run P.law P.history h F,T.stars,T.dark,SunRay T⟩ -- tune
-- custom petition.Strong *additional* qualifications on WC for E Laws already buying CensusGrant
theorem sameHessElection (M L : ℕ) (d h' βmin : ℝ) (hd : 0 < d) :
    ∃ (P : Spine) (K : P.Register) (n:ℕ) (b C : ℝ) (bare_ : ℕ → ℝ),
      2*strive_E 6 < (n:ℝ) ∧ L ≤ P.par.R.L.val ∧ P.par.R.L.val%16=1 ∧ 15 ∣ P.par.R.L.val ∧
      TintCommercial n (crayon (fun _ _ _ _ _ _=>0)) P.par ∧ Solstitial P.par ∧
      Rocky P K M ∧ CathedralQ P ∧ SingleRootFinance P ∧ LitFuture P M ∧
      P.UnderLease P.jump128 0 ∧ h' ≤ P.par.h ∧ P.par.d ≤ d ∧ βmin < P.par.x ∧
      ∀ S:ℕ→ℕ, StrictMono S → ∃ (U:ℕ→ℕ)(W:ℕ→HorizonLens→HorizonLens→ℝ)(β:ℕ→ℝ), StrictMono U ∧
      CouncilGrant P K b C bare_ (S ∘ U) W β ∧ PublicKernel P (S ∘ U) W ∧
      ∀ good:P.Spectrum0 3→Prop, (∀ᵐ x ∂P.pillars 3,good x) → ∃ x, good x ∧ JointTuple.{uΩ} P K x := by
 obtain ⟨P,K,n,b,C,k,k₁,k₂,k₃,h,h₁,t,t₁,t₂,e,f,z,z₁,z₂,w,ϑ⟩:= sameWickElection.{uΩ} M L d h' βmin hd; refine ⟨P,K,n,b,C,k,k₁,k₂,k₃,h,h₁,t,t₁,t₂,e,f,z,z₁,z₂,w,?_⟩ -- tune #bind
 intro S u; obtain ⟨U,W,β,F,x,y⟩:=ϑ S u; exact ⟨U,W,β,F,x,makePub x,y⟩
#check @sameHessElection
#print axioms timely
#print axioms pastoral
#print axioms SunRay
#print axioms sameHessElection
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
