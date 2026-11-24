import Organdy.Opal
import Organdy.Aurora
import Organdy.Vaulting
import Organdy.Mesa
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

open _root_.Zephyr.Chern
open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Yoke Yoke.Bazaar
open Optic Larva -- remove

variable (P:Spine)(i k s:ℕ) {m w:ℕ}
local notation "Λ"=>P.par
local notation "xt"=>hat (Λ).R.L (Λ).x s
local notation "N'"=> age P.run i s
local notation "KL"=> (P.run.voyage i).CapeT s
local notation "R✤"=>RootBook P.run i k s

local notation "p'" => (R✤).p
local notation "Q'"=> pinpr (Λ).R.L xt
local notation "n'" => ((p').B/10)

structure Filigree (m:ℕ)(a b r B δ:ℝ):Prop where
 kickoff:(P.run.voyage i).kick ≤ k -- replace
 off:s<P.run.uv k
 classic : ∀ J T X Y, Kit P i k s 0 m a b J T X Y →
       let W:=scint KL p' X
       (∃ A,Sidelight ((p').B+6) r (p').threshold (stow xt) B δ W A) ∧
       Policy P.run (gleamδ δ) s i k W

lemma filigree {mc:ℕ}(z:Stakes mc P)
 {a b:ℝ}(ca:0<a)(co:0<b)(mo:0 < m):
 ∃ r B δ,0<r ∧ 0<δ ∧ 0<(gleamδ δ) ∧
  ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop, ∀ a' b' w,Tide P i k s m w a' b' →
         Filigree P i k s m a b r B δ:=by
 obtain ⟨C,_,_,Z,_⟩:=z.pressure
 obtain ⟨r,t⟩:=Larva.reel (Λ).dpos
 obtain ⟨D,g,u⟩:=scarf (r:=r) ca
 let B:=D*(Tenant.quota^2*b)
 obtain ⟨c,δ,n,e,d,q⟩:=soldAll P ca co mo
 have v:0<gleamδ δ := div_pos (premium_pos argent_pos d) (by norm_num)
 refine ⟨r,B,δ,t.1,d,v,?_⟩
 have h:=turnover P.par
 let T (s:ℕ):=hat (Λ).R.L (Λ).x s
 filter_upwards [
   banking (b:=B) P.run Z t.1 P.large d,
   h.eventually (dusted c ca),h.eventually (skyline gaugeRules t u g.le),q,
   (Work.E01.radiusB_tendsto.comp h).eventually_ge_atTop (10*n),
   h.eventually (aisleWide 8)] with s s₁ s₂ s₃ s₄ s₅ s₆

 filter_upwards [s₁,(Papal.count_grows P.run s).eventually_gt_atTop (4*(Pressure.radiusB (T s)/10+2)+1)] with i i₁ i₂
 filter_upwards [i₁, eventually_ge_atTop (P.run.voyage i).kick,
    P.run.uv_grows.tendsto_atTop.eventually_gt_atTop s] with k r₁ r₂ r₃ a' b' w G
 refine ⟨r₂,r₃,?_⟩
 intro J TT X Y K U
 let N:=age P.run i s
 let p:=(RootBook P.run i k s).p
 let a₀:=Pressure.radiusB (T s)

 have L:(a₀:ℝ)+20≤webX (T s):=s₆.depth
 change 4*(a₀/10+2)+1<N.val at i₂
 have c₀:p.B=a₀ := G.radius
 have c₁:p.threshold = Pressure.temp (T s) := G.sphere
 have w₀:4*(p.B/10+2) +1 < N.val:= by rw [c₀];exact i₂
 have sz:n≤p.B/10:=by change 10*n≤a₀ at s₅; omega
 have v₀:Sky (More N) (Λ).d r a D p.threshold (p.B/10) gaugeRules:=by
    rw [c₁,c₀]
    have h:N.val≤(More N).val:=by change N.val≤N.val*2;omega
    exact s₃ _ ((show 4*(a₀/10+2) ≤ N.val by omega).trans h)
 obtain ⟨A,h⟩:=opal w₀ v₀ G.stages K.knot ca.le (s₄ i k _ _ _ _ sz (dressing G.stages) K.knot K.shave K.bone)

 have w'':c*Real.exp (-a*((p.B/10:ℕ):ℝ)) ≤ stow (T s):=by
     rw [c₀];exact s₂
 let l:=h.plate
 have H:Domaine (p.B+6) r p.threshold (stow (T s)) B U A:=
     ⟨l.meas,l.move,l.loc,
      fun x=>(l.uniform x).trans (add_le_add_left w'' _),
      l.sym,l.inside,l.purse,fun x y u v j=>(l.priced x y u v j).trans (add_le_add_left w'' _)⟩

 refine ⟨⟨_,H,h.notes,h.lyrics,h.tint⟩,?_⟩
 have y:((p.B+6:ℕ):ℝ)≤webX (T s):=by
   rw [c₀];push_cast;linarith only [L]
 -- rw only threshold (don't unfold p)
 rw [c₁] at H
 exact r₁ _ y _ _ H h.tint

def Carnival (P:Spine)(m:ℕ) (a b a' b' D δ r B γ:ℝ)(w:ℕ)(f g:ℝ→ℝ):Prop:=
  Fairground P m a b a' b' D δ w f g ∧
  0<r ∧ 0<γ ∧ 0<gleamδ γ ∧
  ∀ M v:ℕ, ∀ L:Side, ∃ Ψ Φ α, SignedLease P M L (moveFare f) (moveFare (scaledBirth P g)) Ψ Φ v ∧ 
     ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,
     Reef P i k s m w v M L a b a' b' D δ f g Ψ Φ α ∧
      Filigree P i k s m a b r B γ


lemma carnaval {mc:ℕ}(z:Stakes mc P)(m:ℕ)(v:0 < m):
   ∃ a b a' b' D δ r B γ w f g, Carnival P m a b a' b' D δ r B γ w f g:=by
  obtain ⟨a,b,a',b',D,δ,w,f,g,h⟩:=carousel P z m v
  obtain ⟨r,B,y,c,d,e,q⟩:=filigree P z h.1.slope h.1.cost v
  refine ⟨_,_,_,_,_,_,_,B,_,_,_,_,h,c,d,e,?_⟩
  intro M v L
  obtain ⟨Ψ,Φ,α,c,h₀⟩:=h.2 M v L
  refine ⟨Ψ,Φ,α,c,?_⟩
  filter_upwards [q,h₀] with s u₁ p₁
  filter_upwards [u₁,p₁] with i u₂ p₂
  filter_upwards [u₂,P.run.uv_grows.tendsto_atTop.eventually_gt_atTop s] with k j u
  exact ⟨p₂ k u,j a' b' w (p₂ k u).clearing⟩
