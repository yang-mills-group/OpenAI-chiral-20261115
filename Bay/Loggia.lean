import Bay.Moored
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


namespace Berth
variable (w:Berth)
variable {I:Type}[LinearOrder I][Fintype I]
variable (σ:I→Seat w.side)(x:I→Site w.side)(f:I→w.First)(v:I→Sour.Bag w.side)
abbrev Tall := 20 ≤ w.p.B
abbrev Baskets (σ:I→Seat w.side)(x:I→Site w.side): Prop:=
   ∀i,σ i∈grooveB 24 w.p (node (x i))
abbrev bandY (m:ℕ)(x:I→Site w.side):I→footprint w.side:=fun i=>w.supportY m (x i)
abbrev copiesY (m:ℕ)(x:I→Site w.side)(f:I→w.First):I→Stencil w.side:=
   fun i=> w.marked129 (x i) (f i) m
abbrev agentsY (m:ℕ)(x:I→Site w.side)(f:I→w.First):I→phy w.side:=
   fun i=> w.cloth (x i) (f i) m
abbrev costItem (w:Berth)(b:ℝ):I→ℝ:=fun _=> w.hue *costY b
abbrev certainly (w:Berth):Orbit w.side→Prop:= fun _=>True
lemma indisputable : w.Glut w.certainly:=Eventually.of_forall fun _=>True.intro

variable {w σ x f v} {m L M:ℕ} {a c b:ℝ}
 {F:ℝ→ℝ}
 {r:blazeK w.side}

lemma wearer (d:∀i,w.WearY m (x i) (f i) a c b (v i)):
 w.Quest (w.bandY m x) (w.costItem b) (w.copiesY m x f)
   (w.agentsY m x f) v w.certainly:=

 ⟨fun i=>(d i).fit, fun u i _ p=> (d i).stitch.science u p⟩

lemma stowed (g:w.Tall)
 (h:24*m ≤ w.p.B)(j:w.Baskets σ x)
 (l:LatticeWide σ w.p.B):
 ∀ z,ψS σ z → independent z (w.bandY m x):=by
 have a(i:I)(u)(p:u∈w.bandY m x i):separation (σ i) u ≤ 50*w.p.B:=by
    obtain ⟨b,r,c⟩:= halo_spec.mp p
    rw [mem_singleton.mp r] at c
    obtain ⟨e,y,z⟩:=halo_spec.mp (j i)
    rw [mem_singleton.mp y, separation_comm _ (σ i)] at z
    exact le_trans (separation_triangle _ _ _) (le_trans (Nat.add_le_add z c) (by
      unfold Tall at g;omega))
 intro z p
 refine (List.pairwise_map.mp p).imp ?_
 intro i k u
 refine disjoint_left.mpr ?_
 intro b t v
 have r:= l i k u
 have d0:=le_trans (separation_triangle (σ i) b (σ k)) (Nat.add_le_add (a _ _ t) ((separation_comm ..).trans_le (a _ _ v)))
 unfold Tall at g
 have d1:50*w.p.B+50*w.p.B ≤ 2*w.p.B^3 := by
   have hh:50 ≤ w.p.B^2:= (show 50 ≤ (20:ℕ)^2 by decide).trans (pow_le_pow_left₀ (Nat.zero_le _) g _)
   rw [show (3:ℕ)=2+1 from rfl,pow_succ]; have hx:=Nat.mul_le_mul_right w.p.B hh;omega -- nlinarith
 omega

local notation "C129" => till129 w.P a c b m
local notation "D129" => reserve129 w.P a c b m -- bound notation inserted with vars if coming
-- fees specialized
abbrev ceremony (P:VΩ)(M L:ℕ)(F:ℝ→ℝ)(a c b:ℝ)(m:ℕ):=
   icedCost P M L F (reserve129 P a c b m)

abbrev Yields_m (σ:I→Seat w.side)(x:I→Site w.side)(f:I→w.First)(v:I→Sour.Bag w.side)
 (M L:ℕ) (a c b:ℝ)(m:ℕ) (F:ℝ→ℝ)
 {r:blazeK w.side}
 (g:w.Thermal M L F C129 D129 r) :=
  (∀ z,ψS σ z→ independent z (w.bandY m x)) ∧
  ∃ E B, ∃ d:w.Cached σ v L E B C129 D129, 
       OrbitRack (w.coincert g.1) σ w.q w.R.K w.H (flare d.bill)
         (riseF E) (riseF B) r (flareM (w.melt σ v L)) ∧
       ∀ (s:ℕ)(τ:Ids w.side),w.lampCap ≤ s →
        let U:=w.flareE d σ s τ
        let V:=w.flareF d σ s
        w.Moored (w.bandY m x) σ (w.costItem b) (w.copiesY m x f)
           (w.agentsY m x f) w.certainly L 
           (ceremony w.P M L F a c b m w.x) U V ∧
         ∀ i,νTip U i=kilnTip d.bill σ τ i∧
           emberTip V i=νΦK (rootF w.R (flare d.bill) s) {i}


lemma yields (h:w.Rig a c m)(k:w.Tall)
 (g:w.Thermal M L F C129 D129 r)
 (d:w.GaugeBill M σ)(j:w.Baskets σ x)
 (e:∀ i,w.WearY m (x i) (f i) a c b (v i)):
  Yields_m σ x f v M L a c b m F g:=by
 have u:=wearer e
 obtain ⟨_,_,z,t⟩:=cacheTherm g d
    (fun i=> rootLodge w ((e i).stitch.pouch) (j i))
 exact ⟨stowed k h.sizes.1 j d.2,_,_,z,t,fun s τ v=>
    unspooled g h d z u (indisputable w) s v τ⟩
end Berth

open Buffered.Afterglow.Tower.VacuumSelection.Spine

universe u
structure Sediment(w:Berth)(a c b W δ:ℝ)(m M L:ℕ)(F:ℝ→ℝ) : Prop where
  old : Bourne w a c b W δ m
  tall:w.Tall
  every: ∀ x f,w.Before a b m x f→∃v,w.WearY m x f a c b v
  young: ∃ r,∃q:w.Thermal M L F (till129 w.P a c b m) (reserve129 w.P a c b m) r,
      ∀ (I:Type)[LinearOrder I][Fintype I]
       (σ:I→Seat w.side)(x:I→Site w.side)
       (f:I→w.First)(v:I→Sour.Bag w.side),
       w.GaugeBill M σ → w.Baskets σ x →
       (∀i,w.WearY m (x i) (f i) a c b (v i)) →
       Berth.Yields_m σ x f v M L a c b m F q

def OfBay2 (P:VΩ):Prop:=
 let m:=tabW P
 ∃ a c b W δ:ℝ,∃ F : ℝ→ℝ,0<a ∧ 0<c ∧ 0<b ∧ 0<W ∧ 0<δ ∧
      Ice P F ∧
      NPL (till129 P a c b m) ∧ NPL (reserve129 P a c b m) ∧
      ∀ M L:ℕ,
      PinNPL P (Berth.ceremony P M L F a c b m) ∧
      Dry P (fun w=> Sediment w a c b W δ m M L F)


lemma Hammer.two {P:VΩ}{Mc:ℕ}{X:TintDemand}(j: Hammer P Mc X): OfBay2 P:=by
 obtain ⟨a,c,b,W,δ,t,h,g,v,p,q,k,f⟩:=j.one
 obtain ⟨F,x⟩:=j.ice
 refine ⟨a,c,b,W,δ,F,t,h,g,v,p,x,q,k,fun M L=>?_⟩
 have n:=ripening x M L q k
 refine ⟨n.rate,?_⟩
 filter_upwards [f,n.ready,(Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop 20] with s u y o
 filter_upwards [u,y] with i d b0
 intro k p
 let w:=takeUp P s i k
 have G:= d k p
 have H:= G.cradle.1
 obtain ⟨r,z⟩:=b0 k p (Berth.readyRails H)
 have T:w.Tall:=by unfold Berth.Tall;change 20 ≤ (takeUp P s i k).p.B; rw[H.sizeB]; exact o
 refine ⟨G, T, fun _ _ z=>Berth.weft H z,
   r, z, ?_⟩
 intro I h u σ x f v d g e
 exact Berth.yields H T z d g e

theorem Bay2 (Mc:ℕ)(X:TintDemand) :
 ∃ (P:VΩ)(K:P.Register),
    Hammer P Mc X ∧
    FirstLease P ∧ Post124 P.run ∧
    SprigFee P ∧ OfBay2 P ∧
    ∀(good:P.Spectrum0 3→Prop), (∀ᵐ y∂P.pillars 3,good y)→∃ y,
      good y ∧ JointTuple.{u} P K y :=by
 obtain ⟨P,K,w,s⟩:=harbor.{u} Mc X

 exact ⟨P,K,w,w.leases,w.leases.post,SprigFee.paid P,w.two,s⟩

end YM.CF.Bay
#print axioms YM.CF.Bay.Bay2
