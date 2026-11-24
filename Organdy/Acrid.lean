import Organdy.Copper
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
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



open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Vow.TreasuryFog
section
variable {N:Side}
lemma cymbalUnit (S:Support (More N)) : Cymbal S 1 1 1 := by
 refine ⟨.oneM S,fun x=>by simp,fun g x=>by simp,fun _=>.one,fun _ _ _=>rfl,fun _ _=>rfl⟩
lemma play {S:Support (More N)}{a:ℝ}{F:Mark N} {V:phy N}(h:Cymbal S F V a)
 (l:Scree.Loom N) (W:Orbit N)(y:Phys N) :
 letterRead (F (W.1,l W)) y=beamZ N (acts (V W) y):=by
 have t:=h.tie W (l W)
 change inner ℂ (mateK N) (acts (F (W.1,l W)) y) = inner ℂ _ (acts (V W) y) -- fill
 rw [←act_inner,←act_inner,t]
end

section
variable {N:Side}{α:Type*}{a:α→ℝ}{S:α→Support (More N)}{F:α→ Mark N}{V:α→phy N}
lemma parade (r:List α)(h:∀ i∈r,Cymbal (S i) (F i) (V i) (a i))
 (p:r.Pairwise (fun i j=>Disjoint (S i) (S j)))
 (q:∀ i∈r,0≤a i) :
 Cymbal (r.toFinset.biUnion S) (r.map F).prod (r.map V).prod (r.map a).prod :=by
 induction r with
 | nil => simp only [List.map_nil,List.prod_nil]; exact cymbalUnit _
 | cons i r ih=>
    obtain ⟨v,w⟩:=List.pairwise_cons.mp p
    have d: Disjoint (S i) (r.toFinset.biUnion S) :=
      disjoint_left.mpr (fun x y z=>by
         obtain ⟨j,t,u⟩:=mem_biUnion.mp z
         exact disjoint_left.mp (v _ (List.mem_toFinset.mp t)) y u)
    simp only [List.toFinset_cons,biUnion_insert,List.map_cons,List.prod_cons]
    exact (h i (by simp)).weave (ih (fun j t=>h j (by simp [t])) w (fun j t=>q j (by simp [t]))) (q i (by simp)) d
end


variable (P:Spine)(i k s:ℕ)
local notation "Λ"=>P.par
local notation "xt"=>hat (Λ).R.L (Λ).x s
local notation "N'"=> age P.run i s
local notation "KL"=> (P.run.voyage i).CapeT s
local notation "R✤"=>RootBook P.run i k s


local notation "D✤"=> partitionZ R✤ (Λ).U KL
local notation "T✤"=> denZ R✤ (Λ).U KL
abbrev curtain (z:Orbit N') := pilotH (Λ).U R✤ KL z (projects_here P.run i k s z).1
abbrev floorY (z:Orbit N'):=poseL _ (fueled (R✤).p (R✤).K z)
local notation "π'"=>curtain P i k s
lemma pure_price (z:Orbit N'): T✤ z= π' z (floorY P i k s z) := by
 have h:= showUp (R:=R✤) (Λ).U KL z (projects_here P.run i k s z).1 0 (R✤).K
 have hp:exponentL (R✤).p 0 z.1=0:=by simp [exponentL,numbE]
 rw [hp,exp_zero,one_mul,add_zero] at h
 exact h

/-- Opening that intertwines after pushing through the exponential. -/
def passage (U:phy N')(B: Sour.Bag N'):Prop:=
 ∀ z:Orbit N',∀ x:Wave (Dwell N'),π' z (acts (∑ u:Aura N', B u z) x)=
    acts (U z) (π' z x)

variable {α:Type*}{S:α→Support (More (age P.run i s))}{a:α→ℝ}
 {F:α→Mark (age P.run i s)}{U:α→phy (age P.run i s)}
 (B:α→Sour.Bag (age P.run i s))(r:List α)
def bundle (z:Orbit N') := (r.map (fun j=> ∑ u:Aura N', B j u z)).prod
lemma threaded (g:∀ j∈r,passage P i k s (U j) (B j))(z:Orbit N')
 (x:Wave (Dwell N')):
 π' z (acts (bundle P i s B r z) x)=
  acts ((r.map U).prod z) (π' z x):=by
 unfold bundle
 induction r with
 | nil=>simp
 | cons j r ih=>
  simp only [List.map_cons,List.prod_cons,Pi.mul_apply,act_mul]
  rw [g j (by simp), ih (fun l y=>g l (by simp [y]))]

/-- At all surveys eligible for input_order; exact normalization and signed
not positive priced law. Formulated before exponentiating any marks.
Use with Squid.flight.science. Integrability of the WHOLE coupon, even
where flags fired. -/
lemma till (g:∀ j∈r,passage P i k s (U j) (B j))
 (h:∀ j∈r,Cymbal (S j) (F j) (U j) (a j))
 (p:r.Pairwise (fun i j=>Disjoint (S i) (S j)))
 (q:∀ j∈r,0≤a j)
 (e:(P.run.voyage i).kick≤k)(hs:s≤P.run.uv k):
 let tax:=fun z=>beamZ _ (π' z (acts (bundle P i s B r z) (floorY P i k s z)))
 Integrable tax (city N') ∧ D✤ ≠ 0 ∧
 Afterglow.Journey.compass P.run i k s (r.map F).prod=(∫ z,tax z ∂city N')/D✤:=by
 intro tax
 have v:=parade r h p q
 obtain ⟨m,d,f⟩:= Afterglow.Tapestry.funds P.run s i k v.realc.env e hs
 have he:tax=(fun z=>letterRead ((r.map F).prod (z.1, KL z)) (T✤ z)):=by
  funext z; rw [play v]
  unfold tax
  rw [threaded P i k s B r g, pure_price]
 rw [he]
 exact ⟨m,d,f⟩
