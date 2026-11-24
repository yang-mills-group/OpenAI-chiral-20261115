import Bay.D.Ingot
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

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal
local notation "VΩ"=>VacuumSelection.Spine


variable (P:VΩ)(i k:ℕ→ℕ)
def Dunk(P:VΩ)(s r g:ℕ):=Canopy P.run s r g P.large
def Mile(P:VΩ)(s:ℕ): Prop:=∀r,∀ᶠ g:ℕ in atTop,Dunk P s r g
lemma miles (f:DryDock P.par):∀ᶠ s in atTop,Mile P s:=canopies _ _ f
-- all terraces, preserves election
structure Roadie (P:VΩ)(i k:ℕ→ℕ):Prop where
 profiles:∃ π ψ, StrictMono π∧ StrictMono ψ∧i=P.period ∘ ψ ∧ k=P.cutoff ∘ π
 paired(j): legacy P.run (i j) (k j)
 rowing:Row P i k
 housed:∀s,Mile P s→ Encore P s i k


variable {P i k}
lemma Roadie.opens{φ:ℕ→ℕ}(a:Roadie P i k)(f: StrictMono φ):
   Roadie P (i ∘ φ) (k ∘ φ):=by
 have e:=row_shifts P a.rowing f.tendsto_atTop
 refine ⟨?_,fun _=>a.paired _, e,fun _ h=>⟨e,f.tendsto_atTop.eventually (a.housed _ h).2⟩⟩
 obtain ⟨u,v,w,p,r,s⟩:=a.profiles
 exact ⟨_,_,w.comp f,p.comp f, congrArg (· ∘ φ) r,congrArg (· ∘ φ) s⟩

variable (P)


lemma gated (n:ℕ):∀ᶠ j in atTop, legacy P.run (P.period n) (P.cutoff j):=
  (P.run.uv_grows.tendsto_atTop.comp P.law.pick.grow_k.tendsto_atTop).eventually_ge_atTop _
def CheckM (n j:ℕ):Prop:=legacy P.run (P.period n) (P.cutoff j)∧
  ∀s≤n,Mile P s→ Dunk P s (P.period n) (P.cutoff j)

lemma checked (n):∀ᶠ j in atTop, CheckM P n j:=by
 refine (gated P n).and ?_
 change ∀ᶠ j in atTop,∀s∈Set.Iic n,Mile P s → Dunk P s (P.period n) (P.cutoff j)
 apply (eventually_all_finite (Set.finite_Iic _)).mpr
 intro s _
 by_cases h:Mile P s
 · exact (P.law.pick.grow_k.tendsto_atTop.eventually (h (P.period n))).mono fun _ y _=>y
 exact Eventually.of_forall (fun _ e=>False.elim (h e))
def speed(x:ℕ→ℕ):ℕ→ℕ
 | 0=>x 0
 | n+1=>max (speed x n+1) (x (n+1))
lemma spot :∃π, Roadie P P.period (P.cutoff ∘ π):=by
 choose x h using fun n=>eventually_atTop.mp (checked P n)
 let π:=speed x
 have y : StrictMono π:=strictMono_nat_of_lt_succ (fun n=>lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left (π n +1) _))
 have g(n):=h n (π n) (by cases n with | zero=>exact le_rfl | succ n=>exact le_max_right _ _)
 let hh(n):= (g n).1
 have u:=firstRow P π y.tendsto_atTop (Eventually.of_forall hh)
 exact ⟨π,
    ⟨⟨π,id,y,strictMono_id,rfl,rfl⟩,hh,u,
     fun s v=>⟨u,(eventually_ge_atTop s).mono (fun n p=>(g n).2 _ p v)⟩⟩⟩

-- Dry prices along every Roadie including dose and kick
variable {P:VΩ}
lemma Roadie.chosen (d:Roadie P i k){f:Berth→Prop}
 (h: Dry P f):∀ᶠ s in atTop,∀ᶠ r in atTop,f (port P s i k r) ∧ Ferry P.run s (i r) (k r):=by
 filter_upwards [h] with s p
 filter_upwards [d.rowing.reaches s,d.rowing.growing.eventually p,d.rowing.cooling.eventually (P.run.uv_grows.tendsto_atTop.eventually_gt_atTop s)]
   with r y w v
 exact ⟨w _ v,y⟩
variable (A:Armor)
lemma Roadie.timely (d:Roadie P i k)(h:Armor.Strong P A)(M L:ℕ):
 ∀ᶠ s in atTop,∀ᶠ r in atTop,
  let w:=port P s i k r
  A.doses w M L ∧ A.cape w ∧ Ferry P.run s (i r) (k r) :=by
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,p⟩:=h
 simpa only [and_assoc] using d.chosen (p M L).2
def strikes(w:Berth)(A:Armor):Diadem w:=
  if h:∃x,Seamew w A x then h.choose else default
lemma striking{A:Armor}{w:Berth}(h:∃x,Seamew w A x):Seamew w A (strikes w A):=by
 rw[strikes,dif_pos h];exact h.choose_spec

lemma Roadie.ready (d:Roadie P i k)(h:Armor.Strong P A):
 ∀ᶠ s in atTop,
  NamedCrew P s i k A (fun r=>strikes _ A):=
   (d.timely A h 1 1).mono fun _ g=>g.mono fun _ p=>striking (Armor.mews p.1 p.2.1)

variable (P:VΩ)
lemma gathers (h:Armor.Strong P A):
 ∃ i k:ℕ→ℕ,Roadie P i k∧∀ᶠ s in atTop,Nonempty (Setpiece P A s i k):=by
 obtain ⟨p,r⟩:=spot P
 obtain ⟨q,g,s⟩:=harmonies _ _ P A r.rowing (fun _ _=>strikes _ A)
 exact ⟨_,_,r.opens g, (r.ready A h).mono fun l h'=>
    (s l h').set g h'⟩
end YM.CF.Bay.D
