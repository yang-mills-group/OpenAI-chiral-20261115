import Bay.D.Polyp
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

variable (P:VΩ)(s:ℕ)
local notation "K"=>P.calibration
local notation "N" i:max=>Papal.count P.run s i
local notation "Ω"=>D.scale P s
local notation "SΩ"=> Band inletO (radiusB Ω)
local notation "τ"=>temp (D.scale P s)



variable {i k:ℕ→ℕ}(A:Armor)
variable (t:Mission P s i k)
abbrev scoreList :=fun r=>(t r).leading
abbrev betaList :=fun r=>Diadem.bén (port P s i k r)
def Stills (φ:ℕ→ℕ):Prop:=
 (∃p, Tendsto (fun r=>Diadem.bén (port P s i k (φ r))) atTop (𝓝 p))∧
 (∃p,Tendsto (scoreList P s t ∘ φ) atTop (𝓝 p))∧
 (∃w:campZ P s A,∀ᶠ r:ℕ in atTop, (t (φ r)).signal=w.fleet r ∘ Lifted.onC _)
def SetRoll:= {z:ℕ→ℕ//StrictMono z}
instance: CoeFun SetRoll (fun _=>ℕ→ℕ):=⟨Subtype.val⟩
variable {P s A t}
variable {φ ψ χ:ℕ→ℕ}
-- q:ℕ→ℕ variable. 
def Gather.dive {o:Cover}{b:ℕ}{g d c:ℝ}{q:ℕ→ℕ}
 (w:Gather o b g d c)(h:Tendsto q atTop atTop):Gather o b g d c:=
 ⟨w.fleet ∘ q, w.rise, fun i=>w.wash _,
   by exact w.spun,
   by
     rw [Metric.tendstoUniformly_iff]; intro e h0
     exact h.eventually ((Metric.tendstoUniformly_iff.mp w.dawn) e h0)⟩

def Retains (φ ψ:ℕ→ℕ):Prop:= ∃q:ℕ→ℕ,Tendsto q atTop atTop∧
 φ ∘ q =ᶠ[atTop] ψ

lemma Stills.thin (p: Stills P s A t φ)(q: Retains φ ψ):
 Stills P s A t ψ:=by
 obtain ⟨⟨b,h⟩,⟨a,y⟩,w,l⟩:=p
 obtain ⟨f,u,v⟩:=q
 refine ⟨⟨b,(h.comp u).congr' (v.mono fun _ e=>congrArg (fun r=>Diadem.bén (port P s i k r)) e)⟩,
   ⟨a,(y.comp u).congr' (v.mono fun _ e=>congrArg (scoreList P s t) e)⟩,
   w.dive u,?_⟩
 filter_upwards[v,u.eventually l] with r g d
 rw [←g]; exact d
lemma Stills.set {φ:ℕ→ℕ}
  (p:Stills P s A t φ)
  (q:StrictMono φ)
  (g:NamedCrew P s i k A t):
 Nonempty (Setpiece P A s (i ∘ φ) (k ∘ φ)):=by
 obtain ⟨⟨b,h⟩,⟨a,y⟩,w,l⟩:=p
 exact ⟨⟨fun r=>t (φ r),q.tendsto_atTop.eventually g,w,l,b,h,a,y⟩⟩

lemma friezes (g: Row P i k)(h:NamedCrew P s i k A t)
 (y:StrictMono φ): ∃ζ,StrictMono ζ∧ Stills P s A t (φ ∘ ζ):=by
 let β (r:ℕ):=Diadem.bén (port P s i k r)
 have hβ:∀ᶠ r:ℕ in atTop,(β ∘ φ) r ∈ Set.Icc (Ω/2) (2*Ω):=
   (y.tendsto_atTop.eventually h).mono (fun _ p=>Diadem.per_tick _ p)
 obtain ⟨βg,x,ψ,p,v⟩:=isCompact_Icc.tendsto_subseq' hβ.frequently
 have hl:=y.comp p
 have hp:∀ᶠ r in atTop, scoreList P s t ((φ ∘ ψ) r) ∈ Set.Icc (lbott A.δ) (lcap A.fee) :=
   (hl.tendsto_atTop.eventually h).mono (fun _ s=>Diadem.score_mass _ s)
 obtain ⟨j,a,q,m,b⟩:=isCompact_Icc.tendsto_subseq' (x:=scoreList P s t ∘ φ ∘ ψ) hp.frequently
 let r:= φ ∘ ψ ∘ q
 let rr := (hl.comp m).tendsto_atTop
 have hu:(∀ᶠ u in atTop,AtEase SΩ (N (i u))):=by
   filter_upwards [((Journey.momentum P.run s).comp g.growing).eventually (separates K SΩ)] with u e
   have : AtEase SΩ (P.calibration.c (momentm P.run (i u) s)):=e
   rw [show N (i u) = P.calibration.c (momentm P.run (i u) s) from
     (Journey.terrain P.run P.large (P.run.ir (i u)) s).symm];exact this

 let hs:=rr.eventually (h.mono fun _ v=>Diadem.spruces _ v)
 obtain ⟨v',k',C,l⟩:=gatherings (t:=τ) (d:=P.par.d) (L:=Ω * A.fee) (R:=fun n=>N (i (r n))) (g:=fun n=>(t (r n)).signal) hs (rr.eventually hu)
 exact ⟨ψ ∘ q ∘ v',p.comp (m.comp k'),
    ⟨βg,v.comp (m.comp k').tendsto_atTop⟩,
    ⟨j,b.comp k'.tendsto_atTop⟩,C,Eventually.of_forall l⟩


namespace GrainDiag
abbrev Stairs:=(n:ℕ)→SetRoll
abbrev slash (D:Stairs)(n):=D n n
variable (D:Stairs)
def More (D:Stairs):Prop:= ∀n,∃φ:ℕ→ℕ,StrictMono φ∧ (D n) ∘ φ = D (n+1)
lemma rises(w:More D):StrictMono (slash D):=by
 apply strictMono_nat_of_lt_succ
 intro x
 obtain ⟨φ,t,e⟩:=w x
 exact lt_of_lt_of_eq ((D x).2 (Nat.lt_succ_self x |>.trans_le (t.id_le _))) (congrFun e _)

lemma splice(w:More D)(m n:ℕ)(g:m≤n):∃ζ, n≤ζ∧D m ζ = slash D n:=by
 suffices ∀j,n≤j→∃ζ,n≤ζ∧D m ζ=D n j from this _ le_rfl
 intro j h
 obtain ⟨p,t,e⟩:(∃p:ℕ→ℕ,StrictMono p∧D m ∘ p = D n):=by
    clear h j
    induction n,g using Nat.le_induction with
    | base=>exact ⟨id,strictMono_id,rfl⟩
    | succ n h ih=>
      obtain ⟨φ,x,b⟩:=ih
      obtain ⟨v,r,l⟩:=w n
      exact ⟨φ ∘ v,x.comp r,congrArg (· ∘ v) b |>.trans l⟩
 exact ⟨p j,h.trans (t.id_le _),congrFun e _⟩

lemma carries(w:More D)(m:ℕ):Retains (D m) (slash D):=by
 choose! p h t using splice D w m
 exact ⟨p,tendsto_atTop_mono' _ (f₁:=id)
          ((eventually_ge_atTop m).mono fun n g=>h n g) tendsto_id,
   (eventually_ge_atTop m).mono fun n g=>t n g⟩


end GrainDiag

variable (i k:ℕ→ℕ)(P:VΩ)(A:Armor)
open GrainDiag (Stairs slash carries rises)
abbrev Pilots:=(s:ℕ)→Mission P s i k
-- common diagonal for all paid
lemma harmonies (d:Row P i k) (T:(s:ℕ)→Mission P s i k):
 ∃ψ, StrictMono ψ∧∀s,NamedCrew P s i k A (T s)→
      Stills P s A (T s) ψ:=by
 let B(n):=fun ψ=>NamedCrew P n i k A (T n)→
      Stills P n A (T n) ψ
 have p(n:ℕ)(φ:SetRoll):∃ q:SetRoll,B n (φ ∘ q):=by
    by_cases e:NamedCrew P n i k A (T n)
    · obtain ⟨v,t,x⟩:=friezes d e φ.2
      exact ⟨⟨v,t⟩,fun _=>x⟩
    exact ⟨⟨id,strictMono_id⟩,fun z=>False.elim (e z)⟩
 choose q h using p
 let D:Stairs:=Nat.rec (motive:=fun _=>SetRoll) ⟨id,strictMono_id⟩
     (fun n p=>⟨p ∘ q n p,p.2.comp (q n p).2⟩)
 have a:GrainDiag.More D:=fun n=>⟨_,(q n (D n)).2,rfl⟩
 exact ⟨slash D,rises _ a,fun s e=> (h s (D s) e).thin (carries D a (s+1))⟩
end YM.CF.Bay.D
