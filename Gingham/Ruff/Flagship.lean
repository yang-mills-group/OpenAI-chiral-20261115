import Gingham.Ruff.Sailing
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s

variable {P a c μ d s}
    {ν:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ d ν F)
set_option linter.unusedSectionVars false
open Footlight

variable {n:ℕ}(α:Sailing P a c μ d ν s n)

local notation "iₙ"=>irr P (ν n)
local notation "kₙ"=>uvv P (ν n)
local notation "N"=>Journey.side P.run iₙ s
local notation "Rₙ"=>RootBook P.run iₙ kₙ s
local notation "Aₙ"=> (P.run.voyage iₙ).CapeT s
local notation "Δ"=>denZ Rₙ P.par.U Aₙ
local notation "𝒢"=>Scree.city N
local notation "χ"=>partitionZ Rₙ P.par.U Aₙ
local notation "𝒳"=>fun f:Family P.calibration=>exhibit Y P.large s iₙ f


namespace Letter

include α
/-- Any position request an exact response, by reordering
     to give it custody of the first position. -/
lemma casement
 (l r:List (Letter P))(h:l.Pairwise (Ocean α))(t:l.Perm r):
     stunt α l= stunt α r:=by
 funext x
 suffices q: ((l.map (takes α x)).map primed).Pairwise Commute by
   exact List.Perm.prod_eq' ((t.map _).map _) q
 rw [List.pairwise_map,List.pairwise_map]
 apply h.imp
 intro A B ht
 apply (Footlight.shift _ _ ?_).2
 have a(X:Letter P):(takes α x X).plot=anchorage α X:=by cases X <;> rfl
 rw [Space,a,a];exact ht

local notation "⊙"w:max=>effect (maidS w) 1

abbrev reply(w:List (Axis×ℤ))(x:Orbit N):=
    GarlandBook.answer P.par.U (Rₙ) α.gb α.bre (maidS w) (maidU w) x

def response(l:List (Letter P))(w:List (Axis×ℤ))(z:ℝ)(x:Orbit N):ℂ:=
   z * (⊙w) * beamZ N (acts (stunt α l x) (reply α w x))

lemma assault (l:List (Letter P))(z:ℝ)(w:List (Axis×ℤ))
   (e:(summon z w::l).Pairwise (Ocean α)):
   stuntPrice α (.summon z w::l)=response α l w z:=by
 let d:=maidS w; let u:=maidU w


 funext x
 have g:= α.gears.worn
 have q : acts (α.gb.villa α.bre d u x) (Δ x)=reply α w x:=
    α.gb.vaulted P.par.U (Rₙ) α.bre g.1 g.2.1 d u (maidJ w) x
 let h:=takes α x (.summon z w)
 have t: Commute h.primed (stunt α l x):=by
   apply abridge
   rintro _ b
   obtain ⟨m,t,rfl⟩:=List.mem_map.mp b
   apply (Footlight.shift _ _ ?_).2
   have a(X:Letter P):(takes α x X).plot=anchorage α X:=by cases X <;> rfl
   unfold h
   rw [Space,a,a]
   exact (List.pairwise_cons.mp e).1 m t
 have q': acts h.primed (Δ x)= ((z:ℂ) * (⊙w)) • reply α w x:=by
   change acts ((z:ℂ) • ((⊙w) • α.gb.villa α.bre d u x)) (Δ x)=_
   rw [smul_smul,act_smul,q]
 rw [response]
 change beamZ N (acts (h.primed * stunt α l x) (Δ x))=_
 rw [t.eq,act_mul,q']
 unfold beamZ
 rw [map_smul,inner_smul_right]

#print axioms assault

include β
/-- Compares sharp, denZ response, bare.
  Reorder primed occupants to give one Y the first reply. -/
lemma sailor (l r:List (Letter P))(z:ℝ)(w:List (Axis×ℤ))
    (g:(.summon z w ::r).Pairwise (Ocean α))
    (h:l.Pairwise (Ocean α))
    (p:l.Perm (.summon z w::r))(q:Ferry Y s iₙ kₙ):
   Integrable (response α r w z) 𝒢 ∧
      (∫x,response α r w z x ∂𝒢)/χ=rawE P s (ν n) (guest β s l (some n))∧
   bare_equate P (ν n)
      (finTor P s (ν n) q (guest β s l (some n)))
      ((∫x,response α r w z x ∂𝒢)/χ):=by
   obtain ⟨x,y,t⟩:=shoal β α l q h
   have H:stuntPrice α l=response α r w z:=by
     rw [←assault α r z w g];funext u;unfold stuntPrice;rw [casement α l _ h p]
   rw [←H]
   have p:(∫ x, stuntPrice α l x ∂𝒢)/χ=rawE P s (ν n) (guest β s l (some n)):= t
   rw [p]
   exact ⟨x,rfl,bare_equates P s (ν n) q _⟩

omit α 


def oceanReg (s:ℕ)(l:List (Letter P))(n:ℕ): ℂ:=
 if t:Sailing P a c μ d ν s n then oceanPrice t l else 0

/-- Unconditional mean sharp link. Arbitrary array sizes in `shoal` and
    `sailor` need not have such limits. -/
lemma dip (L:∀ᶠ n:ℕ in atTop, Sailing P a c μ d ν s n)
    (l:List (Letter P))
    (g:∀ᶠ n in atTop, ∀ t:Sailing P a c μ d ν s n,l.Pairwise (Ocean t)):
   Tendsto (oceanReg (a:=a) (c:=c) (μ:=μ) (d:=d) (ν:=ν) s l) atTop (𝓝 (P.E s (cost s F l none))):=by
    apply (ships β s l).congr'
    filter_upwards [L,g,β.grew.tendsto_atTop.eventually (atHeight P s)] with n t r q
    symm
    rw [oceanReg,dif_pos t]
    exact (shoal β t l q (r t)).2.2

#print axioms dip

