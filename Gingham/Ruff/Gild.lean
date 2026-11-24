import Gingham.Ruff.Sunbird
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



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false

/-- charge even for every pose on this regulator. -/
def Shining (P:Spine)(ρ:ℝ)(s i:ℕ)(f:Family P.calibration)(q:ℝ):=
  ∀r:List (Axis×ℤ),Shines ρ ((exhibit P.run P.large s i) (Ballet r f)) q

variable {f:Family P.calibration}{o:Cell}{w:ℕ}
namespace Shining
lemma turned{g:Tile K}(h:Shining P ρ s i f q)
       (p:VelourBoard.Transit w o f g):
    Shines ρ ((𝒳 s i) g.leaf) q:=by
 have a:∃r,Ballet r f=g.leaf:= by
   induction p with
   | here=>exact ⟨[],rfl⟩
   | turn x y z ih=>
       obtain ⟨r,u⟩:= ih
       exact ⟨(y,PaneCut K w o y z)::r,congrArg (Tower.mirror K y (PaneCut K w o y z)) u⟩
 obtain ⟨u,t⟩:=a; rw [←t]; exact h u



lemma tipped (l:List (Tile K)) (h:Shining P ρ s i f q)
        (g:∀d∈l,VelourBoard.Transit w o f d):
    Shines ρ ((𝒳 s i) (Representation l)) (q^l.length):=by
 induction l with
 | nil=> change Shines _ (exhibit _ _ _ _ 1) (_^0); rw [Tapestry.actual_one,pow_zero]; exact Shines.mint
 | cons d l ih=>
      change Shines _ (exhibit _ _ _ _ (d.leaf*Representation l)) (_^(l.length+1))
      rw [actual_product,pow_succ']
      exact (h.turned (g _ List.mem_cons_self)).attach
         (ih (fun x u=>g _ (List.mem_cons_of_mem _ u)))
end Shining
abbrev RegisterPrice (P:Spine)(s w:ℕ)(q:ℝ):=
    Real.exp (Fee P s w)*q
lemma beaming
    (p:Patina P ρ s i k)
    {S:Finset Cover}(t:InTest K true S false f)(x:Parcel K w o 0 S)
    (g:Shining P ρ s i f q)
    (u:0<q)
    (l:List (Tile K))(L U:Cell)
    (d:VelourBoard.Deck (momentm P.run i s) w o f l L U):
    ‖Journey.sharp Y P.large s i k (Representation l)‖ ≤ RegisterPrice P s w q ^ l.length :=by
 obtain ⟨_,h,_⟩:=pavingReservation t x d.paved
 rw [RegisterPrice,mul_pow]
 apply p.earn _ _ h (Shining.tipped _ g (fun _ m=>d.paved.homes _ m)) (pow_pos u _)
 rw [←(show P.calibration.c (momentm P.run i s)= Journey.side P.run i s from terrain P.run P.large (P.run.ir i) s)]
 exact d.fill.1
#print axioms beaming


variable {ν:ℕ→ℕ}{Z:ℕ→Family P.calibration}
variable (g:Tendsto ν atTop atTop) (h:∀ᶠ e:ℕ in atTop, Patina P ρ s (irr P e) (uvv P e))
      (b:∀ᶠ n:ℕ in atTop, Shining P ρ s (irr P (ν n)) (Z n) q)(u:0<q)
variable {S:Finset Cover} (p:VelourBoard.Parcel P.calibration w o 0 S)
include u b g h p
lemma dazzling (x:∀n,InTest K true S false (Z n)):
    Settle Y P.large s P.projection w Z ν o (RegisterPrice P s w q):=by
 filter_upwards [g.eventually h,b] with n hp t d L U z
 exact beaming hp (x n) p t u d L U z

def inLeaf (p' : InTest K true S false f) : P.Test:= ⟨f,(marque K).mpr (aux_test p')⟩
#print inLeaf


variable (t:BQueue S Z f)(j:Axis)(vo:o j=0)(a:0<w)
abbrev CoinPrice (P:Spine)(s w:ℕ)(q:ℝ):=4*RegisterPrice P s w q
include vo
lemma gilding (ice:IcePath P.run (irr P) (uvv P))
   (c: (inLeaf t.landing)∈enclave P.calibration):
   ∃ L:P.InCase j s w (inLeaf t.landing),
    ‖P.Box j s w a L.card‖ ≤ CoinPrice P s w q ∧
    ∀x:P.Spectrum0 j, ‖L.charges x a‖ ≤ CoinPrice P s w q :=by
  have x:=p j
  unfold Wall at x
  simp only [Pi.zero_apply,vo,mul_zero,zero_add,mul_one] at x
  let L:=InCase.sized P j s w c t.landing x
  have d:L.card.val.val=f:=congrArg (fun t:P.Test=>t.val) L.entry
  have hp:=boardPrice P.run P.large P.law s P.projection j w Z S _
       g o ice p vo a (RegisterPrice P s w q)
       (mul_pos (Real.exp_pos _) u)
       (dazzling g h b u p t.whereTo)
       (P.room j) L.card (d.symm ▸ t)
  exact ⟨L,hp,fun x=>(L.cap x a).trans hp⟩
#print axioms gilding

