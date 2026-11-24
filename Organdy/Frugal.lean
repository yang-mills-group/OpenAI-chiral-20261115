import Organdy.Rehearsal
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU Tulip Lat
open Roots
open Vale Buffered QuadClock Neon MeasureTheory
open Swell Hom

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine) (i k t:ℕ)
local notation "Λ"=>P.par
local notation "x'"=> Vale.hat (Λ).R.L (Λ).x t
local notation "N'"=> age P.run i t
local notation "KL"=> (P.run.voyage i).CapeT t
local notation "R✤"=>RootBook P.run i k t
local notation "p'" => (R✤).p
local notation "q'" => (Λ).J.n
local notation "h'" => (Λ).h

variable (s:Sweep (age P.run i t))

variable {S:I→Support (More (age P.run i t))}{D:I→Mark (age P.run i t)}
 {V:I→Bag (age P.run i t)}{U:I→phy (age P.run i t)}{C:I→ℝ}
 {o:I→Site (age P.run i t)}
variable {M:ℕ} {L:Side}{γ μ W:ℝ}

abbrev lip_R (p:BudgetPoint) (x:Seat n) (d:ℕ):=halo (d*p.B) {x}
abbrev gate_R (d:ℕ) :=((d+d+1)^4)^3

/-- (52) upgrade. Whole budget at most μ (hence so is outer by nonnegativity).
All entries on or inside core **itself** zero, hence can have zero cost at power three;
total price ≤ μ*(1+b)^100, the quench granted e.g. in next lemma.
Pick L width after d, no need d or L varying with b. -/
lemma frugal (z:Kyanite P i k t M L a b γ μ W)
   {d:ℕ}(l:gate_R d < L.val)
   {w:Rolls P i k t L o V}
   (v:Recital P i k t L M a b γ μ W o S D U V C w)(j:I):
   IncX Py.primeU (νTip w.Ev j) p' h' μ ∧
   ∀ x:Scree.Hub N',(x.val.1≠node (o j) ∨ x.val.2⊆ lip_R p' (node (o j)) d)→
      νTip w.Ev j x=0:=by

 refine ⟨(v.taught.helix j).vest,fun x h=>?_⟩
 rcases h with hx|hx
 · exact (v.taught.helix j).site x hx
 rw [(w.vanguard j).1]
 unfold pend; split; swap; exact rfl
 have g₁:=Corona.cover_mono hx (p').B
 have g₂: coverNumber (p').B (lip_R p' (node (o j)) d) ≤ (d+d+1)^4:=
    Corona.tile _ _ _ (p').B_pos

 have t:Pavilion L.val p' (incline (node ∘o) L.val p' V j):=
    backed z.launch.large _ _
 unfold flake; rw [vanity _ _
     (t (lagE x) ((Nat.pow_le_pow_left (g₁.trans g₂) 3).trans_lt l))]
 rfl

open Py.Rate.BScale
lemma frugality (R:Patch)(v:ℝ→ℝ)(p:Quench R v)(g:ℕ):
   Quench R (fun y=>(1+ (Pressure.radiusB y:ℝ))^g*v y) :=
 p.bondF (beryl g)
end YM.CF.Organdy
