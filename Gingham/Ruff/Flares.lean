import Gingham.Ruff.Chatelaine
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical


def hoop(y:Site N)(b:ℕ): Support (More N):=Lattice.halo b {bouton y}
/-- The lit ledger per root anchor. price of orientation core possible at any
 fixed multiplier, interest q rate on #S. -/
structure Flares (y:Site N)(u:Side)(l r:ℕ)(E q:ℝ)(p:BudgetPoint)
    (k:ℝ)(A:Orbit N→OP N) where
  wick : Support (More N)→Orbit N→OP N
  cost : Support (More N)→Toll (Single N)
  fee(S): WearL p r (footprint (bouton y) S l r p.B) (wick S) (cost S)
  terrain(S i j): cost S i j ≠ 0 →
     node i.1.1 ∈ S ∧ node j.1.1 ∈ S ∧ Grove (terr _) S ∧ Girder y u S
  assemble(x): A x= ∑ S, wick S x
  paid : watt y E l r p.B q cost ≤ k

namespace Flares

variable {M:Support (More N)} {y:Site N}{u:Side}{l r:ℕ}{E q:ℝ}{p:BudgetPoint}{k:ℝ}
    {A:Orbit N→OP N}(F:Flares y u l r E q p k A)
-- M any: inside root hoop(l*b)
def dark (β:Bool)(b:M⊆hoop y (l*p.B)): Flares y u l r E q p k (silkcut p M β A):=by
  refine ⟨fun S=>silkcut p M β (F.wick S),F.cost,
      fun S=>veil (F.fee S) β le_rfl (b.trans subset_union_left), F.terrain,?_, F.paid⟩
  intro x
  unfold silkcut; split
  · exact F.assemble x
  simp

lemma simplecost {Y Z:Type*}[Fintype Y][Fintype Z][DecidableEq Z] {cost:Seal Z→Toll Y}(g:∀ S i j,0 ≤ cost S i j):
  0≤∑ i:Y,∑ j:Y,∑S,cost S i j:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=> g ..

include F
lemma inall(e:0≤E)(a:0≤q): ∑ i:Single N,∑ j:Single N,∑ S,F.cost S i j ≤k:=by
  apply le_trans _ F.paid
  refine sum_le_sum fun i _=>sum_le_sum fun j _=>sum_le_sum fun S _=>?_
  have h:1 ≤ pique p.B E (footprint (bouton y) S l r p.B):=
    Real.one_le_exp (mul_nonneg e (Nat.cast_nonneg _))
  exact le_mul_of_one_le_left ((F.fee S).floor i j) (one_le_mul_of_one_le_of_one_le h (rent_one a _))



lemma priceall(x:Orbit N): ∑ i,∑ j,‖A x i j‖ ≤ ∑ i:Single N,∑ j:Single N,∑ S,F.cost S i j:=by
  apply sum_le_sum;intro i _
  apply sum_le_sum;intro j _
  rw [F.assemble,Matrix.sum_apply]
  exact (norm_sum_le _ _).trans (sum_le_sum fun S _=> (F.fee S).value x i j)
end Flares

variable {y:Site N}{u:Side}{l r:ℕ}{E q e a c:ℝ}{p:BudgetPoint}{U:Scree.Loom N}
variable {R: Seal (Seat N)→Prop}{B:Fob N e}
variable (g:Briefly p r e U)
def flaring (H:Buttons N e R a c B)(f:∀S,R S →Girder y u S)
  {k:ℝ}(s:watt y E l r p.B q H.cost ≤ k):
  Flares y u l r E q p k (B∘g.roll) where
  wick S := H.mark S∘g.roll
  cost:= H.cost
  fee S := (g.clears (H.pass S)).mono subset_union_right
  terrain S i j t := by
    obtain ⟨v,b,c⟩:= ((H.pass S).expo i j).triggered t
    exact ⟨b,c,v,f S (H.good S i j t)⟩
  assemble x:= H.sum (g.roll x)
  paid:= s

variable {A:Fob N e}
variable (G: Tagbill a E u l r p.B) (H:Plastron y u e (a/4) c A)


def shoot := flaring g (tagLite H) (fun _ h=>h.1) (fanfareLite H G)
def plumeTail := flaring g (tagFar H G) (fun _ h=>h.1) (fanfareFar H G) -- plume collision

abbrev peakL: Support (More N):= hoop y p.B
abbrev liteF : Orbit N→OP N:= H.light (tenderb p.B) ∘ g.roll
abbrev farF : Orbit N→ OP N:= H.flight (tenderb p.B) ∘ g.roll
abbrev coinF(β:Bool) : Orbit N→OP N:= silkcut p (hoop y p.B) β (liteF g H)
-- fee even for whole hoop
def latticeFieldEstimates (β:Bool): Flares y u l r E (a/16) p (fanbill a E c u l)
  (coinF g H β):=
  (shoot g G H).dark β (Corona.halo_mono (by
    have z:=G.largeL
    exact Nat.le_mul_of_pos_left _ (by omega)
  ) le_rfl)

lemma splitF(x:Orbit N):
  A (g.roll x)= coinF g H true x + coinF g H false x + farF g H x :=by
  have p1 : coinF g H true x + coinF g H false x= liteF g H x:= by
    unfold coinF silkcut; cases retina p (hoop y p.B) x <;> simp
  rw [p1]; exact H.split_m _ _

#print axioms latticeFieldEstimates

