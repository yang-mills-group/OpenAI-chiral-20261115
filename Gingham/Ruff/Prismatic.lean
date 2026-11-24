import Gingham.Ruff.Bauble
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}

variable {I:Type*}[Fintype I][LinearOrder I]
namespace Bright
variable {z q ρ :ℝ}{A B:FC I}

lemma raise (h:Bright ρ A q)(p:q≤z) : Bright ρ A z:= fun G a b=>(h G a b).trans p

/-- Allow even negative 'charges' in API: prove nonnegative from same Shaft in question. -/
lemma attach (h:Bright ρ A q)(p:Bright ρ B z): Bright ρ (A*B) (q*z):=by
 intro G a b
 rw [Shaft.glow_mult]
 exact (norm_mul_le _ _).trans (mul_le_mul (h G a b) (p G a b) (norm_nonneg _)
    ((norm_nonneg _).trans (h G a b)))

lemma either (h:Bright ρ A q)(p:Bright ρ B z): Bright ρ (A+B) (q+z):=by
 intro G a b
 rw [Shaft.glow_sum]
 exact (norm_add_le _ _).trans (add_le_add (h G a b) (p G a b))

lemma space : Bright ρ (0:FC I) 0:=by intro G a b; rw [Shaft.glow_zero,norm_zero]
lemma mint : Bright ρ (1:FC I) 1:= by intro G a b; rw [Shaft.glow_nil,norm_one]
lemma scale (h:Bright ρ A q) (r:ℂ): Bright ρ (r • A) (‖r‖*q):= by
 intro G a b; rw [Shaft.glow_free,norm_smul]; exact mul_le_mul_of_nonneg_left (h G a b) (norm_nonneg _)



lemma sum {X:Type*}{T:X→FC I} {U:X→ℝ}{s:Finset X}
   (e:∀x∈s,Bright ρ (T x) (U x)):
   Bright ρ (∑ x∈s,T x) (∑ x∈s,U x):=by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact space
 | insert i s v ih=>
   rw [Finset.sum_insert v,Finset.sum_insert v]
   exact either (e i (by simp)) (ih (fun x h => e _ (Finset.mem_insert_of_mem h)))

lemma fraction (h:Bright ρ A q)(p:Bright ρ B z): Bright ρ (A-B) (q+z):=by
 rw [sub_eq_add_neg]
 apply either h
 simpa only [norm_neg, norm_one, neg_one_smul,one_mul] using p.scale (-1)

#check dg
lemma triumph (M:Op I)(v:0 ≤ ρ) : Bright ρ (dg M) (ρ^2*revE M):=
   fun _ a b=> Shaft.dg_glow _ ρ a b _ v
end Bright

namespace Shines
variable {ρ z q:ℝ} {U V:Mark n}
lemma raise (h:Shines ρ U q)(p:q≤z) : Shines ρ U z:=fun x=>(h x).raise p
lemma attach (h:Shines ρ U q)(p:Shines ρ V z) : Shines ρ (U*V) (q*z):=fun x=>(h x).attach (p x)
lemma mint : Shines ρ (1:Mark n) 1:=fun _=>Bright.mint

