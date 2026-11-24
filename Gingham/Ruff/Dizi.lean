import Gingham.Ruff.Astoria
import Gingham.Ruff.Subito
import Gingham.Ruff.Parasols
import Gingham.Ruff.Starch
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Drapes Fock Peaks Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

abbrev Tune (N:Side)(e:ℝ) := ↥(Openc (More N) e)
variable {n:ℕ}{e ρ b:ℝ} (H:Rialto n e ρ b)
    {S: Support (More N)}{w: Toll (Single N)}
    {F:Raw (Tune N e) (Single N)}
    (A:Suite (badge _) (bail N e) (bail N e) S w F)
variable {q:ℕ}{p:BudgetPoint}{x:Seat N}{U:Pane N}
    (P: Parasols p ρ q)(g:Pinwax p x q U)
def lengthM (x:Seat N)(S: Support (More N))(m:ℕ) : Prop:=
  ∀ a∈S,separation x a ≤ m

include H A
lemma ride (v: Doub N)(Z:Tune N e)(G:Seat N→SU.E)
   (j: ‖v‖<1)(V:Pane N)(r:Z.val=Tulip.profile V)
   (l: Agrees S (pencil ρ v) (Lattice.gauge G V)):
   (F Z).trace=hum H F v:=by
  let M:=(forum N e).drive G Z
  rw [←kelp H A G Z M rfl]
  suffices t:F (pate H v)=F M from congrArg _ t.symm


  have hv:M.val=Tulip.profile (Lattice.gauge G V):=by
    dsimp only [M,forum,affair]
    rw [r,profile_g]
  have hu:(pate H v (N:=N)).val= Tulip.profile (pencil ρ v):=by
    simp [pate,dabble,j]
  ext i k
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  refine ((A.expo i k).variation _ _).trans ?_
  change _ * (fare S (pate H v).val M.val/ |e|) ≤ _
  rw [hv,hu,fare_cyl l,zero_div,mul_zero]


variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]

/- Use arbitrary chart with templates locally as in the lit consultation.
  Agreement as gauge Links; no mask necessary. -/
include g P
lemma lead {m:ℕ}
   (T:Y→L[ℝ]tangD N) (Z:Y→ Tune N e)
   (V:Y→Pane N)
   (r:∀ᶠ i in 𝓝 0, (Z i).val=Tulip.profile (V i))
   (l:∀ᶠ i in 𝓝 0, Agrees S (increment U (p.threshold • T i)) (V i))
   (s:lengthM x S m) (k:m≤q):
 (fun i=>(F (Z i)).trace) =ᶠ[𝓝 0] (fun i=>hum H F (baseL ρ m g+zydeco ρ g T i)):=by
  have c:∀ᶠ i in 𝓝 0,‖baseL ρ m g+zydeco ρ g T i‖<1:=
    ((continuous_const.add (zydeco ρ g T).continuous).norm.tendsto 0).eventually (gt_mem_nhds (by
       simpa using (base_length P m g k).trans_lt (small_lilt P m k)))


  filter_upwards [c,l,r] with i h t z
  refine ride H A _ _ g.color h _ z ?_
  intro j a b
  rw [tune_up P g T _ k _ j (s _ a)]
  unfold Lattice.gauge;rw [t j a b]

omit g
lemma tty {m:ℕ}(k₀:2≤n)
    (k:m≤q) (s:lengthM x S m)(Z:Y→ Tune N e)
    (l: ∃ (_g:Pinwax p x q U)(T:Y→L[ℝ]tangD N)(V:Y→Pane N),
        ‖T‖≤1 ∧ (∀ᶠ i in 𝓝 0,(Z i).val=Tulip.profile (V i)) ∧
          (∀ᶠ i in 𝓝 0, Agrees S (increment U (p.threshold • T i)) (V i))) :
  Allows n (fun i => (F (Z i)).trace-hum H F 0) 0 (blush w*liltCost p ρ m ^2):=by
  obtain ⟨g,T,V,y,r,h⟩:=l
  have v:=Gallery.quadratic k₀ (show Gallery n (hum H F) (blush w) from aria H A)
    (flat_aria H A (by omega)) (small_lilt P m k) (base_length P m g k)
    (zydeco ρ g T) ((zydeco_bill P g T y).trans (rich_lilt P m).2)
  exact v.germ ((lead H A P g T Z V r h s k).mono fun i t=>congrArg (·-hum H F 0) t.symm)

#print axioms tty

