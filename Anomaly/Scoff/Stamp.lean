import Anomaly.Rack.Ink
import Anomaly.Scoff.Nook
import Anomaly.Basis.Helion
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill Buffered StressExchange Reed
open Vow.TreasuryFog Py Neon
variable {N B M L:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h x₀ y c s:ℝ}{k q j l:ℕ}
local notation "Tc"=> mid N B
variable {g:ℕ}{wL:Odd L.val}{H:Pricing g L wL (Thread g)} {U:Grasp H B d}{R:GramM (mid N B)}{T:Scree.Loom (mid N B)}
-- Use any finite collections.
-- for unit/absent cost at all births. Pair with Boost.S. No mask needed for unit.
variable {o:Site (mid N B)}
open Larch TreasuryFog Ione
lemma voidFlint {S:Support (More (mid N B))} (p:node o∈ S): Flint P 0 S 0 0 0 0 o l q h s 0 0 0 0 0:=by
 refine ⟨p,Barrage.zeroR,fun W X t B'=>?_⟩; let Q:=singlePole (P:=P) W 0 B' (node o); have he: Q=0:=by
    funext X V; apply Subtype.ext; by_cases p:X.val.1=node o; swap; · unfold Q; rw [show singlePole _ _ _ _ X=0 from station _ _ _ (fun (_:Fin 1) i=>B' i) _ _ (0:Fin 1) X p]; rfl
    unfold Q; rw [pole_value _ _ _ _ p]; simp [coll_T,Sault.rind]
 change Ice _ _ _ _ _ _ _ (marksCopy P Q) _ _ _ _; rw [he]; refine ⟨nothing_X ..,by simp,fun _ _=>rfl,⟨0,⟨le_refl _,fun i D t w=> Medal.zeroT⟩,fun i=> by simp [tallB],(fun _ p=>False.elim (p rfl))⟩,fun x _=>?_⟩
 rw [prizes0,zero_smul,zero_add,add_zero]
end YM.CF.Swell.Porticus
