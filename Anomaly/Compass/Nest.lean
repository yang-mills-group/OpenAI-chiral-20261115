import Anomaly.Basis.Spirit
import Anomaly.Apert.Sync
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Swell
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry Vow
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Paige Salt Phase Acorn Nacre Dial Urn Laic Skye Scree Stax Sour Sault Rill Ione Py QuadClock Turning Levier
variable {B C L:Side}{Z M:SOp C}{o:Seat C}{a b c d v s t r₀ r₁ r₂ r₃:ℝ}{n l q j:ℕ}{p:RG.BudgetPoint}
variable {h:Odd L.val}{H:Paige.Pricing j L h (Vault.Thread j)}{e:ℝ}(P:Grasp H B e)
open Vow.TreasuryFog Ione.Clock
local notation "N"=> mid C B
variable (R:GramM (mid C B))(K:Scree.Loom (mid C B))
variable {k m:ℝ} {V:phy (mid C B)} (u:Roof (mid C B) k e q K) (z:P.roundZ≤ (mid C B).val)
open Leaf
lemma rankG {X:FC (Dwell C)}(s:Sweep C)(v:rank2 X): rank2 (sauce s.charge (detX s.s) (γS s) X):=by
 intro A B J; let V:=suit_Y s; let Y:= Urn.lotY s.charge (detX s.s) (γS s)
 have he(x: Cipher C): V (suit_Y s⁻¹ x)=x:=by unfold V; rw [moon_Y,inv_mul_cancel,toon_Q] -- order
 let P:=fun i:Dough (Dwell C)=> suit_Y s⁻¹ (show Cipher C from i)
 have hp(i:Dough (Dwell C)): i.val= Y (P i).val:= congrArg Subtype.val (he i).symm
 change bump (bump (bump (Y X) _) _) _=0; rw [hp A,hp B,hp J]; convert congrArg Y (v (P A) (P B) (P J)) using 1 <;> simp [bump]
open scoped Mew
variable {J : Bag (mid C B)}
lemma Motion_link (pK:Vessel P R K J V): nestLink P R K J V:=by intro x t h g; have hp:=pK.science x t h g; rw [giveB,Finset.sum_apply] at hp; exact hp
variable (p':Pearl P)(vP:Vault.Stamped j L h H)(vt:1≤j)(A:R.J.P.toll r₀ r₁ r₂ r₃)(F:Reef.Cry R.J.P)
lemma giveB_turn (Q:Bag C)(s:Sweep C)(x:Orbit C): giveB (cartTurn s Q) (yellA s x)= Urn.lotY s.charge (detX s.s) (γS s) (giveB Q x):=by
 unfold giveB; simp only [Finset.sum_apply,map_sum]; symm; refine Finset.sum_equiv (moldA s) (by simp) ?_; intro i _; exact (runs s Q x i).symm
include p' vP vt A F u z
lemma shipTurn (s:Sweep N)(g:passingR (mid C B) s R.F R.F)(w:R.slip=0)
    (pK:Vessel P R K J V) : Vessel P R K (cartTurn s J) (cartPrice s V) := by
 let t:= link_framed P R K u z p' vP vt A F s g w (Motion_link _ _ _ pK)
 refine ⟨fun X v=>?_,fun x i p e=>?_⟩
 · obtain ⟨x,rfl⟩:= yspec s X; rw [giveB_turn J s x]
   have hh:Injective (priorP x.2):=by have he:=pinject s⁻¹ (yellA s x) v; rw [Clock.y_rev] at he; exact he
   exact rankG s (pK.rank x hh)
 rw [show giveB (cartTurn s J) x= _ from Finset.sum_apply ..]; exact t x i p e
end YM.CF.Swell
