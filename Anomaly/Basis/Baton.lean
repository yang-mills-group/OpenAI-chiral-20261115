import Anomaly.Basis.Cove
import Anomaly.Apert.Spindle
import YM.CF.Brood.Tips
/-! tape of the Seeder. Entitlements must be on singleReceipt of that pointer.
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Porticus Tye Bake Neon
variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
-- proof independent.
local notation "uζ"=>Fin 1
def singlePole {a b: Aura n→ℝ} (τ:Ids n)(A:Bag n)(p:∀ X,Flight P q X h (A X) (a X) (b X))(v:Seat n): RegBudget n:= singleReceipt (fun _:Fin 1=>A) _ _ (fun _ X=>p X) τ (0:uζ) v
variable (J:Scree.Hub n) {F G:Bag n}
    {a b c d k u:Aura n→ℝ}(HA:∀ X, Flight P q X h (F X) (a X) (b X))
variable (t:Ids n)(x:Seat n)
local notation "T_"=> singlePole t F HA x
include HA
-- scratch wrapper avoid charge/proof dependence
lemma pole_value (e:J.val.1=x)(V:Pane n): (T_ J V).val= Sault.rind (coll_T P (lagE J) ∅ (F (lagE J)) (V,t)):=by
 unfold singlePole singleReceipt; rw [if_pos e]; unfold jetSlice Bias.payX; rw [dif_pos (show Bias.αt (lagE J) _ ∅ (cipherK q) from ⟨Subset.refl _,empty_subset _,by simp [Lattice.halo]⟩)]; change Sault.rind (_*(1:FC (Dwell n)))= _; rw [mul_one] -- tune
lemma recollected (K: I→ Bag n)(L M: I→ Aura n→ℝ)(H:∀ (i:I)(X:Aura n),Flight P q X h (K i X) (L i X) (M i X))(i:I)(T:K i=F): singleReceipt K L M H t i x= T_ :=by
 funext X V; by_cases v:X.val.1=x; swap; · unfold singleReceipt singlePole; unfold singleReceipt; rw [if_neg v,if_neg v]
 apply Subtype.ext; rw [pole_value X HA t x v]; unfold singleReceipt jetSlice Bias.payX; rw [if_pos v]; rw [dif_pos (show Bias.αt (lagE X) _ ∅ (cipherK q) from ⟨Subset.refl _,empty_subset _,by simp [Lattice.halo]⟩)]; change Sault.rind (_*1)= _; rw [mul_one]; exact congrArg (fun A:Bag n=> Sault.rind (coll_T P (lagE X) ∅ (A (lagE X)) (V,t))) T
lemma booth_one (H:∀ X,Flight P q X h (F X) (c X) (d X))(t':Ids n): singlePole t' F H x=T_:=by
 rw [←recollected HA t x (fun _:uζ=> F) _ _ (fun _ i=> H i) (0:uζ) rfl]
 funext i V; unfold singlePole singleReceipt; split
 · exact dedicate_fixed _ _ _ (fun (_:Fin 1)i=>H i) (0:uζ) _ _ _ _
 rfl
lemma poles_up (s:∀ X,Flight P q X h (G X) (c X) (d X))(r:∀ X,Flight P q X h ((F+G) X) (k X) (u X)): singlePole t (F+G) r x= T_ + singlePole t G s x :=by
 funext X V; apply Subtype.ext; by_cases z:X.val.1=x
 · change _=(T_ X V).val+(singlePole t G s x X V).val; rw [pole_value X HA t x z,pole_value X s t x z,pole_value X r t x z]; unfold coll_T; split; swap; · simp [Sault.rind]
   exact map_add ..
 simp only [singlePole,singleReceipt,if_neg z,Pi.add_apply, Pi.zero_apply,add_zero]
lemma pole_scale (w:ℂ)(r:∀ X,Flight P q X h ((w • F) X) (c X) (d X)) : singlePole t (w • F) r x=w • T_:=by
 funext X V; apply Subtype.ext; by_cases z:X.val.1=x
 · change _=w • (T_ X V).val; rw [pole_value X HA t x z,pole_value X r t x z]; unfold coll_T; split; swap; · simp [Sault.rind]
   simp only [Pi.smul_apply,Sault.rind,map_smul]
 simp only [singlePole,singleReceipt,if_neg z,Pi.smul_apply, Pi.zero_apply,smul_zero]
lemma rootVisible (e:J.val.1=x)(V: Orbit n)(q':pingS P.threshold J.val.2 V.1): (T_ J V.1).val=Sault.rind (F (lagE J) V):=by
 let K:= lagE J; have hv: (V.1,t) = (V.1,t):= rfl
 rw [pole_value J HA t x e]; have hl: V.1∈ σX P K ∅:=⟨by rw [sdiff_empty]; exact q',empty_subset _⟩
 let Q:= (HA K).tube; rw [(Q.offer _ (Subset.refl _) ∅ (empty_subset _) (by simp [Lattice.halo])).toCrate.pointV (V.1,t) hl,Q.clean _ (Subset.refl _) V hl t]
lemma fringe_pole (e:J.val.1=x)(v:ℝ)(p:Fringe P h (F (lagE J)) (lagE J) v)(b:0≤ h) : PressB P J (T_ J) h (fareX P.B P J.val.2 * v):=by
 let Jv:=lagE J; let Z:=fun (_:uζ) i=>HA i; apply Medal.preservesE t _ b
 rw [show oV (T_ J) =jetSlice (fun _:uζ=>F) _ _ Z (0:uζ) Jv ∅ Jv 1 from ?_]
 · unfold jetSlice Bias.payX; rw [dif_pos (show Bias.αt Jv _ ∅ (cipherK q) from ⟨Subset.refl _,empty_subset _,by simp [Lattice.halo]⟩)]; -- explicit δ
   exact (Fringe.burn (δ:=0) _ p).merit
 funext V; unfold oV singlePole singleReceipt; rw [if_pos e]; exact dedicate_fixed _ _ _ Z (0:uζ) _ _ _ _
omit HA
end YM.CF.Vow.TreasuryFog
