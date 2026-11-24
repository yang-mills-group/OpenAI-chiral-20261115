import Anomaly.Hop.Stamp
/-! Palette forms and reshape. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew
variable {n N B:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots Py Oise Swell Sault Pastry Rue
local notation "Tc"=> mid N B
local notation "Hp"=> hill I
variable (σ:I→ Site (mid N B))(F:Key I→RegBudget (mid N B))(E:Key I→ForceBudget (mid N B))(M:I→I→ℂ)
local notation "T★"=> Cube.node ∘ σ
local notation "Λ"=> toV_C (Cube.node ∘ σ) M
local notation "FΨ"=>clearRoot σ F
local notation "VΨ"=>bustle (Cube.node ∘σ) E
local notation "QΦ"=> FΨ ∘ Λ
local notation "Qμ"=> VΨ ∘ Λ
local notation "H♦"=>Scree.Hub Tc
variable (l:List I)(u:ψS (Cube.node∘σ) l)
private lemma Ψv (z:Key I)(i:H♦)(v:Pane Tc): FΨ z i v =∑ k∈trueSet (T★), pine k z • (νΦX F k i v):=by
 rw [sumOpen]; unfold clearRoot awake core_C rim_C; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply]; congr 1; refine sum_congr rfl fun t _=>?_ ; rw [show pine {t} z=z t from Finset.prod_singleton ..,show νΦX F {t} i v=νTip F t i v from cue_1 _ _]
include u
lemma stampE (i:H♦)(v:Pane Tc): Law_C (T★) M l (fun z=> FΨ z i v) (fun z=>(QΦ) z i v):=by
 unfold Function.comp -- careful occurs in T★. avoid via explicit change
 simp_rw [Ψv σ F]; exact RoofUp _ _ u (trueSet (T★)) _
lemma stampF (i:Force (mid N B))(v:Orbit Tc): Law_C (T★) M l (fun z=> VΨ z i v) (fun z=> (Qμ) z i v):=by
 change Law_C _ _ _ (fun z:Key I=> VΨ z i v) (fun z:Key I=> VΨ (Λ z) i v); unfold bustle; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact RoofUp _ _ u _ _
omit u
lemma tipE_c (i:I): νTip QΦ i= markerCore (T★) M (νTip FΨ) i:=by
 funext x y; unfold markerCore; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact (stampE σ F M [i] (by simp [ψS]) x y).2.2 [i] (List.Sublist.refl _)
lemma tipF_c (i:I): emberTip Qμ i= markerCore (T★) M (emberTip VΨ) i:=by
 funext x y; unfold markerCore; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact (stampF σ E M [i] (by simp [ψS]) x y).2.2 [i] (List.Sublist.refl _)
lemma shape_up (z:Key I): (QΦ) z= (∑ i,z i • (νTip QΦ i)) + rim_C (T★) F (Λ z):=by
 simp_rw [tipE_c σ F M]; have hx:νTip FΨ=νTip F:= funext fun i=> value_E ..; rw [hx,marker_tax]; rfl
lemma shape_po (z:Key I): (Qμ) z= (∑ i,z i • emberTip Qμ i) + ∑ i∈ manySet (T★), pine i (Λ z) • νΦK E i:=by
 simp_rw [tipF_c σ E M]; change VΨ _= _; rw [marker_tax]; unfold bustle; rw [sumOpen]; apply congrArg (· + (∑ i∈manySet (T★),pine i (Λ z) • νΦK E i)); refine sum_congr rfl fun j _=>?_; rw [show pine {j} _= _ from (show pine {j} (Λ z)=Λ z j from Finset.prod_singleton ..)]; exact congrArg (fun k:ForceBudget (mid N B)=>Λ z j • k) ((value_F (T★) E j).symm)
variable (p:Notice σ (clearRoot σ F) (bustle (Cube.node∘σ) E))
include p
set_option pp.unicode.fun true in
lemma moved_notices : Notice σ QΦ Qμ:=by
 have hz:= movesΖ (T★) M
 have he {S:Type} (D:Finset (Seat Tc))(F:Key I→ S)(t:Quiet (T★) D F): Quiet (T★) D (F ∘ Λ) :=by -- Universe Stuck. remove f
    intro i j u; exact t _ _ (fun k w=> sum_congr rfl fun x a=>congrArg (M k x * ·) (u x ((mem_filter.mp a).2 ▸ w)))
 have ht: Differentiable ℂ Λ:= differentiable_pi.mpr fun i=> diff_cost σ M i
 refine ⟨⟨by change FΨ (Λ 0)=_; rw [hz,p.roll.1], ?_⟩,(fun i=> he _ _ (p.col i)),(fun i j=> (p.varE i j).comp ht),(fun i=> he _ _ (p.joinF i)),(fun i j=> (p.varF i j).comp ht),?_⟩ -- use explicit he no f
 · change VΨ _=_; rw [hz,p.roll.2]
 intro i z
 let Z:= update (0:Key I) i z
 let t:=Λ Z
 have he{U:Finset I}(u:U∈ manySet (T★)): pine U t=0:= pine_c (T★) M _ (mem_filter.mp u).2.1 (mem_filter.mp u).2.2 _ z
 have hF {D:Type}[AddCommMonoid D][Module ℂ D](f:I→D): ∑ i:I, Z i • f i=z • f i:=by rw [Finset.sum_eq_single i]; rw [show Z i=z from update_self ..]; intro j _ v; rw [show Z j=0 from update_of_ne v ..,zero_smul]; simp
 refine ⟨?_,?_⟩; · rw [shape_up,hF]; unfold rim_C; rw [sum_eq_zero (fun i v=>by rw [he v,zero_smul]),add_zero]
 rw [shape_po,hF,sum_eq_zero (fun i v=>by rw [he v,zero_smul]),add_zero]
omit p
end YM.CF.Vow.TreasuryFog
