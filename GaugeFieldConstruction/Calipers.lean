import GaugeFieldConstruction.Marrow
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open SelectionAnalysis
namespace Porch
variable {P:Spine}{F G:P.Test}{j:Axis}{cost:ℕ→P.Test→ℂ}(R:Porch P cost j)
local notation "rX"=> R.ρ
local notation "π"=> P.stampPin
local notation "M"=> timeMesh P.par
local notation "η"=> P.HabBox j
local notation "χ"=> P.shifts j
lemma meshM_turn {a:ℤ}{w:ℕ}{s:ℕ}(p:P.BEntry j w (χ (-a) F))(v:Cover):
 P.BEntry j w (χ (-(a+v j)) (P.chartAll v F)) ∧
 rX (η s w (χ (-(a+v j)) (P.chartAll v F))) = R.porchMove (P.vtile s v)*rX (η s w (χ (-a) F))*R.porchMove (-(P.vtile s v)):=by
 have he:P.cruise (spare j (look j)) v (χ (-a) F)=χ (-(a+v j)) (P.chartAll v F):=by
   rw [P.cruise_mesh,P.chart_transverse j v F,P.shifts_sum]; congr 2; ring
 obtain ⟨h,v'⟩:=R.porch_box s v p
 rw [he] at h v'; exact ⟨h,v'.symm⟩
end Porch
variable {P:Spine}{j:Axis}{cost:ℕ→P.Test→ℂ}(R:Porch P cost j)
local notation "Σ"=> P.movesOf j
local notation "ζ"=> R.ρ
noncomputable def transitTile (P:Spine)(j:Axis)(d:P.VMark) : P.Slabs j:=
 let v:ℕ:= (mint_voxel d).exists.choose
 let p:Cover:= (mint_voxel d).exists.choose_spec.choose
 ((look j).map (fun k=> P.movesOf j (v, p k.val, k))).prod

lemma Porch.transitReceipt (a:P.VMark): R.ρ (P.transitTile j a)=R.porchMove a:=by
 let v:= (mint_voxel a).exists.choose
 let r:Cover:= (mint_voxel a).exists.choose_spec.choose
 have hp : P.vtile v r=a:=(mint_voxel a).exists.choose_spec.choose_spec
 change ζ ((look j).map (fun k=>P.movesOf j (v,r k.val,k))).prod=_
 conv_rhs=> rw [←hp]; unfold Porch.porchMove
 generalize look j=i
 induction i with
 | nil=> exact map_one ζ
 | cons d i h=> rw [List.map_cons,List.prod_cons,map_mul,h,Alliance.raw_step]; exact congrArg (fun y:R.H.Op=>y.comp _) (R.canopy_plays d v (r d.val)).symm
local notation "Λ"=>P.transitTile j
lemma transit_plus(a b:P.VMark):Λ (a+b)= Λ a * Λ b:= by
 let Z:=P.publicH j
 apply Subtype.ext
 change Z.ρ (Λ (a+b))=Z.ρ (Λ a * Λ b)
 rw [map_mul,Z.transitReceipt,Z.transitReceipt,Z.transitReceipt,Z.porch_plus]
lemma transit_zero : Λ 0=1:=by
 let Z:=P.publicH j; apply Subtype.ext; change Z.ρ (Λ _)=Z.ρ 1; rw [map_one,Z.transitReceipt,Z.porch_zero]
lemma transit_share(a:P.VMark)(t:ℝ≥0): Λ a * P.Eucl j t=P.Eucl j t * Λ a:=by
 let Z:=P.publicH j; apply Subtype.ext; change Z.ρ (Λ _ * _)=Z.ρ (_ * Λ _); rw [map_mul,map_mul,Z.transitReceipt, ← Z.heat,Z.porch_share]
lemma transit_affordable (a:P.VMark): ‖Λ a‖≤1:=by
 let Z:=P.publicH j
 change ‖Z.ρ (Λ a)‖≤1
 rw [Z.transitReceipt]; refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
 intro x; rw[one_mul]; exact Z.canopy.raw_price _ _ _
lemma transit_Ω (a:P.VMark): R.porchMove a R.Ω=R.Ω:=by
 unfold Porch.porchMove; generalize look j=L; induction L with
 | nil=> rfl
 | cons c l ih=>rw [Alliance.raw_step,ContinuousLinearMap.comp_apply,ih]; exact R.Ω_ready _ _
/-- Move on Slabs (also uncompressed). -/
def ambientTurn (P:Spine)(j:Axis)(a:P.VMark)(X:P.Slabs j):P.Slabs j:=
 (P.transitTile j a)*X*(P.transitTile j (-a))
local notation "μ"=>P.ambientTurn j
lemma ambient_pay (a:P.VMark)(X:P.Slabs j): ‖μ a X‖≤‖X‖:=norm_pads_mul (Λ a) X (Λ (-a)) (transit_affordable a) (transit_affordable _)
lemma ambient_plus(a b:P.VMark)(X:P.Slabs j): μ a (μ b X)= μ (a+b) X:=by
 unfold ambientTurn
 rw [transit_plus, show -(a+b)= -b+ -a by abel,transit_plus]; simp only [mul_assoc]
lemma ambient_norm (a:P.VMark)(X:P.Slabs j): ‖μ a X‖=‖X‖:=by
 refine (ambient_pay a X).antisymm ?_
 have p:=ambient_pay (-a) (μ a X); rw [ambient_plus,neg_add_cancel] at p
 rw [show μ 0 X=X from (by unfold ambientTurn; rw [transit_zero,neg_zero,transit_zero,mul_one,one_mul])] at p; exact p

lemma H_racked {F:P.Test}{A B:P.meshPin}{s:ℕ}{X:P.Slabs j}(p:P.Habitable j F s A B X)
 (u:Cover):P.Habitable j (P.chartAll u F) s (A+(P.vtile s u j)) (B+P.vtile s u j)
 (P.ambientTurn j (P.vtile s u) X):=by
 let d:=P.vtile s u; let M:=timeMesh P.par; let R':=P.publicH j
 obtain ⟨t,k,a,w,r,g,p,rfl⟩:=p
 let v:=castor M s t ∘ u; let G:=P.conveying s (t-s) F; let X:=P.HabBox j t w (P.shifts j (-a) G)
 have he: d=P.vtile t v:=funext fun i =>(notch_up M s t k (u i)).symm
 have hz:P.conveying s (t-s) (P.chartAll u F)=P.chartAll v G:=P.cruise_raise ..
 have pa:= R'.meshM_turn (s:=t) p v
 show P.Habitable j _ s (A+d j) (B+d j) (μ d X)
 refine ⟨t,k,a+v j,w,?_,?_,?_⟩
 · rw [he]; change notch _ _ _ = A+notch _ _ _; rw [notch_add,show notch _ _ _ = A from r]
 · rw [g]; abel
 rw [hz,he]; refine ⟨pa.1,Subtype.ext ?_⟩
 change R'.ρ (Λ _ * X * Λ _) = R'.ρ (P.HabBox j t w _)
 rw [map_mul,map_mul,R'.transitReceipt,R'.transitReceipt]; exact pa.2.symm
lemma H_upRack {F:P.Test}{A B:P.meshPin}{s t:ℕ}{X:P.Slabs j}(p:P.Habitable j F s A B X)(h:s ≤ t)(u:Cover)(v:P.VMark)(w:P.vtile t u=v):
 P.Habitable j (P.chartAll u (P.conveying s (t-s) F)) t (A+v j) (B+v j) (P.ambientTurn j v X):= w ▸ H_racked ((Habitable.forward h).1 p) u
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
