import ZecaNib
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E

variable (D:P.Apron)
local notation "ET" => (P.seasons j x).E
local notation "G" => P.ManyF j x


local notation "K"=>P.wealth j x
local notation "η"=>P.enter j x
local notation "C"=>P.cartage j x

section film
variable {U:Hilbert}{I I₀: Type*} {l:Filter I} {k:Filter I₀}
variable {f g:I→U.Op} {T A:U.Op}


namespace Glaze_LocalFieldBounds

lemma smul (h:Glaze_LocalFieldBounds U l f T)(z:ℂ): Glaze_LocalFieldBounds U l (fun i=> z • f i) (z • T):= by
 obtain ⟨u,a,b⟩:=h.fee
 refine ⟨⟨‖z‖*u,by positivity,?_⟩,fun v=>(h.seeks v).const_smul z⟩
 filter_upwards [b] with i t
 rw [norm_smul]; gcongr
lemma add (h:Glaze_LocalFieldBounds U l f T)(v:Glaze_LocalFieldBounds U l g A):
 Glaze_LocalFieldBounds U l (fun i=> f i+g i) (T+A):=by
 obtain ⟨u,a,b⟩:=h.fee;obtain ⟨e,o,p⟩:=v.fee
 exact ⟨⟨u+e,by positivity,(b.and p).mono fun i h' => (norm_add_le ..).trans (add_le_add h'.1 h'.2)⟩,
        fun y=>(h.seeks y).add (v.seeks y)⟩
lemma sub (h:Glaze_LocalFieldBounds U l f T)(v:Glaze_LocalFieldBounds U l g A):Glaze_LocalFieldBounds U l (fun i=> f i-g i) (T-A):=by
 simpa only [neg_one_smul,sub_eq_add_neg] using h.add (v.smul (-1))

lemma mend {e:I→ℝ}(h:Glaze_LocalFieldBounds U l f T)(p:Tendsto e l (𝓝 0))(u:∀ᶠ i in l, ‖g i-f i‖≤e i):
 Glaze_LocalFieldBounds U l g T:=by
 have r: Glaze_LocalFieldBounds U l (fun i=>g i-f i) 0:=.pops (tendsto_zero_iff_norm_tendsto_zero.2
     (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) u p))
 simpa only [zero_add,sub_add_cancel] using r.add h
lemma sum {J:Type*}(s:Finset J)(f:J→I→U.Op)(g:J→U.Op)
 (h:∀ j∈s,Glaze_LocalFieldBounds U l (f j) (g j)):
 Glaze_LocalFieldBounds U l (fun i=> ∑ j∈s,f j i) (∑ j∈s,g j):=by
 classical
 induction s using Finset.induction with
 | empty=> simpa only [Finset.sum_empty] using Glaze_LocalFieldBounds.const (U:=U) (l:=l) 0
 | @insert u s v ih=>
    simp only [Finset.sum_insert v]; exact (h u (mem_insert_self ..)).add
            (ih (fun y v=>h y (mem_insert_of_mem v)))

end Glaze_LocalFieldBounds
end film
variable {P j x} {F B:P.Nib j x}
namespace NibPay
lemma zero:P.NibPay j x (fun _ _ =>0):=by
 refine ⟨1,0,by norm_num,fun t p r=>?_⟩
 simp
lemma smul (z:ℂ) (p:P.NibPay j x F) : P.NibPay j x (fun a b=> z • F a b):=by
 obtain ⟨u,d,g,h⟩:=p
 refine ⟨(‖z‖+1)*u,d,by positivity,fun t p r=>?_⟩
 rw [norm_smul,mul_div_assoc]
 exact mul_le_mul (le_add_of_nonneg_right zero_le_one) (h t p r) (norm_nonneg _) (by positivity)
lemma add (p:P.NibPay j x F)(q:P.NibPay j x B):P.NibPay j x (fun a b=>F a b+B a b):=by
 obtain ⟨u,m,r,s⟩:=p; obtain ⟨v,n,y,c⟩:=q
 refine ⟨u+v,max m n,by positivity,fun t p d=>?_⟩
 rw [add_div]; apply ((norm_add_le ..).trans (add_le_add (s t p d) (c t p d))).trans
 exact add_le_add
  (div_le_div_of_nonneg_left r.le (pow_pos p _) (pow_le_pow_of_le_one p.le d (le_max_left _ _)))
  (div_le_div_of_nonneg_left y.le (pow_pos p _) (pow_le_pow_of_le_one p.le d (le_max_right _ _)))
lemma sum {J:Type*} (s:Finset J)(f:J→P.Nib j x)
 (h:∀ u∈s,P.NibPay j x (f u)): P.NibPay j x (fun a b=>∑u∈s,f u a b):=by
 classical
 induction s using Finset.induction with
 | empty=> simpa only [Finset.sum_empty] using NibPay.zero (P:=P) (j:=j) (x:=x)
 | @insert u s v ih=>
    simp only [Finset.sum_insert v]
    exact (h u (mem_insert_self ..)).add (ih (fun y v=>h y (mem_insert_of_mem v)))
end NibPay
