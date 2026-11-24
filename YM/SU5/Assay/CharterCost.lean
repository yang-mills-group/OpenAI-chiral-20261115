import YM.SU5.Assay.Reprise
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 100000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Charting the powers *before compression*. Use only `P.VMark` displacements
 on `ColorHil`. No norm or strong continuity assumptions on `truck`.
-/
local notation "ℛ"=> P.charter j x
local notation "G"=> P.truck j x
local notation "τ"=> (P.physicalEnergy j x).wax
local notation "Γ"=> P.VMark
lemma truck_dagger (p:Γ): star (G p)= G (-p):=P.truck_star j x p
lemma truck_splice (p q:Γ):G p*G q=G (p+q):=(P.truck_paves j x p q).symm
lemma truck_null : G 0=1:=P.truck_zero j x
lemma truck_wax (p:Γ)(t:ℝ):G p*τ t=τ t*G p:=
 ContinuousLinearMap.ext fun _=> P.sixWard_truck_heat ..
lemma truck_same {p q:Γ}(h:∀i≠j,p i=q i):G p=G q:=
  congrArg ((P.voyageF j x).raw _) (funext fun i=>h i.val i.property)
lemma truck_vac (A:X)(p:Γ): ℛ p A (Vac)= G p (A (Vac)):=by
 change G _ (A (G _ (Vac)))=_; rw [P.truck_empty]
lemma truck_wash (A:X)(p:Γ): inner ℂ (Vac) (ℛ p A (Vac))=inner ℂ (Vac) (A (Vac)):=by
 rw [P.truck_vac]
 rw [←neg_neg p,←P.truck_inner,P.truck_empty]

lemma charter_eq (p:Γ)(A:X):ℛ p A=G p*A*G (-p):= rfl
lemma charter_star (p:Γ)(A:X): star (ℛ p A)=ℛ p (star A):=by
 rw [P.charter_eq,P.charter_eq,star_mul,star_mul,P.truck_dagger,P.truck_dagger,neg_neg,mul_assoc]
lemma charter_sand (p:Γ)(A:X)(a b:ℝ): ℛ p ((U).sand A a b)= (U).sand (ℛ p A) a b:=by
 simp only [P.charter_eq,sand]
 rw [←mul_assoc _ _ (τ b),←mul_assoc _ (τ a) A,P.truck_wax j x p]
 rw [mul_assoc _ (τ b),←P.truck_wax j x (-p) b];simp only [mul_assoc]
lemma charter_wax (p:Γ)(a:ℝ):ℛ p (τ a)=τ a:=by
 rw [P.charter_eq,P.truck_wax,mul_assoc,P.truck_splice,add_neg_cancel,P.truck_null,mul_one]
lemma charter_add (p:Γ)(A L:X): ℛ p (A+L)= ℛ p A+ℛ p L:=by simp only [P.charter_eq,mul_add,add_mul]
lemma charter_sub (p:Γ)(A L:X): ℛ p (A-L)= ℛ p A-ℛ p L:=by simp only [P.charter_eq,mul_sub,_root_.sub_mul]
lemma charter_smul (p:Γ)(A:X)(a:ℂ): ℛ p (a•A)=a • ℛ p A:=by simp only [P.charter_eq,mul_smul_comm,smul_mul_assoc]
lemma charter_triv (p:Γ):ℛ p 0=0:=by simp only [P.charter_eq,mul_zero,zero_mul]
lemma charter_zero (A:X): ℛ 0 A=A:=by rw [P.charter_eq,neg_zero,P.truck_null,one_mul,mul_one]
lemma charter_list {ι:Type*}(p:Γ)(s:Finset ι)(f:ι→X): ℛ p (∑i∈s,f i)=∑i∈s,ℛ p (f i):=by simp_rw [P.charter_eq,mul_sum,sum_mul]
lemma charter_sum (p q:Γ)(A:X):ℛ p (ℛ q A)=ℛ (p+q) A:=by
 rw [P.charter_eq,P.charter_eq,P.charter_eq]
 rw [neg_add_rev,←P.truck_splice,←P.truck_splice]
 simp only [mul_assoc]
lemma charter_cancel (p:Γ)(A:X): ℛ (-p) (ℛ p A)=A:=by rw [charter_sum,neg_add_cancel,charter_zero]
lemma charter_cost (p:Γ)(A:X): ‖ℛ p A‖= ‖A‖:= le_antisymm (P.charter_pay j x A p) (by
 exact (congrArg norm (P.charter_cancel j x p A)).symm.trans_le (P.charter_pay j x _ _))
lemma charter_dist (p:Γ)(A L:X): ‖ℛ p A-ℛ p L‖= ‖A-L‖:=by rw [←P.charter_sub,P.charter_cost]
lemma charter_vac_cost (p:Γ)(A:X): ‖ℛ p A (Vac)‖= ‖A (Vac)‖:=by rw [P.truck_vac,P.truck_norm]
lemma charter_same {p q:Γ}(h:∀i≠j,p i=q i)(A:X):ℛ p A= ℛ q A:=by
 rw [P.charter_eq,P.charter_eq,P.truck_same j x h,P.truck_same j x (p:= -p) (q:= -q) (fun _ e=>congrArg Neg.neg (h _ e))]

-- Compression respects BSOT and norm convergence.
variable {I:Type*}{l:Filter I}{f:I→(P.ColorHil j x).Op}{A:(P.ColorHil j x).Op}
local notation "π"=> P.reprise j x
lemma reprise_bsot (p:BSOT f l A):BSOT (fun i=>π (f i)) l (π A):=by
 obtain ⟨C,u,v⟩:=p.ceiling
 refine ⟨⟨C,u,v.mono fun i h=> (P.reprise_pay ..).trans h⟩,
    fun y=> ((R).continuous.tendsto _).comp (p.showAt (E y)),?_⟩
 intro y;simp_rw [P.reprise_star]; exact ((R).continuous.tendsto _).comp (p.starAt (E y))
lemma reprise_norm (p:Tendsto f l (𝓝 A)):Tendsto (fun i=>π (f i)) l (𝓝 (π A)):=by
 rw [tendsto_iff_norm_sub_tendsto_zero] at p ⊢
 refine squeeze_zero (fun i=>norm_nonneg _) (fun i=>?_) p
 simp only [←P.reprise_sub];exact P.reprise_pay ..
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
