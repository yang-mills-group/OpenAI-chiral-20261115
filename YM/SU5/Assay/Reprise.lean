import YM.SU5.Assay.Locate
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
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
/-! Fixed compression ColorHil → ManyF. A reading in the latter will always
 also be checked against the actual grid price, not just this compression. -/
abbrev reprise (A:X):Y := (R).comp (A.comp (E).toContinuousLinearMap)
local notation "π"=> P.reprise j x
local notation "ℛ"=> P.locate j x
lemma reprise_table (A:X)(y:Vantage): θ y A= ℛ y (π A):=by ext1 i; rfl
lemma reprise_zero (A:X): θ 0 A=π A:= (P.reprise_table ..).trans (P.locate_zero ..)
lemma reprise_pay (A:X): ‖π A‖≤ ‖A‖:=by rw [←P.reprise_zero j x A]; exact P.tableau_pay ..
lemma reprise_star (A:X): star (π A)=π (star A):=by
 rw [←P.reprise_zero j x A,←P.reprise_zero j x (star A)]; exact P.boards_star ..
lemma reprise_smul (A:X)(a:ℂ): π (a•A)=a • π A:=by
 ext1 i; change R ((a:ℂ)•(A (E i)))= a•R (A (E i)); exact (R).map_smul a _
lemma reprise_add (A D:X): π (A+D)= π A+π D:=by ext1 i; exact (R).map_add (A (E i)) _
lemma reprise_sub (A D:X): π (A-D)= π A-π D:=by ext1 i; exact (R).map_sub (A (E i)) _
lemma bank_inner (u:B)(v:H): inner ℂ u (R v) = inner ℂ (E u) v:=
 by rw [←ContinuousLinearMap.adjoint_inner_left,P.bank_star]; rfl
lemma reprise_unit : π 1=1:=by ext1 i; exact P.rewarded j x i
lemma reprise_vac (A:X):inner ℂ Ω (π A Ω)= inner ℂ Vac (A Vac):= P.bank_inner j x Ω (A Vac)
lemma bank_wax (u:H)(a:ℝ): R ((U).wax a u)= ω a (R u):= P.bankHeat ..
lemma enter_wax (u:B)(a:ℝ):E (ω a u)=(U).wax a (E u):= rfl
lemma reprise_wax (a:ℝ): π ((U).wax a)=ω a:=by
 ext1 i; exact P.rewarded j x (ω a i)
lemma reprise_sand (A:X)(a b:ℝ): π ((U).sand A a b)= (S).sand (π A) a b:=by
 ext1 i; exact P.bankHeat j x _ (A ((U).wax b (E i)))
lemma reprise_hang (A:X)(w a b:ℝ): π ((U).hang w A a b)= (S).hang w (π A) a b:= P.reprise_sand ..

local notation "Q"=> P.truck j x
lemma bank_truck (p:P.VMark)(u:H): R (Q p u)= W (P.laysM p) (R u):=by
 apply ext_inner_left ℂ; intro v
 have h:inner ℂ (E v) (Q p u)=inner ℂ (Q (-p) (E v)) u:=(ContinuousLinearMap.adjoint_inner_left (Q p) u (E v)).symm.trans
   (congrArg (fun L:X=>inner ℂ (L (E v)) u) (P.truck_star ..))
 rw [P.bank_inner,h,P.cart_and,P.lays_neg,←P.bank_inner,←P.cart_reverses, ContinuousLinearMap.adjoint_inner_left]
lemma reprise_charter (p:P.VMark)(A:X): π (P.charter j x p A)= ℛ (P.laysM p) (π A):=by
 ext1 i
 change R (Q p (A (Q (-p) (E i))))=_; rw [P.bank_truck,P.cart_and,P.lays_neg]; rfl

lemma reprise_empty (u:B): R (E u)=u:= P.rewarded j x u
-- congruence of moving costs, even when limit known only on eigen stage subspace B
lemma reprise_receipt {I:Type*}{l:Filter I}{A:I→X}{T:Y}
 (h:∃ C:ℝ,0≤C∧∀ᶠ i in l, ‖A i‖≤C)
 (t:∀u:B, Tendsto (fun i=>A i (E u)) l (𝓝 (E (T u))))
 (v:∀u:B,Tendsto (fun i=>star (A i) (E u)) l (𝓝 (E (star T u)))):
 BSOT (fun i=> π (A i)) l T:=by
 obtain ⟨C,u,e⟩:=h
 refine ⟨⟨C,u,e.mono fun i q=> (P.reprise_pay _ _ _).trans q⟩,fun y=>?_,fun y=>?_⟩
 · have f:=((R).continuous.tendsto _).comp (t y); rw [P.reprise_empty] at f; exact f
 simp only [P.reprise_star]; have f:=((R).continuous.tendsto _).comp (v y); rw [P.reprise_empty] at f; exact f
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
