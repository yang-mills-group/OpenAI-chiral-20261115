import YM.SU5.Assay.Listen
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
private lemma find_open {«H»:Hilbert}(N:Submodule ℂ «H»)(W:«H».Op)(u:«H»)
 (p:‖W u‖=1)(m:u∈N.topologicalClosure){J:Set «H»}(h:J∈𝓝 u):∃v∈N,‖W v‖=1∧v∈J:=by
 let F(y:«H»):«H»:=((‖W y‖:ℂ)⁻¹)•y
 have q: F u=u:=by simp [F,p]
 have r:ContinuousAt F u:= (.smul
   (((Complex.continuous_ofReal.comp W.continuous.norm).continuousAt).inv₀ (by simp [Function.comp,p]))
   continuousAt_id : ContinuousAt F u)
 have e: ∀ᶠ y in 𝓝 u, ‖W y‖≠0:=W.continuous.norm.continuousAt.eventually_ne (by rw [p]; exact one_ne_zero)
 obtain ⟨y,⟨v,s⟩,l⟩:=(mem_closure_iff_nhds (s:=(N:Set «H»))).mp m _ (e.and (r.eventually (show J∈𝓝 (F u) from q.symm ▸ h)))
 refine ⟨F y,N.smul_mem _ l,?_,s⟩
 unfold F; rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),inv_mul_cancel₀ v]

/-! Charges by two auxiliary calipers, past the edges of the single
 claimed caliper by n ticks on each side. -/
variable (P j s w) (n:ℕ)
local notation "W"=>P.singleState j s
local notation "Q"=> μ j s w

def guardPlate := P.euclOp j (Ν s n)
local notation "D"=>P.guardPlate j s n
/-- The operation keeping the raw field. v (after pasting Δt) inserts
    a boundary condition on both sides. -/
def framed (f:P.Test)(z:P.Hil j):ℂ:=inner ℂ (D z) (Q f (D z))
local notation "R"=>P.framed j s w n
lemma framed_cont (f:P.Test):Continuous (R f):= (D).continuous.inner ((Q f).continuous.comp (D).continuous)

def rinse := ν j (Ν s w/2)*D
local notation "A"=>P.rinse j s w n
lemma rinse_unit (p:0<w)(z:P.Hil j):R 1 z=(‖A z‖:ℂ)^2:=by
 let B:=ν j (Ν s w/2)
 have e: (B.adjoint*B)=Q 1:=by
  change star (ν _ _)*_=_
  rw [heats_star,←P.heats_join,add_halves,P.meanBox_unit s _ p]
 exact (by unfold framed;rw [←e,ContinuousLinearMap.mul_apply,ContinuousLinearMap.adjoint_inner_right]; exact inner_self_eq_norm_sq_to_K _)
local notation "iG"=> P.inHil j
lemma rinse_ground (z:P.vacuum j): A (iG z)=iG z∧ D (iG z)=iG z:=by
 have s':= ((P.ground_ok j _).mp z.2).1
 exact ⟨show _ from (by unfold rinse;rw [ContinuousLinearMap.mul_apply,show D (iG z)=iG z from s' _];exact s' _),s' _⟩
lemma ground_seat (z:P.vacuum j)(x:P.Spectrum0 j)(f:P.Test)(p:P.BEntry j w f)(e:‖z‖=1):
 ‖R f (iG z)- W x f‖ ≤ ‖P.compressed j s f z-W x f • z‖:=by
 have t:inner ℂ z (W x f•z)= W x f:=by rw [inner_smul_right,inner_self_eq_norm_sq_to_K,e];simp
 have r:R f (iG z)=inner ℂ z (P.compressed j s f z):= by
   rw [framed,meanBox_state s p,(P.rinse_ground j s w n z).2];exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ..).symm
 calc
   _ = ‖inner ℂ z (P.compressed j s f z-W x f • z)‖:=by rw [r,inner_sub_right,t]
   _ ≤ _ :=(norm_inner_le_norm ..).trans (by rw [e,one_mul])

/-- Charging finitely many inputs on this caliper. -/
lemma framed_earns (L₀:Finset P.Test)(p:∀f∈L₀,P.BEntry j w f)(x:P.Spectrum0 j)(B:P.Register)(δ:ℝ)(y:0<δ):
 ∃a f,P.Placard j w n L₀ a f ∧ let z:=μ j s a f (Ω j)
   ‖z‖<2 ∧ ‖A z‖=1 ∧ ∀i∈L₀,‖R i z-W x i‖<δ:=by
 obtain ⟨v,h,hv,g⟩:=P.near_ground j s w n L₀ p x B δ y
 have e:‖iG v‖=1:=hv
 have u:{z|‖z‖<2∧∀i∈L₀,‖R i z-W x i‖<δ}∈𝓝 (iG v):=by
   refine ((continuous_norm.tendsto (iG v)).eventually (gt_mem_nhds (show ‖iG v‖<2 by rw [e];exact one_lt_two))).and ?_
   refine (L₀.eventually_all).mpr ?_; intro i m
   exact (((P.framed_cont j s w n i).sub continuous_const).norm.tendsto (iG v)).eventually
       (gt_mem_nhds ((P.ground_seat j s w n v x _ (p i m) hv).trans_lt (g i m)))
 obtain ⟨z,⟨a,f,q,rfl⟩,h',k,l⟩:=find_open (P.procession j s w n L₀) A (iG v)
   (by rw [(P.rinse_ground j s w n v).1,e]) h u
 exact ⟨a,f,q,k,h',l⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
