import YM.SU5.Assay.Distant
import YM.SU5.Assay.Deskroom
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
variable (P j)
lemma shifts_commute (k:Axis)(x y:ℤ)(f:P.Test):σ x (P.shifts k y f)=P.shifts k y (σ x f):=
 Subtype.ext (twin_slide _ _ _ _ f.property.paid.choose_spec)
variable(s) (f g)
lemma two_enter:∃ a w:ℕ,P.BEntry j w (σ a f) ∧ P.BEntry j w (σ a g):=by
 obtain ⟨u,p⟩:=findsBay _ f
 obtain ⟨l,r⟩:=findsBay _ g
 obtain ⟨a,h,y,v⟩:= ((P.eventually_BFits u).and ((P.eventually_BFits l).and (eventually_gt_atTop 0))).exists
 exact ⟨a,a+a,h.admit p a j le_rfl (by omega) (by omega),y.admit r a j le_rfl (by omega) (by omega)⟩

lemma strata (n:ℕ){a:ℕ}(p:P.BEntry j w (σ a f))(q:P.BEntry j v (σ a g)):
 P.E s ((f *σ (w+n:ℕ) g).val)=
   inner ℂ (Ω j) ((μ j s w (σ a f)*ν j (Ν s n)*μ j s v (σ a g)) (Ω j)):=by
 rw [←meanBox_right s p]
 have u:=p.right (Nat.le_add_right w n)
 rw [←meanBox_concat s u q,meanBox_earns s (u.concat q)]
 conv_lhs =>rw [← P.E_invariant j s a, map_mul,P.shifts_sum,add_comm (↑a:ℤ)]
 rw [P.shifts_sum]
lemma shifting_front (k:ℕ): Tendsto
   (fun n:ℕ=>P.E s ((f*σ (k+n:ℕ) g).val)-P.E s ((f*σ n g).val)) atTop (𝓝 0):= by
 obtain ⟨a,v,p,q⟩:=P.two_enter j f g
 let F:=μ j s v (σ a f)
 let G:=μ j s v (σ a g)
 let φ(t:(P.Hil j).Op):ℂ:=inner ℂ (Ω j) ((F*t*G) (Ω j))
 have h:Continuous φ:=continuous_const.inner (𝕜:=ℂ)
   (((continuous_const.mul continuous_id).mul continuous_const).clm_apply continuous_const)
 have h₁:= (P.distant j s (Ν s k)).comp (tendsto_sub_atTop_nat v)
 have h':= (h.tendsto 0).comp h₁
 have g₀:φ 0=0:=by simp [φ]
 rw [g₀] at h'
 apply h'.congr'
 filter_upwards [eventually_ge_atTop v] with n y
 simp only [Function.comp_apply,φ,F,G,←when_add]
 have h₃:=P.strata j s f g (n-v) p q
 have h₄:=P.strata j s f g (k+(n-v)) p q
 rw [Nat.add_sub_of_le y] at h₃
 rw [show v+(k+(n-v))=k+n by omega] at h₄
 rw [h₃,h₄,_root_.mul_sub, _root_.sub_mul, sub_apply, inner_sub_right]
local notation "Yf"=>μ j s w f
local notation "Yg"=>μ j s v g
lemma across_ask (d:Trans j)(p:P.BEntry j w f)(q:P.BEntry j v g)(a:ℤ):
 inner ℂ (Yf (Ω j)) (T j (s,a,d) (Yg (Ω j)))=
 P.E s (((P.riposte j w f)*P.shifts d a (σ w g)).val):=by
 have z: T j (s,a,d) (Yg (Ω j)) = μ j s v (P.shifts d a g) (Ω j):=by
   change (T j (s,a,d)*Yg) (Ω j)=_
   rw [meanBox_across s q,ContinuousLinearMap.mul_apply,P.floor_moves]
 let A:=P.shifts d a g
 rw [z,←ContinuousLinearMap.adjoint_inner_right]
 change inner ℂ _ ((star Yf *μ j s v A) (Ω j))=_
 rw [meanBox_star s p,←meanBox_concat s p.riposte (q.across ..),meanBox_earns s (p.riposte.concat (q.across ..)),P.shifts_commute]

lemma across_ask_fee (d:Trans j)(p:P.BEntry j w f)(q:P.BEntry j v g)(k:ℕ): Tendsto
    (fun n:ℕ=>inner ℂ (Yf (Ω j)) ((T j (s,↑(k+n),d)-T j (s,n,d)) (Yg (Ω j)))) atTop (𝓝 0):=by
 -- n expected ℕ cast k+n?
 refine (P.shifting_front d s (P.riposte j w f) (σ w g) k).congr fun n=>?_ 
 rw [sub_apply,inner_sub_right,P.across_ask j s f g d p q,P.across_ask j s f g d p q]
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
