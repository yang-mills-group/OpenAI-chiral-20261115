import YM.SU5.Reconstruction.Cashier.Booth
import YM.SU5.Reconstruction.Chambers.Operator
/-! near −E metric and meaning in the chosen actor; there is no requirement actor state restricted to convex limits or even any spectral indicator properties. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 490000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification Tapestry PhaseChoice
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)(j:Axis) (C:Arena Y H G.history.circuit j 0 false)(w:ℕ)
  (S:Finset Cover)(t:Between (tent Y H) j 0 (ruler Λ.block*w) S)(hw:0<w)
local notation "uM"=> (L₀^(s+1-s)*w)
local notation "Wh"=>wingspan Λ l S
local notation "Rx"=>render S (tent Y H)
local notation "B"=>allBox Y H V G j S s C w t hw
local notation "Ξ" s:max w:max=>advance Y H V G.history.circuit j 0 false C (MeshClock.whenly (timeMesh Λ) s w)
open Selected
open FirstWindows (ticket)
open FirstWindows.Chambers
open Vacancy
variable {x:Marks (tent Y H) false}{J:ℝ}
local notation "Hf"=>StampFoot Y H V s G j C w S
local notation "Θ"=>MeshClock.whenly (timeMesh Λ) s w
open scoped InnerProductSpace
private lemma cashier_eval {K₁:Hilbert} {v:ℝ}{A Y:K₁.Op}{x:K₁}{z:ℂ}(h:‖x‖=1)(p:Y x=x)(c:‖A+Y‖ < v)(e:inner ℂ x (A x)=z):‖z+1‖<v∧1-v< ‖z‖:=by
 have ht:=norm_inner_le_norm (𝕜:=ℂ) x ((A+Y) x); rw [h,one_mul] at ht; have hu:= (A+Y).le_opNorm x
 have hd: inner ℂ x ((A+Y) x)=z+1:=by rw [ContinuousLinearMap.add_apply,p,inner_add_right, e,inner_self_eq_norm_sq_to_K,h]; simp
 rw [hd] at ht; have hw:=ht.trans hu; rw [h,mul_one] at hw; have he:=hw.trans_lt c; exact ⟨he,(by
    have hv:1 ≤ ‖z+1‖+‖z‖:= by have h:=norm_sub_le (z+1) z; rwa [add_sub_cancel_left,norm_one] at h; -- `(a+b)-a`
    linarith)⟩
lemma origin {f: Family (tent Y H)} (h:Hf f J): ‖E s f+1‖<J ∧ 1-J<‖E s f‖:=by
 obtain ⟨k,v,h,a,p,u⟩:=h; subst f; exact cashier_eval (vane Y H V G.history.circuit j 0 false C) (advance_vacuum ..) u (boxed_at Y H V s G.history G.clipped j false C w a h)

variable (χ: displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "G₀"=>ride Y H V G.history G.clipped j false C χ
local notation "I₀"=>indoor Y H V G.history G.clipped j false C χ
local notation "Ω"=>doorstep Y H V G.history G.clipped j false C χ
local notation "E'"=>response Y H V s G.history G.clipped j false C χ
local notation "Π₁"=>procession Y H V G.history G.clipped j false C χ
local notation "κ"=>heatStamp Y H V s G.history G.clipped j false C w

lemma operator_relation (y:Tapestry.Dome (tent Y H)) (h:Hf y.val J)(g:x.val=y.val) : ∃ M:(indoor Y H V G.history G.clipped j false C χ).Op, Follows Y H V G j C χ (ticket Y H G s y) (MeshClock.notch (timeMesh Λ) s w) M ∧ ‖M+(G₀).E Θ‖<J∧ inner ℂ Ω (M Ω)=E' x :=by
 obtain ⟨c,v,p,X,t,q⟩:=h
 let M:=entrance Y H V s G.history G.clipped j false C X p
 have ht:inner ℂ Ω ((Π₁ M) Ω)= E' (actorLabel Y H s j false X.val):=by rw [←arrive_vec,arrive_mean]; exact entry_read Y H V s G.history G.clipped j false C χ X p
 refine ⟨Π₁ M,?_,?_,?_⟩
 · have h:= arrangement Y H V G j C χ s w X p; rw [show (FirstWindows.Chambers.base Y H j s w X).val=y from Subtype.ext t] at h; -- match? 
   exact h

 · have hx: ‖Π₁ (M+κ)‖<J:= (NonUnitalStarAlgHom.norm_apply_le (Π₁) (M+κ)).trans_lt q
   rw [map_add] at hx; exact hx
 rw [ht]; exact congrArg (fun z=>E' z) (Subtype.ext (t.trans g.symm))

lemma viewpoint (h:Hf x.val J): ‖E' x+1‖<J ∧ 1-J<‖E' x‖:=by
 obtain ⟨k,v,h,a,p,u⟩:=h; let M:=entrance Y H V s G.history G.clipped j false C a h
 have hx : ‖Π₁ (M+κ)‖<J:=(NonUnitalStarAlgHom.norm_apply_le (Π₁) (M+κ)).trans_lt u
 rw [map_add] at hx; refine cashier_eval (ready Y H V G.history G.clipped j false C χ) (hinges Y H V s G.history G.clipped j false C χ w) hx ?_
 rw [← arrive_vec,arrive_mean]; unfold M; rw [entry_read]; exact congrArg (fun z=> E' z) (Subtype.ext p)
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.operator_relation
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.viewpoint
