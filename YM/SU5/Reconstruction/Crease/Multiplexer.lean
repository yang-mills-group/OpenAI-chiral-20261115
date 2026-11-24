import YM.SU5.Reconstruction.Crease.Mouth
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Club
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H D K:Hilbert}{M: Net H}{C: Clasp K H D}{J:Flash H}{Γ:Set H.Op}{Ω:H}
local notation "P"=>C.plume
local notation "R"=>C.shadow
local notation "J₀"=>J.f
local notation "B"=>BasePort C
local notation "Υ"=> WPort C Ω
variable (h:Club C J M Ω Γ)
variable {N A:H.Op} (k:N∈M.commutant) (q:A∈M) {u:ℂ}(p:WPort C Ω u N A)
include h q p
lemma lookup (x:H.Op)(e:x∈ M): inner ℂ (x Ω) (N Ω)= inner ℂ (star A Ω) (star x Ω)+ u*inner ℂ (x Ω) (A Ω):=by
 let y:=N Ω-u • (A Ω);
 let x':= J.f (star A Ω);
 have ht: P y= R x':= by
    apply C.plume_inj; unfold y x'; rw [map_sub,map_sub,map_smul,map_smul,p,show P (R _)=R (P (J.f (star A Ω))) from DFunLike.congr_fun C.opponents.eq _,h.charge A q]; abel
 let z:= label J Ω x; have t:= C.formulates (x Ω) (J.f (star x Ω)) (h.charge x e)
 have hx: x Ω=P z:=t.1; have he:inner ℂ (x Ω) y=inner ℂ (R z) x':= by rw [hx, Clasp.through_self P C.plume_self,ht,Clasp.through_self R C.shadow_self]
 unfold y x' at he; rw [inner_sub_right, inner_smul_right] at he; rw [← show J.f (star x Ω)=R z from t.2,J.light] at he; exact sub_eq_iff_eq_add.mp he
omit p
lemma pill(x y:H)(X:H.Op)(e: X∈M)(t: B x=X Ω): inner ℂ (X (star A Ω)) (P (R y))=inner ℂ (R (R x)) (J.shade (star A) (P (P y))):= by
 have he: J.f (star X Ω)=R (R x):= by
    apply C.plume_inj; rw [h.charge X e, ←t]; change R (P _) =_; exact DFunLike.congr_fun C.opponents.symm.eq _
 have ht:P (J.shade A (R (R x)))= R (X (star A Ω)):= by
    have hx:= h.charge (X*star A) (mul_mem e (star_mem q)); rw [star_mul,star_star,mul_apply_eq_comp,mul_apply_eq_comp] at hx; rw [←he, J.shade_light]; exact hx
 rw [show P (R y)=R (P y) from DFunLike.congr_fun C.opponents.eq y, ← Clasp.through_self _ C.shadow_self, ← ht, Clasp.through_self _ C.plume_self, Flash.shade_star]; exact (adjoint_inner_right ..).symm
include p k
lemma torque (x y:H): inner ℂ (P (R x)) (N (P (R y)))=inner ℂ (R (R x)) (J.shade (star A) (P (P y)))+u*inner ℂ (P (P x)) (J.shade (star A) (R (R y))):=by
 have he(x y:H)(X Y:H.Op)(m:X∈M)(q':Y∈M)(t:P (R x)=X Ω)(T:P (R y)=Y Ω):inner ℂ (P (R x)) (N (P (R y)))=inner ℂ (R (R x)) (J.shade (star A) (P (P y)))+u*inner ℂ (P (P x)) (J.shade (star A) (R (R y))):= by
   rw [t,T,show N (Y Ω)=Y (N Ω) from Eq.symm (DFunLike.congr_fun (VonNeumannAlgebra.mem_commutant_iff.mp k Y q') Ω),← adjoint_inner_left]
   have ht(y:H): Y.adjoint y= star Y y:= rfl
   have hy: Y.adjoint (X Ω)=(star Y*X) Ω:= rfl; rw [hy, h.lookup q p _ (mul_mem (star_mem q') m)]; congr 1
   · rw [star_mul,star_star,mul_apply_eq_comp,show star X=X.adjoint from rfl,adjoint_inner_right,← T]; exact h.pill q _ _ X m t
   congr 1
   have hk:= h.pill (A:=star A) (star_mem q) y x Y q' T; rw [star_star] at hk -- check expands
   -- right term <(star Y X)Ω,AΩ>=<P R x,Y A Ω>; use reverse conj hk: <Y AΩ,P R x>=<R^2 y, shade A P² x>. then adjoint.
   rw [← hy,adjoint_inner_left,← t];
   have hu:= congrArg (fun x:ℂ=>star x) hk; simp only [Complex.star_def,inner_conj_symm] at hu; rw [hu,J.shade_star, show star (J.shade A)=(J.shade A).adjoint from rfl]; exact (adjoint_inner_right ..).symm
 have e(x:H)(hp:x∈ {x:H|∃ X∈M, B x=X Ω}) : inner ℂ (P (R x)) (N (P (R y)))=inner ℂ (R (R x)) (J.shade (star A) (P (P y)))+u*inner ℂ (P (P x)) (J.shade (star A) (R (R y))):=by
   obtain ⟨X,v,t⟩:=hp; apply closure_minimal ?_ (show IsClosed {y:H| inner ℂ (P (R x)) (N (P (R y)))=inner ℂ (R (R x)) (J.shade (star A) (P (P y)))+u*inner ℂ (P (P x)) (J.shade (star A) (R (R y)))} from isClosed_eq (by fun_prop) (by fun_prop)) (h.admission y); rintro y ⟨Y,q,T⟩; exact he x y X Y v q t T
 exact closure_minimal (fun (i:H) hx=> e i hx) (show IsClosed {x:H|inner ℂ (P (R x)) (N (P (R y)))=inner ℂ (R (R x)) (J.shade (star A) (P (P y)))+u*inner ℂ (P (P x)) (J.shade (star A) (R (R y)))} from isClosed_eq (by fun_prop) (by fun_prop)) (h.admission x)
end YM.BridgeClub.Club
