import YM.SU5.Fineness.Duty
import Mathlib.Analysis.Matrix.PosDef
/-! # Zero proof and real torsion positivity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Fineness
open Function Lattice RG Matrix Exterior Precision Tree
open scoped Matrix Topology BigOperators
variable {I J : Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{n:Side}(H:Sheet I){x:I→ℝ}
def qpay (H:Sheet I)(x:I→ℝ) := dotProduct x (H *ᵥ x)
lemma q_at (h:H.PosDef)(p:x≠0): 0<qpay H x:=by simpa [qpay] using ((Matrix.posDef_iff_dotProduct_mulVec).mp h).2 p
lemma cost_zero (h:H.PosDef)(x:I→ℝ) : 0 ≤ qpay H x:=by by_cases p:x=0; simp [p,qpay]; exact (q_at _ h p).le
lemma q_iff : H.PosDef ↔ Hᵀ=H ∧ ∀ x:I→ℝ, x≠0 → 0 < qpay H x:=by
 rw [Matrix.posDef_iff_dotProduct_mulVec]; simp only [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial,star_trivial]; rfl -- binder implicit
lemma l2pos (x:I→ℝ)(p:x≠0):0<dotProduct x x:=by simpa [qpay] using q_at 1 (Matrix.PosDef.one) p
lemma qgain {A:Tab I J}(u: J→ℝ) : qpay (Aᵀ*H*A) u=qpay H (A *ᵥ u):=by unfold qpay; simp only [←Matrix.mulVec_mulVec]; rw [dotProduct_transpose_mulVec,dotProduct_comm]
lemma priced_plus {A B: Sheet I}(x:I→ℝ): qpay (A+B) x=qpay A x+qpay B x:=by unfold qpay; rw [Matrix.add_mulVec,dotProduct_add]
lemma gram_price {T:Tab I J} (u:J→ℝ) : qpay (Tᵀ*T) u=dotProduct (T*ᵥ u) (T*ᵥ u):=by unfold qpay; rw [← mulVec_mulVec,dotProduct_transpose_mulVec]
lemma Rail.spike {X:Tab I J}(h:Rail X)(x:J→ℝ)(p:X *ᵥ x=0) : x=0:=by
 have he:=congrArg (axes X *ᵥ ·) p; change axes X*ᵥ (X*ᵥ x)=_ at he; rwa [mulVec_mulVec,axes_deck h,one_mulVec,mulVec_zero] at he
lemma Rail.gramPos {X:Tab I J}(h: Rail X) : (Xᵀ * X).PosDef:=by
 apply (q_iff _).2; refine ⟨by simp,fun v hv=>?_⟩; rw [gram_price]; exact l2pos _ (fun p=>hv (h.spike v p))
variable {z:form 1 n}
local notation "d₁"=> d 1 n
local notation "X₀"=>sightZero n
lemma circulation_cost (p:d₁*ᵥ z=0)(x:Site n)(a b:Axis) : z (x+step a, coord b) - z (x,coord b)=z (x+step b,coord a)-z (x,coord a) :=by
 have he(y:Site n)(i j:Axis)(h:i<j):= d_plaquettes y ⟨(i,j),h⟩ z
 rcases lt_trichotomy a b with h|h|h
 · have he':= he x a b h; rw [p] at he'; exact sub_eq_zero.mp he'.symm
 · rw [h]
 have hp:= he x b a h; rw [p] at hp; exact (sub_eq_zero.mp hp.symm).symm
lemma no_wind (p:d 1 n*ᵥ z=0)(h:∀ u,dotProduct z (sightZero n *ᵥ u)=0) : z=0:=by
 have hu (a:Axis) (x:Site n) (b:TypeFace 1) : z (x+step a,b)=z (x,b):=by
    let T (i:Body 0 n):= z (i.1,coord a); let g:= d 0 n*ᵥ T
    let e : Body 1 n≃ Body 1 n:=Equiv.prodCongr (Equiv.addRight (step a)) (Equiv.refl (TypeFace 1))
    have he:z∘e=z+g:=by
       funext ⟨x,b⟩; obtain ⟨i,rfl⟩:=axisEquiv.surjective b; have hx:=circulation_cost p x a i; change _=z (x,coord i)+(d 0 n*ᵥ T) (x,coord i); rw [d_sites, add_comm]; exact sub_eq_iff_eq_add.mp hx
    let v:= fun i:Puncture n=> T (i.val,vac) - T (0,vac)
    have hg:dotProduct z g=0:=by
       have hy:= h (Sum.elim v 0); rw [sightZero, fromCols_mulVec_sumElim,Matrix.mulVec_zero,add_zero, show rootGrad n*ᵥ v=g from trimmed T] at hy; exact hy
    have hh: dotProduct (z∘⇑e) (z∘⇑e)=dotProduct z z:= Equiv.sum_comp e (fun i=>z i*z i)
    rw [he, add_dotProduct, dotProduct_add,dotProduct_add, dotProduct_comm g z,hg,zero_add,add_zero,add_eq_left] at hh
    have hv:g=0:= dotProduct_self_eq_zero.mp hh; rw [hv,add_zero] at he; exact congrFun he (x,b)
 have hp (x:Site n) (b:TypeFace 1) : z (x,b)=z (0,b):=by
    let T : form 0 n:=fun y=>z (y.1,b); have hv:d 0 n*ᵥ T=0:=by
       funext ⟨x,i⟩; obtain ⟨a,rfl⟩:=axisEquiv.surjective i; rw [coord_map,d_sites]; exact sub_eq_zero.mpr (hu ..)
    by_cases e:x=0; rw [e]; let w:Puncture n:=⟨x,e⟩; let q:=fun i:Puncture n=> T (i.val,vac)-T (0,vac)
    have he:q=0:=puncture_off q ((trimmed T).trans hv); exact sub_eq_zero.mp (congrFun he w)
 let q (a:Axis):= z (0,coord a); have hz:harmonic n*ᵥ q=z:=by
    funext ⟨x,i⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective i; rw [coord_map,coord_read]; exact (hp _ _).symm
 apply dotProduct_self_eq_zero.mp
 have he:= h (Sum.elim 0 q); rwa [sightZero,fromCols_mulVec_sumElim,Matrix.mulVec_zero,hz,zero_add] at he
lemma arena_comm : d₁*X₀=0:=by rw [sightZero,mul_fromCols,rootGrad,← Matrix.mul_assoc,closed 0 n,Matrix.zero_mul,null_const,fromCols_zero]
lemma flecks (p:d 1 n*ᵥ z=0) : ∃ u,sightZero n *ᵥ u=z:=by
 let Z:=(X₀)ᵀ; let K:=Z*X₀; have hp:(X₀ᵀ*X₀).PosDef:= (lattice_null (n:=n) (1:Sheet (Body 2 n)) (by simp)).rail.gramPos
 let u:= K⁻¹*ᵥ (Z*ᵥ z); let f:= z-X₀*ᵥ u; have ht: K*K⁻¹=1:= K.mul_nonsing_inv ((K.isUnit_iff_isUnit_det).1 hp.isUnit)
 have hu:f=0:=no_wind (z:=f) (by unfold f; rw [mulVec_sub,p,mulVec_mulVec,arena_comm,zero_mulVec,sub_zero]) (fun u'=>by
    rw [←dotProduct_transpose_mulVec] -- goal maybe ← ? formula
    unfold f; rw [mulVec_sub,mulVec_mulVec,show ((X₀)ᵀ* X₀)*ᵥ u=Z*ᵥ z from (by change K*ᵥ (K⁻¹*ᵥ (Z*ᵥ z))=_; rw [mulVec_mulVec,ht,one_mulVec]),(show Z=(X₀)ᵀ from rfl),sub_self]; apply dotProduct_zero -- rfl tune
    )
 exact ⟨u,(sub_eq_zero.mp hu).symm⟩
lemma lattice_pos {M: Sheet (Body 2 n)} (h:M.PosDef) : 0 < leasePart M:=by
 let X:= X₀; let T:= axes X
 have v:T*X=1:=axes_deck (lattice_null M ((q_iff _).1 h).1).rail
 apply (show Matrix.PosDef (K M+Tᵀ*T) from ?_).det_pos
 apply (q_iff _).2; refine ⟨?_,fun x hx=>?_⟩
 · rw [transpose_add,(lattice_null M ((q_iff _).1 h).1).symmA,transpose_mul,transpose_transpose]
 rw [priced_plus,gram_price,show qpay (K M) x=qpay M (d₁*ᵥ x) from qgain M x]
 by_cases hz:d₁*ᵥ x=0
 · obtain ⟨u,p⟩:=flecks hz
   refine add_pos_of_nonneg_of_pos (cost_zero M h _) (l2pos _ ?_); rintro he
   rw [← p, show T *ᵥ (sightZero n *ᵥ u)=u from (by rw [Matrix.mulVec_mulVec,v,one_mulVec])] at he
   apply hx; rw [←p,he,Matrix.mulVec_zero]
 exact add_pos_of_pos_of_nonneg (q_at _ h hz) (FreeResolvent.normSum_nn _)
end YM.Fineness
#print axioms YM.Fineness.lattice_pos
