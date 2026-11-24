import YM.SU5.Fineness.Ratio
import YM.Push.FREE_RESOLVENT.Flat
/-!
# Real zero columns (not just gradients); canonical choice puncturing zero vertex
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Fineness
open Function Lattice RG Matrix Exterior Precision Tree
open scoped Topology Matrix BigOperators
variable {I J : Type*} [Fintype I][Fintype J][DecidableEq I][DecidableEq J]
lemma Rail_of_zero (A:Tab I J)(g:∀ u:J → ℝ,A *ᵥ u=0 → u=0) : Rail A := by
 let D:=A.mulVecLin; have he:LinearMap.ker D=⊥:=by
    apply eq_bot_iff.mpr; intro u h; exact g u h
 obtain ⟨x,v⟩:= LinearMap.exists_leftInverse_of_injective D he; refine ⟨LinearMap.toMatrix' x,mulVec_injective (funext fun u=>?_)⟩
 simp only [← Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec,Matrix.one_mulVec]
 exact congrArg (fun L : _→ₗ[ℝ]_ => L u) v
/-- Rearrange using an equiv. -/
lemma ZeroBasis.page {A: Sheet I}{B:Tab I J}(h:ZeroBasis A B){K:Type*}[Fintype K][DecidableEq K] (e:K≃J): let W:=B.submatrix id e; ZeroBasis A W ∧ torsion A W=torsion A B:=by
 intro W
 let V:= (1:Sheet J).submatrix id e; let H:=Vᵀ
 have hV:B*V=W:= by
    have he:=submatrix_mul_equiv B (1:Sheet J) id (Equiv.refl J) (fun i=> e i); rw [Matrix.mul_one] at he; exact he
 have hv:V*H=1:=by unfold H V; rw [transpose_submatrix,submatrix_mul_equiv]; simp
 have hu:H*V=1:= (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hv
 refine ⟨h.slide_basis V H hv hu hV,?_⟩; have ht:= h.basis_expense e.symm V H hv hu hV; rw [show V*Vᵀ= _ from hv,det_one,one_mul] at ht; exact ht.symm
variable {n c f : Side}
abbrev Puncture (n:Side) := {x:Site n//x≠0}
local notation "D" n:max=> d 0 n
local notation "L" n:max=> d 1 n
def switch (n:Side) : Tab (Body 0 n) (Puncture n):= FreeResolvent.insertion fun (i:Puncture n)=> (i.val,vac)
def rootGrad (n:Side) : Tab (Body 1 n) (Puncture n):= D n * switch n
def harmonic (n:Side) : Tab (Body 1 n) Axis:= Matrix.of fun i j => if coord j=i.2 then 1 else 0
def sightZero (n:Side) := fromCols (rootGrad n) (harmonic n)
lemma coord_read (v:Axis→ℝ)(i:Axis)(x:Site n) : (harmonic n *ᵥ v) (x,coord i)=v i:=by simp [mulVec,dotProduct,harmonic, Exterior.coord_iff]
lemma null_const : (d 1 n)*harmonic n=0:=by
 apply mulVec_injective; funext v; rw [← mulVec_mulVec,zero_mulVec]; ext ⟨i,j⟩; obtain ⟨j,rfl⟩:=plaqEquiv.surjective j; rw [plaq_map,d_plaquettes]; simp only [coord_read]; simp
lemma switch_origin (p:Puncture n→ℝ) : (switch n*ᵥ p) (0,vac)=0:=by
 unfold mulVec dotProduct; rw [Finset.sum_eq_zero]; intro i hi; simp [switch,FreeResolvent.insertion,i.property]
lemma switch_punct (p:Puncture n→ℝ) (i:Puncture n): (switch n*ᵥ p) (i.val,vac)=p i:=by
 simp [mulVec,dotProduct,switch,FreeResolvent.insertion,Subtype.coe_inj]
lemma puncture_off (p: Puncture n→ℝ)(h:rootGrad n*ᵥ p=0): p=0:=by
 let v:=switch n *ᵥ p; have hx:D n*ᵥ v=0:= by unfold v; rw [Matrix.mulVec_mulVec]; exact h
 funext i
 let x:Site n:=i.val; let l:= route 0 (Lattice.lift x) 1
 have ht:stop (0:Site n) l=x:=by
    have h: wrap n 0=(0:Site n):=map_zero _
    rw [← h, ← wrap_stop_cover]; unfold l; rw [route_end,wrap_lift]
 have hL:= telescopes v (0:Site n) l; rw [hx,map_zero,ht,show v (0,vac)=0 from switch_origin p,sub_zero,show v (x,vac)=p i from switch_punct p i] at hL; exact hL.symm
lemma sumGrad_zero (v: form 0 n)(j:Axis) : ∑ i:Site n,(D n*ᵥ v) (i,coord j) =0:= by
 simp_rw [d_sites]; rw [Finset.sum_sub_distrib,sub_eq_zero]; exact Equiv.sum_comp (Equiv.addRight (step j)) (fun i=> v (i,vac))
lemma no_ghost (n:Side) {x:(Puncture n⊕Axis)→ℝ}(u: sightZero n *ᵥ x=0) : x=0:= by
 let p:= x∘ Sum.inl; let q:= x∘ Sum.inr
 have ht: D n *ᵥ (switch n*ᵥ p) + harmonic n*ᵥ q=0:=by
    rw [Matrix.mulVec_mulVec]; exact (fromCols_mulVec (rootGrad n) (harmonic n) x).symm.trans u
 have he:q=0:=by
    funext j; have h:=congrArg (fun v:form 1 n=>∑ i:Site n,v (i,coord j)) ht
    simp only [Pi.add_apply, Finset.sum_add_distrib, sumGrad_zero, coord_read,Finset.sum_const,Pi.zero_apply,Finset.card_univ,nsmul_eq_mul,mul_zero,zero_add,mul_eq_zero] at h
    exact h.resolve_left (by exact_mod_cast Fintype.card_pos.ne_zero)
 rw [he,Matrix.mulVec_zero,add_zero,Matrix.mulVec_mulVec] at ht; have hp:= puncture_off p ht; ext (i|i); exact congr_fun hp i; exact congr_fun he i
lemma lattice_null (A: Sheet (Body 2 n)) (h:Aᵀ=A) : ZeroBasis (Precision.K A) (sightZero n) := by
 constructor; rw [Precision.K,transpose_mul,transpose_mul,h,transpose_transpose,Matrix.mul_assoc]
 · unfold Precision.K; rw [sightZero,Matrix.mul_assoc, mul_fromCols,null_const,rootGrad, ← Matrix.mul_assoc,closed 0 n, Matrix.zero_mul,fromCols_zero,Matrix.mul_zero] -- closed ambiguous
 exact Rail_of_zero (sightZero n) (fun _=> no_ghost n)

section fine
variable (S:StepData c f)
/-- Read harmonic columns under resolution. Gradient part may be corrected freely at next stage. -/
lemma agrees_mean (i:Axis)(p:Axis→ℝ)(x: Site c) : (mean S *ᵥ (harmonic f *ᵥ p)) (x,coord i) = (S.patch.L.val:ℝ)*p i:=by
 rw [mean,LinearMap.toMatrix'_mulVec]
 have he: axisEquiv.symm (coord i)=i:= axisEquiv.symm_apply_apply i
 simp only [LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.smul_apply,he,smul_eq_mul]
 have ht(y:Site f)(t:ℕ) : integralLink y (List.replicate t (posDir i)) (harmonic f*ᵥ p)=(t:ℝ)*p i:=by
   induction t generalizing y with
   |zero=>simp [integralLink,linkSum]
   |succ t h=>
      rw [List.replicate_succ]; change (harmonic f*ᵥ p) (y,coord i)+integralLink _ _ _= _
      rw [h,coord_read,Nat.cast_succ]; ring
 simp_rw [StepData.repath,ht]; rw [← Finset.sum_mul,S.patch.weight_sum,one_mul] -- repath inspect
lemma trimmed (v:form 0 n) : let u :Puncture n → ℝ:= fun i=> v (i.val,vac) - v (0,vac); rootGrad n *ᵥ u=D n *ᵥ v:= by
 intro u
 unfold rootGrad
 rw [← Matrix.mulVec_mulVec]; funext ⟨x,b⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective b
 have hp(x:Site n) : (switch n *ᵥ u) (x,vac) = v (x,vac)-v (0,vac):=by
    by_cases h:x=0; subst x; simp only [switch_origin,sub_self]
    exact switch_punct u ⟨x,h⟩
 rw [coord_map, d_sites,d_sites,hp,hp]; abel
lemma roots_flow(D':Tab (Puncture c) Axis) (h:∀ u: Axis→ℝ, D' *ᵥ u=fun i=> (fixRoot S*ᵥ (harmonic f*ᵥ u)) (i.val,vac)-(fixRoot S*ᵥ (harmonic f*ᵥ u)) (0,vac)) : probe S * harmonic f=rootGrad c*D'+(S.patch.L.val:ℝ) • harmonic c:=by
 apply mulVec_injective; funext v; rw [←mulVec_mulVec, add_mulVec, ←mulVec_mulVec,h,trimmed, Matrix.smul_mulVec]
 unfold probe; rw [add_mulVec,←mulVec_mulVec]
 ext ⟨i,b⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective b; rw [coord_map]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,agrees_mean,coord_read]; rw [add_comm]
end fine
end YM.Fineness
#print axioms YM.Fineness.lattice_null
#print axioms YM.Fineness.roots_flow
