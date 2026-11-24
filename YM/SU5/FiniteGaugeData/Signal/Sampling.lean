import YM.SU5.FiniteGaugeData.Signal.Compression
/-! # Stencil lanterns. Truncate only the lower approximation within fixed native stencils.
Carry exact evaluation even for Finite approximants. Uniform cost despite support size. -/
set_option autoImplicit false
set_option maxHeartbeats 430000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Sparkle
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea Supplies
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]{N:Side}{a b c u v s:ℝ}{d j k:ℕ}
open Condense Retain OrbitPort LocalPlane Branch Tenant
namespace Circuit
section algebra
local notation "R~" j:max=> acts (cutM j)
def register (T:Finset I) : Submodule ℂ (Ket I) where
 carrier:={x | acts (cutM T) x=x}
 add_mem':=fun x y=> by rw [Set.mem_setOf_eq] at *; rw [map_add,x,y]
 smul_mem':=fun k _ h=> by rw [Set.mem_setOf_eq] at *; rw [map_smul,h]
 zero_mem':= map_zero _
-- solve on restriction with one reusable bound. use comp lower, output point all read.
lemma solveMark (W:Finset I)(P:Op I)(e:0<b)(h:∀ x: Ket I, acts (cutM W) x=x→ b*‖x‖^2 ≤ (inner ℂ x (acts P x)).re)(z:Ket I)(t:acts (cutM W) z=z):
    ∃ y:Ket I,acts (cutM W) y=y ∧ acts (cutM W) (acts P y)=z ∧ b*‖y‖≤‖z‖:=by
 let K:=register W
 let L:K→ₗ[ℂ]K:= (((acts (cutM W)).toLinearMap.comp (acts P).toLinearMap).domRestrict K).codRestrict K (fun x=>bore (cutM_idp W) _)
 have hc (x:K): b*‖x.val‖ ≤ ‖(L x).val‖:= by
    let y:=x.val; have he : acts (cutM W) y=y:=x.property; have hz:= h _ he; let u:=‖y‖; have ht: (inner ℂ y (acts P y)).re ≤ u*‖(L x).val‖:=by
       rw [show inner ℂ y (acts P y)=inner ℂ y (L x).val from ?_]; exact (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans (norm_inner_le_norm ..)
       change _=inner ℂ y (acts (cutM W) _); rw [←act_inner (cutM W),(cutM_idp _).isSelfAdjoint,he]; rfl
    have hb:= hz.trans ht; by_cases e:u=0; · change b*u≤_; rw [e,mul_zero]; exact norm_nonneg _
    apply le_of_mul_le_mul_left _ (show 0<u from lt_of_le_of_ne (norm_nonneg _) (Ne.symm e)); change _ ≤ _; exact hb.trans' (le_of_eq (by unfold u y; ring)) -- left/right name swapped?
 have ht:Injective L:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun i v=>by
    have h:= hc i; rw [v] at h; change b*_ ≤ ‖(0:Ket I)‖ at h; have hx:‖i.val‖≤0:= le_of_mul_le_mul_left (by rw [mul_zero]; exact h.trans_eq norm_zero) e; exact Subtype.ext (norm_le_zero_iff.mp hx))) -- le_mul...
 obtain ⟨j,hj⟩:= (LinearMap.injective_iff_surjective.mp ht) (⟨z,t⟩:K); have he:= hc j; rw [hj] at he; exact ⟨j.val,j.property,congrArg Subtype.val hj,he⟩
end algebra
section free
variable (S:Finset (Site N))(l:Slot)
def colorsOne (S:Finset (Site N))(l:Slot) := (univ:Finset (Single N)).filter fun i=> i.2=l∧i.1.1∈S
local notation "W"=> colorsOne S l
abbrev distinct (S:Finset (Site N))(k:ℕ): Prop:= (S:Set (Site N)).Pairwise fun x y=> k < separation (node x) (node y)
lemma embargo_slot (x:Ket (Single N))(M:Jill.Male)(t:Pad j N)(p: acts (cutM (colorsOne (N:=N) univ l)) x=x): acts (cutM (colorsOne (N:=N) univ l)) (acts (funde j M N 1) x)=acts (funde j M N 1) x:=by
 apply sectorwiseCut _ p; rw [nightly M t]; intro i v j p; simp [colorsOne] at v p; exact colorOne _ j i (Ne.symm ((v ▸ Ne.symm p))) -- type check
local notation "Λ"=>forum N s
lemma flex {x:Ket (Single N)}{P B:Op (Single N)}
    (p : distinct S k)(f:FiniteOp (forum N s) k B) (h:IsStarProjection P)(t:‖P-B‖ ≤ b)
    (v0:∀ (x:Ket SpinIdx),∀ a∈S, u *‖x‖^2≤ ‖acts P (capsule a l x)‖^2)(e:acts (cutM W) x=x):
    (u-2*b)*‖x‖^2 ≤ (inner ℂ x (acts P x)).re:=by
 let Y(i:Site N):= colorsOne {i} l; have he(i:Site N)(j:Single N): j∈ Y i ↔ j.1.1=i∧j.2=l:=by simp [colorsOne,Y]; tauto
 have H: S.biUnion Y=W:=by ext; simp [Y, colorsOne]; aesop
 apply Condense.packed (S:=S) («W»:=Y) (fun i _ j _ v=>Finset.disjoint_left.mpr (fun x a b=>v (((he i x).1 a).1.symm.trans ((he j x).1 b).1))) (fun i a j b t=>?_ ) (fun i a y v=>?_) (H.symm ▸ e) t
 · ext x y; rw [cutM,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases u:x∈ Y i <;> by_cases v:y∈Y j <;> simp [u,v]; apply f; change k<separation (node x.1.1) (node y.1.1); rw [((he i x).1 u).1, ((he j y).1 v).1]; exact p a b t
 have hh : y=capsule i l (LocalPlane.hall y l i):=by
    apply PiLp.ext; rintro ⟨⟨x,y'⟩,l'⟩; rw [capsuleAt]; by_cases w:x=i <;> by_cases z:l'=l <;> simp [LocalPlane.hall, w,z] <;> apply closedCut_iff.mp v <;> simp [colorsOne,Y,w,z]
 rw [loop_p h,Complex.ofReal_re]; rw [hh,budgetV]; exact v0 _ _ a

-- required geometry can be checked at any single ample prices. Produce obtains these before h, even projection aperture d known. t prevents layout if insufficient stencil.
def Screen (j:ℕ)(s C:ℝ)(l:Slot)(N:Side)(S:Finset (Site N)):Prop:=∀ (M:Jill.Male)(x:Ket (Single N)), acts (cutM (colorsOne (N:=N) S l)) x=x → C*‖x‖^2≤ (inner ℂ x (acts (funde j M N 1) x)).re
theorem screening {w F:ℝ}(j:ℕ)(p:1≤j)(e:0<s)(q:Produce j u v w F s):∃ C:ℝ,∃ k:ℕ,0<C∧ ∀ᶠ n:Side in atTop,Even n.val→ Pad j n∧∀ S:Finset (Site n),distinct S k→∀ l:Slot, Screen j s C l n S:=by
 obtain ⟨a,b,d,t,f,H,_⟩:=q.outset; obtain ⟨C,g,hC⟩:= countScale j p; obtain ⟨k,W0⟩:= sunray a b t f (C/4) (by positivity); refine ⟨C/2,k,by positivity,?_⟩
 filter_upwards [hC,eventually_ge_atTop (⟨d+1,by omega⟩:Side)] with N h₁ h₂ he; change d+1 ≤ N.val at h₂; obtain ⟨hv,u⟩:=h₁ he; refine ⟨hv,fun S d l M x t0=>?_⟩; obtain ⟨G,p,r,z⟩:= supply (Drapes.Crown.lib (H N (by omega) M)) t _ (by positivity) k W0
 let y:Openc (More N) s := ⟨1,vacancy0 _ e⟩; convert flex S l (s:=s) d (p y) (compass M j hv) (r y) (fun i k _=>u M i k l) t0 using 1; congr 2 <;> try linarith
end free
end Circuit
end YM.CF.Signal.Sparkle
#print axioms YM.CF.Signal.Sparkle.Circuit.screening
