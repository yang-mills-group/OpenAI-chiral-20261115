import YM.SU5.Reconstruction.Crease.Keeper
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Club
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame Opera Moth
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H K D: Hilbert}(C:Clasp K H D)
local notation "U" => C.cLeft
local notation "Ξ"=>pond C
lemma clear (t:ℝ): U t * U (-t)=1:=by rw [C.groupLeft,add_neg_cancel]; exact (C.left_credentials t).1
lemma invert (t:ℝ)(A:H.Op): Ξ t (Ξ (-t) A)=A:=by
 unfold pond; calc
  _ = (U t* U (-t))*A*(U (-(-t))*U (-t)):= by simp only [mul_assoc]
  _ = _:= by rw [neg_neg,clear,mul_one,one_mul]
lemma pulsed (t:ℝ)(A B:H.Op): Ξ t (A*B)=Ξ t A*Ξ t B:=by
 unfold pond; rw [show U t*A*U (-t)*(U t*B*U (-t))= U t*A*(U (-t)*U t)*B*U (-t) from (by simp only [mul_assoc])]; rw [show U (-t)*U t=1 from (by simpa only [neg_neg] using clear C (-t)),mul_one]; simp only [mul_assoc]
variable {C} {M N:Net H}{Ω:H}{Γ:Set H.Op}{J:Flash H}(h:Club C J M Ω Γ)(q:∀ A∈M, J.shade A∈ N)
include h q
lemma warmth (A:H.Op)(p:A∈M.commutant)(x:ℝ): Ξ x A ∈ N:= by
 rw [← N.commutant_commutant]; refine VonNeumannAlgebra.mem_commutant_iff.mpr (fun B v=>?_)
 ext1 t; apply ext_inner_left ℂ; intro s
 let f(r:ℝ):= inner ℂ (B.adjoint s) (Ξ r A t); let g(r:ℝ):=inner ℂ s (Ξ r A (B t))
 change inner ℂ s (B _) = g _; rw [← adjoint_inner_left]; apply sub_eq_zero.mp 
 apply consumes (f:=fun r=> f r-g r) (Continuous.sub (pondPaddle C A (B.adjoint s) t) (pondPaddle C A s (B t))) (M:=‖ B.adjoint s‖*(‖A‖*‖t‖)+‖s‖*(‖A‖*‖B t‖)) ?_ ?_
 · intro d; exact (norm_sub_le ..).trans (add_le_add (pondCost C A d _ _) (pondCost C A d _ _))
 intro θ k; obtain ⟨e,a,w⟩:= h.cranes (spin θ) (grace θ) (grace_works θ k).1 (grace_works θ k).2 A p
 unfold f g; simp_rw [mul_sub]; rw [integral_sub (lake C θ k A _ _) (lake C θ k A _ _),brush θ k h p a w, brush θ k h p a w,adjoint_inner_left];
 have he:=DFunLike.congr_fun (VonNeumannAlgebra.mem_commutant_iff.mp v _ (q (star e) (star_mem a))) t; change J.shade (star e) (B t)=B ((J.shade (star e)) t) at he -- tune v: B∈N' yes he
 rw [he,sub_self]
variable (y:N≤ M.commutant)
include y
lemma equality : M.commutant=N:= by
 apply le_antisymm ?_ y; intro A p; have ht:= h.warmth q _ p 0; unfold pond at ht; rw [neg_zero,(C.left_credentials 0).1,one_mul,mul_one] at ht; exact ht
lemma proceeds (u:ℝ)(A:H.Op): Ξ u A ∈ N↔ A∈N:=by
 refine ⟨fun p=> ?_,fun p=> h.warmth q A (h.equality q y ▸ p) u⟩
 have he:Ξ (-u) (Ξ u A)=A:=by simpa only [neg_neg] using invert C (-u) A
 rw [←he]; exact h.warmth q _ (h.equality q y ▸ p) _
lemma answers (u:ℝ)(A:H.Op): Ξ u A∈ M↔ A∈ M:=by
 have hx:M=N.commutant:= by rw [← h.equality q y,M.commutant_commutant];
 have ht(u:ℝ)(A:H.Op)(p:A∈M):Ξ u A ∈ M:=by
   rw [hx] at p ⊢; refine VonNeumannAlgebra.mem_commutant_iff.mpr (fun B v=>?_)
   have he:= (VonNeumannAlgebra.mem_commutant_iff.mp p _ ((h.proceeds q y (-u) B).mpr v)); apply_fun (Ξ u) at he; rwa [pulsed,pulsed,invert] at he -- apply_fun needs?
 refine ⟨fun p=> ?_,ht u A⟩
 have he:=ht (-u) (Ξ u A) p; rwa [show Ξ (-u) (Ξ u A)=A from (by simpa using invert C (-u) A)] at he
end YM.BridgeClub.Club
