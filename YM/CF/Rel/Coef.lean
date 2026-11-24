import YM.CF.Rel.Taur
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Braid
def Ca(M:Space m→ℂ)(d:DialT n m):ℂ:= (frameX n m)⁻¹*∑ z,(cMul z d)⁻¹ * M (tollX z)
lemma litZ (F:Space m→ℂ)(A:DialT n m→ℂ)(h:∀ z: DialT n m, F (tollX z)=∑ d, cMul z d * A d)(x:DialT n m): Ca F x=A x:=by
 unfold Ca; apply mul_left_cancel₀ (frame_ne n m); rw [←mul_assoc (frameX n m),mul_inv_cancel₀ (frame_ne n m),one_mul]; simp_rw [h, mul_sum]; rw [sum_comm]
 simp_rw [←mul_assoc, ←sum_mul];
 rw [Fintype.sum_eq_single x]; swap
 · intro d hd; have hm: ∑ i,(cMul i x)⁻¹*cMul i d=0:=by simp_rw [mul_comm (_⁻¹) _]; rw [detU,if_neg hd]
   rw [hm,zero_mul]
 have he : ∑ i,(cMul i x)⁻¹*cMul i x=frameX n m:=by simp_rw [mul_comm (_⁻¹) _]; rw [detU,if_pos rfl]
 rw [he]
lemma supF {F:Space m→ℂ} (d:DialT n m)(h:∀ z: DialT n m, ‖F (tollX z)‖ ≤ A): ‖Ca F d‖≤ A:=by
 unfold Ca; rw [norm_mul,norm_inv]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr (norm_nonneg _))).trans
 simp_rw [norm_mul,norm_inv,cUnit,inv_one,one_mul]
 apply (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>A) (fun i _=>h i)) (inv_nonneg.mpr (norm_nonneg _))).trans_eq
 rw [sum_const, card_univ,nsmul_eq_mul, frameX,Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
def ketch (r:ℕ)(n:Side)(m:ℕ):=Fintype.piFinset fun _:Fin m=>pavilion r (0:Site n)
lemma ketch_p (d:DialT n m):d∈ketch r n m↔∀ i,separation 0 (d i)≤r:=by simp [ketch,theatre]
lemma ketch_b(r m:ℕ): (ketch r n m).card≤plot r^m:= by unfold ketch; simp; exact pow_le_pow_left₀ (Nat.zero_le _) (pay_v _) _
lemma coil_size {x:stencil m}(h:size x ≤ r): coil n x ∈ ketch r n m:=by
 apply (ketch_p ..).mpr; intro i
 let y:= fun k:Axis=> x (i,k); simp only [coil]; rw [←zero_add (wrap _ _)]; apply (Font.fstop (n:=n) ..).trans; apply le_trans _ h
 unfold Laurent.size; simp only [Fintype.sum_prod_type]; exact Finset.single_le_sum (f:=fun i=>∑ k,(x (i,k)).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
lemma left_b {F:Space m→ℂ}(hp:Pond r A F)(h:2*r<n.val):
 ∃ S : Finset (stencil m), ∃ v:stencil m →ℂ,(∀ i∈S,size i ≤ r)∧(∑ i∈S,‖v i‖) ≤ A ∧ (∀ z,F z=∑ i∈S, mode z i*v i) ∧ ∀ i: DialT n m,Ca F i=∑ j∈S,if coil n j=i then v j else 0:=by
 obtain ⟨S,v,hx,hv,H⟩:=hp.there
 refine ⟨S,v,hx,hv,H,fun i=> litZ F (fun i=> ∑ j∈S,if coil n j=i then v j else 0) (fun z=>?_) i⟩
 rw [H]; simp_rw [cord,mul_sum]; rw [sum_comm (s:=(univ:Finset (DialT n m)))]; exact sum_congr rfl fun j hj=> by simp [mul_ite]
lemma reports {F:Space m→ℂ}(hp:Pond r A F)(h:2*r < n.val):
 (∑ i:DialT n m,‖Ca F i‖) ≤ A ∧ (∀ i:DialT n m,i∉ketch r n m→ Ca F i=0) ∧ ∀ z:DialT n m,F (tollX z)=∑ i,cMul z i*Ca F i:=by
 obtain ⟨S,v,hx,hv,H,he⟩:= left_b hp h
 refine ⟨?_,fun i hi=>?_, fun z=> ?_⟩
 · simp_rw [he]; apply (sum_le_sum (fun i _=> norm_sum_le ..)).trans; rw [sum_comm]; simp_rw [apply_ite (‖·‖)]; simpa using hv -- tune
 · rw [he]; exact sum_eq_zero fun j hj=>if_neg (show coil n j ≠ i from fun hz=> hi (hz ▸ coil_size (hx j hj)))
 rw [H]; simp_rw [cord,he, mul_sum]; rw [sum_comm (s:= (univ:Finset (DialT n m)))]; simp [mul_ite]
lemma stocks {F:Space m→ℂ}(hp:Pond r C F)(h:2*r<n.val)(he:∀ z:DialT n m,‖F (tollX z)‖≤A)(ha:0 ≤ A): Pond r ( (plot r^m:ℕ)*A) F:=by
 obtain ⟨S,v,hx,hv,H,hY⟩:= left_b hp h
 have he'(i)(hi:i∈ S): v i=Ca F (coil n i):=by rw [hY,sum_eq_single i _ (by simp [hi]),if_pos rfl]; intro j hj hp; rw [if_neg fun hg=>hp (two_size (hx j hj) (hx i hi) hg h)]
 have hf:S.card ≤ plot r^m:= (card_le_card_of_injOn (coil n) (fun i hi=> coil_size (hx i hi)) (fun i hi j hj he=>two_size (hx i hi) (hx j hj) he h)).trans (ketch_b ..)
 exact ⟨S,v,hx,(sum_le_sum (g:=fun _=> A) (fun i hi=>by rw [he' i hi]; exact supF _ he)).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hf) ha),H⟩
end YM.CF.Rel
