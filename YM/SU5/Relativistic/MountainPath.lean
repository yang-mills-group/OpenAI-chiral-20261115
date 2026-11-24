import YM.SU5.Relativistic.Passant
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Fock Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
attribute [local instance] screen_fin

lemma agree_seam(k:Behind)(i:Axis) : heatLine k (-π) i=heatLine k π i:=by
 let d:Cover:= tack 0 1
 have he : tack k π=tack k (-π)+stem d:=by ext j; induction j using Fin.lastCases <;> unfold d tack <;> simp only [Pi.add_apply,stem,Fin.lastCases_last,Fin.lastCases_castSucc,Int.cast_one,Pi.zero_apply,Int.cast_zero] <;> ring
 have hk(j:Cover): slat (tack k (-π)) (d+j) i= slat (tack k π) j i:=by unfold slat; rw [he,stem_a,add_assoc]
 unfold heatLine tough; rw [← Equiv.tsum_eq (Equiv.addLeft d)]; apply tsum_congr; intro j; exact hk j
lemma swell_seam(s c)(k:Behind): swell s c k (-π)=swell s c k π:=by
 unfold swell; refine Finset.sum_congr rfl fun i _=> ?_; rw [show surge (i:ℝ) π=surge i (-π) from ?_]; have hz:=wrap_surge i 1 (-π); rw [show -π+φ*(↑(1:ℤ):ℝ)=π from (by push_cast; ring)] at hz; exact hz

-- commit probe construction before any budgets at all s
variable {U:Set Behind}{a:ℝ}(hu:IsCompact U)(h:U⊆ sunshine)
include h hu
-- shove by n in pluse to shift v amplitude to positive time-K. use excited emission
lemma sponsorSignal(p:0<a)(T:ℤ)(W:Behind→ℂ)(v:Continuous W) : ∃ (s:Finset ℤ)(c: ℤ → Behind→ℂ),
 (∀ i∈s,T≤ i) ∧ (∀ i,ContinuousOn (c i) U) ∧
 (let V₁(k:Behind)(t:ℝ):=∑ i∈s,c i k * soundT i t
  (∀ k∈U, wrapT 0 (fun t=>V₁ k t*faceR k t)=W k) ∧
  ∀ i:Axis, TollS a U (fun k n=> pluse n (fun u=> V₁ k u*heatLine k u i))) ∧
 (∀ i k,W k=0→ c i k=0):=by
 obtain ⟨S,c,h₁,h₂⟩:=tariff a
 let h':= Cuest.mk h₁ h₂
 obtain ⟨n,v₀⟩:∃ n:ℕ,∀ j∈S,T≤(n:ℤ)-j ∧ 4≤ (n:ℤ)-j:=by
    refine ((eventually_all_finset (l:=atTop) S).2 ?_).exists; intro i j; obtain ⟨n,k⟩:=exists_nat_gt ((max T 4)+i); exact (eventually_ge_atTop n).mono (fun m t=>by omega)
 let fee(k):=wrapT (-(n:ℤ)) (etched S c k); have he(k:Behind)(u:k∈U):fee k≠0:=by
    have hp:=h' |>.pressing true (-(n:ℤ)) (k:=k) (fun i v=> by have he:=v₀ i v; simp only [sg,if_true,neg_mul,one_mul]; exact_mod_cast (by omega: (4:ℤ) ≤ -(-((n:ℕ):ℤ)+i))) (h u)
    change (↑(φ:ℝ):ℂ)⁻¹ * _ ≠_; refine mul_ne_zero (inv_ne_zero ?_) ?_
    · exact_mod_cast (show φ ≠0 from (by positivity))
    intro h; rw [h,Complex.zero_re,mul_zero] at hp; exact lt_irrefl _ hp
 let M(k: Behind):= W k/fee k
 have hM:ContinuousOn M U:= v.continuousOn.div (continuousOn_const.mul (circle_continuous _ _ (etch_c hu h h') hu)) he
 let d(i:ℤ)(k:Behind):= M k * (c k ((n:ℤ)-i):ℂ); let V₀(k:Behind)(t:ℝ):= swell S c k t
 let S':=S.image (fun i:ℤ=> (n:ℤ)-i); let V₁(k:Behind)(t:ℝ):=∑ i∈S',d i k *soundT i t
 have height(k:Behind)(t:ℝ): V₁ k t=M k*(soundT n t* V₀ k t):=by
    unfold V₁ d S' V₀ swell; rw [sum_image]; simp_rw [mul_sum]
    · apply sum_congr rfl; intro i _; rw [sub_sub_self]; unfold soundT; rw [Int.cast_sub,neg_sub,sub_eq_add_neg,surge_left]; ring
    intro i _ j _ k; exact sub_right_injective k
 refine ⟨S',d,fun i (t:i∈S')=> by obtain ⟨j,u,rfl⟩:=mem_image.mp t; exact (v₀ j u).1,fun i=> hM.mul (Complex.continuous_ofReal.comp ((h₁ _))|>.continuousOn), ⟨?_,?_⟩,fun i k p=>by unfold d M; rw [p,zero_div,zero_mul]⟩
 · intro k e; change wrapT 0 (fun t=> V₁ k t * faceR k t) = _
   simp_rw [height]; unfold wrapT; rw [show (fun t=> M k*(soundT n t*V₀ k t)*faceR k t)=(fun t=> M k*(surge (-(n:ℤ)) t*etched S c k t)) from ?_]; swap; · ext1 t; unfold soundT V₀ etched; push_cast; ring
   rw [pluse_const, ←Int.cast_neg, pluse_after,zero_add, mul_left_comm]; change M k*fee k=_; exact div_mul_cancel₀ _ (he k e)
 intro i
 change TollS _ _ (fun k j=> pluse j (fun t=>V₁ k t*heatLine k t i))
 have hk(k j): pluse j (fun t=>V₁ k t*heatLine k t i)= M k*pluse (j+-((n:ℕ):ℤ)) (outlined i S c k):=by
    rw [show (fun t=> V₁ k t*heatLine k t i)=(fun t=> M k*(surge (-(n:ℤ)) t*outlined i S c k t)) from ?_,pluse_const,←Int.cast_neg,pluse_after]; ext1 t; rw [height]; unfold outlined soundT V₀; push_cast; ring
 simp_rw [hk]; exact (((h'.collected hu h i).shifts p (-((n:ℕ):ℤ))).scaleU hu M hM) -- arguments tune

end YM.CF.Crest.Sleet
