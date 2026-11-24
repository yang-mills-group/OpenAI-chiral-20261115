import YM.CF.Aroma.Hill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N M:Side}{J:InJ n N}
lemma pose_cut (H:∀ᶠ x in 𝓝 0,flatV n N*J x=J x):∀ᶠ x in 𝓝 0,flatV n N*Met J x=Met J x-(1-flatV n N):=by
 filter_upwards [H] with x hx; unfold Met; rw [mul_add,←mul_assoc,hx,mul_sub,mul_one,flatA.1, sub_self,add_zero,add_sub_cancel_right]
lemma vis_a (J:InJ n N)(x):star (Met J x)=Met J x:=by unfold Met; simp only [star_add,star_mul,star_star,star_sub,star_one,flatA.2]
lemma legM (h:ContDiffAt ℝ ω J 0)(x): JD (Met J) x= JD J x*star (J 0)+J 0*star (JD J x):=by
 let f:=Met J; let P:= JD (Met J); have hx:HasFDerivAt J (JD J) 0:= (h.differentiableAt (by simp)).hasFDerivAt
 let L:Cab n N→L[ℝ] Cab n N:= (starL ℝ).toContinuousLinearMap
 let G(s:ℝ):= s • x
 have ht:G 0=0:=zero_smul ..
 have he:HasDerivAt G x 0:= by simpa using ((hasDerivAt_id' (0:ℝ)).smul_const x)
 have hg:HasDerivAt (J ∘ G) (JD J x) 0:= (show HasFDerivAt J (JD J) (G 0) by rw [ht]; exact hx).comp_hasDerivAt 0 he
 have hh:= (((met_ray _ h).differentiableAt (by simp)).hasFDerivAt:HasFDerivAt f P 0); have hw: HasFDerivAt f P (G 0):=by rwa [ht]
 have hb:= (hw.comp_hasDerivAt 0 he).unique ((hg.mul (L.hasFDerivAt.comp_hasDerivAt 0 hg)).add_const (1-flatV n N))
 change _= JD J x *star (J (G 0))+J (G 0)*star (JD J x) at hb; rw [ht] at hb; exact hb

lemma aside {q:Momentum} (F:Tide N q) : zinnia (-q)= -(zinnia q:Air N) ∧ amber (-q)=(amber q:Air N):=by
 constructor <;> ext x <;> simp [amber,zinnia,dialH,mode_negate _ F.phys]
namespace Foot
variable {T:Op n}{j:ℕ}(P:Foot T j M J)
include P
lemma shadeM(x): flatV n N * JD (Met J) x= JD (Met J) x ∧ star (JD (Met J) x)= JD (Met J) x:=by
 let L: Cab n N→L[ℝ] Cab n N:= (starL ℝ).toContinuousLinearMap
 let D:= JD J; let F:=flatV n N; let p:=Met J; have H:HasFDerivAt J D 0:= (P.smooth.differentiableAt (by simp)).hasFDerivAt
 let Q: Cab n N→L[ℝ] Cab n N:= ContinuousLinearMap.mul ℝ (Cab n N) F
 have hv : F*D x=D x:= DFunLike.congr_fun ((Q.hasFDerivAt.comp 0 H).unique (H.congr_of_eventuallyEq (show Q ∘ J=ᶠ[𝓝 0] J from P.heft))) x
 have hh : F*J 0=J 0:= (show (fun x=> F*J x)=ᶠ[𝓝 0] J from P.heft).eq_of_nhds
 rw [legM P.smooth]; change F*(_+_)=_∧ _ ; rw [mul_add,←mul_assoc,←mul_assoc,show F*JD J x=_ from hv,hh]; constructor; rfl; simp [add_comm]
lemma star_cost(q:Momentum)(F:Tide N q): star (firstH (Met J) (-q))= firstH (Met J) q:=by
 unfold firstH; rw [(aside F).1,(aside F).2,map_neg, smul_neg,star_add,star_neg,star_smul,show star Complex.I= -Complex.I from Complex.conj_I,(P.shadeM _).2,(P.shadeM _).2, neg_smul, neg_neg]
lemma railH {η C:ℝ}(U:Tween T j M N η C)(q: Momentum)(H:Tide N q)(p:∀ i:Site N,spoon (mel i) q∈realCube zone)(e:U.stem=oak J) : firstH (Met J) q=hub H.σ fun i=> U.rail (mel i) q:=by
 let f:= H.σ; let X:=J 0; let D:=JD J; let Z:=fun k : Site N=> fuel n j M (mel k); let G:=firstH J q; let K:= firstH J (-q)
 have hk:firstH (Met J) q=G*star X+X*star K:=by
    unfold firstH G K; rw [legM P.smooth,legM P.smooth]; simp only [firstH,(aside H).1,(aside H).2,map_neg,star_add,star_neg,smul_neg,star_smul, show star Complex.I= -Complex.I from Complex.conj_I, neg_smul, neg_neg]; simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul]; unfold X; module
 let V (k:Site N):=oak J (q,mel k); let W (k:Site N):= oak J (-q,mel k)
 rw [hk,show G=hub f V from oak_bind J P.smooth P.curve _ H, show K=hub f.symm W from oak_bind J P.smooth P.curve _ (opp H),show X=subHub Z from P.around,subhub_star,lung,hub_star]; change _+subHub Z*hub f _=_; rw [heart,hubsum]; congr 1; ext1 i; obtain ⟨w,hw⟩:=H.cost i; simp only [Pi.add_apply,Tween.rail,e,show star q=q from H.phys, show star (mel i)=mel i from (mel_h i).1] -- tune
 rw [show Z (f i)= _ from (slid_f (n:=n) _ H i (p i) j M).1, hw,oak_per]; rfl
lemma paidU {η C:ℝ}(U:Tween T j M N η C)(q: Momentum)(H:Tide N q)(e:U.halo=float (Met J)): secondH (Met J) q=subHub fun i=>U.halo (q,mel i):=by simp_rw [e]; exact float_bind (Met J) (met_ray _ P.smooth) (met_curve _ P.curve) q H
lemma weights:Aroma.Met J 0=subHub (fun i=> shell j M (mel i) • bins n) +(1-flatV n N):=by
 unfold Met; rw [P.around,subhub_star]; congr 1; rw [show subHub (N:=N) _ * subHub (N:=N) (fun _=> star _) =_ from lung (Equiv.refl _) _ _]; congr 1; exact funext fun i=> fuel_p _ _ _ P.oddM _ (base_subset_realCube zone_pos (mel_h i))
lemma census : IsUnit (Met J 0) ∧ (Met J 0)⁻¹ =subHub (fun i=> edgeH n j M (mel i))+(1-flatV n N):=by
 let A:=flatV n N; let X:=subHub (fun i=>shell j M (mel (N:=N) i) • bins n); let Y:=subHub (fun i=> edgeH n j M (mel (N:=N) i)); let F:= subHub (fun _:Site N=> bins n); have he:A=F:=bin_hub.symm
 have hp(k:Site N):shell j M (mel k) ≠0:=div_ne_zero (fun h=> (noGhost (p:=mel k) (N:=M) (base_subset_realCube zone_pos (mel_h k)) (mel_away k)).ne' (congr_arg Complex.re h)) (mass_ne j _ P.oddM (base_subset_realCube zone_pos (mel_h k))) -- tune
 have hG (U V:Site N→Op (coneA n)): subHub U*subHub V=subHub (fun i=> U i*V i) := lung (Equiv.refl _) U V
 have h: (X+(1-A))*(Y+(1-A))=1:=by
   have ht:X*Y=A:=by unfold X Y; rw [hG]; simp_rw [edgeH,Matrix.mul_smul,Matrix.smul_mul,binsSq, inv_smul_smul₀ (hp _),he]; rfl
   have hu: X*A=X:=by unfold X; rw [he,hG]; simp_rw [Matrix.smul_mul,binsSq]
   have hv:A*Y=Y:=by unfold Y; rw [he,hG]; simp_rw [edgeH,Matrix.mul_smul,binsSq]
   rw [add_mul,mul_add,mul_add,ht,mul_sub,sub_mul (1:Cab n N) A Y,hu,hv,mul_one,one_mul,sub_self,sub_self,mul_sub,mul_one,sub_mul 1 A A,one_mul,show A*A=A from flatA.1]; abel
 rw [P.weights]; refine ⟨Fock.live_of h,?_⟩; let J:=X+(1-A); let K:=Y+(1-A); change J⁻¹=K; rw [← one_mul K, ← (Fock.live (Fock.live_of h)).2,mul_assoc, h, mul_one] -- tune
end Foot
end YM.CF.Aroma
