import YM.CF.Buffered.Resonance
/-! Comparison to a FINITE polynomial, in site columns of L and its adjoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Glaze
open YM.CF.Onyx YM.CF.Emu
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia)
variable {v V j k:ℕ}{r C:ℝ}
section
variable {R:Type*}[Ring R]
def sculpt (A F : R) : ℕ → R | 0 => 0 | k+1 => (1-A)*F*A+sculpt A F k*(A-A*F*A)
end
variable {A: Peb}{t:ℝ}
private lemma nn : ‖Aop‖=1 := by
 have he:= norm_entry (A:=Aop) 0 0; have hp:Aop (0:SpinIdx) (0:SpinIdx)=1:=by rw [Adef,←raising,cutM,Matrix.diagonal_apply_eq,if_pos (by decide)]
 exact (IsStarProjection.norm_le _ A_id).antisymm (by simpa [hp] using he)
private lemma unitcap (h: IsStarProjection A) (p:0 ≤ t) (z:Aop*A*Aop=t • Aop) : t ≤ 1 := by
 have ht:‖A‖≤1:= h.norm_le _; have hh:= norm_mul_le (Aop*A) Aop
 rw [z,norm_smul, nn, Real.norm_of_nonneg p,mul_one,mul_one] at hh
 exact hh.trans ((norm_mul_le Aop A).trans (by rw [nn,one_mul]; exact ht))
private lemma prism (F: Peb) (k:ℕ) : sculpt Aop F k * Aop=sculpt Aop F k := by
 induction k with
 | zero => simp [sculpt]
 | succ k ih => rw [sculpt,add_mul,mul_assoc,AOne,mul_assoc _ (Aop-_),sub_mul Aop _ Aop,mul_assoc _ Aop,AOne]
lemma sculptor (A:Peb) (z:Aop*A*Aop=t • Aop) (k:ℕ) : sculpt Aop A (k+1)=(minA*A*Aop)+(1-t) • sculpt Aop A k := by
 rw [sculpt,z,show Aop-(t • Aop)=(1-t) • Aop from (by module),Matrix.mul_smul,prism]
private lemma sculpture (h:IsStarProjection A)(p:0≤t)(z:Aop*A*Aop=t • Aop) (k:ℕ) : ‖sculpt Aop A k‖ ≤ k := by
 induction k with
 | zero => simp [sculpt]
 | succ k ih=>
   let F:=minA*A
   have hl:‖minA*A*Aop‖ ≤ 1:= (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans ((mul_le_mul (minA_p.norm_le _) (h.norm_le _) (norm_nonneg _) zero_le_one).trans_eq (mul_one (1:ℝ)))) (norm_nonneg _)).trans (by rw [nn,mul_one]))
   rw [sculptor _ z]; apply (norm_add_le ..).trans
   rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr (unitcap h p z))]
   calc
     _ ≤ 1+1*(k:ℝ) := add_le_add hl (mul_le_mul (by linarith) ih (norm_nonneg _) zero_le_one)
     _ = _ := by push_cast; ring
private lemma chisel (p:0<t) (z:Aop*A*Aop=t • Aop) (k:ℕ) : let P := t⁻¹ • (minA*A*Aop)
 P-sculpt Aop A k=(1-t)^k • P := by
 intro P; induction k with
 | zero => simp [sculpt]
 | succ k ih=>
   rw [sculptor _ z, pow_succ', mul_smul, ← ih]; change P-((minA*A*Aop)+_)=_
   rw [show minA*A*Aop=t • P from (smul_inv_smul₀ p.ne' _).symm]; module
variable {N:Side}{d:Candle}{F:Slide N d}{M:Jill.Male}
def sculptU (F:Slide N d) (j:ℕ)(M:Jill.Male)(k:ℕ)(i:Stag N):Peb := sculpt Aop (field F j M i) k
private lemma h_crest(g:Even N.val) (F:Slide N d) (x:Slot)(i:Site N)(j:ℕ)(M:Jill.Male) : let A:=field F j M (Emu.rake F i x)
 IsStarProjection A ∧ Aop*A*Aop=disk j M (glen (F.u x) i) • Aop := by
   intro A; have he:=(crestQ j M F g (Emu.rake F i x)); exact ⟨he.1,by rw [← Emu.ramp]; exact he.2.2.1⟩
private lemma sculpture_e(g:Even N.val)(F:Slide N d)(A:Stag N→Peb)(x: Slot)(u:FormU (F.u x) j M r C (trackF F A x)) (p:0<r)(i:Site N)(z:r*pinch N^2<disk j M (glen (F.u x) i))(k:ℕ) :
 trackF F (A-sculptU F j M k) x i=(1-disk j M (glen (F.u x) i))^k • dip j M (tmap (glen (F.u x) i)) := by
 let B:=field F j M (Emu.rake F i x)
 let a:=glen (F.u x) i; let t:=disk j M a
 have ht:0<t:=lt_trans (mul_pos p (pow_pos (pinch_pos N) _)) z
 have he:=h_crest g F x i j M
 change trackF F A x i-sculpt Aop B k=_
 rw [u.far i z,dip,←pear, ice_h g i,← Complex.ofReal_inv,BZ.ofReal_action]
 change t⁻¹ • (minA*bar j M.val (tmap a)*Aop)-_= (1-t)^k • (t⁻¹ • (minA*bar j M.val (tmap a)*Aop)) -- real s vs ↑; not defeq
 rw [show bar j M.val (tmap a)=B from ?_]
 · exact chisel ht he.2 k
 unfold B field; rw [Emu.ramp]
lemma sculpture_bill (g:Even N.val)(F:Slide N d)(A:Stag N→Peb)(x: Slot)(u:FormU (F.u x) j M r C (trackF F A x)) (p:0<r)(k:ℕ)(ht:k*pinch N ≤ 1): CoverBill (F.u x) j M r (C+1) (trackF F (A-sculptU F j M k) x) := by
 constructor
 · intro i h; rw [sculpture_e g F A x u p i h,norm_smul]
   let t:=disk j M (glen (F.u x) i)
   have hC:0≤t:=norm_nonneg _
   have he:=h_crest g F x i j M
   rw [Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr (unitcap he.1 hC he.2)) _)]
   exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (sub_nonneg.mpr (unitcap he.1 hC he.2)) (by linarith only [show 0≤disk j M (glen (F.u x) i) from hC]))
 intro i h; let t:=disk j M (glen (F.u x) i); have he:=h_crest g F x i j M
 change ‖trackF F A x i-sculpt Aop _ k‖≤_
 refine (norm_sub_le ..).trans ((add_le_add (u.near i h) (sculpture he.1 (norm_nonneg _) he.2 k)).trans ?_)
 rw [add_div]; exact add_le_add_right ((le_div_iff₀ (pinch_pos N)).2 ht) _
-- high-z convergence
lemma shaping (H:1≤j)(p:0<r)(l:ℝ)(v:0<l)(e:ℝ) (q:0<e) : ∃ k:ℕ, ∃ a:ℝ,0<a ∧ ∀ {N:Side}, pinch N ≤ a → ∀ {d:Candle}(F:Slide N d)(M:Jill.Male) (A:Stag N→Peb)(x: Slot) {C:ℝ}, FormU (F.u x) j M r C (trackF F A x) → Even N.val →∀ i:Site N,l<‖glen (F.u x) i‖→ ‖trackF F (A-sculptU F j M k) x i‖≤e := by
 obtain ⟨w,b,V,W,S⟩:=Onyx.soul j H
 obtain ⟨y,c,U,Z,X⟩:=Onyx.stern H p
 obtain ⟨u,z,o,hz,Q⟩:= Jill.zip H
 let d:=min (1/2:ℝ) (u*l^2); have he:0<d:=lt_min (by norm_num) (by positivity)
 let G:=1-d; have ht:G<1:= by unfold G; linarith
 have hr:0 ≤ G:= sub_nonneg.mpr ((min_le_left ..).trans (by norm_num))
 obtain ⟨k,K⟩:= ((show Tendsto (fun x:ℕ=>G^x*(b/l)) atTop (𝓝 0) from by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr ht).mul_const (b/l)).eventually (gt_mem_nhds q)).exists
 refine ⟨k,l/y, by positivity,fun {N} i {c} F M A x {C} h g j' l'=>?_⟩
 let a:=glen (F.u x) j'; change l<‖a‖ at l'
 have hy: Bound Real.pi a:=orb j' (F.u x) g
 let t:=disk j M a
 have hf:d ≤ t:=(min_le_right ..).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ v.le l'.le _) o.le).trans (Q _ _ hy).1)
 have hp:= h_crest g F x j' j M; have hh:0≤1-t:=sub_nonneg.mpr (unitcap hp.1 (he.trans_le hf).le hp.2)
 rw [sculpture_e g F A x h p j' ((X N M (F.u x) j' g).1 ?_), norm_smul,Real.norm_of_nonneg (pow_nonneg hh _)]
 · change (1-t)^k*‖dip _ _ _‖≤_
   exact (mul_le_mul (pow_le_pow_left₀ hh (by dsimp [G]; linarith) _) (((S M _ hy 1 one_pos).2).trans (by gcongr)) (norm_nonneg _) (pow_nonneg hr k)).trans ((show G^k*(b/l)<e from K).le)
 change y*pinch N≤ ‖a‖; linarith [(le_div_iff₀ U).1 i]

lemma pick_depth (l:ℝ)(p:0<l) : ∃ v:ℕ,∀ {N:Side},v≤ N.val → pinch N ≤ l := by
 obtain ⟨w,W⟩:=exists_nat_gt (Real.pi/l)
 refine ⟨w,fun {N} h=>?_⟩; rw [pinch,div_le_iff₀ (nPos N),mul_comm]; exact (div_le_iff₀ p).1 (W.le.trans (by exact_mod_cast h))
lemma spare (H:1≤j)(p:0<r)(u:0<C)(e:ℝ)(q:0<e) : ∃ k v:ℕ, ∀ {N:Side}, v ≤ N.val → ∀ {d:Candle}(F:Slide N d) (M:Jill.Male) (A:Stag N→Peb), (∀ x:Slot,FormU (F.u x) j M r C (trackF F A x)) → Even N.val → let P:=sculpt (tickA N) (Dofu N (field F j M)) k
  ∀ i:Single N, ‖acts (Dofu N A-P) (basisKet i)‖≤ e ∧ ‖acts (star (Dofu N A-P)) (basisKet i)‖≤ e := by
 let d:=(e/2)^2; have he:0<d:=by unfold d; positivity
 obtain ⟨l,g,L⟩:=furring H p (show 0<C+1 by linarith) d he
 obtain ⟨k,a,f,Q⟩:=shaping H p l g (e/2) (by positivity)
 obtain ⟨w,z⟩:=pick_depth (min (min l a) (1/((k:ℝ)+1))) (lt_min (lt_min g f) (by positivity))
 refine ⟨k,w,fun {N} v {d'} F M A h t =>?_⟩
 intro P i
 let X:=A-sculptU F j M k; let x:=i.2; let V:ℝ:=N.val; have hV:0<V:=nPos _
 have hP: pinch N ≤ min l a∧pinch N ≤ 1/((k:ℝ)+1):=le_min_iff.mp (z v); obtain ⟨u',f'⟩:=le_min_iff.mp hP.1
 have hk:(∑ v:Site N,‖X (v,x)‖^2)/V^4≤ e^2 := by
   let T:= univ.filter fun v:Site N=> ‖glen (F.u x) v‖ ≤ l
   rw [Gall.rime X F,div_le_iff₀ (pow_pos hV _),← sum_add_sum_compl T]
   have ht := sculpture_bill t F A x (h x) p k (by nlinarith [(le_div_iff₀ (by positivity : 0< (k:ℝ)+1)).1 hP.2,pinch_pos N])
   refine le_trans (add_le_add (L (trackF F X x) (F.u x) t u' ht T (fun i hi=> (mem_filter.mp hi).2)) (sum_le_sum (g:=fun _=>d) (fun i hi=> ?_))) ?_
   · apply pow_le_pow_left₀ (norm_nonneg _)
     apply Q f' F M A x (h x) t
     simpa only [T,mem_compl,mem_filter, mem_univ,true_and,not_le] using hi
   rw [sum_const,nsmul_eq_mul]
   have hh : (Tᶜ.card:ℝ) ≤ V^4 := by unfold V; exact_mod_cast (card_le_univ Tᶜ).trans_eq (site_card N)
   refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hh he.le) _) ?_
   change d * V^4+V^4*d≤_; unfold d; nlinarith only [mul_nonneg (sq_nonneg e) (pow_nonneg hV.le 4)]
 have hp:Dofu N A-P=Dofu N X:=by
   suffices H: ∀ k:ℕ,sculpt (tickA N) (Dofu N (field F j M)) k=Dofu N (sculptU F j M k) by rw [show P =_ from H k]; unfold X; rw [map_sub]
   intro n; induction n with
   | zero => exact (map_zero (Dofu N)).symm
   | succ n ih => rw [sculpt, ih, landP]; let G:Stag N→Peb:= field F j M; let V:Stag N→Peb:=fun _=>Aop; rw [←map_one (Dofu N), ←map_sub, ←map_mul,←map_mul,←map_mul,←map_mul,←map_sub,←map_mul,←map_add]; rfl
 rw [hp]
 refine ⟨(sq_le_sq₀ (norm_nonneg _) q.le).1 ((Gall.wave X i).trans hk),(sq_le_sq₀ (norm_nonneg _) q.le).1 ?_⟩
 rw [←Dofu_s]; exact (Gall.wave (star X) i).trans (by simp_rw [Pi.star_apply,norm_star]; exact hk)
#print axioms spare
end YM.CF.Buffered.Glaze
