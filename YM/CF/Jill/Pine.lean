import YM.CF.Jill.Kin
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {N:Side}{j:ℕ}{d r:ℝ}
structure RayH where
  M:Male
  x:Bin
  cap:Bound Real.pi x
  width:0<‖x‖
def crop:Tax RayH:=⟨fun i=>‖i.x‖,Real.pi,RayH.width,RayH.cap⟩
def disk(j:ℕ)(M:Male)(x:Bin):ℝ:=‖shell j M.val (tmap x)‖
lemma zip (h:1≤j):∃ c T:ℝ,0<c ∧ 0<T ∧ ∀ (M:Male)(x:Bin),Bound Real.pi x→c*‖x‖^2 ≤ disk j M x∧ disk j M x ≤ T*‖x‖^2:=by
 obtain ⟨c,H,R⟩:= court j h RayH.M RayH.x (t:=crop) (fun _=>rfl) RayH.cap
 let x:=RayH.x; have ht:=go_b (t:=crop) x (fun _=>rfl) RayH.cap; obtain ⟨a,T,ha,hT,P⟩:= ht.glass (fun i=>i.M.val) (fun i=>i.M.property) j h
 refine ⟨c,T,H,hT,fun M v g=>?_⟩; by_cases p:v=0
 · subst v; unfold disk; rw [show tmap (0:Bin)=0 from rfl]; simp
 let w:RayH:=⟨M,v,g,norm_pos_iff.mpr p⟩; have hx:‖(0:ℂ)‖<a:=by simpa
 have he:= (P w (0:ℂ) hx).2; rw [zpow_ofNat] at he; exact ⟨R w,he⟩
variable (N)(j)
def cup(M: Male)(r:ℝ)(x:Bin):ℝ:=max (r*pinch N^2) (disk j M x)
def cold(M:Male)(r:ℝ)(x:Bin):ℝ:= Real.log (cup N j M r x)-Real.log (r*pinch N^2)
variable {N j}
lemma cup_p(M:Male){r}(p:0<r)(x:Bin):0<cup N j M r x:=lt_of_lt_of_le (mul_pos p (pow_pos (pinch_pos _) _)) (le_max_left ..)
lemma local_frost (h:1≤j){r:ℝ}(p:0<r)(A:ℝ)(t:0<A):∃ T:ℝ,0<T∧∀ N:Side,∀ (M:Male)(x:Bin),Bound Real.pi x→‖x‖≤ A*pinch N →‖cold N j M r x‖ ≤ T:=by
 obtain ⟨u,v,hx,hv,H⟩:= zip h; let K:=max (1:ℝ) (v*A^2/r); have he:1≤K:=le_max_left ..; refine ⟨Real.log K+1,by linarith [Real.log_nonneg he],fun N M x g t'=>?_⟩
 let Q:=cup N j M r x; let V:=r*pinch N^2; have ht:V≤Q:=le_max_left ..; have hp:0<V:=by unfold V; have hh:=pinch_pos N; positivity
 have hk:Q≤K*V:=by apply max_le; exact le_mul_of_one_le_left hp.le he; calc
    _ ≤ _:= (H M x g).2
    _ ≤ v*(A*pinch N)^2:=by gcongr
    _ = (v*A^2/r)*V:=by unfold V; field_simp
    _ ≤ _:= mul_le_mul_of_nonneg_right (le_max_right ..) hp.le -- tune
 change ‖Real.log Q-Real.log V‖ ≤ _; rw [← Real.log_div (hp.trans_le ht|>.ne') hp.ne', Real.norm_of_nonneg (Real.log_nonneg ((one_le_div hp).mpr ht))]; exact (Real.log_le_log (div_pos (hp.trans_le ht) hp) ((div_le_iff₀ hp).mpr hk)).trans (by linarith)
lemma high_frost (h:1≤j)(p:0<r):∃ A:ℝ,0<A∧∀ N:Side,∀ (M:Male)(x:Bin),Bound Real.pi x→ A*pinch N ≤‖x‖→ cup N j M r x=disk j M x:=by
 obtain ⟨u,v,hx,hv,H⟩:=zip h; let W:=1+r/u; have hw:0<W:=by unfold W; positivity
 refine ⟨W,hw,fun N M x g t=>?_⟩; apply max_eq_right; have he:r ≤ u*W^2:=by
   have hi:u*W=u+r:=by unfold W; field_simp
   have hp:1≤W:=by unfold W; simp; positivity
   nlinarith [pow_le_pow_right₀ hp (by decide : (1:ℕ)≤2)]
 have hk:=(H M x g).1; refine le_trans (mul_le_mul_of_nonneg_right he (sq_nonneg _)) (le_trans ?_ hk); rw [mul_assoc,←mul_pow] -- tune order
 have _p:=pinch_pos N; gcongr
lemma shaft(u:ℂ)(a:Axis)(z:Bin)(i:Axis)(p:i≠a): (spark a u) i=0:=by simp [spark,step,p]
-- polynomial cost transfer unnormalized
lemma snap (t:RayH)(a:Axis)(x:ℝ)(u:ℝ):tmap (t.x)+spark a (raf crop t ((x:ℂ)*(u:ℂ)))=tmap (t.x+beam a (x*(‖t.x‖*u))):=by
 funext i; simp only [tmap,spark,beam,Lattice.step,raf,crop, Pi.add_apply,Pi.smul_apply,smul_eq_mul]; by_cases h:i=a <;>simp [h] <;> ring
end YM.CF.Jill
