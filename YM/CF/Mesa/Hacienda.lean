import YM.CF.Mesa.Stucco

/-! All-field local filling to a prescribed chord at cost only near marked sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B:Side} {K:ℝ}
lemma room_y {x:Per (Domain m B)} :∃ p,roomX m B p x∧roomX m B p (x+1):=by
  obtain ⟨a,z,hx,hz,h⟩:=local_coords x; rw [h]
  have hy (p) (w:ℤ) (t:w.natAbs≤B.val) (l:OddAxis m p):roomX m B p (high m B p+↑w):= by unfold roomX; rw [d_small _ w t,broadface,if_pos l]; exact t
  by_cases k:OddAxis m a
  · exact ⟨a,hy a z (by omega) k, by rw [show high m B a+↑z+1=high m B a+(↑(z+1):Per (Domain m B)) by push_cast; abel]; exact hy a _ (by omega) k⟩
  have e:=(oddAtAdd _).mpr k
  rw [show high m B a+↑z=high m B (a+1)+(↑(z-(B.val:ℤ)):Per (Domain m B)) by rw [high_inc]; push_cast; abel]
  refine ⟨a+1,hy _ _ (by omega) e,?_⟩; rw [show _ + ↑(z-_) + (1:Per (Domain m B))=high m B (a+1)+(↑(z-(B.val:ℤ)+1): Per (Domain m B)) by push_cast; abel]; exact hy _ _ (by omega) e
lemma spanning {x:Site (Domain m B)}{i j:Axis}(h:i≠j): ∃ a,x∈room m B a∧x+step i∈room m B a∧x+step j∈room m B a∧x+step i+step j∈room m B a:=by
  choose a l w using fun k:Axis=>room_y (x:=x k)
  refine ⟨a, (room_mem ..).mpr l, (room_mem ..).mpr (fun k=>?_), (room_mem ..).mpr (fun k=>?_), (room_mem ..).mpr (fun k=>?_)⟩
  · by_cases e:k=i
    · simpa [e] using w i
    simpa [e] using l k
  · by_cases e:k=j
    · simpa [e] using w j
    simpa [e] using l k
  by_cases e:k=i; subst k; simpa [h] using w i
  by_cases g:k=j; subst k; simpa [e] using w j
  simpa [e,g] using l k
lemma covering (K:ℝ)(X:Au m B→Au m B)(h:marked X K)(U)(x)(i:PlaqAxes):lambda (faceValue (X U) (x,i))≤ 4*(K/((B.val:ℝ)*Real.sqrt (SU.group.repDim:ℝ))) :=by
  rcases i with ⟨⟨i,j⟩,he⟩; let p:PlaqAxes:=⟨(i,j),he⟩; change i<j at he; let V:= X U
  let k:=Real.sqrt (SU.group.repDim:ℝ); have hk:0<k:=Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)
  obtain ⟨a,h₁,h₂,h₃,h₄⟩:=spanning (m:=m) (B:=B) (x:=x) he.ne; obtain ⟨u,T⟩:= (h.2 a).2.2 U
  let W:=gauge u V; let v:=K/((B.val:ℝ)*k)
  have ha (i) (t:Plug (B:=B) a i):lambda (W i) ≤ v:=by
    have hs:=T i t
    rw [GDist,←bolt _ _ (u (i.1+step i.2))⁻¹, mul_inv_cancel,dist_eq_norm] at hs
    unfold v lambda Gauge.chord; rw [← div_div]; exact div_le_div_of_nonneg_right hs hk.le
  rw [show lambda (faceValue (X U) (x,p))=lambda (faceValue W (x,p)) by unfold W; rw [face_gauge]; exact (SU.group.chord_conj ..).symm]
  have hz:x+step j+step i=x+step i+step j:=by abel
  have hr: faceValue W (x,p)= W (x,i)*W (x+step i,j)*(W (x+step j,i))⁻¹*(W (x,j))⁻¹:=by
    unfold faceValue; simp only [p,square, travel,Step.neg_read, Step.pos_read,Step.vec_neg,Step.vec_pos, inv_one, mul_one]
    rw [show x+step i+step j-step i=x+step j by abel,show x+step i+step j+ -step i-step j=x by abel]; group
  change lambda (faceValue W (x,p))≤ 4*v; rw [hr]; unfold lambda
  apply (SU.group.chord_triangle ..).trans; rw [SU.group.chord_inv]
  apply (add_le_add (le_trans (SU.group.chord_triangle ..) (add_le_add (le_trans (SU.group.chord_triangle ..) (add_le_add (ha _ ⟨h₁,h₂⟩) (ha _ ⟨h₂,h₄⟩))) (show SU.group.chord _≤ v from ?_))) (ha _ ⟨h₁,h₃⟩)).trans; ring_nf; norm_num
  rw [SU.group.chord_inv]; exact ha _ ⟨h₃,hz.symm ▸ h₄⟩

def Prequel (m B:Side)(d e:ℝ)(X:Au m B→Au m B):Prop:= Measurable X ∧ (∀ U:Au m B, ∀ i: Face (Per (Domain m B)), lambda (faceValue (X U) i) ≤ d) ∧ ∀ a:Index m,(∀ U: Au m B, weakPin a U e→Agrees (room m B a) (X U) U)∧∀ U V:Au m B,Agrees (room m B a) U V → Agrees (room m B a) (X U) (X V)
theorem trench {d:ℝ} (h:0<d):∃ N:ℕ, ∀ B:Side,N≤B.val→∃ e:ℝ,0<e∧∀ (m:Side),2≤m.val→∃ X:Au m B→Au m B,Prequel m B d e X:=by
  obtain ⟨N,K,l,H⟩:=yieldX; let k:=Real.sqrt (SU.group.repDim:ℝ); have hk:0<k:=Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)
  obtain ⟨n,hn⟩:= exists_nat_gt (4*K/(k*d)); refine ⟨max N n,fun B sx=>?_⟩
  obtain ⟨e,p,u⟩:= booth B; have hy: (4*K/ (k*d))<(B.val:ℝ):=lt_of_lt_of_le hn (by exact_mod_cast (le_max_right ..|>.trans sx : n ≤ B.val))
  rw [div_lt_iff₀ (mul_pos hk h)] at hy
  refine ⟨e,p,fun m hm=>?_⟩; obtain ⟨X,t⟩:=H m B ((le_max_left ..).trans sx) hm
  refine ⟨X,t.1,?_,fun a=>⟨fun U e=>(t.2 a).2.1 U (u m a hm U e), (t.2 a).1⟩⟩
  rintro U ⟨x,i⟩; refine (covering K X t U x i).trans ?_
  rw [← mul_div_assoc]; apply (div_le_iff₀ (mul_pos (by positivity) hk)).mpr; change _≤d*(B.val*k); nlinarith only [hy]
end YM.CF.Mesa
