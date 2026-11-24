import YM.CF.Jill.Lake
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {N:Side}
def stem(z:Cover):Bin:=fun i=>2*Real.pi*z i
def peers(x y:Bin):Prop:= ∃ z:Cover, y=x+stem z
lemma stem_0:stem 0=0:=by ext; simp [stem]
lemma stem_a(x y:Cover):stem (x+y)=stem x+stem y:=by ext; simp [stem,mul_add]
lemma peers.roll (x:Bin):peers x x:=⟨0,by rw [stem_0,add_zero]⟩
lemma peers.flip {x y:Bin} (h:peers x y):peers y x:=by obtain ⟨z,rfl⟩:=h; exact ⟨-z,by rw [add_assoc, ← stem_a,add_neg_cancel,stem_0,add_zero]⟩
lemma peers.over {x y z:Bin} (h:peers x y)(p:peers y z):peers x z:=by obtain ⟨u,rfl⟩:=h; obtain ⟨v,rfl⟩:=p; exact ⟨u+v,by rw [stem_a,add_assoc]⟩
lemma peers.both {x y:Bin}(h:peers x y)(u:Bin):peers (x+u) (y+u):=by obtain ⟨w,g⟩:=h; exact ⟨w,g ▸ add_right_comm ..⟩
lemma map_stem(x:Bin)(y:Cover): tmap (x+stem y)=tmap x + reciprocal y:=by funext i; simp [stem,tmap,reciprocal]
lemma peers.map_shell {x y:Bin} (h:peers x y)(p:tmap x∈realCube zone)(q:tmap y∈realCube zone)(M:Side)(j:ℕ):shell j M (tmap y)=shell j M (tmap x):=by obtain ⟨z,rfl⟩:=h; rw [map_stem] at q ⊢; exact shell_overlap _ _ _ p z q
lemma peaks {x y:Bin} (p:Bound Real.pi x)(h:peers x y):‖x‖≤‖y‖:=by
 obtain ⟨v,rfl⟩:=h; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; refine le_trans ?_ (norm_le_pi_norm (x+stem v) i); change |x i|≤|x i+2*Real.pi*(v i)|; rcases lt_trichotomy (v i) 0 with h|h|h
 · have he: (v i:ℝ)≤-1:=by exact_mod_cast show v i ≤ -1 by omega
   have hx:2*Real.pi*(v i)≤2*Real.pi*(-1:ℝ):=by gcongr
   have hh:|x i|≤Real.pi:=(b_abs x i).trans p; rw [abs_of_nonpos (by linarith [abs_le.mp hh,Real.pi_pos] : x i+2*Real.pi*(v i)≤0)]; apply abs_le.mpr; constructor <;> linarith [abs_le.mp hh,Real.pi_pos]
 · simp [h]
 have he:1 ≤ (v i:ℝ):=by exact_mod_cast show 1 ≤ v i by omega
 have hx:2*Real.pi*1≤2*Real.pi*(v i):=by gcongr
 have hh:|x i|≤Real.pi:=(b_abs x i).trans p; rw [abs_of_nonneg (by linarith [abs_le.mp hh,Real.pi_pos] : 0≤x i+2*Real.pi*(v i))]; apply abs_le.mpr; constructor <;> linarith [abs_le.mp hh,Real.pi_pos]
-- shifting by integer mesh
lemma chert_cast(u:Per N):(chert u:Per N)=u:=by unfold chert; split <;> simp [-Nat.cast_ofNat] -- tune
lemma tap_c(k:Site N)(z:Cover): peers (pm k+fun i=> (2*pinch N)*(z i)) (pm (k+wrap N z)):=by
 let K:=k+wrap N z
 have he(i:Axis) : (↑(chert (K i)):Per N)= ((chert (k i)+ z i:ℤ):Per N):=by rw [chert_cast]; simp only [Int.cast_add,chert_cast]; rfl
 have hc(i) : (N.val:ℤ) ∣ chert (K i)-(chert (k i)+z i):=by apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp; rw [Int.cast_sub,he i,sub_self]
 choose a ha using hc; refine ⟨a,?_⟩; funext i; change principal (K i)=principal (k i)+_+_
 rw [ch_price,ch_price (k i)]; change ((2 * (chert _:ℝ)+1)*pinch N)=_+2*Real.pi*(a i); rw [payH (N:=N),show chert (K i) = _ from eq_add_of_sub_eq (ha i)]; push_cast; ring
abbrev beam(a:Axis)(x:ℝ):Bin:= x • (step a)
lemma beam_cost(a:Axis)(x:ℝ): ‖beam a x‖ ≤ |x| :=(pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i=> by by_cases h:i=a <;> simp [beam,step,h]
lemma sprout(a:Axis)(x:Bin) (k:Site N) (w:ℕ):peers (pm k+x+beam a ((w:ℝ)*(2*pinch N))) (pm (k+wrap N (w • step a))+x):=by
 have ht:= (tap_c k (w • step a)).both x; rw [add_right_comm]; convert ht using 3; funext i; by_cases h:i=a <;> simp [h,beam,step,mul_comm]
-- reduced shift $p \in(-π,π]/n$
abbrev Offset(N:Side):= {u:Bin//Bound (pinch N) u}
lemma orb(k:Site N)(z:Offset N)(h: Even N.val): Bound Real.pi (pm k+z.val):=by
 apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr; intro i; change |principal (k i)+z.val i|≤Real.pi; obtain ⟨u,v⟩:=shelf (k i) h; have hx:= abs_le.mp ((b_abs z.val i).trans z.property); rw [abs_le]; constructor <;> linarith
lemma fragment(y:ℝ)(h:0<y)(x:ℝ):∃ z:ℤ,|x-(2*y)*z|≤y:=by
 let z:ℤ:=⌊(x+y)/(2*y)⌋; refine ⟨z,?_⟩; have he:0<2*y:=by positivity
 have hh:= (_root_.le_div_iff₀ he).mp (show (z:ℝ)≤_ from Int.floor_le _)
 have hx:=(_root_.div_lt_iff₀ he).mp (show _<_ from Int.lt_floor_add_one ((x+y)/(2*y))); change x+y < ((z:ℝ)+1)*_ at hx
 apply abs_le.mpr; constructor <;> linarith
lemma moved(N:Side)(x:Bin):∃ z:Offset N,∃ k:Cover,x=z.val+(fun i=> 2*pinch N*k i):=by
 choose k hk using (fun i=>fragment _ (pinch_pos N) (x i)); let v:Bin:=fun i=> 2*pinch N*k i; exact ⟨⟨x-v,(pi_norm_le_iff_of_nonneg (pinch_pos _).le).mpr fun i=>hk i⟩,k,(sub_add_cancel x v).symm⟩
end YM.CF.Jill
