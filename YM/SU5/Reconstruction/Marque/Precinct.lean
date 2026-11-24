import YM.SU5.Reconstruction.Marque.Lot
import YM.SU5.Reconstruction.Crease.Dance
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric Real BridgeClub Picket Anvil
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical
local notation "Ω"=>Wedge
variable (a b r:Axis)(p:b≠a)
local notation "ℵ"=> Picket.move a b
local notation "F"=> BridgeClub.turn a r
include p
lemma turnsBack(u:ℝ)(x:E4):(ℵ (-u)) (ℵ u x)=x:= by rw [show Picket.move a b (-u) (ℵ u x)=x from ?_]; simpa only [neg_neg] using outdance p (-u) x
noncomputable def stroll(t:ℝ): E4≃ₜ E4 where
 toFun:=Picket.move a b t
 invFun:=Picket.move a b (-t)
 left_inv:=fun x=>turnsBack a b p t x
 right_inv:=outdance p t
 continuous_toFun:=smooth_move ..
 continuous_invFun:=smooth_move ..
local notation "M"=> stroll a b p
@[simp] lemma stroll_at (t:ℝ)(x:E4):M t x=ℵ t x:=rfl
@[simp] lemma stroll_neg(t:ℝ): M (-t)=(M t).symm:=by ext1; rfl
@[simp] lemma stroll_zero(x:E4):M 0 x=x:= by simp [Picket.move,stroll_at, Picket.lee]
lemma stroll_add(t u:ℝ)(x:E4): M (t+u) x=M t (M u x):= by
 ext1 i; simp_rw [stroll_at]; rcases eq_or_ne i a with h|h
 · rw[h,eye_high p,eye_high p,eye_low p,eye_high p];rw [Real.cosh_add,Real.sinh_add]; ring
 by_cases v:i=b
 · rw [v,eye_low p,eye_low p,eye_high p,eye_low p, Real.cosh_add,Real.sinh_add]; ring
 simp only [others _ _ i h v]
lemma stroll_time :Continuous (fun x:ℝ × E4=> (M x.1) x.2):= by simp_rw[stroll_at]; unfold Picket.move Picket.rise Picket.lee Picket.rise; fun_prop -- Lee continuity
lemma strolling (s:ℝ)(x y:E4): M s (x+y)= M s x + M s y:= dances p s x y
lemma reverseDance(t:ℝ)(x:E4)(u:r≠a)(v:r≠b): (F) (M t x)= M (-t) ((F) x) := by
 ext1 i; rcases eq_or_ne i a with w|w;·rw [w,stroll_at,stroll_at,turn_at, eye_high p,eye_high p]; simp [turn_at,p,v.symm]; ring
 by_cases h:i=b; rw [h,stroll_at,stroll_at,turn_at,eye_low p,eye_low p]; simp[turn_at,p,v.symm]; -- maybe ring
 simp only [turn_at,stroll_at,others _ _ i w h]
omit p in
lemma flip_cont : Continuous (BridgeClub.turn a r):= by unfold BridgeClub.turn; exact (PiLp.continuous_toLp _ _).comp (continuous_pi fun (i:Axis)=> (by by_cases w:i=a∨i=r <;> (simp only [w, ↓reduceIte, dite_eq_ite]; fun_prop))) -- tune
omit p in
noncomputable def backward : E4≃ₜ E4:={
 toFun:=F,invFun:=F,left_inv:=BridgeClub.turn_turn a r,right_inv:=BridgeClub.turn_turn a r, continuous_toFun:=flip_cont .., continuous_invFun:=flip_cont .. }
variable {x: Set E4}
-- neighbourhood utilities
abbrev strace(q:E4)(V:Set E4):Set E4:=(fun x=> x+q) '' V
omit p
@[simp] lemma strace_zero (x:Set E4):strace 0 x=x:=by simp[strace]
lemma strace_add (q s:E4)(V:Set E4): strace q (strace s V)=strace (q+s) V:=by simp_rw [strace,image_image,add_assoc, show s+q=q+s from add_comm ..]
lemma trace_bound (V:Set E4)(p: Bornology.IsBounded V)(q:E4) : Bornology.IsBounded (strace q V):= (p.add (Bornology.isBounded_singleton (x:=q))).subset (by rintro _ ⟨x,h,rfl⟩; exact ⟨x,h,q,rfl,rfl⟩) -- defeq singleton sum? tune
-- push far wedge
include p
lemma enter {V:Set E4}(t:Bornology.IsBounded V) : ∃ q:E4,V⊆ strace q (Wedge a b):=by
 obtain ⟨R,k⟩:= (Metric.isBounded_iff_subset_closedBall (0:E4)).mp t
 let d:=2*R+1; use -(d • basis b); intro x h; have hv: ‖x‖≤R:= by simpa only [Set.mem_setOf_eq,Metric.mem_closedBall,dist_zero_right] using k h
 refine ⟨x+d • basis b,?_,by simp⟩; change |(x+_) a|<(x+_) b; simp[p,p.symm]; have hw(i:Axis):|x i|≤R:= (show |x i|≤ ‖x‖ from ?_).trans hv; dsimp[d]; linarith [hw a, (abs_le.mp (hw b)).1]
 simpa [basis, EuclideanSpace.inner_single_right] using abs_real_inner_le_norm x (basis i)
lemma passAll(t:ℝ)(V:Set E4)(x:E4): M t '' (strace x (Wedge a b))= strace (M t x) (Wedge a b):= eitherShift p t true x
-- thickening & geometry
omit p
lemma withTrace (V:Set E4){p q:ℝ}:∀ y∈ thickening p V, strace y (ball (0:E4) q)⊆ thickening (q+p) V:= by
 rintro y w i ⟨a,v,rfl⟩; refine Metric.mem_thickening_iff.mpr ?_; obtain ⟨z,x,d⟩:=Metric.mem_thickening_iff.mp w
 exact ⟨z,x, lt_of_le_of_lt (dist_triangle (a+y) y z) (add_lt_add (by simpa using (show dist a 0< q from v)) d)⟩
lemma ahead (T: E4≃ₜ E4)(V W:Set E4) (p:IsCompact V)(b:IsOpen W)(w:T '' V⊆ W) : ∃ a>0,∃ d>0,∀ y∈thickening a V, strace (T y) (ball (0:E4) d)⊆ W:= by
 obtain ⟨q,v,z⟩:=(p.image T.continuous).exists_thickening_subset_open b w
 have he:V⊆ T ⁻¹' thickening (q/2) (T '' V):= fun x b=> show T x∈ thickening (q/2) (T '' V) from self_subset_thickening (by positivity) (T '' V) (a:=T x) ⟨x,b,rfl⟩
 obtain ⟨j,e,h⟩:=p.exists_thickening_subset_open (isOpen_thickening.preimage T.continuous) he
 exact ⟨j,e,q/2,by positivity, fun y b=> (withTrace (T '' V) (q:=q/2) (p:=q/2) (T y) (h b)).trans (by rw [add_halves];exact z)⟩ -- orientation
-- continuity input margin parameter
include p
lemma stamp_cont(t:ℝ)(V W:Set E4)(w:IsOpen W)(h:IsCompact V)(s:M t '' V ⊆ W) : ∀ᶠ z in 𝓝 t,M z '' V ⊆ W:= by
 -- generalized tube lemma
 let U : Set (ℝ × E4):=(fun x:ℝ× E4=> M x.1 x.2)⁻¹' W
 have he : IsOpen U:= w.preimage (stroll_time a b p)
 have hv : Set.prod ({t}:Set ℝ) V⊆ U:= fun z (h:z.1=t∧z.2∈V)=> s (show M z.1 z.2∈ M t '' V from ⟨z.2,h.2,by rw[h.1]⟩)
 obtain ⟨X,Y,h0,h1,k,e,w₀⟩ := generalized_tube_lemma (isCompact_singleton (x:=t)) h he hv
 refine (show ∀ᶠ z in 𝓝 t,z∈ X from h0.mem_nhds (Set.singleton_subset_iff.mp k)).mono fun z q=> ?_
 rintro _ ⟨y,v,rfl⟩; exact (show (z,y)∈ U from w₀ ⟨q,e v⟩)
end YM.Marque.Flow
