import YM.SU5.Reconstruction.Quartz.MonSoon
import YM.SU5.Reconstruction.Quartz.Vapor
/-!
# Rents and interpretation of the physical common-space spectrum / projections
-/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval ComplexOrder
open CrossedFrame Clasp Picket Lens Ravin BridgeClub Anvil ConePrice Sail Ship
variable {a b:Axis}(p:b≠a)
def stowed (a b:Axis)(x:E4): Prop := |x a|≤ x b
lemma sun_plus {x y:E4}(h:x ∈ Wedge a b)(k:stowed a b y): x+y∈ Wedge a b:= (abs_add_le ..).trans_lt (add_lt_add_of_lt_of_le h k)
lemma sun_min {x y:E4}(h:x∈Counter a b)(k:stowed a b (-y)): x+y∈ Counter a b:= by change -(x+y)∈ Wedge a b; rw [neg_add]; exact sun_plus (x:=-x) (y:=-y) (show -x∈ Wedge a b from h) k -- neg_add name
include p
lemma plus_step(k:ℝ)(c:0≤k) : stowed a b (k • basis b):= by simpa [stowed,p.symm]
lemma steward {r s M δ t L:ℝ}(h: |s|≤3)(hr:0≤r)(ht:|t|≤ L)(hδ:|δ| ≤L)(hp : M+3*L≤ Real.exp (-3)*r) : stowed a b (path a b (t+δ,t)+ move a b s (r • basis b)- M • basis b):=by
 let F:= path a b (t+δ,t); let V:= move a b s (r • basis b)
 have ht₁: F a = t+δ/2:= by simp[path,F,p.symm];rw [add_div]; ring -- tune
 have ht₂: F b = δ/2:= by simp[path,F,p] -- tune
 have hv: V b+ V a=Real.exp s*r∧ V b - V a=Real.exp (-s)*r:= by unfold V; rw[eye_high p,eye_low p]; simp[p.symm,Real.cosh_eq,Real.sinh_eq]; constructor<;>ring
 unfold stowed; change |(F+V-M • basis b) a| ≤ _; simp only[PiLp.sub_apply,PiLp.add_apply, PiLp.smul_apply,smul_eq_mul]; change |F a+V a-_|≤ F b+V b-_; rw [ht₁,ht₂]; simp[p.symm]; rw [abs_le]; have hg:=abs_le.mp ht; have hM:=abs_le.mp hδ; have H1:Real.exp (-3)≤Real.exp s:= Real.exp_le_exp.mpr ((abs_le.mp h).1); have H2:Real.exp (-3)≤Real.exp (-s):=Real.exp_le_exp.mpr (neg_le_neg ((abs_le.mp h).2)); constructor<;>nlinarith [hv.1,hv.2,hg.1,hg.2,hM.1,hM.2] -- scope
omit p in
lemma adequate (u R:ℝ): ∃ r>0, u+3*R ≤ Real.exp (-3)*r:= by
 let r:=max 1 ((u+3*R)/Real.exp (-3)); exact ⟨r,lt_of_lt_of_le zero_lt_one (le_max_left ..),((div_le_iff₀ (Real.exp_pos _)).mp (le_max_right _ _)).trans_eq (mul_comm ..)⟩ -- include p error
omit p
-- generate common with pin orbit in positive Mink cone plane and spectators; sharp use Rank
variable {H K:Hilbert}(S:OS.Semigroup H a)(N:Net H)(Ω:H)
local notation "P"=> parish N Ω
local notation "U"=>trans S
lemma transport_home(A:H.Op)(h:A∈N) : A Ω∈ parish N Ω:= Submodule.le_topologicalClosure _ (Submodule.subset_span (show A Ω∈ (fun x:H.Op=>x Ω) '' (N:Set H.Op) from ⟨_,h,rfl⟩))
variable (u:∀ x:E4, trans S x Ω=Ω)(C:∀ A∈N,∀ x:E4,stowed a b x→ parcelUp S x A∈N)
include u C
lemma stowed_move(x:E4)(h:stowed a b x) : MapsTo (U x) (parish N Ω) (parish N Ω):= by
 let X:= P; let Y:= X.comap ((trans S x):H.Op).toLinearMap
 suffices t : X ≤ Y from fun i p=>t p
 let hF:IsClosed (Y:Set H):=(Submodule.isClosed_topologicalClosure _).preimage (U x).continuous
 apply Submodule.topologicalClosure_minimal _ _ hF; apply Submodule.span_le.mpr; rintro _ ⟨i,p,rfl⟩; change U x (i Ω) ∈ X; rw [show U x (i Ω)=(parcelUp S x i) Ω from (by simp only[parcelUp,mul_apply_eq_comp,u])]; exact transport_home N Ω _ (C i p x h)
variable (v: Paces b S)
include v p
lemma beam_run(t:ℝ)(z:H)(h:z∈ P) : U (t • head a b 1) z∈ P:=by
 apply polaris b 1 t S (by simp) v P (Submodule.isClosed_topologicalClosure _) z 0 1 zero_lt_one
 intro q d; apply stowed_move S N Ω u C _ _ h; unfold stowed; simp [head,p,p.symm,abs_of_pos d.1] -- 
lemma beam_back(t:ℝ)(z:H)(h:z∈ P) : U (t • head a b (-1)) z∈ P:=by
 apply polaris b (-1) t S (by simp) v P (Submodule.isClosed_topologicalClosure _) z (-1) 0 neg_one_lt_zero; intro q d; apply stowed_move S N Ω u C _ _ h; unfold stowed; simp [head,p,p.symm,abs_of_neg d.2] -- 
lemma stay_everywhere(x:E4) : MapsTo (U x) (parish N Ω) (parish N Ω):=by
 intro y h; nth_rw 1 [← heft a b x, trans_sum]; simp only [trans_sum S, mul_apply_eq_comp]
 -- watch left-assoc head sum last
 apply beam_run p S N Ω u C v _ _; apply beam_back p S N Ω u C v _ _; exact stowed_move S N Ω u C _ (by unfold stowed; rw [(lees p x).1,(lees p x).2,abs_zero]) h
end YM.Quartz.Waltz
