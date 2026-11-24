import YM.SU5.Relativistic.ExpandBehind
set_option autoImplicit false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Fock Lat UnitAddTorus
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=> 2*Real.pi
local notation "Φ"=> Set.Icc (-π) π

variable {κ:Type*}(n:ℕ)(A:ℤ→ℂ)
abbrev TwistT(n:ℕ) :Finset ℤ:= Finset.Icc (-(n:ℤ)) (n:ℤ)
-- overspend rate from β to β'<β/2
lemma smaller (n:ℕ)(a:ℝ)(p:0<a)(B:ℝ)(t:0≤B) {g:ℤ→ℂ} (C:ℂ)(h:HasSum g C)(u:∀ i:ℤ, ‖g i‖≤ B*spangle (2*a) i):
    ‖C-∑ j∈TwistT n,g j‖ ≤ (∑' j:ℤ,spangle a j) *(B*spangle a n):=by
 classical
 let b := B* spangle a n
 have he:0≤b:= mul_nonneg t (spangle_pos ..).le
 let X:= (TwistT n)
 let Y:Set ℤ:=(X:Set ℤ)ᶜ
 have hx(i:Y):‖g i.val‖≤ spangle a i.val*b:=by
    let j:= i.val; have hp:n ≤ j.natAbs:=by
       have hk:j∉ TwistT n:= i.property
       simp only [TwistT, Finset.mem_Icc] at hk; omega
    apply (u i.val).trans; rw [mul_left_comm (spangle a i.val)]; gcongr
    unfold spangle; rw [← Real.exp_add]; apply Real.exp_monotone; have ht:(n:ℝ) ≤ (i.val.natAbs:ℝ):=by exact_mod_cast hp
    rw [Int.natAbs_natCast]; nlinarith
 have hi:=spangle_sum p
 have hg:(∑ j∈TwistT n,g j)+ ∑' i:Y,g i.val=C:= (h.summable.sum_add_tsum_subtype_compl _).trans h.tsum_eq
 rw [←hg,add_sub_cancel_left, ←tsum_mul_right]
 apply (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun i=>norm_nonneg _) hx ((hi.mul_right b).subtype Y))).trans
 exact (Summable.tsum_le_tsum hx ((h.summable.subtype _).norm) ((hi.mul_right b).subtype Y)).trans (Summable.tsum_subtype_le (fun i=> spangle a i*b) Y (fun i=>mul_nonneg (spangle_pos ..).le he) (hi.mul_right b)) -- name

variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ}
namespace UpStart
variable (P:UpStart d s c r (2*a))
local notation "Ω"=>target s c
local notation "Z"=>turned s c
local notation "U"=>launch d r
def sailV (i:SpinIdx)(n:ℤ)(s:Finset ℤ)(c:ℤ→Behind→ℂ)(k:Behind) :ℂ:=wrapT n (turned s c i k)
def beforeT (i:SpinIdx) (n:ℕ)(s:Finset ℤ)(c:ℤ→Behind→ℂ)(k:Behind)(t:ℝ):=∑ j∈ TwistT n,sailV i j s c k*soundT j t
include P
lemma sail_cont(i:SpinIdx)(n:ℤ) : Continuous (sailV i n s c):= by
 apply continue_g (W:=launch d r) (launch_compact d r) (f:=sailV i n s c)
 · refine continuousOn_const.mul (circle_continuous (Z i) n ?_ (launch_compact ..)); apply (P.turned_c i).mono; rintro ⟨x,t⟩ ⟨p,h⟩; exact ⟨Set.mem_univ _,h⟩
 intro x e; unfold sailV wrapT pluse turned; simp [P.elsewhere x e]
lemma sail_support (i:SpinIdx)(n:ℤ){k:Behind}(p:k∉sunshine) : sailV i n s c k=0:=by
 unfold sailV wrapT pluse turned; simp [P.elsewhere k (show k∉ interior (launch d r) from fun e=> p (launch_sun P.wage P.tail (interior_subset e)))]
lemma sail_t(p:0<a)(i:SpinIdx) : ∃ B> (0:ℝ),∀ k n t, t∈ Set.Icc (-π) π → ‖turned s c i k t - beforeT i n s c k t‖ ≤ B*spangle a n:=by
 obtain ⟨C,t,cL⟩:= P.projectedReceipt i
 let B:= (∑' j:ℤ,spangle a j:ℝ); have hB:0<B:= (spangle_sum p).tsum_pos (fun i=>(spangle_pos ..).le) 0 (spangle_pos ..)
 refine ⟨B*C,mul_pos hB t, fun k n u v=>?_⟩
 have hp(x):‖wrapT x (Z i k)‖≤ C*spangle (2*a) x:=by
    by_cases g:k∈ U; exact cL k g x
    unfold turned wrapT pluse; simp_rw [P.elsewhere k (fun t=>g (interior_subset t))]; simp [(mul_pos t (spangle_pos ..)).le]
 have hh:ContinuousOn (Z i k) Φ:= (P.turned_c i).comp (f:=fun t=> (k,t)) (continuous_const.prodMk continuous_id|>.continuousOn) (fun t p=> ⟨Set.mem_univ _,p⟩)
 let f(j:ℤ):= sailV i j s c k*soundT j u
 have hg:HasSum f (Z i k u):= buzz (Z i k) hh (homeEnd ..) (Summable.of_norm (Summable.of_nonneg_of_le (fun i=> norm_nonneg _) hp ((spangle_sum (show 0<2*a from (by positivity))).mul_left C))) u v
 rw [mul_assoc]; exact smaller n a p _ t.le (Z i k u) (g:=fun j=> sailV i j s c k*soundT j u) hg (fun j=> (le_of_eq (by rw [norm_mul,sound_norm,mul_one]; rfl)).trans (hp j))
-- phoned bills for trig chart
abbrev array (f:WalkA→₀ℂ) (k:Behind) := f.sum fun i z=> z*spax (-i) k
def boardZ(s:ℕ)(F:SpinIdx→ℤ→(WalkA→₀ℂ))(i:SpinIdx)(k:Behind)(t:ℝ):=∑ x∈TwistT s,array (F i x) k * soundT x t
lemma sail_m (i:SpinIdx)(n:ℕ)(ε:ℝ)(p:0<ε) : ∃ f: ℤ→ WalkA→₀ℂ,(∀ k∈backPane,∀ t:ℝ, ‖(∑ x∈TwistT n,array (f x) k* soundT x t)-beforeT i n s c k t‖≤ε) ∧
     ∀ j:ℤ,j∉s→ i∈plusHalf→ f j=0:=by -- parsing `∑ x` includes sub? parentheses
 classical
 let T:=TwistT n; let D:ℝ:=T.card+1; have h:0<D:=by unfold D; positivity
 have hp(j:ℤ) : ∃ f: WalkA→₀ℂ,(∀ k∈backPane, ‖array f k-sailV i j s c k‖≤ ε/D)∧ (j∉s → i∈plusHalf→ f=0):=by
    by_cases t:j∈s ∨ i∉plusHalf
    · obtain ⟨a,g⟩:= summit _ (P.sail_cont i j).continuousOn (fun k h=>P.sail_support i j h) _ (div_pos p h); exact ⟨a,g, fun x w=> Or.elim t (fun u=>(x u).elim) (fun u=>(u w).elim)⟩
    push Not at t; refine ⟨0,fun k _=>?_,fun _ _=>rfl⟩; unfold array sailV; rw [P.landing t.2 k _ t.1]; simp [(div_pos p h).le]
 choose f u v using hp
 refine ⟨f,fun k y t=>?_,v⟩; unfold beforeT; rw [← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; simp_rw [←sub_mul,norm_mul,sound_norm,mul_one]; apply (sum_le_sum (fun i e=>u i k y)).trans; rw [sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one : (T.card:ℝ)≤D) (div_pos p h).le).trans (Eq.le (mul_div_cancel₀ _ h.ne'))
end UpStart
end YM.CF.Crest.Sleet
