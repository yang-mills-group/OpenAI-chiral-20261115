import YM.SU5.Relativistic.GlassWave
/-! # Normalized moment arcade, analytic rate proof. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
def spangle(a:ℝ)(i:ℤ) := Real.exp (-a*(i.natAbs:ℝ))
lemma spangle_pos(a:ℝ)(i:ℤ):0<spangle a i:=Real.exp_pos _
lemma spangle_sum {a:ℝ}(p:0<a) : Summable (fun i:ℤ=> spangle a i):= by
 have hi:=summable_geometric_of_lt_one (Real.exp_pos (-a)).le (by simpa using Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr p))
 have ht(i:ℕ): spangle a i=(Real.exp (-a))^i:=by rw [←Real.exp_nat_mul]; unfold spangle; simp [mul_comm]
 rw [summable_int_iff_summable_nat_and_neg]; constructor
 · simp_rw [ht]; exact hi
 have he(i:ℕ):spangle a (- (i:ℤ))=spangle a i:=by simp [spangle]
 simp_rw [he,ht]; exact hi
lemma spangle_once {a:ℝ}(p:0<a) (c:ℤ): ∃ B:ℝ,0<B ∧ ∀ i:ℤ, spangle a (i+c)≤ B*spangle a i:= by
 refine ⟨Real.exp (a*↑(c.natAbs)),Real.exp_pos _,fun i=>?_⟩
 unfold spangle; rw [←Real.exp_add]; have hv:i.natAbs ≤ (i+c).natAbs + c.natAbs:=by omega
 have he : (i.natAbs:ℝ) ≤ ((i+c).natAbs:ℝ)+(c.natAbs:ℝ):=by exact_mod_cast hv
 exact Real.exp_monotone (by nlinarith)
variable {U:Set Behind}{a:ℝ} (pa:0<a) (hu:IsCompact U) (hk:U⊆sunshine)
def TollS (a:ℝ)(U:Set Behind)(f:Behind→ℤ→ℂ) := ∃ B:ℝ,0<B ∧ ∀ k∈U,∀ n:ℤ, ‖f k n‖≤B*spangle a n
include pa
lemma TollS.paidSum{f:Behind→ℤ→ℂ}(h:TollS a U f) {k:Behind}(u:k∈U) : Summable (fun i:ℤ=>‖f k i‖):=by obtain ⟨B,v,r⟩:= h; exact Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (r k u) ((spangle_sum pa).mul_left _)
lemma TollS.shifts{f:Behind→ℤ→ℂ}(h:TollS a U f)(c:ℤ) : TollS a U (fun k i=> f k (i+c)):=by obtain ⟨B,v,r⟩:= h; obtain ⟨b,p,H⟩:= spangle_once pa c; exact ⟨B*b,mul_pos v p,fun k hk n=>(r k hk (n+c)).trans ((mul_le_mul_of_nonneg_left (H n) v.le).trans_eq (mul_assoc ..).symm)⟩
omit pa
include hu
lemma TollS.scaleU {f:Behind→ℤ→ℂ}(h:TollS a U f)(g:Behind→ℂ)(hg:ContinuousOn g U) : TollS a U (fun k i=> g k * f k i):=by
 obtain ⟨B,v,r⟩:= h; obtain ⟨C,p⟩:= hu.exists_bound_of_continuousOn hg
 refine ⟨(|C|+1)*B,by positivity,fun k hk0 i=>?_⟩; change ‖g k*f k i‖ ≤ _; rw [norm_mul,mul_assoc]; exact mul_le_mul ((p k hk0).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))) (r k hk0 i) (norm_nonneg _) (by positivity) -- potential `simp`
omit hu
lemma TollS.addX{f g:Behind→ℤ→ℂ}(h:TollS a U f)(p:TollS a U g):TollS a U (fun k i=>f k i+g k i):=by obtain ⟨B,v,r⟩:=h; obtain ⟨C,w,q⟩:=p; exact ⟨B+C,add_pos v w,fun k u i=> (norm_add_le ..).trans ((add_le_add (r _ u _) (q _ u _)).trans_eq (add_mul ..).symm)⟩
-- Cuest theorem after shifting
variable (f:Behind→ℤ→ℂ)(n:ℤ)(hf:∀ i:ℤ, ContinuousOn (fun k=>f k i) U)
include hu
private lemma short_s (l:Finset ℤ)(h:∀ i∈l,ContinuousOn (fun k=> f k i) U): ∃ B:ℝ,0<B ∧ ∀ k∈U,∀ i∈l, ‖f k i‖≤B*spangle a i:=by
 induction l using Finset.induction_on with
 | empty=> exact ⟨1,one_pos,fun i v x p=>(by simp at p)⟩
 | @insert i s hv ih=>
    obtain ⟨B,v,p⟩:= ih (fun i w=>h _ (mem_insert_of_mem w)); obtain ⟨C,t⟩:= hu.exists_bound_of_continuousOn (h i (mem_insert_self i s))
    let b:=(|C|+1)/spangle a i; have hb:0<b:=div_pos (by positivity) (spangle_pos ..)
    refine ⟨B+b,add_pos v hb,fun x e l w=>?_⟩; rw [add_mul]
    rcases mem_insert.mp w with y|y
    · subst l; unfold b; rw [div_mul_cancel₀ _ (spangle_pos ..).ne']; exact (((t x e).trans (le_abs_self C)).trans (le_add_of_nonneg_right zero_le_one)).trans (le_add_of_nonneg_left (mul_nonneg v.le (spangle_pos ..).le))
    exact (p x e l y).trans (le_add_of_nonneg_right (mul_nonneg hb.le (spangle_pos ..).le))
include hf
lemma TollS.gathers (N:ℕ)(h:∀ b:Bool, let n:ℤ:= if b then -(N:ℤ) else (N:ℤ); ∃ B:ℝ,0<B∧∀ k∈U,∀ q:ℤ, 0 ≤ sg b*q→ ‖f k (n+q)‖ ≤ B* Real.exp (-a*(sg b*(q:ℝ)))):TollS a U f:=by
 obtain ⟨B,v,r⟩:=h false; obtain ⟨D,e,p⟩:=h true; obtain ⟨C,c,q⟩:= short_s (a:=a) hu f (Finset.Icc (-(N:ℤ)) (N:ℤ)) (fun i _=>hf i)
 let A := Real.exp (a*N); refine ⟨C+(B+D)*A,add_pos c (mul_pos (add_pos v e) (Real.exp_pos _)),fun k hk i=>?_⟩; rcases lt_or_ge i (-(N:ℤ)) with hh|hh
 · let w:= i+N; have ht : (↑(i.natAbs):ℝ) = -(i:ℝ):= by simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun x:ℤ=> (x:ℝ)) (show ((i.natAbs:ℕ):ℤ)=-i by omega)
   have hv:=p k hk w (by simp only [sg,if_true,neg_mul,one_mul,Left.nonneg_neg_iff]; exact_mod_cast (show w≤0 by unfold w; omega)) -- tune order
   change ‖f k (-(N:ℤ)+w)‖ ≤ D* Real.exp (_ ) at hv
   rw [show -(N:ℤ)+w=i by unfold w; abel, show Real.exp ( -a*(sg true *(w:ℝ)))= A*spangle a i from (by unfold A spangle w; rw [ht, ←Real.exp_add]; congr 1; push_cast; unfold sg; simp only [if_true]; ring)] at hv
   refine hv.trans ((mul_le_mul_of_nonneg_right (show D≤ B+D from le_add_of_nonneg_left v.le) (mul_nonneg (Real.exp_pos _).le (spangle_pos ..).le)).trans ?_); rw [←mul_assoc,add_mul C]; exact le_add_of_nonneg_left (mul_nonneg c.le (spangle_pos ..).le)
 by_cases y: (N:ℤ) < i; swap; · refine (q k hk i (Finset.mem_Icc.mpr ⟨hh,(le_of_not_gt y)⟩)).trans ?_; rw [add_mul]; exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (add_pos v e).le (Real.exp_pos _).le) (spangle_pos ..).le)
 let w:= i-(N:ℤ); have ht : (↑(i.natAbs):ℝ) = (i:ℝ):= by simpa only [Int.cast_natCast] using congrArg (fun x:ℤ=> (x:ℝ)) (show ((i.natAbs:ℕ):ℤ)=i by omega)
 have hv:= r k hk w (by simp only [sg,Bool.false_eq_true,if_false,one_mul]; exact_mod_cast (show 0 ≤ w by unfold w; omega)); change ‖f k ((N:ℤ)+w)‖ ≤ B* Real.exp (_ ) at hv
 rw [show (N:ℤ)+w=i by unfold w; abel, show Real.exp ( -a*(sg false *(w:ℝ)))= A*spangle a i from (by unfold A spangle w; rw [ht, ←Real.exp_add]; congr 1; push_cast; unfold sg; simp only [Bool.false_eq_true, if_false]; ring)] at hv
 refine hv.trans ((mul_le_mul_of_nonneg_right (show B≤ B+D from le_add_of_nonneg_right e.le) (mul_nonneg (Real.exp_pos _).le (spangle_pos ..).le)).trans ?_); rw [←mul_assoc,add_mul C]; exact le_add_of_nonneg_left (mul_nonneg c.le (spangle_pos ..).le)

omit hf
include hk
namespace Cuest
variable {s:Finset ℤ}{c:Behind→ℤ→ℝ}(Q:Cuest s c a)
include Q
lemma collected (i:Axis) : TollS a U (fun k n=>pluse n (outlined i s c k)):=by
 let n:=Nat.succ (s.sup Int.natAbs)+4
 have hn(j)(p:j∈s):j.natAbs+4 ≤ n:=by have he:=Finset.le_sup (f:=Int.natAbs) p; unfold n; omega
 apply TollS.gathers hu _ (fun j=>circle_continuous _ _ (outline_c hu hk Q i) hu) n
 intro b k
 have hl:∀ u∈s,4 ≤ sg b*(k+u:ℤ) := by
    intro j p; have hx:=hn j p; cases b <;> unfold sg k <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul,neg_mul]; exact_mod_cast (show 4 ≤ ((n:ℕ):ℤ)+j by omega); exact_mod_cast (show 4 ≤ -(-((n:ℕ):ℤ)+j) by omega)
 obtain ⟨B,v,p⟩:= budgetStep hu hk Q b k hl; exact ⟨B,v,fun x p' u y=>p x p' u y i⟩
end Cuest
end YM.CF.Crest.Sleet
