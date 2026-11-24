import Bay.D.Conifer
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
variable {E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {I:Type*}[Fintype I]

/-- Bilinear matrix with explicit symmetric scatter reads. -/
abbrev Icey (I:Type*) := I → I → ℂ
def swirl (A:Icey I)(x y:I→ℝ) := ∑ i,∑ j, (x i*y j) • A i j
def splash(A:Icey I)(x:I→ℝ):=swirl A x x
def swill(A:Icey I):ℝ:=∑ i,∑ j,‖A i j‖
structure Rake (s:Finset I)(K:ℝ)(A:Icey I):Prop where
 sym(i j:I):A i j = A j i
 fits (i j:I):A i j≠0→i∈s ∧ j∈s
 fee:swill A≤K
abbrev Brine (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E]:= E→L[ℝ] E→L[ℝ] ℂ
abbrev Rink (I:Type*) := EuclideanSpace ℝ I
structure Crate (s:Finset I)(L:E→ₗ[ℝ]Rink I)(B:Brine E)(K:ℝ):Prop where
 nonneg:0≤K
 fits(i:I)(x:E):L x i≠0→i∈s
 sym(x y:E):B x y=B y x
 fee(x:E):‖B x x‖≤K*‖L x‖^2
namespace Crate
variable {s:Finset I}{L:E→ₗ[ℝ]Rink I}{B:Brine E}{K:ℝ}
lemma lost(p:Crate s L B K){x:E}(hx:L x=0)(y:E):B y x=0:=by
 by_contra h
 let C:=K*‖L y‖^2

 have hc:0≤C:=mul_nonneg p.nonneg (sq_nonneg _)
 have hh:0<‖B y x‖:=norm_pos_iff.mpr h
 let t:=(C+1)/‖B y x‖
 have he(u:ℝ):‖B (y + u • x) (y+ u • x)‖≤ C:=by
    simpa only [map_add L,map_smul L,hx,smul_zero,add_zero] using p.fee (y+(u:ℝ) • x)
 have hp := (norm_sub_le ..).trans (add_le_add (he t) (he (-t)))
 rw [show _ - _=(4*t) • B y x from ?_, norm_smul, Real.norm_of_nonneg (by unfold t;positivity)] at hp
 · unfold t at hp
   rw[mul_assoc,div_mul_cancel₀ _ hh.ne'] at hp -- tune
   linarith
 simp_rw [map_add, map_smul, add_apply, smul_apply, p.sym x y, Complex.real_smul]; push_cast; ring
lemma same(p:Crate s L B K){x y:E}(e:L x=L y):B x x=B y y:=by
 have h:= fun z=>p.lost (x:=x-y) (by rw[map_sub,e,sub_self]) z
 exact ((sub_eq_zero.mp (by rw[←map_sub (B x) x y]; exact h x)):B x x=B x y).trans ((p.sym x y).trans (sub_eq_zero.mp (by rw[←map_sub];exact h y)))

lemma fair(p:Crate s L B K)(x y:E)(h:‖L x‖≤1)(t:‖L y‖≤1): ‖B x y‖≤2*K:=by
 let c:=B (x+y) (x+y)
 let d:=B (x-y) (x-y)
 have w:c-d=4*B x y:=by
   unfold c d; simp_rw[map_add,map_sub,add_apply,sub_apply,p.sym y x];ring

 have hx: ‖L (x+y)‖≤2:=by rw[map_add];exact (norm_add_le ..).trans (by linarith)
 have hy: ‖L (x-y)‖≤2:=by rw[map_sub];exact (norm_sub_le ..).trans (by linarith)
 have ht:‖c‖≤K*2^2:=(p.fee (x+y)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx _) p.nonneg)
 have hu:‖d‖≤K*2^2:=(p.fee (x-y)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy _) p.nonneg)
 have hb:4*‖B x y‖ ≤ 8*K:=by
    have he:= norm_sub_le c d
    rw[w,norm_mul] at he; norm_num at he; linarith only [ht,hu,he]
 linarith

lemma slush(p:Crate s L B K):∃ A:Icey I,Rake s (2*K*s.card^2) A ∧ ∀ x:E,B x x=splash A (L x):=by
 let V:=EuclideanSpace.basisFun I ℝ
 let Q:= (LinearMap.range L).starProjection
 choose y hy using (show ∀ i:I, ∃ x:E,L x=Q (V i) from
   fun i=> (LinearMap.range L).orthogonalProjectionOnto (V i)|>.2)
 let z(i):=if i∈s then y i else 0
 have hm(i):‖L (z i)‖≤1:=by
   unfold z; split_ifs
   · rw[hy];exact ((LinearMap.range L).norm_starProjection_apply_le _).trans_eq (V.orthonormal.1 i)
   simp
 let A:Icey I:=fun i j=> B (z i) (z j)
 have hf(i j): ‖A i j‖ ≤ if i∈s then if j∈s then 2*K else 0 else 0:=by
   split_ifs with u v
   · exact p.fair _ _ (hm _) (hm _)
   · simp [A,z,v]
   simp [A,z,u]
 refine ⟨A,⟨fun i j=>p.sym ..,fun i j h=>⟨of_not_not (fun n=>h (by simp [A,z,n])),of_not_not (fun n=>h (by simp [A,z,n]))⟩, ?_⟩,fun x=>?_⟩
 · refine (sum_le_sum (s:=univ) fun i _=>sum_le_sum (s:=univ) fun j _=>hf i j).trans_eq ?_
   have he(i): (∑ j, if i ∈ s then if j∈s then 2*K else (0:ℝ) else 0) =
               (if i∈s then (s.card:ℝ)*(2*K) else 0):=by
     by_cases h:i∈s
     · simp only [h,ite_true,← Finset.sum_filter];simp
     simp [h]
   simp_rw [he,←Finset.sum_filter]; simp; ring

 have hk:(∑ i,L x i • L (z i))=∑ i,L x i • Q (V i):=by
   refine sum_congr rfl fun i _=>?_
   by_cases h:i∈s
   · simp [z,h,hy]
   rw[show L x i=0 from of_not_not fun n=> h (p.fits i x n)]; simp
 have hj:∑ i,L x i • V i=L x:=V.sum_repr (L x)
 let u:= fun i=> L x i • z i
 have he:L (∑ i,u i)=L x:=by
   unfold u; rw [map_sum]; simp_rw[map_smul,hk,←map_smul,←map_sum,hj]
   exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self ..)
 rw[←p.same he]
 simp_rw [map_sum, _root_.sum_apply, u, map_smul, smul_apply, smul_smul]
 exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>congrArg ((_ :ℝ) • ·) (p.sym ..)

end Crate
variable {A:Icey I}{s:Finset I}{K:ℝ}
namespace Rake
lemma widen(p:Rake s K A){s'}{K':ℝ}(h:s⊆s')(g:K≤K'):Rake s' K' A:=⟨p.sym,fun i j n=>let t:=p.fits i j n;⟨h t.1,h t.2⟩,p.fee.trans g⟩
lemma nonneg(p:Rake s K A):0≤K:=(by unfold swill; positivity:0≤ swill A).trans p.fee
lemma zero : Rake s 0 (0:Icey I):=by
 constructor
 · exact fun _ _=>rfl
 · simp
 simp[swill]
lemma swirl_same {x y z w:I→ℝ}(p:Rake s K A)(hx: Set.EqOn x z s)(hy:Set.EqOn y w s):
   swirl A x y=swirl A z w:=by
 refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_
 by_cases h:A i j=0
 · simp[h]
 rw[hx (p.fits _ _ h).1,hy (p.fits _ _ h).2]
/-- Use for true clipping.
-/
lemma fee_swirl(p:Rake s K A){x y:I→ℝ}{b c:ℝ}(t:0≤b)(u:0≤c)
   (hx:∀i∈s, |x i|≤b) (hy:∀i∈s, |y i|≤c):
   ‖swirl A x y‖≤b*c*K:=by
 refine (norm_sum_le ..).trans (le_trans ?_ (mul_le_mul_of_nonneg_left p.fee (mul_nonneg t u)))
 unfold swill; simp_rw[mul_sum]
 refine sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)

 rw[norm_smul,Real.norm_eq_abs,abs_mul]
 by_cases h:A i j=0
 · simp [h]
 exact mul_le_mul_of_nonneg_right (mul_le_mul (hx _ (p.fits _ _ h).1) (hy _ (p.fits _ _ h).2)
    (abs_nonneg _) t) (by positivity)
lemma shake(p:Rake s K A)(v:ℂ):Rake s (‖v‖*K) (v • A):=by
 constructor
 · intro i j; simp [p.sym i j]
 · intro i j h; exact p.fits i j (by contrapose! h; simp[h])
 apply le_trans _ (mul_le_mul_of_nonneg_left p.fee (norm_nonneg _))
 simp [swill,mul_sum]

lemma add{B:Icey I}{L:ℝ}(p:Rake s K A)(q:Rake s L B):
   Rake s (K+L) (A+B):=by
 refine ⟨fun i j=>congrArg₂ (·+·) (p.sym i j) (q.sym i j),fun i j n=>?_,le_trans ?_ (add_le_add p.fee q.fee)⟩
 · by_cases h:A i j=0
   · exact q.fits i j (by contrapose! n; simp[h,n])
   exact p.fits i j h
 unfold swill; rw[←sum_add_distrib]; exact sum_le_sum fun i _=>le_trans (sum_le_sum fun j _=> norm_add_le ..) sum_add_distrib.le

end Rake
variable {J:Type*}
lemma rakes (As:J→Icey I)(ls:J→ℝ)(n:Finset J)
  (h:∀j∈n,Rake s (ls j) (As j)):Rake s (∑j∈n,ls j) (∑j∈n,As j):=by
 induction n using Finset.induction_on with
 | empty=> simpa using (Rake.zero (s:=s))

 | @insert i n f g=>
    rw[sum_insert f,sum_insert f]
    exact (h _ (mem_insert_self ..)).add (g fun u l=>h u (mem_insert_of_mem l))

lemma swirl_add(B A:Icey I)(x y:I→ℝ):swirl (B+A) x y=swirl B x y+swirl A x y:=by simp [swirl, smul_add,sum_add_distrib]

@[simp] lemma swirl_zero(x y:I→ℝ):swirl 0 x y=0:=by simp [swirl]
lemma swirl_scalar(v:ℂ)(A:Icey I)(x y:I→ℝ):swirl (v • A) x y=v*swirl A x y:=by simp [swirl, Complex.real_smul, mul_sum, mul_left_comm v]

lemma swirling(As:J→Icey I)(x y:I→ℝ)(n:Finset J):
  swirl (∑ j∈n,As j) x y=∑j∈n,swirl (As j) x y:=by
 induction n using Finset.induction_on with
 | empty=>simp
 | @insert i n f g=>rw[sum_insert f,sum_insert f,swirl_add,g]
lemma swirl_xyScale(a b:ℝ)(A:Icey I)(x y:I→ℝ):
    swirl A (a • x) (b • y)= (a*b) • swirl A x y:=by
 simp only [swirl,Pi.smul_apply,Finset.smul_sum,smul_eq_mul,Complex.real_smul]; push_cast
 exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by ring

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.Crate.slush
