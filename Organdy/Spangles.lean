import YM.SU5.FiniteGaugeData.Tower.Gauge
import YM.SU5.FiniteGaugeData.Tower.Baggage

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower


/- Uniform Borel projective limiting coefficients for the actual moving tests: one ultrafilter,
   no countability demand on sets of poses. -/

section menu
variable {I X:Type*}[MeasurableSpace X](l:Ultrafilter I){f:I→X→ℂ}(u:Menu f)
local notation "L" => (l:Filter _)
lemma places(P:Deck X): ∃ Z:Set X,Z.Finite∧∀ x, ∃ y∈Z,P.withZ x y:=by
 let h(x:X)(i:↥P):Prop:=x ∈ i.val
 choose r a using (fun v:Set.range h=> (v.property : ∃ y,h y=v.val))
 refine ⟨Set.range r,Set.finite_range _,fun x=> ⟨_,Set.mem_range_self ⟨h x,Set.mem_range_self x⟩,?_⟩⟩
 intro i b; exact Iff.of_eq (congrFun (a ⟨h x,Set.mem_range_self x⟩) ⟨i,b⟩).symm

include u
theorem braid : ∃ g:X→ℂ,(∃ C:ℝ, 0≤C ∧ (∀ i x,‖f i x‖ ≤ C) ∧ ∀ x,‖g x‖≤C)∧∀ ε:ℝ,0 < ε → ∀ᶠ i in L,∀ x,‖f i x-g x‖ ≤ ε:=by
 obtain ⟨C,c,h⟩:=u.budget

 choose g hg t using fun x=> (isCompact_closedBall (0:ℂ) C).ultrafilter_le_nhds' (l.map fun i=> f i x) (show ∀ᶠ i in L,f i x ∈ closedBall (0:ℂ) C from Eventually.of_forall fun _=> by rw [mem_closedBall,dist_zero_right]; apply h)
 have tc(x:X): Tendsto (fun i=>f i x) L (𝓝 (g x)) := t x
 refine ⟨g,⟨C,c,h,fun x=>by simpa only [mem_closedBall,dist_zero_right] using hg x⟩,fun ε e=>?_⟩
 obtain ⟨P,a,b⟩:= u.deal (ε/4) (by linarith); obtain ⟨Z,r,v⟩:= places P
 letI := r.fintype
 filter_upwards [show ∀ᶠ i in L,∀ x:Z,dist (f i x.val) (g x.val) < ε/4 from eventually_all.mpr fun x=> tendsto_nhds.mp (tc _) (ε/4) (by linarith)] with i z x
 obtain ⟨y,c,p⟩:=v x
 have e₁:dist (g x) (g y)≤ε/4:= le_of_tendsto ((tc x).dist (tc y)) (Eventually.of_forall fun i=>(b _ _ p i).le)
 rw [←dist_eq_norm]; exact (dist_triangle _ (f i y) _).trans (by linarith [dist_triangle (f i y) (g y) (g x),dist_comm (g x) (g y),z ⟨y,c⟩,b _ _ p i])
end menu

section coeff
variable {S:Finset Cover}{I:Type*}
theorem marquis (l:Ultrafilter I) {f:I→PairsC→ℂ} (u:Menu f) (a:∀ i,Coeff true S (f i)):
 ∃ g,(Coeff true S g) ∧ (∃ C:ℝ,0≤C ∧ (∀ i x,‖f i x‖ ≤ C) ∧ ∀ x,‖g x‖≤C) ∧ ∀ ε:ℝ,0 < ε → ∀ᶠ i in (l:Filter I),∀ x,‖f i x-g x‖ ≤ ε:=by
 obtain ⟨g,h,t⟩:=braid l u
 -- build sequence for measurability
 choose v p using fun n:ℕ=>(t (1/(↑n+1)) (by positivity)).exists
 have hx(x:PairsC):Tendsto (fun n=> f (v n) x) atTop (𝓝 (g x)):=by
    refine Metric.tendsto_nhds.mpr fun ε e=>?_
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds e)] with n a; rw [dist_eq_norm]; exact (p n x).trans_lt a
 have ht:Measurable g:= measurable_of_tendsto_metrizable (fun n=>(a (v n)).env.meas) (tendsto_pi_nhds.mpr hx)
 refine ⟨g,⟨fun _=>by contradiction,⟨ht,h.imp fun _ r=> r.2.2⟩,?_⟩,h,t⟩
 intro x y e b; exact tendsto_nhds_unique (hx x) ((hx y).congr fun i=> ((a _).locus _ _ e b).symm)
end coeff

/-- With pure counting this is BQueue (here both input cargos defined everywhere);
    general filters enable **one** ultralimit. -/
structure Q {I:Type*} (l:Filter I) {K:Calibration}
    (S:Finset Cover)(F:I→Buffered.Family K)(f:Buffered.Family K) :Prop where
 goes(i:I): InTest K true S false (F i)
 toBe: InTest K true S false f
 budget: ∃ C:ℝ,0 < C∧ pay f C ∧ ∀ᶠ i in l,pay (F i) C
 car(e:ℝ):0<e→ ∀ᶠ i in l,pay (F i-f) e

namespace Q
variable {K:Calibration}{S T:Finset Cover}{I:Type*}{l:Filter I}{F G:I→Buffered.Family K}{x y:Buffered.Family K}
lemma baggage {F:ℕ→Buffered.Family K}(a:Q atTop S F x): SlabMark.BQueue S F x:=⟨a.goes,a.toBe,a.budget,a.car⟩
lemma sitePlus (a:Q l S F x)(e:S⊆T):Q l T F x:=⟨fun i=>(a.goes i).mono e,a.toBe.mono e,a.budget,a.car⟩
lemma identity : Q l S (fun _=> (1:Buffered.Family K)) 1:=
 ⟨fun _=>.one,.one,⟨1,one_pos,(fun _ _=>norm_one.le),Eventually.of_forall fun _ _ _=>norm_one.le⟩,fun _ p=>Eventually.of_forall fun i=>by rw [sub_self]; intro t x; exact (show ‖(0:FC _)‖=0 from norm_zero).le.trans p.le⟩

-- proofs in the spirit of Baggage (multiplication and motion)
variable (j:Axis)
lemma revolve(v:ℤ)(p:Q l S F x): Q l (reflectedBox j v S) (fun i=>mirror K j v (F i)) (mirror K j v x):=by
 obtain ⟨t,h,⟨C,f,a,b⟩,e⟩:=p
 refine ⟨fun _=>axial K j _ (t _),axial K j _ h,⟨C,f,pay_flips K a _ _,b.mono fun i h=>pay_flips K h j v⟩,fun k vk=>?_⟩
 filter_upwards [e k vk] with i hx
 rw [show mirror K j v (F i)-mirror K j v x=mirror K j v (F i-x) from ?_]
 · exact pay_flips K hx j v
 rw [sub_eq_add_neg (F i), ←neg_one_smul ℂ x, mirror_plus,mirror_scale, star_neg,star_one,neg_one_smul,←sub_eq_add_neg]
open SlabMark in
lemma station(v:ℤ)(p:Q l S F x):Q l (plow K j v S) (fun i=> relocate K j v (F i)) (relocate K j v x):=by
 obtain ⟨t,h,⟨C,f,a,b⟩,e⟩:=p
 refine ⟨fun _=>flow_port K j _ (t _),flow_port K j _ h,⟨C,f,chime_pay _ _ _ _ a,b.mono fun i h=>chime_pay _ _ _ _ h⟩,fun k vk=>?_⟩
 filter_upwards [e k vk] with i hx
 rw [show relocate K j v (F i)-relocate K j v x=relocate K j v (F i-x) from ?_]
 · exact chime_pay K j _ k hx
 unfold relocate; rw [sub_eq_add_neg (F i), ←neg_one_smul ℂ x,chime_plus,chime_scale,neg_one_smul,←sub_eq_add_neg]
lemma multiply (a:Q l S F x)(b:Q l T G y): Q l (S∪T) (fun i=> F i*G i) (x*y):=by
 obtain ⟨t,h,⟨C,f,a,b'⟩,e⟩:=a; obtain ⟨u,h',⟨B,g,c,d⟩,e'⟩:=b
 refine ⟨fun i=>((t i).mono subset_union_left).mul ((u i).mono subset_union_right),(h.mono subset_union_left).mul (h'.mono subset_union_right),⟨C*B,by positivity,pay_mul a c,(b'.and d).mono fun i ⟨p,q⟩=>pay_mul p q⟩,fun i v=>?_⟩
 let ε:=i/(2*max C B); have he:0<ε:= by unfold ε; positivity
 have ht:ε*B+C*ε ≤ i:=by
    have k:ε*(2*max C B)=i:=div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (le_max_right C B) he.le,mul_le_mul_of_nonneg_right (le_max_left C B) he.le]
 filter_upwards [b',e ε he,e' ε he] with n m w j
 have hx: F n*G n-x*y= (F n -x)*y+F n*(G n-y):=by noncomm_ring
 rw [hx]
 intro u r; specialize m u r; specialize w u r; specialize j u r; specialize c u r
 simp only [Pi.sub_apply,Pi.add_apply, Pi.mul_apply] at *
 refine le_trans ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans ?_) ((norm_mul_le ..).trans ?_))) ht
 · exact mul_le_mul w c (norm_nonneg _) he.le
 exact mul_le_mul m j (norm_nonneg _) f.le


lemma plus (a:Q l S F x)(d:Q l S G y):Q l S (fun i=>F i+G i) (x+y):=by
 obtain ⟨A,t,p,h⟩:=a.budget; obtain ⟨D,y₀,q,k⟩:=d.budget
 refine ⟨fun _=> .add (a.goes _) (d.goes _),.add a.toBe d.toBe,⟨A+D,by positivity,(fun i v=> (norm_add_le ..).trans (add_le_add (p i v) (q i v))), (h.and k).mono fun i ⟨r,s⟩ _ _=> (norm_add_le ..).trans (add_le_add (r ..) (s ..))⟩,fun ε x₀=> ?_⟩
 filter_upwards [a.car (ε/2) (by positivity), d.car (ε/2) (by positivity)] with i c e
 rw [show F i+G i-(x+y)=(F i-x)+(G i-y) from by abel,show ε=ε/2+ε/2 by ring]; intro j v; exact (norm_add_le ..).trans (add_le_add (c j v) (e j v))

lemma scale(a:Q l S F x)(c:ℂ):Q l S (fun i=>c • F i) (c • x):=by
 have hx:=norm_nonneg c; obtain ⟨C,y,p,g⟩:= a.budget
 have hc{A:ℝ}(t:0<A){x:Buffered.Family K}(q:pay x A):pay (c • x) ((‖c‖+1)*A):=fun i v=> (norm_smul c (x i v)).le.trans (mul_le_mul (by linarith) (q i v) (norm_nonneg _) (by positivity))
 refine ⟨fun _=> .smul _ (a.goes _),.smul _ a.toBe,⟨_,by exact mul_pos (by linarith : 0 < ‖c‖+1) y,hc y p,g.mono fun _ r=>hc y r⟩,fun e v=>?_⟩
 have he:0 < e/(‖c‖+1):=by positivity
 filter_upwards [a.car _ he] with i u; have hv:=hc he u
 have iu: (‖c‖+1)*(e/(‖c‖+1))=e:=by field_simp <;> positivity
 rw [iu] at hv
 rw [←smul_sub]; exact hv
lemma zero : Q l S (fun _=> (0:Buffered.Family K)) 0:= by simpa using (identity (S:=S) (K:=K) (l:=l)).scale 0
lemma sum {J:Type*}(r:Finset J) (u:J→I→Buffered.Family K)(t:J→Buffered.Family K)(v:∀ j,Q l S (u j) (t j)):Q l S (fun i=>∑ j∈r,u j i) (∑ j∈r,t j):=by
 induction r using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact zero
 | insert i r h ih=>simp only [sum_insert h]; exact (v i).plus ih

lemma atP(a:Q l S F x)(n:Side)(v:Fields (K.c n)):
 Tendsto (fun i=> F i n v) l (𝓝 (x n v)):=by
  refine Metric.tendsto_nhds.mpr fun e h=>?_
  filter_upwards [a.car (e/2) (by positivity)] with i p; rw [dist_eq_norm]; exact (p n v).trans_lt (by linarith)
lemma color [l.NeBot](a:Q l S F x)(n:Side)(p:∀ᶠ i in l,covariant (F i n)):covariant (x n):=by
 intro v t
 refine tendsto_nhds_unique (a.atP n _) ?_
 have g:Tendsto (fun i=>twist (quantU (tradew (K.c n) v)) (F i n t)) l (𝓝 _):=
   (Continuous.tendsto (breeze _) _).comp (a.atP n t) -- breeze maybe
 exact g.congr' <| p.mono (fun _ h=> (h _ _).symm)
end Q
section
variable {K:Calibration}{S:Finset Cover}{I:Type*}{l:Filter I}
 {f:I→PairsC→ℂ}{g:PairsC→ℂ}
lemma noteQ (q:Evens S) (a:∀ i,Coeff true S (f i))(b:Coeff true S g)
 (h:∃ C:ℝ,0≤C∧ (∀ i x,‖f i x‖ ≤ C)∧(∀ x,‖g x‖ ≤ C)) (p:∀ε:ℝ,0 < ε → ∀ᶠ i in l,∀ x,‖f i x-g x‖ ≤ ε):
 Q l S (fun i=>note K (f i) (tagWord S q.val)) (note K g (tagWord S q.val)):=by
 let t:=tagWord S q.val
 have ck{x:PairsC→ℂ}(hx:Coeff true S x): InTest K true S false (note K x t):=by
    have k:=note_t K _ hx (brand S q.val); rw [q.property] at k; exact k
 obtain ⟨C,u,w,y⟩:=h
 have hc(C:ℝ) (u:0≤C) {x:PairsC→ℂ}(r:∀ v,‖x v‖ ≤ C):pay (note K x t) (C+1):=by
    intro m v; rw [note_v,norm_smul]; exact (mul_le_mul (r _) (chorus_size K t m v) (norm_nonneg _) u).trans (by linarith)
 refine ⟨fun i=> ck (a i),ck b,⟨_,by exact show 0 < C+1 by positivity, hc C u y,Eventually.of_forall fun _=>hc C u (w _)⟩, fun e x=>?_⟩

 filter_upwards [p e x] with i h; intro m v; rw [Pi.sub_apply,Pi.sub_apply,note_v,note_v,←sub_smul,norm_smul]; exact (mul_le_mul (h _) (chorus_size K t m v) (norm_nonneg _) x.le).trans_eq (mul_one _)
end
