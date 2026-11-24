import YM.CF.Broc.Coin
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Y Z D E G H: Type*} [Fintype Y][Fintype Z][DecidableEq Y][DecidableEq Z][TopologicalSpace D][TopologicalSpace E]
structure Exceed {Y Z:Type*}[Fintype Y][Fintype Z][DecidableEq Y][DecidableEq Z] (b:Branch.Field Y) (c: Branch.Field Z) (F:Seal Y→ Seal Z)(v w:ℝ):Prop where
 plus : ∀ {S}, Grove b S→ Grove c (F S)
 band : ∀ {S}, Grove b S → ((F S).card:ℝ) ≤ v*S.card
 coverage (z:Z): ∃ S: Seal Y, (S.card:ℝ)≤ w∧ ∀ T:Seal Y,Grove b T→ z∈F T→∃ y∈S,y∈T
variable {b:Light Y D G}{c: Light Z E H}{Φ: Seal Y→ Seal Z}{v w a K q:ℝ}
lemma gossip(K:Seal Y→ℝ)(h: Exceed b.frame c.frame Φ v w)(X:Seal Y→E→ℂ)(e:∀ i,Peak c (Φ i) (X i) (K i))(p:ℝ)(g:0≤p)(L:E→ℂ)(u:∀ x,L x=∑ i,X i x)(hq:0≤q)(hv:q*v≤a) (hp:∀ i, K i≠0→Grove b.frame i) (r:∀ i:Y,hitE a K i≤p): Seat c L q (w*p):=by
 let W(T:Seal Z):=dest Φ T; let k(T:Seal Z):= ∑ i∈ W T,K i
 have he(T): Peak c T (fun t=>∑ i∈W T, X i t) (k T):= Peak.collects _ _ _ (fun i h=> by rw [←show Φ i=T from (mem_filter.mp (show _ from h)).2]; exact e i)
 refine ⟨_,k,⟨he,fun i=>?_⟩, fun x=> (u x).trans (lump ..)⟩
 obtain ⟨z,hz,hl⟩:= h.coverage i; let f(S:Seal Y):=if i∈Φ S then Branch.rent q (Φ S)*K S else 0
 have hh : hitE q k i=∑ S,f S:=by
   rw [lump Φ f]; unfold hitE hit0; rw [sum_filter]; apply sum_congr rfl; intro t _; unfold k; rw [mul_sum]; unfold W; by_cases hx:i∈t
   · rw [if_pos hx]; exact sum_congr rfl fun b he=> by unfold f; rw [(mem_filter.mp he).2,if_pos hx]
   rw [if_neg hx,sum_eq_zero]; intro z h; unfold f; rw [(mem_filter.mp h).2,if_neg hx]
 have hm(y:Y): hitE a K y=∑ S, if y∈S then Branch.rent a S*K S else 0:=Finset.sum_filter ..
 rw [hh]; apply le_trans _ (show ∑ y∈z,hitE a K y≤ w*p from (sum_le_sum fun y (_:y∈z)=> r y).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hz g)); simp_rw [hm]; rw [Finset.sum_comm]
 apply sum_le_sum; intro S _; have ht(y:Y):0≤(if y∈S then Branch.rent a S*K S else 0):=by split; exact mul_nonneg (rent_pos ..).le (e _).pos; rfl
 unfold f; split_ifs with k
 · by_cases he:K S=0; rw [he,mul_zero]; simpa only [←he] using (sum_nonneg (fun y _=> ht y) : 0≤∑ y∈z,if y∈S then Branch.rent a S*K S else 0)
   have hK:= hp S he; obtain ⟨y,z,Y⟩:=hl S hK k
   apply le_trans _ (single_le_sum (f:=fun y=> if y∈S then Branch.rent a S*K S else 0) (fun y _=>ht y) z); rw [if_pos Y]
   apply mul_le_mul_of_nonneg_right _ (e _).pos; exact Real.exp_monotone ( (mul_le_mul_of_nonneg_left (h.band hK) hq).trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hv (by positivity)))
 exact sum_nonneg (fun y _=>ht y)
lemma Seat.shop (h:Exceed b.frame c.frame Φ v w) {X:D→ℂ}(p:Seat b X a K)(d:E→D)(e:Continuous d)(y: 0≤K)(s:0≤q)(l:q*v≤a)
   (g:∀ S x z,c.rel (Φ S) x z→ b.rel S (d x) (d z))(f:∀ x y,∃ g':G,d (c.dress y x)=b.dress g' (d x)): Seat c (X ∘ d) q (w*K):=by
 obtain ⟨M,k,P,hB⟩:=p
 apply gossip k h (fun S=> (M S) ∘ d) _ K y _ (fun x=> hB (d x)) s l (fun i =>(P.ordered i).travel) (fun y=>P.pays y); intro i; have he:= P.ordered i; exact ⟨he.pos,fun v=>h.plus (he.travel v),he.cont.comp e,fun x=>he.sumline _,fun x y h=> he.reads _ _ (g i x y h),fun x y=>by obtain ⟨g,h⟩:=f x y; simp only [comp_apply,h,he.gauge]⟩
-- alt namespace collision `shop`.
end YM.CF.Broc
