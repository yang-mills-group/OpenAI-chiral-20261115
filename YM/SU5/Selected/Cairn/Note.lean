import YM.SU5.Selected.Cairn.North
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz Rubric Stencil
open Commission
open Afterglow Tower Tower.SlabMark Tapestry
attribute [local instance] opCStarAlgebra
namespace Torrent
-- grid arithmetic any 5 near-zero cannot cover both.
abbrev chord(u:ℕ)(a b c:ℂ):= a+(u:ℂ)*b+(u:ℂ)*(u:ℂ)*c
abbrev fare : ℝ:= (100:ℝ)⁻¹
lemma fare_p:0<fare:= by unfold fare; positivity
private def weightL(u v w:ℕ):ℂ:=(((u:ℂ)-v)*((u:ℂ)-w))⁻¹
private lemma weight_d(u v:ℕ)(h:u≠v): 1 ≤ ‖(u:ℂ)-v‖:=by
 obtain a|a:=Nat.lt_or_gt_of_ne h
 · rw [norm_sub_rev]; apply le_trans _ (Complex.re_le_norm _); simp [Complex.sub_re]; exact_mod_cast (show (1:ℤ)≤ v-(u:ℤ) from by omega) -- maybe simp field
 apply le_trans _ (Complex.re_le_norm _); simp [Complex.sub_re]; exact_mod_cast (show (1:ℤ)≤ (u:ℤ)-v from by omega)
variable {u v w:ℕ} {a b c:ℂ} (hu:u≠v)(hv:v≠w)(hw:w≠u)
private lemma wt (hu:u≠v)(hw:u≠w) (p:‖chord u a b c‖≤fare) : ‖weightL u v w * chord u a b c‖≤fare:=by
 rw [norm_mul]; apply le_trans (mul_le_mul (b:=(1:ℝ)) _ p (norm_nonneg _) (zero_le_one)) ; · rw [one_mul]
 unfold weightL; rw [norm_inv]; apply inv_le_one_of_one_le₀; rw [norm_mul]; exact one_le_mul_of_one_le_of_one_le (weight_d _ _ hu) (weight_d _ _ hw)
private lemma wv (hu:u≠v)(hw:u≠w)(hv':v<5)(hw':w<5) (p:‖chord u a b c‖ ≤fare) : ‖(v:ℂ)*((w:ℂ)*(weightL u v w*chord u a b c))‖ ≤4*(4*fare):=by
 simp only [norm_mul (v:ℂ),norm_mul (w:ℂ),Complex.norm_natCast]; have hp:(v:ℝ)≤ 4:=by exact_mod_cast (Nat.le_of_lt_succ hv')
 have h':(w:ℝ) ≤4:=by exact_mod_cast (Nat.le_of_lt_succ hw')
 exact mul_le_mul hp (mul_le_mul h' (wt hu hw p) (norm_nonneg _) (by norm_num)) (by positivity) (by norm_num)
-- algebraic interpolation tests
private lemma approx_cancel(x y:ℕ)(p:x≠ y): (x:ℂ)-y≠0:= sub_ne_zero.mpr (by exact_mod_cast p)
include hu hv hw
private lemma choc (p:‖chord u a b c‖ ≤fare)(q:‖chord v a b c‖≤ fare)(t:‖chord w a b c‖ ≤ fare)(u':u<5)(v':v<5)(w':w<5): ‖a‖ ≤1 ∧ ‖c‖≤1:=by
 let f (z:ℕ):= chord z a b c; let x:= weightL u v w * f u; let y:= weightL v w u * f v; let z:=weightL w u v*f w; have ht:= approx_cancel u v hu; have hs:=approx_cancel v w hv; have hz:=approx_cancel w u hw
 have h': a= v*((w:ℂ)*x)+w*((u:ℂ)*y)+u*((v:ℂ)*z):=by unfold x y z f weightL chord; rw [show (u:ℂ)-w= -((w:ℂ)-u) from (neg_sub ..).symm, show (v:ℂ)-u= -((u:ℂ)-v) from (neg_sub ..).symm, show (w:ℂ)-v= -((v:ℂ)-w) from (neg_sub ..).symm]; field_simp; ring
 have he:c=x+y+z:=by unfold x y z f weightL chord; rw [show (u:ℂ)-w= -((w:ℂ)-u) from (neg_sub ..).symm, show (v:ℂ)-u= -((u:ℂ)-v) from (neg_sub ..).symm, show (w:ℂ)-v= -((v:ℂ)-w) from (neg_sub ..).symm]; field_simp; ring
 constructor
 · have h₁: ‖(v:ℂ)*((w:ℂ)*x)‖≤_:= wv hu (Ne.symm hw) v' w' p; have h₂: ‖(w:ℂ)*((u:ℂ)*y)‖ ≤ _:= wv hv (Ne.symm hu) w' u' q; have h₃: ‖(u:ℂ)*((v:ℂ)*z)‖ ≤ _:= wv hw (Ne.symm hv) u' v' t; rw [h']; apply le_trans ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h₁ h₂)) h₃)); unfold fare; norm_num
 have h₁: ‖x‖ ≤ _:= wt hu (Ne.symm hw) p; have h₂: ‖y‖ ≤ _:= wt hv (Ne.symm hu) q; have h₃: ‖z‖ ≤ _:= wt hw (Ne.symm hv) t; rw [he]; apply le_trans ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h₁ h₂)) h₃)); unfold fare; norm_num
omit hu hv hw
private def wash(a b c:ℂ):= (range 5).filter fun i=> ‖chord i a b c‖≤ fare
private lemma washes (p:1< ‖a‖ ∨ 1 < ‖c‖): (wash a b c).card ≤2:=by
 let S:= wash a b c; by_contra! h; have hu : 2<S.card:= h; obtain ⟨i,e⟩:= Finset.card_pos.mp (lt_trans (by norm_num:0<2) hu)
 have hj:1< (S.erase i).card:=by rw [card_erase_of_mem e]; omega
 obtain ⟨j,v,k,w,t⟩:= Finset.one_lt_card.mp hj
 obtain ⟨h',v⟩:=mem_erase.mp v; obtain ⟨hw,w⟩:=mem_erase.mp w; let H':= choc (b:=b) h'.symm t hw (mem_filter.mp e).2 (mem_filter.mp v).2 (mem_filter.mp w).2 (mem_range.mp (mem_filter.mp e).1) (mem_range.mp (mem_filter.mp v).1) (mem_range.mp (mem_filter.mp w).1); exact p.elim (fun p=> p.not_ge H'.1) (fun p=> p.not_ge H'.2)
theorem peacocks(a b c a' b' c':ℂ)(p:1<‖a‖)(v:1<‖c'‖): ∃ i<5, fare< ‖chord i a b c‖∧fare< ‖chord i a' b' c'‖:=by
 let S:=wash a b c; let T:=wash a' b' c'
 have ht : (S∪T).card < (range 5).card:= by rw [card_range]; exact ((card_union_le ..).trans (add_le_add (washes (.inl p)) (washes (.inr v)))).trans_lt (by decide)
 obtain ⟨i,h,e⟩:= exists_mem_notMem_of_card_lt_card ht; exact ⟨i,mem_range.mp h,lt_of_not_ge fun t=> e (mem_union_left _ (mem_filter.mpr ⟨h,t⟩)),lt_of_not_ge fun t=> e (mem_union_right _ (mem_filter.mpr ⟨h,t⟩))⟩ -- arg order
end Torrent
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Torrent
#print axioms peacocks
#check @peacocks
