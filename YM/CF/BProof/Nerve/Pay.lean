import YM.CF.BProof.Nerve.Vote
/-! Use weighted Voronoi gaps instead of Delaunay lemma. This surrogate has
 dimension-4 *abstract simplices of barycentric weights*, used only in making
 the Basic maps. No eta' for other distances needed: can use any MinAbs tie lift beyond.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4800
set_option maxHeartbeats 780000
noncomputable section
namespace YM.CF.BProof.Mesh.Nerve
open Lattice Function Finset Equiv Regard Rows Sleet
open scoped BigOperators Classical
variable {n:Side}{C A:Type*}{s z l k R d:ℕ}
namespace Pie
open Guard
variable {U : Field n A Prop}{g:Field n A (Fin z)}{F:Field n A ℝ}
local notation "Xκ"=>Site n
local notation "Y_"=> supporters U F s z
local notation "π↑"=>valueU s U F z
local notation "γ"=>alpha z
local notation "Voc"=>SmallN s n
local notation "Fσ"=>stageD U g s z
variable (D:Birthday s U F)
-- hypothesis for tie count
abbrev Lustre (U:Field n A Prop)(F:Field n A ℝ)(s z:ℕ) : Prop:= ∀ w X, Test (crowd U w) s X→ slip z z/6 ≤|Drift s X (F w)|
variable (L:Lustre U F s z)(h:2 * press s < alpha z)(t:SmallN s n)(p: 0<s)
include D L h t p
lemma quint (w:A)(x y:Xκ)(d: separation x y≤ 1): let V:= (supporters U F s z w x)∪supporters U F s z w y; V.card ≤ 5:=by
 intro V; have he(i:Xκ)(p':i∈V) : U w i∧soil s (F w) x i < rim s U F w x+2*alpha z :=by rcases mem_union.mp p' with p'|p'; exact bonds D p t w x x i (by simp) z h p'; exact bonds D p t w x y i d z h p'
 by_contra! ht; let Y:(Fin 6) ↪ V:= Classical.choice ((Function.Embedding.nonempty_of_card_le (by simpa using (show 5 +1 ≤ V.card from ht) : Fintype.card (Fin 6)≤Fintype.card V))) -- tune
 let X(i:Fin 6):= (Y i).val; have hp(i:Fin 6):= he _ (Y i).2; have hv(i):= stick D p w x _ (hp i).1 (hp i).2; let S:=crowd U w; have hQ(i):separation (X i) x ≤ Halo*s:= separation_comm .. ▸ (hv i).1; have P: Test (crowd U w) s X:=⟨Subtype.val_injective.comp Y.injective, fun i=> (Sleet.crowd_in ..).2 (hp i).1,fun i j=> (separation_triangle (X i) x (X j)).trans (by rw [two_mul]; exact Nat.add_le_add (hQ i) (hv j).1)⟩
 let W:= F w; let c:=wind X; let q:=rim s U F w x; let E(i:Fin 6):= soil s W x (X i); let a:=γ; let f(i:Fin 6):= c i*(E i-q); have ha:= (tiny z).1
 have hk(i):|f i|≤(4:ℝ)/3*2*a:=by
    let A:|E i-q|≤2*a:= abs_le.mpr ⟨by have ht:q≤E i:=rim_a _ _ (hp i).1; change _≤E i-_; unfold a; linarith, by have hx:E i < q+2*a:= (hp i).2; linarith⟩
    unfold f; rw [abs_mul]; refine ((mul_le_of_le_one_left (abs_nonneg _) ((permit X).2.2.1 i)).trans A).trans ?_; unfold a; linarith
 have hh:∑ i,f i= Drift s X W:=by
    apply Eq.trans _ (orbit_sum X W _ hQ t); unfold f c Mode; simp_rw [show ∀ i,E i= _ from (show ∀ i,E i=sizeD s (X i) x+W (X i) from fun i=>(hv i).2),mul_sub,sum_sub_distrib,←sum_mul,(permit X).1,zero_mul,sub_zero]
 have hg:|Drift s X W| ≤ 6*((4:ℝ)/3*2*a):=by rw [← hh]; exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=>hk i)).trans_eq (by simp))
 unfold a alpha at hg; linarith only [hg,(slip_pos z z),(L w X P : slip z z/6 ≤|Drift s X W|)] -- numerical 16/100 < 1/6

variable (U F s z) -- definitions, same param order depends declared earlier tune
-- weights global Fen; use cost normalization const
abbrev warm(w:A)(x:Site n) :ℝ:=∑ i,valueU s U F z w x i
def cent(w:A)(x y:Site n):ℝ:= valueU s U F z w x y / warm s z U F w x
variable {U F s z}
omit L p t h
lemma heat (w:A)(x:Xκ): alpha z ≤ warm s z U F w x:=by obtain ⟨i,h⟩:=seat (z:=z) D w x; exact h ▸ single_le_sum (fun i _=> (cash w x i).1) (mem_univ i)
lemma heat_pos(w:A)(x:Xκ):0 < warm s z U F w x:=(tiny z).1.trans_le (heat D w x)
local notation "ξ"=>cent s z U F
lemma material_p (w:A)(x:Xκ): (∀ i,0≤ξ w x i) ∧ ∑ i,ξ w x i=1:=⟨fun i=>div_nonneg (cash w x i).1 (heat_pos D w x).le,by simp only [cent, ←sum_div]; exact div_self (heat_pos D w x).ne'⟩
lemma cent_self (w:A)(x i:Xκ):i∈supporters U F s z w x↔ ξ w x i≠ 0:=by simp only [starP x i, cent,ne_eq,div_eq_zero_iff,(heat_pos D w x).ne',or_false]
lemma rt (w:A)(x:Xκ){p:Support n}(h:Y_ w x⊆ p) : ∑ i∈p,valueU s U F z w x i=warm s z U F w x:=by
 refine sum_subset (subset_univ _) ?_; intro i _ v; exact not_not.mp fun k=> v (h ((starP ..).2 k))
include h t p L
def rate(s z:ℕ):ℝ:= (20*press s)/(alpha z) -- want cap for normalized. heat diff ≤10 gap per neighbours. derive.
lemma visit(w:A)(x y:Xκ)(d: separation x y ≤1)(i :Xκ) : |ξ w x i-ξ w y i| ≤ rate s z:=by
 let X:=valueU s U F z w x; let Y:=valueU s U F z w y; let S:= supporters U F s z w x∪supporters U F s z w y; let p':= press s; let l:= warm s z U F w x; let k:=warm s z U F w y 
 have hx:|l-k|≤10*p':=by
    rw [← (show ∑ i∈S,X i =l from rt D _ _ subset_union_left),← (show ∑ i∈S,Y i=k from rt D _ _ subset_union_right), ←sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>2*p') (fun i _=>level D p t w x y i d)).trans ?_); rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (_: (S.card:ℝ) ≤ 5) (by unfold p' press; positivity)).trans_eq (by ring); exact_mod_cast (quint D L h t p w x y d : S.card≤5)
 have hk:= heat_pos (z:=z) D w y; have hl:= heat_pos (z:=z) D w x; have hu:0<l:=hl; have hg:0<k:=hk; let A:= alpha z; have ha:0<A:= (tiny z).1; have hX: Y i/k ≤ 1:= (div_le_one hg).mpr ((cash w y i).2.trans (heat D _ _)); have hY:0≤Y i/k:= div_nonneg (cash w y i).1 hg.le
 change |X i/l-Y i/k|≤_; rw [show X i /l-Y i/k=(X i-Y i)/l+Y i/k*((k-l)/l) from by field_simp; ring]; refine (abs_add_le ..).trans ?_; rw [abs_div,abs_mul,abs_of_nonneg hY,abs_div,abs_of_nonneg hu.le]; refine le_trans (b:=2*p'/A+10*p'/A) ?_ ?_
 · have e:A≤l:= heat D w x; exact add_le_add (div_le_div₀ (by unfold p' press; positivity) (level D p t w x y i d) ha e) ((mul_le_of_le_one_left (by positivity) hX).trans (div_le_div₀ (by unfold p' press; positivity) ((abs_sub_comm l k) ▸ hx) ha e))
 rw [← add_div]; apply div_le_div_of_nonneg_right _ ha.le; have hr:0 ≤ p':=by unfold p' press; positivity
 change _≤20*p'; linarith
end Pie
end YM.CF.BProof.Mesh.Nerve
