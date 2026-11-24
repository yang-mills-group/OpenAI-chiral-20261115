import YM.CF.BPress.Wealth.Levy
/-! eq:B-Mcost pricing. Mark-only scalar. use nonnegative pay per GEM even though real values can have either sign. sum via fullWeak and `eq:B-wn` for the connected support price. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}{G:Gauge}(X:Bands s b) (R:PathData G) (d:Clip)(p:BudgetPoint)(β:ℝ)(M:ℕ)
local notation "kCnt" => (Option Signed×PlaqAxes)
-- anchor prices per center. injection
def brand : Root s → kCnt:= Sum.elim (fun x=>(none,x.2)) fun ⟨a,x⟩=>(a,x.2)
lemma levyH_inj : Injective (fun x :Root s=> (central x, Wealth.brand x)) := by
 rintro (i|⟨a,i⟩) (j|⟨u,j⟩) h <;> obtain ⟨v,H⟩ := Prod.mk.inj h
 · exact congrArg _ (Prod.ext v ((Prod.mk.inj H).2))
 · have h: (none:Option Signed) = some u := (Prod.mk.inj H).1; cases h -- tune shadow
 · have h: (none:Option Signed) = some a := (Prod.mk.inj H).1.symm; cases h
 have f:a=u:= Option.some.inj (Prod.mk.inj H).1; subst u; exact congrArg (fun i=> Sum.inr (a,i)) (Prod.ext (a.act_injective v) (Prod.mk.inj H).2)
set_option maxRecDepth 4000 in
lemma count_H (h:1≤M)(i:X.Index) : (univ.filter (account X M i)).card ≤ (X.band i).card* Fintype.card kCnt:= by
 rw [←card_product (X.band i) (univ:Finset kCnt)|>.trans (show _=(X.band i).card*Fintype.card kCnt from (by rw [card_univ]))]; apply card_le_card_of_injOn (fun x=>(central x, Wealth.brand x)) (fun x v=>?_ ) levyH_inj.injOn; have hv: account X M i x:= (mem_filter.mp (mem_coe.mp v)).2; change (central x,Wealth.brand x)∈ X.band i ×ˢ (univ: Finset (Option Signed × PlaqAxes)); exact mem_product.mpr ⟨deposit_band X M h hv (central_mem M x |>.1),mem_univ _⟩
lemma GEM.sum {I:Type*} (t:Finset I) (f:I→ Config G s→ℝ) (b:I→ℝ) (S:Support s) (p:∀ i∈t,GEM S (f i) (b i)) : GEM S (fun x=> ∑ i∈t,f i x) (∑ i∈t,b i) := by
 induction t using Finset.induction_on with|empty=> simp_rw [sum_empty]; exact GEM.vac _ | insert i t ht ih=> simp_rw [sum_insert ht]; exact (p i (mem_insert_self ..)).plus (ih fun i k=>p _ (mem_insert_of_mem k))
lemma GEM.charges {S T:Support s}{f : Config G s→ℝ}{a b : ℝ}(p:GEM S f a)(t:S⊆T)(v:a≤b): GEM T f b:= ⟨p.zero.trans v,fun x=>(p.price x).trans v,p.meas,fun _ _ e=>p.loc _ _ (agrees_mono e t),p.inv⟩

def priceMark (C D:ℝ) (i:X.Index):=((X.band i).card:ℝ)*Fintype.card kCnt*(payC d β C)+ (X.band i).card*D
lemma pay_zero {C:ℝ} (β:ℝ)(p:0≤β): 0≤payC d β C:= by unfold payC; positivity [d.tail_pos,d.quadratic_pos,chPrice_pos]
lemma score_pos {x:Site s} {P:Support s}{a C:ℝ}{f: Support s→Config G s→ℝ}{K: Support s→ℝ}(p : Thinner f K a C): 0 ≤ score id K a x P:= (p.cash.hits x).1 P
lemma thinner_spending {f:Support s→ Config G s→ℝ}{K:Support s→ℝ}{a D:ℝ}(h:Thinner f K a D)(p:0≤a)(S : Finset (Support s))(T:Support s)(f:∀ P∈S,P.Nonempty∧P⊆T): (∑ X∈S,K X) ≤ (T.card:ℝ)*D:=by
 let v(X:Support s)(o:Site s):= score id K a o X; have he (P) (u:P∈S) : K P ≤ ∑ o∈T,v P o:= by
    obtain ⟨x,w⟩:= (f P u).1; refine le_trans (b:= Real.exp (a*P.card)*K P) (le_mul_of_one_le_left (h.cash.pos _) (exp_one P a p)) ?_; exact le_trans (b:=v P x) (Eq.le (if_pos w|>.symm)) (single_le_sum (f:=v P) (fun i _=>(h.cash.hits i).1 P) ((f P u).2 w))
 apply le_trans (sum_le_sum he); rw [sum_comm]; refine le_trans (sum_le_sum (g:=fun _=>D) fun i _=> budget_sum (h.cash.hits i) _) ?_; simp
lemma realMarks {σ C Λ a D:ℝ} (v: Thinner (s:=s) (totalWeak d R p β M) (fullWeak R p β M) a D)(x: Checks M p d)(t:R.Bounds d σ C Λ)(g:0≤a)(h:1≤M)(e:0≤β)(i:X.Index) : GEM (X.band i) (levy X R d p β M i) (priceMark X d β C D i):=by
 let S:= univ.filter (account X M i); have hp : GEM (X.band i) (bandH X R d p β M i) (↑(X.band i).card*Fintype.card kCnt*payC d β C):=by
    apply GEM.charges (S:=X.band i) (p:= (GEM.sum S (f:= heavy R d p β M) (fun _=>payC d β C) (X.band i) (fun j l=> (merit R d p β M t x e j|>.1).charges (deposit_band X M h ((mem_filter.mp l).2)) le_rfl))) (Subset.refl _); rw [sum_const,nsmul_eq_mul]; gcongr; exact pay_zero d β e; exact_mod_cast count_H X M h i
 refine hp.plus (GEM.charges (S:=X.band i) ?_ (Subset.refl _) (thinner_spending v g (univ.filter (oneWeak X i)) (X.band i) (fun j k=>(mem_filter.mp k).2)))
 exact GEM.sum _ _ _ _ (fun j h=> (v.unit j).charges (show oneWeak X i j from (mem_filter.mp h).2).2 le_rfl) -- tune

open Pressure
-- for cost purchases, t-dependent ≤power(y). requires only lower on x. return fixed power bound with multiplier + choose loosen later.
lemma income (W:GapSize)(C:ℝ)(R:ℝ→ℝ)(p:NPL R) : ∃ K:ℝ,0<K∧∀ᶠ y:ℝ in atTop, ∀ s:Side,∀ X:Bands s (W.select y),∀ (β:ℝ), β∈Set.Icc (y/2) (2*y) → ∀ i:X.Index, priceMark X d β C (R y) i ≤ K*y^2*(s.val:ℝ)^3 :=by
 let P:= payC d 2 C; have hp:0≤ P:= pay_zero d 2 (by norm_num); let N:ℝ:= Fintype.card kCnt; have hn:0≤ N:= Nat.cast_nonneg _; refine ⟨4*(N*P+1),by positivity,?_ ⟩; filter_upwards [W.bound_y,p.drop.eventually (ge_mem_nhds zero_lt_one),eventually_ge_atTop (1:ℝ)] with y t u h s X β e i
 have g:0≤β:=le_trans (by positivity : 0≤ y/2) e.1; let w:=(X.band i).card; have he: (w:ℝ) ≤ 4*y*(s.val:ℝ)^3:=by
    let z:=W.select y; unfold w; rw [X.band_card]; push_cast; apply mul_le_mul_of_nonneg_right ?_ (by positivity); have k:=t; change (z.P:ℝ)≤ _ at k; have hv:(z.marked.val:ℝ) ≤ z.P:= Nat.cast_le.mpr (by unfold BandWidth.P; omega); change (z.marked.val:ℝ)+1≤_; linarith
 have hv: payC d β C ≤ y*P:=by
    refine le_trans ?_ (le_of_eq (show payC d (2*y) C=y*P by unfold P payC; ring)); unfold payC; have hh:= e.2; gcongr <;> positivity [d.quadratic_pos,d.tail_pos,chPrice_pos]
 change (w:ℝ)*N*_+(w:ℝ)*_≤_; calc
   _ ≤ 4*y*(s.val:ℝ)^3*N*(y*P)+4*y*(s.val:ℝ)^3*1:= by
      exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right he hn) hv (pay_zero d _ g) (by positivity)) ((mul_le_mul_of_nonneg_left u (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right he zero_le_one))
   _ ≤ _:=by nlinarith only [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 4*y*(s.val:ℝ)^3)]
end YM.CF.BPress.Wealth
