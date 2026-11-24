import YM.CF.Spark.Org
import YM.CF.Mint.Bier
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Phase.Sample Branch MeasureTheory RG Wilson WilsonStartup RP Nova Kea Ave Fock SU CF.Jet Broc Petal Spire Scroll Peaks Pastry Pic Sods Paige Vault Graph Dial Brace Mint Bloch Fir Ember Onyx
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B m N: Side}{e H a b c d v σ h Y w r:ℝ}{i j k n:ℕ}{O:Odd L.val}{T:Pricing j L O (Thread j)}{P:Grasp T B e}
local notation "n'"=>Domain m B
local notation "U'"=>Briar m B e
local notation "E'"=>Elf m B
local notation "M'"=>CSide m B
variable {f:ℕ→Side}{V:Pearl P}(F: Pic.Span V H b v c a r n)
def bean(f:ℕ→Side)(i:ℕ):ℝ:= (f i).val
def scarf(m:Side):=m.val^9
lemma tipsie {i: Side}(g:0<r)(z:Jill.Male)(j:ℕ): let b:=r*(Ember.pinch i)^2; Real.exp (-(b⁻¹)*Fintype.card (Stag i))≤ iceK j (Kea.too i) z r:=by
 intro b; let F:= Kea.too i; have hb:0<b:=mul_pos g (pow_pos (pinch_pos _) _); let y:= Real.exp (-(b⁻¹)); have hx:y≤b:=by
    unfold y; rw [Real.exp_neg]; nth_rw 2 [show b=b⁻¹⁻¹ by simp] -- tune
    apply inv_le_inv₀ (Real.exp_pos _) (by positivity)|>.mpr; calc
      _ ≤ b⁻¹+1 := by simp
      _ ≤ _:= Real.add_one_le_exp _
 have hY : Real.exp (-(b⁻¹)*Fintype.card (Stag i))= ∏ _x:Stag i,y:=by simp [← Real.exp_nat_mul,y,mul_comm]
 rw [hY]; exact Finset.prod_le_prod (fun _ _=>(Real.exp_pos _).le) (fun x _=>hx.trans (le_max_left ..))
-- volume polynomial log det lower
include F
lemma eyes :∃ D:ℝ,0<D ∧ ∀ m:Side,n≤ (CSide m B).val→ Real.exp (-D*(m.val:ℝ)^6) ≤ Kea.angel m P firstM:=by
 let X:ℝ:= 2*B.val; let r':=r* Real.pi^2; let i:ℝ:= Fintype.card SU.Slot
 have ht:0<X:=by unfold X; have h:B.val≥1:=B.property; positivity
 have hx:0<r':=by unfold r'; have h:=F.rP; positivity
 refine ⟨i*X^6/r', div_pos (by unfold i; positivity) hx,fun m p=>?_⟩
 let N:=CSide m B; rw [←F.fits m p firstM]; refine le_trans (le_of_eq ?_) (tipsie (i:=N) F.rP firstM _); congr 1; unfold i r' Ember.pinch; have he: (N.val:ℝ)=X*m.val:=by unfold X; change ((m.val*2*B.val:ℕ):ℝ)=_; push_cast; ring
 have hp:Fintype.card (Stag N)= N.val^4 * Fintype.card SU.Slot:=by rw [show Fintype.card (Stag N)= _ from (Fintype.card_prod (Site N) SU.Slot),site_card]
 have h:m.val>0:=m.property; have hv:=F.rP; have hy:=Real.pi_pos; rw [hp]; push_cast; rw [he]; field_simp
omit F
variable (g:Tendsto (bean f) atTop atTop)
include g
lemma ar_p (k:ℕ):∀ᶠ i in atTop,k≤(f i).val∧k ≤ (CSide (f i) B).val:=by
 filter_upwards [g.eventually_ge_atTop k] with i v; have he:k≤(f i).val:=by unfold bean at v; exact_mod_cast v
 exact ⟨he,he.trans (by change _ ≤ (f i).val*2*B.val; have hu:1≤ B.val:=B.property; nlinarith only [Nat.mul_le_mul_left ((f i).val*2) hu, show 0≤(f i).val by omega])⟩
lemma grid:Gray (bean f) fun i=> (CSide (f i) B).val:=by
 let Q(i:ℕ):ℝ:=(f i).val; have he(i): ((CSide (f i) B).val:ℝ)= (bean f i *2)* B.val:=by change (((f i).val*2*B.val:ℕ):ℝ)=_; unfold bean; push_cast; ring
 simp_rw [he]; exact ((Gray.arg g).mul (Gray.coef g 2)).mul (Gray.coef g _)
lemma grants: Gray (bean f) fun i=> Fintype.card (Site (Domain (f i) B)):=by
 have he(i): ((Domain (f i) B).val:ℝ) = ((CSide (f i) B).val:ℝ)*2:=by change (_:ℝ) = _; rw [show (Domain (f i) B).val = _ from natM (CSide (f i) B)]; push_cast; rfl -- tune
 simp_rw [site_card,Nat.cast_pow,he]; exact ((grid g).mul (Gray.coef g 2)).powG g 4 -- order
lemma indie: Gray (bean f) fun i=> Fintype.card (Index (f i)):=by
 have he(i): ((Fintype.card (Index (f i))):ℝ)= (bean f i *4)^4:=by
    change ((Fintype.card (Site (GridN (f i)))):ℝ)= _; rw [site_card]; change ((( (f i).val*2*2)^4:ℕ):ℝ)=_; push_cast; unfold bean; ring
 simp_rw [he]; exact ((Gray.arg g).mul (Gray.coef g _)).powG g 4
lemma costT (R:Reg 0 e B): Gray (bean f) fun i=> R.time (scarf (f i)):=by
 refine (((Gray.arg g).powG g 9).add g (Gray.coef g 1)).higher (Eventually.of_forall fun i=>?_); have he:= R.charges (scarf (f i)); change ‖R.time _‖≤_; rw [Real.norm_of_nonneg (show 0≤R.time _ from le_trans (Nat.cast_nonneg _) he.1.le)]; unfold bean; rw [← Nat.cast_pow]; exact he.2.le
lemma alive (R:Reg 0 e B)(h a c Y:ℝ)(l:0<h)(u:0<a): Aqua (bean f) fun i=> lid (f i) B h a (R.time (scarf (f i))) c Y:=by
 let X(A:ℝ)(B':ℕ→ℝ)(C:ℝ):=fun i=> rollerU A (B' i) C (f i); have he(A:ℝ)(B':ℕ→ℝ) (C:ℝ)(p:0<A)(h:Gray (bean f) B'):Aqua (bean f) (X A B' C):= (Aqua.exp_neg g A p).pays ((Gray.coef g 2).mul (h.mul (Gray.coef g C))) g
 exact ((he _ _ _ (half_pos l) (indie g)).panel ((he _ _ _ l (indie g)).fed (costT g R) g)).panel (he _ _ _ u (grants g))
omit g
lemma skiff_h (s m:Side)(d:0<σ):0 ≤ skiff m h σ k :=by unfold skiff; have hp:0≤Petal.bulk h 16:= tsum_nonneg fun i=>(by positivity); positivity
lemma helm (hp:0<c)(D:ℝ)(d:0<D) (u:ℝ):∃ x:ℝ,0<x ∧ ∀ y:ℝ,x≤y→ -c*y^9+D*y^6 ≤ -u*y:=by
 let k:=(D+max u 0+1)/c; have hk:0<k:=by have he:0≤ max u 0:=le_max_right ..; unfold k; positivity
 refine ⟨max k 2,hk.trans_le (le_max_left ..),fun y h=>?_⟩; have he:2≤y:=(le_max_right ..).trans h; have hr:(D+max u 0+1)≤ y*c:=(div_le_iff₀ hp).1 ((le_max_left ..).trans h); have ht:0≤ max u 0:=le_max_right ..; have hP:u≤ max u 0:=le_max_left ..
 have hx: (max u 0)*y ≤ (max u 0)*y^6:=mul_le_mul_of_nonneg_left (by exact le_self_pow₀ (by linarith) (by omega)) ht
 nlinarith only [hx,mul_le_mul_of_nonneg_right hr (show 0≤ y^6 by positivity),mul_le_mul_of_nonneg_right hP (show 0≤ y by linarith),mul_le_mul_of_nonneg_left (show y^7 ≤ y^9 from pow_le_pow_right₀ (by linarith) (by omega)) hp.le,show 0≤ y^6 by positivity]
include g
lemma fiscalX (D h:ℝ)(q:0<D)(l:0<σ)(w:σ<1): let f' i:= Real.exp (D*((f i).val:ℝ)^6); Aqua (bean f) (fun i=> skiff (f i) h σ (scarf (f i))* f' i):=by
 intro F; let L:=-Real.log σ; have hp:0<L:= neg_pos.mpr (Real.log_neg l w)
 let V(i):=σ^scarf (f i)*F i; have he(i):V i= Real.exp (-L*(bean f i)^9+D*(bean f i)^6):=by
    unfold V F bean scarf; unfold L; rw [Real.exp_add,neg_neg,mul_comm (Real.log _),← Nat.cast_pow, ← Nat.cast_pow,Real.exp_nat_mul,Real.exp_log l] -- tune
 obtain ⟨x,hx,H⟩:= helm hp D q 1
 have hy:Aqua (bean f) V := (Aqua.exp_neg g 1 one_pos).clip g ((g.eventually_ge_atTop x).mono fun i u=>⟨by rw [he]; positivity, (he i).trans_le (Real.exp_le_exp.mpr (H _ u))⟩)
 apply (hy.fed ((indie g).mul (Gray.coef g (Petal.bulk h 16*(1/3)))) g).changeA
 apply Eventually.of_forall; intro i; unfold skiff V; dsimp only; ring
include F
lemma kim (l:0<σ)(w:σ<1)(h:ℝ): Aqua (bean f) (fun i=> (Real.exp (skiff (f i) h σ (scarf (f i)))-1)/Kea.angel (f i) P firstM):=by
 obtain ⟨D,d,H⟩:=eyes F; let S(i):= skiff (f i) h σ (scarf (f i)); let B'(i):= Real.exp (D*((f i).val:ℝ)^6); have he:Aqua (bean f) fun i=> S i * B' i:= fiscalX g D h d l w; have hp(i):0 ≤ S i:= skiff_h 1 _ l
 have ht:= (he.clip g (F:=S) (Eventually.of_forall fun i=> ⟨hp i,le_mul_of_one_le_right (hp i) (Real.one_le_exp (by positivity))⟩)).shrinks
 refine (he.fed (Gray.coef g 2) g).clip g ?_; filter_upwards [ar_p (B:=B) g n,ht.eventually (ge_mem_nhds one_pos)] with i t y; let A:= Kea.angel (f i) P firstM; have hx:A ≥ (B' i)⁻¹:=(by unfold A B'; rw [←Real.exp_neg,←neg_mul]; exact H _ t.2); have hz:0<B' i:=Real.exp_pos _; have hy:0<A:=lt_of_lt_of_le (by positivity) hx
 change 0 ≤ (Real.exp _-1)/A ∧ _; refine ⟨div_nonneg (sub_nonneg.mpr (Real.one_le_exp (hp i))) hy.le,?_⟩; refine (div_le_iff₀ hy).mpr ((Pic.score (hp i) y).trans ?_); have hv: 1 ≤ B' i*A:=by rw [mul_comm]; apply (div_le_iff₀ hz).mp; rw [one_div]; exact hx
 refine (le_mul_of_one_le_right (mul_nonneg (show 0 ≤ (2:ℝ) by norm_num) (hp i)) hv).trans_eq (by ring)
end YM.CF.Spark
