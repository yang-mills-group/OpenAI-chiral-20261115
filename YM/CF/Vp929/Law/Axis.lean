import YM.CF.Vp929.Law.Stamina
import YM.CF.Vp929.Law.Stroll
import YM.CF.Mesa.Ties
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric
open scoped Topology Classical
namespace Rooms
open Mesa
variable {s t x:Rooms}{r K:ℕ}{C:Side}{i:Axis}{a b:Cover}
private def Len (x:Wall):ℝ:= x.b - (x.a:ℝ)
private def coord(x:Wall)(z:ℤ):ℝ:=2*((z:ℝ)-(x.a:ℝ))/Len x-1
private lemma len_pos {x:Wall}(p:x.win):0<Len x:=sub_pos.mpr (by exact_mod_cast p)
def arms (x:Rooms): Fin x.dim ≃ (x.doors) := (Fintype.equivOfCardEq (by rw [Fintype.card_fin,Fintype.card_coe]; rfl))
def deck (x:Rooms)(a:Cover): Mesa.Board x.dim := fun i=> coord (x (arms x i)) (a (arms x i))
private lemma posCoord {x:Wall}{z:ℤ}(v:x.win)(e:Wall.lone z ≤ x): |coord x z| ≤ 1:=by
 obtain ⟨r,k⟩:= Wall.seen e; unfold coord; let h:= len_pos v; rw [abs_le]; constructor <;> (field_simp; unfold Len; push_cast; first | linarith only [show (x.a:ℝ) ≤ z by exact_mod_cast r] | linarith only [show (z:ℝ) ≤ x.b by exact_mod_cast k])
private lemma endsCoord{x:Wall}{z:ℤ}(p:x.win)(e:x.tips z) : |coord x z|=1:=by cases e with | inl e=> subst z; simp [coord] | inr e=> subst z; unfold coord; rw [show (_:ℝ)-_=Len x from rfl,mul_div_cancel_right₀ _ (len_pos p).ne']; norm_num
private lemma atCoord{x:Wall}{z:ℤ}(p:x.win)(e:Wall.lone z ≤ x)(h:|coord x z|=1): x.tips z:=by
 unfold Wall.tips; unfold coord at h; let a:= len_pos p; obtain ⟨r,s⟩:=Wall.seen e
 by_contra! q; apply h.not_lt; rw [abs_lt]; constructor <;> (field_simp; unfold Len; push_cast; first | linarith only [show (x.a:ℝ)< z by exact_mod_cast (lt_of_le_of_ne r q.1)] | linarith only [show (z:ℝ)<x.b by exact_mod_cast (lt_of_le_of_ne s (Ne.symm q.2))])
lemma sail (e:here a ≤ x): deck x a∈ terrace _:= by rw [mem_closedBall,dist_pi_le_iff zero_le_one]; intro i; rw [Pi.zero_apply,Real.dist_eq,sub_zero]; exact posCoord (intro_door.1 (x.arms i).property) (e _)
lemma sail_peri (p:(here a).boundary x):deck x a∈ Peri _:=by
 obtain ⟨i,h,v,x₁,x₂⟩:= bound_edge p; let j:= x.arms.symm ⟨i,intro_door.mpr h⟩; have he:deck x a j=coord (x i) v:=by have eq:a i=v:= congrArg Wall.a x₁; simp [deck,j,eq]
 apply le_antisymm (show _ from sail p.1); exact le_trans (le_of_eq (b:=dist (deck x a j) ((0:Board _) j)) (by rw [Pi.zero_apply,Real.dist_eq,sub_zero,he]; exact (endsCoord h x₂).symm)) (dist_le_pi_dist _ _ _)
private lemma coordDist {a:Wall}(h:a.win)(x y:ℤ) : dist (coord a x) (coord a y) = 2*((x-y).natAbs:ℝ)/Len a:=by
 unfold coord; simp only [Real.dist_eq, sub_sub_sub_cancel_right,←sub_div,←mul_sub,sub_sub_sub_cancel_right,abs_div,abs_of_pos (len_pos h),abs_mul]; rw [abs_of_pos (show (0:ℝ)<2 by norm_num),← Int.cast_sub, ← Int.cast_abs, ←Int.natCast_natAbs]; rw [Int.cast_natCast]
lemma adjacent (h:Wide C.val x) {i:Axis}{a b:Cover} (q: Range 1 a b): dist (deck x a) (deck x b) ≤ 2/(C.val:ℝ) :=by
 refine (dist_pi_le_iff (by positivity)).2 fun i=>?_ ; let j:=(x.arms i).val; have hq:j∈ x.doors:=(x.arms i).property; change dist (coord _ _) (coord _ _)≤_; rw [coordDist (intro_door.1 (x.arms i).property)]; have ht:C.val ≤ Len (x j):=by unfold Len; exact (le_sub_iff_add_le').mpr (by exact_mod_cast (h j hq))
 have he: (0:ℝ)< C.val:=(by positivity); change 2*(((a j-b j).natAbs:ℕ):ℝ)/ Len (x j) ≤ _; apply (div_le_div_iff₀ (he.trans_le ht) he).2; nlinarith only [ht,show (((a j-b j).natAbs:ℕ):ℝ) ≤ 1 by exact_mod_cast (q j),he]
lemma taxDeck {B:ℕ} (e:x.bounded (B*C.val))(h:here a ≤ x)(q:here b ≤ x)(i:Axis):((a i-b i).natAbs:ℝ) ≤ dist (deck x a) (deck x b)*(B*C.val):=by
 by_cases v:(x i).win
 · have f:= v; obtain ⟨j,eq⟩:= (x.arms).surjective ⟨i, intro_door.2 v⟩
   have he:Len (x i) ≤ B*C.val:=by rw [Len,sub_le_iff_le_add]; exact_mod_cast (by have h:=e i; norm_cast at *; omega : (x i).b ≤ ↑(B*C.val)+ (x i).a)
   have k:= dist_le_pi_dist (deck x a) (deck x b) j; unfold deck at k; rw [eq] at k; change dist (coord (x i) _) (coord (x i) _)≤_ at k; rw [coordDist v,div_le_iff₀ (len_pos v)] at k; change 2* ((a i-b i).natAbs:ℝ) ≤ dist (deck x a) (deck x b) * _ at k
   let V:= dist (deck x a) (deck x b); nlinarith [mul_le_mul_of_nonneg_left he (show 0≤ V from dist_nonneg),show 0 ≤ ((a i-b i).natAbs:ℝ) from Nat.cast_nonneg _]
 have eq:a i=b i:=by have f:= (Wall.stay v (h i)).trans (Wall.stay v (q i)).symm; exact congrArg Wall.a f
 rw [eq]; simpa using (show 0≤ dist (deck x a) (deck x b)*((B:ℝ)*C.val) from by positivity)
lemma deckInj (B:ℕ)(e:x.bounded (B*C.val)): Set.InjOn (deck x) x.marks:= by
 intros a p b q h; funext i; have ht:=taxDeck e p q i; rw [h,dist_self,zero_mul] at ht; have ht:(a i-b i).natAbs ≤ 0:=(by exact_mod_cast ht); omega
private lemma sampleAxis (R:Wall) (t:Wall.win R) (p:R.a+C.val ≤ R.b)(z:ℝ)(v:|z|≤1): ∃ m:ℤ, Wall.lone m ≤ R∧ |z-coord R m| ≤ 2/(C.val:ℝ)∧(|z|=1→ R.tips m):=by
 let h:= len_pos t; let H: (C.val:ℝ) ≤ Len R:= by unfold Len; exact (le_sub_iff_add_le').mpr (by exact_mod_cast p)
 let x:= R.a+ Len R*((z+1)/2); have hb: (R.a:ℝ)≤ x ∧ x ≤ (R.b:ℝ):=by
    obtain l:= abs_le.mp v; unfold x; let g:= Len R; have he:g= (R.b:ℝ)-R.a:=rfl; constructor <;> nlinarith
 rcases eq_or_ne z 1 with zQ|zQ
 · subst z; exact ⟨R.b,Wall.tipBox (Or.inr rfl),(by change |1-(2*Len R/Len R-1)| ≤ _; rw [mul_div_cancel_right₀ _ h.ne']; have e: 0 ≤ 2/(C.val:ℝ):=(by positivity); norm_num; positivity),fun _=>Or.inr rfl⟩
 rcases eq_or_ne z (-1) with z|zT; · subst z; exact ⟨R.a,Wall.tipBox (Or.inl rfl),by simpa [coord] using (show 0 ≤ 2/(C.val:ℝ) from by positivity),fun _=> Or.inl rfl⟩
 let m:= Int.floor x; have l : Wall.lone m ≤ R:= ⟨Int.le_floor.mpr hb.1,(by change Int.floor _ ≤ _; exact_mod_cast (Int.floor_le x).trans hb.2) ⟩
 let p:0 < (C.val:ℝ):=by positivity
 refine ⟨m,l,?_ ,fun w=>?_⟩
 · apply le_trans _ (show 2/Len R≤_ from div_le_div_of_nonneg_left (by norm_num) p H)
   have h0: (m:ℝ) ≤ x:= Int.floor_le x; have h1:x < (m:ℝ)+1:= Int.lt_floor_add_one _; rw [abs_le]; unfold x at h0 h1; unfold coord; constructor <;> field_simp <;> linarith
 cases abs_cases z with | inl u=> exact (zQ (by linarith [u.1])).elim | inr u=> exact (zT (by linarith [u.1])).elim
lemma followsRim (p:here a≤ x) (t:deck x a∈ Peri _):∃ i∈ x.doors,(x i).tips (a i):=by
 by_contra! q; apply (mem_sphere.mp t).not_lt; refine (dist_pi_lt_iff zero_lt_one).mpr (fun i=>?_) ; rw [Pi.zero_apply,Real.dist_eq,sub_zero]; apply lt_of_le_of_ne (posCoord (intro_door.1 (x.arms i).property) (p ((x.arms i).val))); exact fun h=> q _ (x.arms i).property (atCoord (intro_door.1 (x.arms i).property) (p _) h)
lemma deckNet (p:Wide C.val x)(v:Board x.dim)(e:v∈ Peri _):∃ a:Cover, (here a).boundary x ∧ dist v (deck x a) ≤ 2/(C.val:ℝ):=by
 have l(i:Fin x.dim): |v i|≤ 1:= by simpa [Peri,mem_sphere] using (dist_pi_le_iff (f:=v) (g:=(0:Board x.dim)) zero_le_one).mp ((show dist v 0=1 from e).le) i
 choose w t u g using fun i:Fin x.dim=> sampleAxis (x (arms x i)) (intro_door.1 (arms x i).property) (p _ (arms x i).property) _ (l i)
 let A:Cover:=fun j=>if p:j∈ x.doors then w (x.arms.symm ⟨j,p⟩) else (x j).a
 have H(i:Fin x.dim): A (arms x i) = w i:=by simp [A]
 have r:here A ≤ x:=by
    intro j; by_cases t':j∈ x.doors; obtain ⟨i,u⟩:= (x.arms).surjective ⟨j,t'⟩; have hx:= t i; rw [←H i,u] at hx; exact hx
    change Wall.lone (A j)≤ _; unfold A; rw [dif_neg t']; exact Wall.tipBox (Or.inl rfl)
 refine ⟨A, ⟨r,?_⟩,?_⟩
 · intro t; apply (mem_sphere.mp e).not_lt; refine (dist_pi_lt_iff zero_lt_one).mpr (fun i=>?_); rw [Pi.zero_apply,Real.dist_eq,sub_zero]; apply lt_of_le_of_ne (l i); intro e; exact Wall.boundaryOut (intro_door.mp (arms x i).property) (show (x (arms x i)).tips (A (arms x i)) from (H i).symm ▸ g i e) (show ¬ (here A (arms x i)).win from lt_irrefl _) (t _)
 rw [dist_pi_le_iff (by positivity)]; intro i; unfold deck; rw [H i,Real.dist_eq]; exact u i
end Rooms
end YM.CF.VolumeCape
