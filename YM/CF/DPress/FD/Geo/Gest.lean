import YM.CF.DPress.FD.Geo.Gene
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {q l m t w:ℕ} {i j:Site n}
namespace Geo
/- twice budget stagger, any later centre t can take its first legal choice. boundedly
 many exclusions per earlier centre. -/
abbrev Lag(l m a:ℕ):= 2*l+8*a*m
abbrev lng (b:Bool)(h:ℕ):ℤ:= if b then -h else h
lemma lng_v (b:Bool)(h:ℕ): lng (!b) h= - lng b h:=by cases b<;> simp [lng]
abbrev Ask:= Axis × Bool × Bool
def Fee(p:Ask)(i j:Site n)(a b x:ℕ):Prop:= 3*x < (pole i j p.1 + lng p.2.2 b - lng p.2.1 a).natAbs
abbrev Agree(m:ℕ)(i j:Site n)(t w:ℕ):Prop:=∀ p:Ask, Fee p i j t w m -- abbrev references private declaration? cannot later unfold Fee. expose
lemma fee_v (p:Axis)(a b:Bool)(h:close l i j)(q:2*s10 l<n.val): Fee (p,a,b) i j t w m ↔ Fee (p,b,a) j i w t m:=by
 unfold Fee; dsimp only; rw [poleV h q,Pi.neg_apply]; nth_rw 1 [show pole i j p+lng b w-lng a t= -(-pole i j p+lng a t-lng b w) from (by abel)]; rw [Int.natAbs_neg]
lemma agreeV (h:close l i j)(q:2*s10 l<n.val)(a:Agree m i j t w): Agree m j i w t:=by rintro ⟨p,x,y⟩; exact (fee_v p y x h q).1 (a _)
lemma agree_rot (h:close l i j)(q:2*s10 l<n.val)(s:Signed)(x:Site n): Agree m (aura s x i) (aura s x j) t w ↔ Agree m i j t w:=by
 let sP (b:Bool)(t:Axis):= if s.flip t then !b else b;
 have he (p:Axis)(a b:Bool): Fee (s.perm p,a,b) (aura s x i) (aura s x j) t w m ↔ Fee (p,sP a p,sP b p) i j t w m:=by
   unfold Fee; dsimp only; rw [pole_s h q s x,Signed.act_at]; unfold sP; split; next hf=> rw [lng_v,lng_v,show - (pole i j p)+lng b w-lng a t= -(pole i j p + - lng b w - - lng a t) from (by abel),Int.natAbs_neg]
   next hf=> rfl
 constructor
 · intro v ⟨p,a,b⟩; have hp (a: Bool) : sP (sP a p) p=a:=by unfold sP; by_cases v:(s.flip p)=true <;> simp [v];
   let ha: Fee (p,sP (sP a p) p,sP (sP b p) p) i j t w m := (he p (sP a p) (sP b p)).1 (v _); simpa only [hp] using ha
 intro v ⟨p,a,b⟩; obtain ⟨j,rfl⟩:= s.perm.surjective p; exact (he j a b).2 (v _)
private lemma v8(p:0<m){i j:ℕ}(h:i<j): Lag l m i+7*m≤ Lag l m j:=by unfold Lag; have ht:8*(i+1)≤8*j:= Nat.mul_le_mul_left 8 h; have he:= Nat.mul_le_mul_right m ht; rw [mul_add,mul_one,add_mul] at he; omega
private lemma part (v:0<m)(p:Ask)(x y:ℕ)(h:x<y)(hx:¬ Fee p i j (Lag l m x) t m)(hy:¬ Fee p i j (Lag l m y) t m):False:=by
 unfold Fee at *; have he:= v8 (l:=l) v h; cases p with|mk p s=> cases s with|mk a b=> cases a <;> cases b <;> dsimp only [lng] at hx hy<;> omega
-- Use natural parameter k for # of prior centres permissible via pack bound, prevent stuck reduction on the constants
abbrev Wide (k m l:ℕ):Prop := 8*(k*Fintype.card Ask)*m ≤ l
lemma loan (k:ℕ)(v:0<m)(t:Wide k m l) (D: Support n) (p:D.card≤k)(f: Site n→ℕ)(i: Site n):∃ s:ℕ, 2*l≤s ∧ s≤4*l ∧ ∀ j∈D, Agree m i j s (f j):=by
 let S:=D×ˢ (univ:Finset Ask); let R:=range (k*Fintype.card Ask+1); let hull(p:Site n×Ask):=R.filter fun x=> ¬ Fee p.2 i p.1 (Lag l m x) (f p.1) m
 have ht(p:Site n×Ask): (hull p).card≤1:=card_le_one.mpr (fun a ha b hb=> Classical.byContradiction fun q=> by
    have ht:¬ Fee p.2 _ _ _ _ m:= (mem_filter.mp ha).2; have hu:=(mem_filter.mp hb).2; rcases lt_or_gt_of_ne q with h|h; exact part v _ a b h ht hu; exact part v _ b a h hu ht)
 have hc: (S.biUnion hull).card≤∑ i∈S,(hull i).card:= card_biUnion_le
 have hh:(S.biUnion hull).card<R.card:=by
    unfold R; rw [card_range]; apply lt_of_le_of_lt hc; apply lt_of_le_of_lt (sum_le_sum (show ∀ p∈ S,(hull p).card≤1 from (fun p _=>ht p))); unfold S; simp; exact p -- tune
 obtain ⟨x,w,u⟩:= exists_mem_notMem_of_card_lt_card hh; refine ⟨Lag l m x,Nat.le_add_right ..,?_,?_⟩
 · have hp:x≤ k*Fintype.card Ask:= Nat.le_of_lt_succ ((mem_range).1 w); unfold Lag; have he:= Nat.mul_le_mul_right m (Nat.mul_le_mul_left 8 hp); unfold Wide at t; omega
 intro j y p; by_contra q; exact u (mem_biUnion.mpr ⟨(j,p),mem_product.mpr ⟨y,mem_univ _⟩,mem_filter.mpr ⟨w,q⟩⟩)
end Geo
end YM.CF.DPress.FD
