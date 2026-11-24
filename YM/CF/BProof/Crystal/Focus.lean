import YM.CF.BProof.Crystal.Paint
import YM.CF.BProof.Moment.Priced
/-! rent price of decorations. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle Lattice Tenant Palot Gas Branch RG Push.AbsoluteSums
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I]{P:Dew V I}
variable {N:Side}
def puff(a:ℝ)(o y:Site N):= Real.exp (-a*separation o y)
def ppT(a:ℝ) (i:ℕ):= Real.exp (-a*i)*(16*((i:ℝ)+1)^4)
def puffPrice(a:ℝ):= ∑' i,ppT a i
lemma puffPrice_p {a:ℝ} :0 ≤ puffPrice a:=tsum_nonneg (fun i=> by unfold ppT; positivity)
lemma puff_price(a:ℝ)(h:0<a)(o:Site N): (∑ y,puff a o y)≤puffPrice a:=by
 let k:=univ.image (separation o); have hs:Summable (ppT a):= (fund_hit _ 16 (mul_pos (by norm_num) h : (0:ℝ)<2*a) (by norm_num)).congr (fun i=>by unfold ppT; ring_nf)
 refine le_trans ?_ (hs.sum_le_tsum k (fun i _=>by unfold ppT; positivity)); rw [←sum_fiberwise_of_maps_to (t:=k) (g:=separation o) (by intro i _; exact mem_image_of_mem _ (mem_univ _))]; -- tune
 apply sum_le_sum; intro i _; let X:Support N:=univ.filter (fun y=> separation o y=i); let m:=Real.exp (-a*i); change (∑ y∈X,puff a o y)≤_; rw [sum_congr rfl (g:=fun _=>m) (by intro y hy; unfold puff; rw [(mem_filter.mp hy).2]),sum_const,nsmul_eq_mul,mul_comm]; apply mul_le_mul_of_nonneg_left (le_trans ?_ (Tenant.reach o i)) (Real.exp_pos _).le; exact_mod_cast card_le_card (show X⊆ bay _ o i from fun y hy=>(bay_mem i).mpr (mem_filter.mp hy).2.le) -- tune
variable {f:I→I→Support N→ℝ}
def weight (f:I→I→Support N→ℝ)(i:I)(k:Prism I N):ℝ:= k.elim 1 (fun x=> if i<x.1 then f i x.1 x.2 else 0)
def light (f:I→I→Support N→ℝ)(r:ℝ)(i:I)(k:Prism I N):ℝ:= weight f i k*rent r (prism k)
namespace Civic
variable {p:Civic N P}{a α H:ℝ}
structure Bright (p:Civic N P)(f:I→I→Support N→ℝ)(a H:ℝ) : Prop where
 grave:∀ i j S,i<j→0≤f i j S
 lit:∀ i j S,i<j→f i j S ≠0 → Grove (terr _) S ∧ p.home i ∈S∧ p.home j∈S
 access(i:I):∑ j:I,∑ Y:Support N,(if i<j then f i j Y*rent a Y else 0)≤ H-1
lemma weightPositive(z:Bright p f a H)(i:I)(k:Prism I N):0≤weight f i k:=by cases k; exact zero_le_one; unfold weight; rw [Option.elim_some]; split; exact z.grave _ _ _ ‹_›; rfl -- tune
lemma totalLight (z:Bright p f a H)(i:I) : (∑ j:Prism I N,light f a i j)≤H:=by
 let G(i j:I):=∑ Y:Support N,(if i<j then f i j Y*rent a Y else 0); change (∑ k:Option (I×Support N),_)≤_; rw [Fintype.sum_option,Fintype.sum_prod_type]; apply le_trans (b:=1+(H-1)); swap; · exact le_of_eq (by ring)
 apply add_le_add; change 1*rent a (∅:Support N) ≤1; simp [rent]; simp_rw [light,prism,weight,Option.elim_some,ite_mul,zero_mul]; exact z.access i
def expense(w:V→ℝ)(f:I→I→Support N→ℝ)(i:Deco P N):ℝ:=w i.1*∏ j:P.Slots i.1,weight f j.val (i.2 j)
def costW(P:Dew V I)(w:V→ℝ)(H:ℝ)(i:V):ℝ:= w i*H^(P.line i).length
lemma meter(z:Bright p f a H){w:V→ℝ}(e:∀ i,0≤w i)(i:Deco P N):0≤expense w f i:=mul_nonneg (e _) (prod_nonneg (fun _ _=>weightPositive z ..))
lemma trackSkin(z:Bright p f a H){w:V→ℝ}(h:∀ i,w i≠0→ Grove (terr _) (p.zone i).val)(i:Deco P N)(t:expense w f i≠0) : Grove (terr N) (p.border i).val:=by
 have ht(j:P.Slots i.1):weight f j.val (i.2 j)≠0:=fun hx=> right_ne_zero_of_mul t (prod_eq_zero (mem_univ _) hx); have he:=h _ (left_ne_zero_of_mul t); unfold border skin; dsimp only; generalize (univ:Finset (P.Slots i.1))=Y; induction Y using Finset.induction_on with
 | empty=> simpa using he
 | insert x Y k ih=>
    let Q:= Y.biUnion fun j=>prism (i.2 j); let X:=(p.zone i.1).val; rw [biUnion_insert, union_left_comm (p.zone _).val, union_comm (prism (i.2 x))]; cases g:i.2 x with
    | none=> rw [show prism (none:Prism I N)=∅ from rfl,union_empty]; exact ih
    | some j=>
      have hp:=ht x; rw [g,weight,Option.elim_some] at hp; split at hp; rename_i y; · obtain ⟨c,d,e⟩:=z.lit _ _ _ y hp; exact ih.unite c (mem_union_left Q (p.belt _ _ x.property)) d -- tune
      contradiction -- indent
-- suppression
abbrev countB(i:Deco P N):ℝ:=∑ j:P.Slots i.1, (((prism (i.2 j)).card:ℕ):ℝ)
lemma border_pay (p:Civic N P)(i:Deco P N) : ((p.border i).val.card:ℝ) ≤ ((p.zone i.1).val.card:ℝ)+ countB i:=by
 have ht:((p.border i).val).card ≤ (p.zone i.1).val.card+∑ j:P.Slots i.1,(prism (i.2 j)).card := (card_union_le ..).trans (Nat.add_le_add_left (card_biUnion_le ..) _); exact_mod_cast ht -- maybe push unfolds
lemma origin_port{w:V→ℝ}(z:Bright p f a H)(i:Deco P N)(t:expense w f i≠0)(o:Site N)(h:o∈ (p.border i).val) : ∃ y∈(p.zone i.1).val,(separation o y:ℝ) ≤ countB i:=by
 have hx(j:P.Slots i.1): 0≤(((prism (i.2 j)).card:ℕ):ℝ):= by positivity
 rcases mem_union.mp h with h|h; exact ⟨o,h,by simpa only [separation_self,Nat.cast_zero] using (sum_nonneg (fun i _=> hx i))⟩
 obtain ⟨j,_,u⟩:=mem_biUnion.mp h; have ht:weight f j.val (i.2 j)≠0:=fun hx=>right_ne_zero_of_mul t (prod_eq_zero (mem_univ _) hx); cases g:i.2 j with
 | none => rw [g] at u; exact False.elim (notMem_empty _ u)
 | some X=>
    rw [g,weight,Option.elim_some] at ht; split at ht; rename_i y; · rw [g] at u; obtain ⟨x,v,_⟩:=z.lit _ _ _ y ht; refine ⟨p.home j.val,p.belt _ _ j.property,le_trans ?_ (single_le_sum (fun i _=>hx i) (mem_univ j))⟩; rw [g]; exact_mod_cast (show separation o _≤X.2.card from (x.lim o u _ v).le)
    contradiction
end Civic
end YM.CF.BProof.Crystal
