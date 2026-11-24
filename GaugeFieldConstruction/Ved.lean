import GaugeFieldConstruction.Vines
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
variable (ι:G→J)(a b h r:ℝ)(U:G→ G→Toil I J B)(c d:ℝ)(p:FumedH a b ι U c d)(q:Book0 I J G B)(D:ℝ)(t:Puffion ι q)(s:MajorZ a b h q D)
variable (hr:0≤r)(ha:0≤a)(hb:0≤b)(ht:1≤h)
local notation "WG"=>weightV a b
local notation "WX"=>bil a b
-- structural.Follow val. Pair inside. endpoints always from single.tie O.
include p hr
lemma seed_Ω (e:Lem I J (Option (G×G)) B)(v:0≤e.won)(q:puffQ ι e)(i:G)(k)(u:k∈feint U r i e) : 0≤ k.won ∧ ι k.val∈k.seat:=by
 unfold feint at u
 cases X:e.val with
 | none=> simp [X] at u
 | some x=>
    rcases x with ⟨x,y⟩; have ht:= q x y X; simp only [X,Option.elim_some,List.mem_append,List.mem_map] at u; cases u with
    | inl u=> obtain ⟨w,a,e⟩:=u; subst k; exact ⟨mul_nonneg (mul_nonneg hr v) (p.fee0 i x _ a),Finset.mem_union_left _ ht.2⟩
    | inr u=> obtain ⟨w,a,e⟩:=u; subst k; exact ⟨mul_nonneg (mul_nonneg hr v) (p.fee0 i y _ a),Finset.mem_union_left _ ht.1⟩
include t
lemma seed_Λ (i:G) : OpenB (frond U r q i) ∧∀ v∈frond U r q i,v=leaf i∨ ι v.val∈v.seat:=by
 have hx(k)(u:k∈ q.flatMap (feint U r i)):0≤ k.won∧ ι k.val∈ k.seat:=by obtain ⟨e,v,t₀⟩:=List.mem_flatMap.mp u; exact seed_Ω ι a b r U c d p hr e (t.1 _ v) (t.2 _ v) _ k t₀
 refine ⟨fun k u=>(List.mem_cons.mp u).elim (fun e=> e ▸ zero_le_one) (fun V=>(hx k V).1),fun k u=>?_⟩; exact (List.mem_cons.mp u).imp id fun p=>(hx k p).2
omit t hr p
-- unique shape.Texture.Reindex charges.Cost dilation. double landing.
lemma toa (L: List O)(X V Y: O→ℝ)(x:B)(p:∀i∈L,X i ≤ V i+Y i): Lee L X ≤ Lee L V+Lee L Y:= by rw [←lea_pair]; exact lea_p L _ _ p
lemma mapf_κ{F:Type}[Fintype F][DecidableEq F](S:List O)(p:F→ℝ)(X:O→ F)(W:O→ℝ)(V:F→ℝ)(v:∀ i:F,0≤V i)(h:∀ i:F,Lee S (fun q=>if X q=i then W q else 0) ≤ p i): Lee S (fun q=> W q*V (X q)) ≤∑ i,p i* V i:=by
 let Z(q:O)(i:F):ℝ:=V i*(if X q=i then W q else 0)
 calc
  _ = ∑ i:F,Lee S fun q=> Z q i:=by rw [lea_sum]; refine paidA _ _ _ fun q _=>?_ ; unfold Z; simp [mul_ite,mul_comm]
  _ ≤ _:= Finset.sum_le_sum fun i _=> (lea_scale S _ (V i)).le.trans ((mul_le_mul_of_nonneg_left (h i) (v i)).trans_eq (mul_comm (V i) (p i)))
-- partial option (for leg tags). all sums at any leg i using ι & incidence.
lemma mapf_ζ{F:Type}[Fintype F][DecidableEq F](S:List O)(p:F→ℝ)(X:O→ Option F)(W:O→ℝ)(V:F→ℝ)(v:∀ i:F,0≤V i)(h:∀ i:F,Lee S (fun q=>if X q=some i then W q else 0) ≤ p i): Lee S (fun q=> W q*(X q).elim 0 V) ≤∑ i,p i* V i:=by
 let Z(q:O)(i:F):ℝ:=V i*(if X q=some i then W q else 0)
 calc
  _ = ∑ i:F,Lee S fun q=> Z q i:=by rw [lea_sum]; refine paidA _ _ _ fun q _=>?_ ; unfold Z; cases k:X q <;> simp [mul_ite,mul_comm]
  _ ≤ _:= Finset.sum_le_sum fun i _=> (lea_scale S _ (V i)).le.trans ((mul_le_mul_of_nonneg_left (h i) (v i)).trans_eq (mul_comm _ _))
include ha hb p hr
variable {μ:ℝ}
-- compute feint at fixed i unweighted extraction charges $U` via incidence.
local notation "V0"=> Lem I J (Option (G×G)) B
local notation "Zv"=> Lem I J G B
lemma flick_fee (i:G)(e:Lem I J (Option (G×G)) B)(h:0≤ e.won): let P':= fun j=>Lee (U i j) fun u=>WG u; Lee (feint U r i e) (fun v=>WG v) ≤ r*(WG e)* ((e.val.map Prod.fst).elim 0 P'+(e.val.map Prod.snd).elim 0 P'):=by
 intro V
 unfold feint
 cases w:e.val with
 | none=>simp only [w,Option.elim_none,Option.map_none,add_zero,mul_zero]; exact le_rfl
 | some y=>
    rcases y with ⟨u,v⟩; simp only [w,Option.elim_some,Option.map_some,appA,mul_add]; unfold V; simp_rw [mapA,←lea_scale]
    exact add_le_add (lea_p _ _ _ fun q t=>WP_pair _ _ r _ _ ha hb hr h (p.fee0 i u q t) v) (lea_p _ _ _ fun q t=> WP_pair _ _ r _ _ ha hb hr h (p.fee0 i v q t) u)
omit ha p hr
include t ht s hb
-- at all G selected Leg kind
lemma legP (V:G×G→G)(X:∀ i j,V (i,j)=i ∨ V (i,j)= j)(i:G): Lee q (fun e=>if e.val.map V=some i then WG e else 0) ≤ D:=by
 apply le_trans _ (MajorZ.lower _ _ _ ht hb t.1 s (ι i))
 apply lea_p
 intro e u
 split
 next v=>
    obtain ⟨⟨i',j⟩,z,g⟩:= Option.map_eq_some_iff.mp v -- tune
    have hh:= t.2 e u _ _ z
    have hz:ι i∈ e.seat := by rw [←g]; cases X i' j with| inl p=>rw [p]; exact hh.1| inr p=>rw [p]; exact hh.2
    exact (if_pos hz).symm.le
 exact WP_p _ _ _ hb (t.1 e u) _
def RadBill(r c D:ℝ):=1+ r*(D*c+D*c)
include p hr ha
lemma frond_cost(i:G)(hP:0≤ D): Lee (frond U r q i) (fun v=>WG v) ≤ RadBill r c D:=by
 let V(j):= Lee (U i j) fun v=> WG v
 have hv(j):0≤ V j:=lea_n _ _ fun x h=>WP_v _ _ _ hb (p.fee0 _ _ _ h)
 let PX(P:G×G→G):= fun e:V0=> (e.val.map P).elim 0 V
 have h(P:G×G→G)(w:∀ i j,P (i,j)=i ∨ P (i,j)=j): Lee q (fun e=> WG e * PX P e) ≤ D*c:=(mapf_ζ _ _ _ _ _ hv (legP _ _ _ _ q D t s hb ht P w)).trans ((mul_sum _ _ _).ge.trans (mul_le_mul_of_nonneg_left (p.σ0 i) hP)) -- infer
 let A: V0→ℝ := PX Prod.fst; let T:V0→ℝ:= PX Prod.snd
 unfold frond RadBill; rw [consA,show weightV _ _ (leaf i)=1 from (by simp [weightV]),joinA]; refine add_le_add le_rfl ((lea_p q _ (fun e=>r* (WG e*A e+WG e*T e)) ?_).trans ?_) -- k.tune
 · intro j u; rw [←mul_add, ←mul_assoc]; exact flick_fee _ _ _ _ _ _ _ p hr ha hb _ _ (t.1 _ u)
 rw [lea_scale,lea_pair]; exact mul_le_mul_of_nonneg_left (add_le_add (h Prod.fst (fun i j=>Or.inl rfl)) (h Prod.snd (fun i j=>Or.inr rfl))) hr
#print axioms frond_cost
end YM.CF.Fock.Wosk
end
