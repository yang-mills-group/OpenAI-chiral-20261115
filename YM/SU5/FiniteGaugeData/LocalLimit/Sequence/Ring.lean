import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.Normed.Operator.Basic
/-!
Diagonal thinning with uniform bills for the paired subsequences. `inCone` is
not assumed monotone; we'll be able to exclude early points nevertheless.
Everything indexed by UV k and period i. Designed for bounded-function sup
metrics (not necessarily separable).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SU5.FiniteGaugeData.LocalLimit.Rings
open Function Filter Metric Finset
open scoped Classical Topology
variable {ι:Type}[Countable ι]{f:ι→Type}[∀ i,PseudoMetricSpace (f i)] (G:∀ i,ℕ→ℕ→ f i)
variable (A:ℕ→ ι→Prop) (ad:ℕ→ℕ→ι→Prop)(χ:ℕ→ℕ→Prop) (box:ℕ→Finset ι)(eps:ℕ→ℝ)
structure Tent (i k:ℕ→ℕ) (g:∀ j,ℕ→f j)(h:∀ j,f j) : Prop where
 per : StrictMono i
 dep : StrictMono k
 cut : ∀ j n,Tendsto (fun d=>G j n (k d)) atTop (𝓝 (g j n))
 ir : ∀ j,Tendsto (fun d=>g j (i d)) atTop (𝓝 (h j))
 card : ∀ s t, χ (i s) (k t) ↔ s ≤ t
 cont : ∀ s j, j ∈ box s → A (i s) j
 line : ∀ s t, s≤t→ ∀ j∈box s, ad (i s) (k t) j ∧ dist (G j (i s) (k t)) (h j) ≤ eps s

section choice
variable {P : ℕ→ℕ→Prop} {Q : ℕ→ℕ→ℕ→Prop}
private lemma alternate (p:∀ s,∀ᶠ i in atTop,P s i) (q:∀ s i,P s i→ ∀ᶠ k in atTop,Q s i k) (hv: ∀ k, ∀ᶠ i in atTop, ¬ χ i k) :
 ∃ (i k:ℕ→ℕ), StrictMono i ∧ StrictMono k ∧ (∀ s,P s (i s)) ∧ (∀ s t,s≤t → Q s (i s) (k t)) ∧ (∀ s t,t<s→¬ χ (i s) (k t)) := by
 choose d hd using fun s i (p:P s i)=> eventually_atTop.mp (q s i p)
 choose u Xh Y H using fun s N L=> (show ∃ i:ℕ, i>N ∧ P s i ∧ ∀ j:ℕ, j≤L →¬ χ i j from by
    let R(j:ℕ):Fin L.succ→Prop:=fun x=> ¬χ j x.val
    obtain ⟨i,u,v,t⟩:=((eventually_gt_atTop N).and ((p s).and ((Filter.eventually_all (ι:=Fin (L+1))).mpr fun z=>hv z.val))).exists
    exact ⟨i,u,v,fun j p=>t ⟨j,p.trans_lt (Nat.lt_succ_self L)⟩⟩)
 let X(s):={i: ℕ×ℕ // P s i.1 ∧ ∀ k, i.2≤k→Q s i.1 k}
 let K s N L: X s := ⟨(u s N L,d s (u s N L) (Y s _ _)+L+1),Y _ _ _,fun k p=> hd _ _ (Y _ _ _) k (by change d s (u s N L) (Y _ _ _)+L+1≤_ at p; omega)⟩ -- tune
 let l : ∀ s, X s := Nat.rec (K 0 0 0) (fun (s:ℕ) (v:X s)=> K (s+1) v.val.1 v.val.2)
 let i s := (l s).val.1; let k s:=(l s).val.2
 have hi:StrictMono i:= strictMono_nat_of_lt_succ fun s=> (Xh (s+1) (i s) (k s))
 have hk:StrictMono k:= strictMono_nat_of_lt_succ fun s=> by change k s < (K (s+1) (i s) (k s)).val.2; dsimp only [K]; omega
 refine ⟨i,k,hi,hk,fun s=>(l s).property.1,fun s t p=> (l s).property.2 (k t) (hk.monotone p),?_ ⟩
 rintro (_|s) t p; · omega
 exact H (s+1) _ _ _ (hk.monotone (show t≤s by omega))
end choice
lemma two_steps (h:∀ j,∃ A:Set (f j),IsCompact A ∧ ∀ i k,G j i k∈A)
   (g:∀ j, ∀ᶠ i in atTop,A i j)(w:∀ i j, A i j→∀ᶠ k in atTop,ad i k j)
   (hm:∀ i,∀ᶠ k in atTop,χ i k)(hk:∀ k,∀ᶠ i in atTop,¬ χ i k)
   (he:∀ i,0 < eps i)(i k:ℕ→ℕ)(hi:StrictMono i)(ht:StrictMono k) :
 ∃ i' k' L H,StrictMono i' ∧ StrictMono k' ∧ Tent G A ad χ box eps (i ∘ i') (k ∘ k') L H := by
 choose S hS hU using h
 let T:= fun z:ι×ℕ=> f z.1
 obtain ⟨H,hH,Q,hQ,t⟩ := (isCompact_pi_infinite (fun u:ι×ℕ=> hS u.1)).tendsto_subseq (fun t :ℕ=> show (fun x:ι×ℕ=>G x.1 x.2 (k t))∈_ from fun x=>hU ..)
 let V(j:ι)(i:ℕ):= H (j,i); have hz: ∀ j i,V j i∈ S j:=fun j n=>hH (j,n); let u:= k ∘ Q
 have hV(j n):Tendsto (fun x=>G j n (u x)) atTop (𝓝 (V j n)):= tendsto_pi_nhds.mp t (j,n)
 obtain ⟨Z,hZ,R,hR,tR⟩:= (isCompact_pi_infinite hS).tendsto_subseq (fun t:ℕ=> show (fun x=>V x (i t))∈_ from fun x=>hz ..); let y:=i ∘ R; have hr:=hi.comp hR; have hb:= ht.comp hQ
 have Hm(j):Tendsto (fun t=>V j (y t)) atTop (𝓝 (Z j)):= tendsto_pi_nhds.mp tR j -- shadow hm rename
 let P(s:ℕ)(t:ℕ):= ∀ i∈box s,A (y t) i ∧ dist (V i (y t)) (Z i) ≤ eps s/2
 let B(s:ℕ)(x k:ℕ):=χ (y x) (u k)∧ ∀ i∈box s, ad (y x) (u k) i ∧ dist (G i (y x) (u k)) (V i (y x)) ≤ eps s/2
 let v(x k):=χ (y x) (u k)
 have Hp s : ∀ᶠ t in atTop,P s t:= (eventually_all_finite (box s).finite_toSet).mpr fun i _=> (hr.tendsto_atTop.eventually (g i)).and ((Metric.tendsto_nhds.mp (Hm i) _ (half_pos (he s))).mono (fun _ h=>h.le))
 have Hq(s x) (e:P s x): ∀ᶠ k in atTop,B s x k:= (hb.tendsto_atTop.eventually (hm (y x))).and ((eventually_all_finite (box s).finite_toSet).mpr (fun i p=> (hb.tendsto_atTop.eventually (w (y x) i (e i p).1)).and ((Metric.tendsto_nhds.mp (hV i (y x)) _ (half_pos (he s))).mono (fun _ h=>h.le))))
 obtain ⟨x,b,hx,v',hx',hx'',hy⟩:= alternate v Hp Hq fun k=> hr.tendsto_atTop.eventually (hk (u k))
 refine ⟨R ∘ x,Q ∘ b,V,Z,hR.comp hx,hQ.comp v',hi.comp (hR.comp hx),hb.comp v',fun j n=>(hV j n).comp v'.tendsto_atTop,fun j=>(Hm j).comp hx.tendsto_atTop,fun s t=>⟨fun p=>?_ ,fun p=>(hx'' s t p).1⟩,fun s i p=>(hx' s i p).1,?_ ⟩
 · by_contra! h; exact hy s t h p
 intro s t u0 j p; obtain ⟨h,e'⟩ := (hx'' s t u0).2 j p; refine ⟨h,?_⟩; change dist (G j _ (u (b t))) (Z j) ≤ _; change dist (G j (y (x s)) _) _ ≤ _; linarith [dist_triangle (G j (y (x s)) (u (b t))) (V j (y (x s))) (Z j), (hx' s j p).2]
end YM.SU5.FiniteGaugeData.LocalLimit.Rings
