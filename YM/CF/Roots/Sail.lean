import YM.CF.Roots.Mara
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Roots
open Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g u v:Key I→E}{a b a' b': Key I→N}{s t r:List I}
section storm
variable {J:Type*}[DecidableEq J](σ:I→J)(C: I→ I→ℂ) -- matrix (old index i, new p).
local notation "τ"=> pipe_ζ σ
local notation "wS"=> ψS σ
local notation "Ω"=> fuelΦ σ C
local notation "W"=> Storm_C σ C
lemma sumY_C {κ:Type*}(R:Finset κ)(F G:κ→Key I→E)(p:∀ i∈R, River (F i)∧River (G i)∧Storm_C σ C s (F i) (G i)): River (fun x=>∑ i∈R,F i x)∧ River (fun x=>∑ i∈R,G i x) ∧ Storm_C σ C s (fun x=>∑ i∈R,F i x) (fun x=>∑ i∈R,G i x):=by
 classical
 induction R using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; exact ⟨zeroR _,zeroR _,constant_C _ _ _⟩
 | insert i r h ih=>
    obtain ⟨u,v,w⟩:=p i (mem_insert_self ..); obtain ⟨x,y,z⟩:=ih fun j v=>p j (mem_insert_of_mem v); simp_rw [sum_insert h]; exact ⟨dub_V u x,dub_V v y,Aζ _ _ u x v y w z⟩
lemma prodY_C {κ:Type*}(R:Finset κ)(F G:κ→Key I→N)(q:ψS σ s)(p:∀ i∈R, River (F i)∧River (G i)∧Storm_C σ C s (F i) (G i)): River (fun x=>∏ i∈R,F i x)∧ River (fun x=>∏ i∈R,G i x) ∧ Storm_C σ C s (fun x=>∏ i∈R,F i x) (fun x=>∏ i∈R,G i x):=by
 classical
 induction R using Finset.induction_on with|empty=>simp_rw [Finset.prod_empty]; exact ⟨zeroR _,zeroR _,constant_C _ _ _⟩|insert i r h ih=> obtain ⟨u,v,w⟩:=p i (mem_insert_self ..); obtain ⟨x,y,z⟩:=ih fun j v=>p j (mem_insert_of_mem v); simp_rw [Finset.prod_insert h]; exact ⟨u.mul_T x,v.mul_T y,roof_e _ _ u x v y q w z⟩
-- activity covariance.
abbrev toV_C(σ:I→J)(C:I→I→ℂ)(x: Key I):Key I:=fun i=>∑ j∈pipe_ζ σ i,C i j*x j
lemma north_r (i:I) : River (fun x:Key I=> x i):= by exact (pine_r ({i}:Finset I)).cong (fun z _=> (Finset.prod_singleton ..).symm)
lemma coin_R (i:I):River (fun x:Key I=> toV_C σ C x i):= (tip_bank _ _ (fun j _=> show River (fun x=>C i j*x j) from River.scale (north_r _) _)).1
lemma tale_R (i:I)(p:s.Nodup): tipI (fun x:Key I=> x i) s = if s.toFinset={i} then 1 else 0:= by simpa [pine] using tip_tape s p ({i}:Finset I) (1:ℂ)
private lemma pix{u v:I}(p:u∈τ v):σ u=σ v:=(mem_filter.mp p).2
lemma optic_P (q:wS s)(i:I): W s (fun x:Key I=> x i) (fun x:Key I=> toV_C σ C x i):=by
 intro l p; have hv:= (p.map σ).nodup q; unfold ψS at q; have hx:=p.nodup (uS_b σ q); cases l
 case nil=>
   change (∑ j∈τ i,_*_) = _; change (∑ j∈τ i,C i j*0)=0; simp
 case cons k l=>
    let F(j:I)(x:Key I):= C i j * x j
    rw [show tipI _ _ = ∑ j∈τ i,tipI (F j) (k::l) from (tip_bank _ F fun j _=> River.scale (north_r _) _).2 _]; unfold fuelΦ; rw [snow]; have hT(j):tipI (F j) (k::l)=C i j * (if (k::l).toFinset={j} then 1 else 0):=(tip_C (north_r j) (C i j) _).trans (congrArg (C i j*·) (tale_R j hx)) -- ambiguous sier
    cases l
    case nil=>
       change ∑ j∈τ i,tipI (F j) _=∑ j∈τ k,C j k*tipI (fun x:Key I=>x i) [j]
       simp_rw [show ∀ j:I,tipI (fun x:Key I=>x i) [j]=if [j].toFinset={i} then 1 else 0 from fun j=> tale_R i (by simp),hT,List.toFinset_cons,List.toFinset_nil]; simp only [insert_empty_eq,singleton_inj, mul_ite,mul_one,mul_zero, sum_ite_irrel]; -- inspect
       by_cases p:k∈τ i; swap; · have he:i∉τ k:=fun h=>p (mem_filter.mpr ⟨mem_univ _,(pix σ h).symm⟩); rw [sum_eq_zero (fun j v=> if_neg (fun h:k=j=> p (h ▸ v))),sum_eq_zero (fun j v=>if_neg (fun h:j=i=>he (h ▸ v)))]
       have he:i∈τ k:=mem_filter.mpr ⟨mem_univ _,(pix σ p).symm⟩; rw [sum_eq_single_of_mem k p,sum_eq_single_of_mem i he]; simp
       · intro j h x; exact if_neg x
       intro j h x; exact if_neg (Ne.symm x)
    case cons o s'=>
       let t:= o::s'; let K:= k::t; have hu:1< K.length:=by simp [K,t]
       have he(j):(k::t).toFinset ≠ {j}:=fun p=> by have hg:=congrArg Finset.card p; rw [List.toFinset_card_of_nodup hx,Finset.card_singleton] at hg; change K.length=1 at hg; omega
       rw [sum_eq_zero (fun j _=> (hT j).trans (by rw [if_neg (he j), mul_zero]))]; symm; apply sum_eq_zero; intro j u
       suffices hk:snow σ C (fun s=>tipI (fun x:Key I=>x i) (j::s)) t=0 by rw [hk,smul_zero]
       refine (rer σ C t (G:=fun s=>tipI (fun x:Key I=>x i) (j::s)) («W»:=fun _=>0) (fun l q=>?_)).trans (women ..)
       have hz:wS (j::l):=by unfold ψS; rw [List.map_cons,pix σ u,q]; exact hv
       rw [tale_R _ (uS_b σ hz),if_neg]; intro i'; have he:=congrArg List.length q; simp only [List.length_map] at he; have ht:=congrArg Finset.card i'; rw [List.toFinset_card_of_nodup (uS_b σ hz),Finset.card_singleton] at ht; unfold t at *; simp only [List.length_cons] at *; omega -- shadow i'.
lemma north_F (q:wS s) (D:Finset I): River (fun x=> pine D (toV_C σ C x))∧W s (pine D) (fun x=> pine D (toV_C σ C x)):= (prodY_C σ C D (fun i x=>x i) (fun i x=> toV_C σ C x i) q (fun i _=>⟨north_r i,coin_R σ C i,optic_P σ C q i⟩)).2
lemma sky_up (q:wS s)(i:Finset I)(a:E) : River (fun x:Key I=> pine i (toV_C σ C x) • a)∧ W s (fun x:Key I=> pine i x • a) (fun x:Key I=> pine i (toV_C σ C x) • a):=by
 let G:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) a; obtain ⟨h,p⟩:= north_F σ C q i; exact ⟨sc_V h G, scope_C σ C (pine_r i) h p G⟩
lemma RoofUp (q:wS s)(X:Finset (Finset I))(g:Finset I→E): let F(z):=∑ i∈ X,pine i z • g i; River F ∧ River (F ∘ toV_C σ C)∧ W s F (F ∘ toV_C σ C):=by
 intro F; refine sumY_C σ C X _ _ fun i hi=> ⟨lift_b i (g i),?_⟩; exact sky_up σ C q _ _ -- tune inference
-- projection through currency
abbrev seedΞ {E:Type*}[AddCommMonoid E][SMul ℂ E](F:Finset I→E)(L:Finset (Finset I))(z:Key I):= ∑ i∈L,pine i z •F i
def realm_C (σ:I→ J):Finset (Finset I):=by classical exact univ.filter (fun i=>Set.InjOn σ (i:Set I))
abbrev palm_R (f:Key I→E)(σ:I→ J):Key I→E:= seedΞ (gemI f) (realm_C σ)
lemma pays_z (p:wS t): Set.InjOn σ (t.toFinset:Set I):=by
 -- known list.Nodup
 classical
 let Y:=t.toFinset; apply Finset.card_image_iff.mp; rw [show t.toFinset.image σ=(t.map σ).toFinset from (by ext x; simp),List.toFinset_card_of_nodup p,List.toFinset_card_of_nodup (uS_b σ p), List.length_map]
lemma spark_U (p:River f)(q:wS s) : tipI (palm_R f σ) s = tipI f s:=by
 have hx:s.toFinset∈realm_C σ:=mem_filter.mpr ⟨mem_univ _,pays_z σ q⟩; let F:=gemI f; rw [show tipI _ _=∑ i∈realm_C σ,tipI (fun z:Key I=>pine i z • F i) s from (tip_bank _ _ (fun i _=>lift_b i (F i))).2 _]; simp_rw [tip_tape s (uS_b _ q)]; simp only [Finset.sum_ite_eq,if_pos hx]; exact orbit_ζ p (uS_b σ q) -- tune
lemma κEmit (p:River f)(q:wS s) : River (palm_R f σ ∘ toV_C σ C)∧W s f (palm_R f σ ∘ toV_C σ C):=by
 obtain ⟨Q,h,H⟩:= RoofUp (E:=E) σ C q (realm_C σ) (gemI f); refine ⟨h,fun i v=>?_⟩; have hu:= (v.map σ).nodup q; exact (H i v).trans (rer σ C i (fun l p'=>spark_U σ p (by unfold ψS; rw [p']; exact hu)))
end storm
end YM.CF.Roots
