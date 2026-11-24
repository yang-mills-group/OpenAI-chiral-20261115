import Anomaly.Hop.Wipe
import Anomaly.Hop.Charge
/-! Unit receipt via ribbon, not an attempt to approximate 1 by Core mask.
 The offset ALSO charges and must be retained when estimating Key matrices.
 This handles using such receipts on top of all other physical operations.
 -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function Set Metric Mew Roots Neon MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable {G G':Key I→ℂ}{a b:Key I→E}{s t r:List I}
local notation "soft" A:max f:max => fun z:Key I=> A z • (f z)
lemma soft_tip (i:I)(s:List I)(h:River G)(t:River a): tipI (soft G a) (i::s)=tipI (soft (cutI G i) (a ∘ dune i)) s+tipI (soft (G∘ dune i) (cutI a i)) s:=by
 have he:EqOn (cutI (soft G a) i) (fun x=>(soft (cutI G i) (a ∘ dune i)) x + (soft (G∘ dune i) (cutI a i)) x) (hill I):= fun v p=>(mitt (κscale h t) p i).deriv.symm.trans (((mitt h p i).smul (mitt t p i)).deriv.trans (add_comm ..))
 exact (lace_C _ he roots).trans (tip_A (κscale (h.flow i) (t.stay i)) (κscale (h.stay i) (t.flow i)) s)
-- version comparing two covered germs prices on restricted l
abbrev chipQ (s:List I)(a b:Key I→ E):Prop:=∀ t:List I,t.Sublist s → tipI a t=tipI b t
lemma chip_S(i:I)(h:s.Nodup)(t:i∉s)(p:chipQ s a b): chipQ s (a∘ dune i) (b∘ dune i):=by
 intro l u; have hz:i∉ l:=fun h=>t (u.subset h); rw [tip_V i l hz,tip_V i l hz]; exact p _ u
lemma chip_N(i:I)(p:chipQ (i::s) a b): chipQ s (cutI a i) (cutI b i):=fun l u=>p (i::l) (List.cons_sublist_cons.mpr u)
lemma soft_S (h:River G)(w:River G')(t:River a)(l:River b)(p:chipQ s a b)(x:chipQ s G G')(u:s.Nodup):chipQ s (soft G a) (soft G' b):=by
 induction s generalizing a b G G' with
 | nil=> intro j U; rw [List.sublist_nil.mp U]; exact congrArg₂ (· • ·) (x [] (List.Sublist.refl _)) (p [] (List.Sublist.refl _))
 | cons i j ih=>
    have h_:=List.sublist_cons_of_sublist i (List.Sublist.refl j); have hx:chipQ j a b:=fun _ t=>p _ (List.Sublist.trans t h_); have hf:chipQ j G G':=fun _ t=>x _ (List.Sublist.trans t h_)
    obtain ⟨ha,u⟩:=List.nodup_cons.mp u; intro k q; cases q with
    | cons _ t'=> exact ih h w t l hx hf u k t'
    | cons_cons _ v=>
       rw [soft_tip _ _ h t,soft_tip _ _ w l]; exact congrArg₂ (·+·) (ih (h.flow _) (w.flow _) (t.stay _) (l.stay _) (chip_S i u ha hx) (chip_N i x) u _ v) (ih (h.stay _) (w.stay _) (t.flow _) (l.flow _) (chip_N i p) (chip_S i u ha hf) u _ v)
open NormedSpace
variable (D:Finset I)(t:I→ℂ)
lemma bill_exp : River (I:=I) (Complex.exp ∘ α_ξ t):=by
 rw [Complex.exp_eq_exp_ℂ]; exact (show River (α_ξ t) from rer_C t).exp_V
lemma hack (s: List I)(p:s.Nodup):tipI (Complex.exp ∘α_ξ t) s= (s.map t).prod:=by
 let H:= Complex.exp ∘ α_ξ t
 induction s with
 | nil=> change Complex.exp _=_; rw [show α_ξ t 0=0 from sum_eq_zero fun i _=>zero_mul _,Complex.exp_zero]; rfl
 | cons i j ih=>
    obtain ⟨h,u⟩:=List.nodup_cons.mp p; specialize ih u
    let U:= (ζexp (id:I→I) (show River (α_ξ t) from rer_C t) i (s:=j) (by simpa [ψS] using List.nodup_cons.mpr ⟨h,u⟩))
    rw [← Complex.exp_eq_exp_ℂ] at U
    have he(x:Key I)(u:x∈hill I):cutI (α_ξ t) i x=t i:=by
       rw [← (mitt (f:=α_ξ t) (rer_C t) u i).deriv]; let a:=α_ξ t (dune i x); have he(z:ℂ): α_ξ t (update x i z)= z*t i+a:=by
          unfold a α_ξ; rw [←add_sum_erase (s:=univ) (f:=fun j=>update x i z j*t j) (mem_univ i),←add_sum_erase (s:=univ) (f:= fun j=> dune i x j*t j) (mem_univ i),update_self,show dune i x i=0 from update_self ..,zero_mul,zero_add]; congr 1; apply sum_congr rfl; intro j w; let v:= (mem_erase.mp w).1; rw [update_of_ne v,show dune i x j=x j from update_of_ne v ..]
       simp_rw [he]; convert (((hasDerivAt_id' (0:ℂ)).mul_const (t i)).add_const a).deriv using 2; rw [one_mul]
    have hv:tipI (cutI (α_ξ t) i*H) j=t i • tipI H j:=((lace_C j (g:=soft (fun _=>t i) H) (show EqOn _ _ (hill I) from fun x u=>by rw [Pi.mul_apply,he x u]; rfl) roots).trans (tip_C (bill_exp _ ) _ _ ))
    rw [U,hv]; change t i* tipI H j=_; rw [show tipI H j=_ from ih,List.map_cons,List.prod_cons]
lemma boost_Q (hp:∀ i∉D,t i=0)(g:River a)(p:s.Nodup)(u:∀ l:List I,l.Sublist s→∀ i∈ D,i∈ l→ tipI a l=0):let T:=Leit D s; tipI (soft (Complex.exp ∘ α_ξ t) a) s = (T.map t).prod • tipI a (Leit (Finset.univ \ D) s):=by
 intro T; let b:=a ∘ wipe D; let N:=Leit (Finset.univ \ D) s; let W:=Complex.exp ∘ α_ξ t; let f:= soft W b; let h:=bill_exp t
 have hz:tipI (soft (Complex.exp ∘ α_ξ t) a) s=tipI f s:=by
    refine soft_S h h g (wipeSweep _ _ g) (b:=b) ?_ (fun _ _=>rfl) p s (List.Sublist.refl _)
    intro l v; by_cases x:∀ i∈l,i∉D; · exact (wipe_list _ _ l x).symm
    push Not at x; obtain ⟨i,c,w⟩:= x; exact (u l v i w c).trans (wipe_out D _ g _ _ c w).symm
 let Q:E→L[ℂ] E:= (T.map t).prod • ContinuousLinearMap.id ℂ E
 rw [hz]; refine mix_rule D f s (κscale h (wipeSweep _ _ g)) a g Q (fun x p' u'=>?_)
 have he:f ∘ antler D x= fun z:Key I=> W z • (a x):=by
    funext z; have ht:wipe D (antler D x z)=x:=by funext i; by_cases v:i∈D; rw [wipe,if_pos v,u' i v]; rw [wipe,if_neg v,antler,if_neg v]
    have hf:α_ξ t (antler D x z)=α_ξ t z:=by
       refine Finset.sum_congr rfl fun i _=>?_ ; by_cases v:i∈D; rw [antler,if_pos v]; rw [hp i v,mul_zero,mul_zero]
    exact congrArg₂ (· • ·) (congrArg Complex.exp hf) (congrArg a ht)
 let G:ℂ→L[ℂ] E:= (ContinuousLinearMap.id ℂ ℂ).smulRight (a x)
 rw [he]
 change tipI (fun z=> G (W z)) T=_
 rw [show tipI (fun z=> G (W z)) T=G (tipI W T) from sim_H h G T roots, show tipI W T= _ from hack t T (List.Nodup.sublist (List.filter_sublist) p)]; rfl
end YM.CF.Vow.TreasuryFog
