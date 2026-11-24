import YM.CF.Fixed.Voltage.OfferF
/-! uniform tiny flag ledgers. no claiming transfer w/o shared budget. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson SU Scree Skye Fock Lat Cube MeasureTheory Vow RG Rue Spire
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{x a b h w:ℝ}(P:BudgetPoint)(D:Support (More n)) {Q:Sweep n→Prop}
local notation "N"=> More n
local notation "A"=> deck_F P D
variable {F G:Copy n}
abbrev holderV (c:ℝ):= Vow.chi_f P.order*c
lemma holder_scale(C:ℝ)(h:0 ≤ C):0 ≤ holderV P C:=mul_nonneg (spicy_f _) h
lemma mass_live (u:0≤x):0≤P.mass D x:=mul_nonneg (Real.exp_pos _).le u
lemma mass_pays (h:0≤x): x≤ P.mass D x:= le_mul_of_one_le_left h (Real.one_le_exp (mul_nonneg P.exponent_pos.le (by positivity)))
lemma credit_E (X:RegBudget n)(u:IncX Q X P w b)(p:1≤w)(i:Scree.Hub n): ∃ v, PressB P i (X i) w v ∧ 0 ≤ v∧ v≤b:=by
  obtain ⟨f,g,t⟩:= u.weight; have h(i):0 ≤ f i := Beau.grit_p P (g i) (zero_le_one.trans p); refine ⟨f i,g i,h i,(mass_pays P i.val.2 (h i)).trans (le_trans ?_ (t i.val.1))⟩; have he: ∀ j:Scree.Hub n,0 ≤ if i.val.1=j.val.1 then P.mass j.val.2 (f j) else 0:= by intro j; split; exact mass_live P _ (h j); exact le_rfl
  simpa only [↓reduceIte] using single_le_sum (fun j _=>he j) (mem_univ i)
lemma force_cost (i:Force n)(g:ForceB P i F w h)(u:1≤w):0≤h:=by obtain ⟨c,t,v,p⟩:=g.costP; exact (sum_nonneg (fun i _=> mul_nonneg (by unfold Scree.tariff; have he:0≤w:=zero_le_one.trans u; positivity) (t i))).trans p
lemma credit_D (X:ForceBudget n)(u:Dark Q X P w b)(p:1≤w)(i:Force n): ∃ v, ForceB P i (X i) w v∧ 0 ≤ v ∧ v≤b:=by
  obtain ⟨f,g,t⟩:=u.weight; have h(i):0≤ f i:= force_cost _ i (g i) p; let k:=i.val.1.val.1; refine ⟨f i,g i,h i,(mass_pays P i.val.1.val.2 (h i)).trans (le_trans ?_ (t k))⟩; have he: ∀ j:Force n, 0 ≤ if k∈j.val.1.val.2 then P.mass j.val.1.val.2 (f j) else 0:= by intro j; split; exact mass_live P _ (h j); exact le_rfl
  simpa only [if_pos (show k∈i.val.1.val.2 from i.val.1.property)] using single_le_sum (fun j _=>he j) (mem_univ i)
lemma spent_E(X:RegBudget n)(u:IncX Q X P w b)(p:1≤w):0≤b:=by let i:Scree.Hub n:=⟨(0,univ),mem_univ _⟩; obtain ⟨v,_,k,h⟩:= credit_E _ _ u p i; exact k.trans h
lemma spent_D(X:ForceBudget n)(u:Dark Q X P w b)(p:1≤w):0≤b:=by let i:Scree.Hub n:=⟨(0,univ),mem_univ _⟩; let j:Force n:=⟨(i,univ),univ_nonempty,Subset.refl _⟩; obtain ⟨v,_,k,h⟩:= credit_D _ _ u p j; exact k.trans h
abbrev wholePrice (P:BudgetPoint)(n:Side):ℝ:= Fintype.card (Scree.Hub n)*chi_f P.order
lemma meter_hub(X:RegBudget n)(u:IncX Q X P w b)(p:1≤w):Metered P D (oV (exponentL P X)) w (wholePrice P n * b):=by
 let f(i:Hub n):= oV (numbE P.threshold i.val.2 (X i)); choose B h hv hr using credit_E P _ u p; have ht:= Metered.pile univ f (fun _i=>chi_f P.order*b) (fun i _=> (stretch_P P D (X i) i (h i) p).mono (mul_le_mul_of_nonneg_left (hr i) (spicy_f _)))
 rw [sum_const,card_univ,nsmul_eq_mul, ←mul_assoc] at ht; exact ht.related (fun i _=> by simp only [Finset.sum_apply,f]; rfl)
-- full tuple
local notation "Φ"=>Set.PairwiseDisjoint
abbrev flagTuple(V:Finset (Force n))(X:Support (More n)):Prop:= V.biUnion (fun x=> x.val.2)=X ∧ Φ (↑V : Set (Force n)) (fun x=>x.val.1.val.2)
abbrev flagPrice (n:Side)(c:ℝ):ℝ:=∑ i:Finset (Force n), c^i.card
abbrev markPrice (P:BudgetPoint)(n:Side)(c:ℝ):= flagPrice n (chi_f P.order*c)
lemma flagp_pos (g:0≤x):0≤flagPrice n x:=sum_nonneg fun _ _=>pow_nonneg g _
lemma meter_tuple(X:ForceBudget n)(u:Dark Q X P w b)(p:1≤w)(s:Finset (Force n)):let K:Copy n:=fun V=> if flagTuple s (flags P.threshold V.1) then (∏ i∈s, Scree.clamp P i (X i) V) else 0; Metered P D K w ((holderV P b)^s.card):=by
 intro K; have he:0 ≤ w:= zero_le_one.trans p; let k:=holderV P b; have hk:0 ≤k:= holder_scale P b (spent_D _ _ u p); by_cases h:flagTuple s D; swap
 · apply (Metered.mono Metered.vacant (pow_nonneg hk s.card)).related; intro V v; unfold K; rw [show flags P.threshold V.1=D from v.2]; exact (if_neg h).symm
 let f(i:Force n):=Scree.clamp P i (X i); have hv(i:Force n)(g:i ∈ s): Metered P D (f i) w k:=by
   let L:= i.val.1.val.2; let A':= i.val.2; obtain ⟨v,y,z,w'⟩:=credit_D P X u p i; by_cases l:Disjoint (L\A') D; swap
   · refine (Metered.mono Metered.vacant hk).related fun V c=> ?_; unfold f Scree.clamp; have hb: ¬boundF i P V.1:= fun k=>l ((show flags _ _ = D from c.2) ▸ ping_le k); split; contradiction; rfl
   have heX:A'⊆ D:=by have h': s.biUnion (fun x=> x.val.2)=D:=h.1; rw [←h']; exact subset_biUnion_of_mem (fun x:Force n=>x.val.2) g
   refine ((Metered.of_cast ((rimP y he).2.stretchB (subset_univ _) heX (fun i' p'=>mem_sdiff.mpr ⟨mem_univ _,fun t=>Finset.disjoint_left.mp l p' t⟩))).mono (mul_le_mul_of_nonneg_left w' (spicy_f _))).related fun V c=> ?_
   unfold f Scree.clamp; have he':pingS P.threshold (i.val.1.val.2\i.val.2) V.1:= (shoreK _ V.1 c.1 _).1 (by unfold Healthy; rw [show flags _ _ = _ from c.2]; exact l); rw [if_pos (show boundF i P V.1 from he')]
 have hx:= Metered.plot s f _ hv he; rw [prod_const] at hx; refine hx.related fun V v=> ?_; unfold K; simp only [Finset.prod_apply,f]; rw [show flags P.threshold V.1=D from v.2,if_pos h]
lemma meter_fuel(X:ForceBudget n)(u:Dark Q X P w b)(p:1≤w):Metered P D (fueled P X) w (markPrice P n b):=by
  let f(i:Finset (Force n))(V:Orbit n):=if flagTuple i (flags P.threshold V.1) then (∏ j∈i,Scree.clamp P j (X j) V) else (0:Cipher n); have he(i):=meter_tuple P D X u p i; refine (Metered.pile univ f _ (fun i _=>he i)).related (fun V v=>?_) ; unfold fueled; simp only [Finset.sum_apply,f]
end YM.CF.Fixed.Voltage
