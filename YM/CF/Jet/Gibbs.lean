import YM.CF.Jet.Quasar
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice Cube Lat
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {K:ℝ}
lemma strain_w(l n:ℕ)(h:0≤K): ∃ C:ℝ,0≤C∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (f:E→Vect)(L:List (E→Vect))(x:E), Allows n f x K→ L.length≤l → (∀ i∈L, Allows n i x K) →Allows n (fun x=> restrain margin (L.map (fun i=>i x)) (f x)) x C:=by
 induction l with
 | zero=> refine ⟨K,h,fun E _ _ f L x hf hl H=>?_⟩; have h:L=[]:=by simpa using hl
          rw [h]; exact hf
 | succ l ih=>
    obtain ⟨C,hC,H⟩:=ih
    let g (x:Vect×Vect):= shave margin x.1 x.2
    obtain ⟨V,v,hV⟩:= compact_allow n hC g (shaved n)
    refine ⟨max K (composeCost n V C),le_max_of_le_left h,fun E _ _ f L x hf hl Hk=>?_⟩
    cases L; exact hf.mono (le_max_left ..)
    next y w=>
       have ht:w.length≤l:=by simpa using hl
       have hv (p) (k:p∈w):=Hk p (List.mem_cons_of_mem _ k)
       let G(x:E):=(restrain margin (w.map (fun i=>i x)) (y x),restrain margin (w.map (fun i=>i x)) (f x))
       have hm: Allows n G x C:= (H E y w x (Hk y List.mem_cons_self) ht hv).pair (H E f w x hf ht hv)
       exact ((hV (G x) hm.value).comp (f:=G) hm).mono (le_max_right ..)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{n:ℕ}
def CashCold (f:E→ℝ)(x:E)(n:ℕ)(K:ℝ): Prop:= Allows n f x K ∧ (f x=0→Allows n f x 0)
lemma cashUp {f:E→ℝ}{V:ℝ}(h:CashCold f x n K)(g:K≤V):CashCold f x n V:=⟨h.1.mono g,h.2⟩
lemma prod_raft (l n:ℕ)(h:0≤K): ∃ C:ℝ,0≤C∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](X:Type)(s:Finset X)(F:X→E→ℝ) (x:E), s.card≤l→ (∀ i∈s,CashCold (F i) x n K)→ CashCold (fun x=>∏ i∈s,F i x) x n C :=by
 classical
 induction l with
 | zero=> refine ⟨1,zero_le_one,fun E _ _ X s F x k p=>?_⟩
          have hs:s=∅:= Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero k); rw [hs]; simp only [CashCold, prod_empty, one_ne_zero,false_implies,and_true]; exact allows_const x (by simp)
 | succ l ih=>
    obtain ⟨C,hC,H⟩:=ih; let A:=ContinuousLinearMap.mul ℝ ℝ; let z := 2^n*‖A‖*K*C
    refine ⟨max C z,le_max_of_le_left hC,fun E _ _ X s F x L t=>?_⟩
    by_cases p:s.Nonempty
    swap; apply cashUp (H E X s F x (by simp [not_nonempty_iff_eq_empty.mp p]) t) (le_max_left ..)
    obtain ⟨i,hv⟩:=p; let q:=s.erase i
    have g := H E X q F x (by unfold q; rw [card_erase_of_mem hv]; omega) (fun j h=> t j (mem_erase.mp h).2)
    have he : (fun x=> ∏ i∈s,F i x)=(fun y=> F i y * (∏ j∈q,F j y)):=by funext; nth_rw 1 [←insert_erase hv]; simp [q]
    rw [he]; refine ⟨(((t i hv).1).bilinear A g.1 le_rfl).mono (le_max_right ..),fun h=>?_⟩
    rcases mul_eq_zero.mp h with h|h
    · simpa [A] using ((t i hv).2 h).bilinear A g.1 le_rfl
    simpa [A] using (t i hv).1.bilinear A (g.2 h) le_rfl
lemma token (n:ℕ)(h:0≤K)(B:Side):∃ C:ℝ,0≤C∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (m:Side)(U:E→Skin m B)(x:E)(f:E→ ArrayF m), TransK n U x K→arr n f x K→∀ r a,CashCold (fun t=> fundF m B (U t) (f t) r a) x n C:=by
 obtain ⟨D,d,Y⟩:=velour n h B 6; let r:=max D K; obtain ⟨Z,z,G⟩:=strain_w 6 n (show 0≤r from le_max_of_le_right h)
 obtain ⟨C,k,H⟩:=compact_allow n z glue (glu_glob n); obtain ⟨A,p,P⟩:=prod_raft budgetW n (show 0≤composeCost n C Z by unfold composeCost; positivity)
 refine ⟨A,p,fun E _ _ m U x f ht hv r a=>?_⟩
 apply P E (List (Ramp m)) (permits m a r) (fun l t=>expNegInvGlue (rateF m B (U t) (f t) a l-broad)) _ (permits_cap ..); intro i s
 have e:=(permits_iff.mp s).1; obtain ⟨L,c,g,V⟩:=Y E m U x f ht hv a i e (total_len e)
 have hg:= G E (fun x=> (f x a).val) L x ((hv a).mono (le_max_right ..)) (c ▸ total_len e) (fun i h=> (V i h).mono (le_max_left ..))
 let A (x:E):= restrain margin (L.map (fun i=>i x)) (f x a).val
 rw [show (fun t=> expNegInvGlue (rateF m B (U t) (f t) a i-broad))=glue ∘ A from funext fun t=> by simp only [rateF,g]; rfl]
 exact ⟨(H _ hg.value).comp (f:=A) hg,fun v=>Allows.weave (glu_dead n v) hg⟩
variable {X:Type}[Fintype X][DecidableEq X]
abbrev ToR (n:ℕ){m:Side}(A:E→Cue m)(x:E)(K:ℝ):Prop:=∀ i, Allows n (fun x=>(A x i).val) x K
lemma aqua (n:ℕ)(g:0≤K)(B:Side)(S:Finset X):∃ C:ℝ,0≤C ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (m:Side)(U:E→Skin m B)(x:E)(f:E→X→ArrayF m)(A:E→Cue m), TransK n U x K→ (∀ i∈ S, arr n (fun t=>f t i) x K)→ ToR n A x K→∀ r j a, CashCold (fun x=>draw m B S (U x) (f x) r j a (A x)) x n C :=by
 obtain ⟨C,hC,H⟩:=token n g B; obtain ⟨V,hV,P⟩:=prod_raft S.card n hC
 refine ⟨V,hV,fun E _ _ m U x f A h l w r j a=>?_⟩; apply P E X S (fun i t=> dry m B (U t) (f t i) (r i) j a (A t)) _ le_rfl; intro i k; apply H E m U x (fun u=>capRow (f u i) j (A u)) h; intro v; by_cases p:v.2=j
 · simpa only [capRow,p,if_true] using w v.1
 simp_rw [capRow,if_neg p]; exact l i k v
lemma zap (S:Finset X)(hS:S.card≤6)(n:ℕ)(B:Side)(h:1≤K):∃ C:ℝ,0≤C∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (V:Set E),IsOpen V→∀(m:Side)(U:E→ Skin m B)(p:E→ X→ ArrayF m)(A:E→Cue m), (∀ x∈V,TransK n U x K ∧ ToR n A x K ∧ ∀ i∈S,arr n (fun t=>p t i) x K)→∀ j r a x,x∈V → CashCold (fun y=> priceW m B S (U y) (p y) r j a (A y)) x n C:=by
 obtain ⟨L,g,G⟩:= aqua n (zero_le_one.trans h) B S; obtain ⟨s,hs,H⟩:= payment S hS
 obtain ⟨C,u,q⟩:=payment_for n (isCompact_Icc (α:=ℝ) (a:=s) (b:=L)) (Inv.inv) (fun _ e=>contDiffAt_id.inv (hs.trans_le e.1).ne')
 let W:= composeCost n C L; have hw:0≤W:=by unfold W composeCost; positivity
 refine ⟨2^n*‖ContinuousLinearMap.mul ℝ ℝ‖*L*W,by positivity,fun E _ _ _ V e m U p A l j r a x hx=>?_⟩
 let F(t:Ballot)(y:E):= draw m B S (U y) (p y) r j a (update (A y) a t)
 let f(y:E) := limitW m B S (U y) (p y) r j a (A y); have hp y (k:y∈V) t:Allows n (F t) y L:=by
    apply (G E m U y p (fun x=>update (A x) a t) (l y k).1 (l y k).2.2 ?_ r j a).1
    intro i; by_cases he:i=a
    · simp only [he,update_self]; exact allows_const _ ((vote_unit t).trans_le h)
    simp_rw [update_of_ne he]; exact (l y k).2.1 i
 have hc(y:E):Continuous (fun t=>F t y) :=by
   let M:= turn_draw_cont m B S r j a
   let Y:=fun t:Ballot=> ((U y,p y,A y),t)
   have hp:Continuous Y:=continuous_const.prodMk continuous_id
   have ht:=M.comp hp; exact ht
 have T:= under (μ':=cloud) e (f:=F) (fun t y m=> (hp y m t).smooth) (fun y _=> (hc y).stronglyMeasurable) (integrable_const L) (fun t y k=> hp y k t)
 have hb:Allows n f x L:=by
    refine ⟨T.germ e hx,fun i hi=>?_⟩; change ‖iteratedFDeriv ℝ i (Planned.AtomRegular.average cloud F) x‖ ≤ L; rw [(T.less hi).differentiate e hx]; simpa using norm_integral_le_of_norm_le_const (C:=L) (μ:=cloud) (Eventually.of_forall (fun j=> (hp _ hx j).norm_le _ hi)) -- tune
 let f':E→ℝ:=fun y=>(f y)⁻¹; have hj:s ≤ f x := H ..; have hy:f x≠0:=(hs.trans_le hj).ne'
 have gD : Allows n f' x W:= (q (f x) ⟨hj,(le_abs_self _).trans hb.value⟩).comp hb
 have hg := G E m U x p A (l x hx).1 (l x hx).2.2 (l x hx).2.1 r j a
 simp_rw [priceW,div_eq_mul_inv]; refine ⟨hg.1.bilinear (ContinuousLinearMap.mul ℝ ℝ) gD (le_refl ‖ContinuousLinearMap.mul ℝ ℝ‖),fun h=>?_⟩
 have he:= (hg.2 ((mul_eq_zero.mp h).resolve_right (inv_ne_zero hy))).bilinear (ContinuousLinearMap.mul ℝ ℝ) gD le_rfl
 rw [mul_zero,zero_mul] at he; exact he
end YM.CF.Jet
