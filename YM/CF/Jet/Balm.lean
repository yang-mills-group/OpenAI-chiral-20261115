import YM.CF.Broc.Savant
import YM.CF.Jet.Roc
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
lemma breezeT(n:ℕ){K:ℝ}(hK:0≤K) (B:Side):∃ C:ℝ, 0≤C ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](m:Side)(U:E→Skin m B)(f:E→ArrayF m)(x:E),TransK n U x K→ arr n f x K→∀(q:Sq),prob q→∀ z,Allows n (fun x=>paint m B (U x) (f x) q z) x C :=by
 obtain ⟨D,d,H⟩:=factor_is hK n (4*B.val)
 let N:=max D K; have hn:0≤N:=hK.trans (le_max_right ..)
 let F(x:Op SU.F×Vect):=acts x.1 x.2
 obtain ⟨C,v,T⟩:= compact_allow n hn F (act_is n)
 let c:=composeCost n C N; have hp:0≤c:=by unfold c composeCost; positivity
 let r:ℝ:=Fintype.card Lattice.Order; let W:=|r⁻¹| *(r*c); have ht:0≤W:=by unfold W r; positivity
 refine ⟨W,ht,fun E _ _ m U t x h q s a z=> ?_⟩
 have hg (i:Spot m) (b:i∈bandS m B z s) (o:Lattice.Order):Allows n (fun x=>launch m B (U x) z i.1 o (t x i)) x c:=by
    let P(v:E):= (SU.fund (tax m B (U v) z i.1 o),(t v i).val); have he:separation (address m B i.1) z ≤ B.val := (separation_comm ..).trans_le (node_dist (spot_hit b)).le
    have hh:Allows n P x N:= ((H E _ _ x h z (march z (address m B i.1) o) (march_len _ _ _ he)).mono (le_max_left ..)).pair ((q i).mono (le_max_right ..))
    exact (T (P x) hh.value).comp (f:=P) hh
 have hp(i:Spot m)(b:i∈bandS m B z s): Allows n (fun x=> freight m B (U x) z i.1 (t x i)) x W:=by
    unfold W r; have he:=(allows_sum (s:= Finset.univ) (fun o (_:o∈ Finset.univ)=>hg i b o)).smul r⁻¹
    unfold freight; simp only [sum_const,nsmul_eq_mul,card_univ] at he; exact he
 let c(i:Spot m):=cash m B z s i
 have hc:= allows_sum (n:=n) (x:=x) (s:=Finset.univ) (f:=fun i x=> c i • freight m B (U x) z i.1 (t x i)) (C:=fun i=>c i*W) (fun i _=> ?_)
 · rw [←sum_mul, show ∑ i:Spot m,c i=1 from cash_sum _ _ _ _ a, one_mul] at hc; exact hc
 by_cases g:i∈bandS m B z s
 · have he:= (hp i g).smul (c i); rw [abs_of_nonneg (show 0≤c i from cash_nonneg ..)] at he; exact he
 rw [show c i=0 from outside g,zero_mul]; simp_rw [zero_smul]; exact allows_const _ (norm_zero.le)
lemma box_k (n:ℕ){K:ℝ}(p:0≤K):∃ C:ℝ, 0≤C ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](f:E→Vect) x,Allows n f x K→ low/2 ≤ ‖f x‖→ Allows n (fun x=>(Brace.box (f x)).val) x C:=by
 let S := closedBall (0:Vect) K ∩ {x:Vect| low/2≤‖x‖}
 have h(y)(hy:y∈S):ContDiffAt ℝ (↑n:WithTop ℕ∞) ren y:=by
    have he:0<‖y‖:=(half_pos low_p).trans_le hy.2
    exact ((contDiffAt_norm ℝ (norm_pos_iff.mp he)).inv he.ne').smul contDiffAt_id
 obtain ⟨C,v,T⟩:= payment_for n ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)) _ h
 refine ⟨composeCost n C K,by unfold composeCost; positivity,fun E _ _ f x hx he=>?_⟩
 apply ((T (f x) ⟨mem_closedBall_zero_iff.mpr hx.value,he⟩).comp hx).germ
 filter_upwards [hx.smooth.continuousAt.eventually_ne (norm_pos_iff.mp ((half_pos low_p).trans_le he))] with y hy using (box_u hy).symm
lemma ark_quota(n:ℕ){K:ℝ}(hK:0≤K) (B:Side):∃ C:ℝ, K≤C ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](m:Side)(U:E→Skin m B)(f:E→ArrayF m)(X:E→Sheen m B)(x:E),TransK n U x K→ arr n f x K → seek X n x K → ∀ (q:Sq),prob q→∀ v:ℝ,v∈ Set.Icc 0 1→(∀ z, low/2 ≤ ‖roofV m B (U x) (f x) (X x) v q z‖)→ seek (fun y=>ark m B (U y) (f y) (X y) v q) n x C :=by
 obtain ⟨C,c,P⟩:=breezeT n hK B; obtain ⟨W,w,G⟩:= box_k n (add_nonneg c hK)
 refine ⟨max K W,le_max_left ..,fun E _ _ m U f X x h i j q p v ev hp y=>?_⟩
 let F(t:E):=roofV m B (U t) (f t) (X t) v q y
 obtain ⟨he,hV⟩:=ev; have hl:0≤1-v:=by linarith
 have hx:= P E m U f x h i q p y; have hz: Allows n F x (C+K):=by
    apply Allows.add (f:=fun x=>v • paint m B (U x) (f x) q y) (f':=fun x=>(1-v) • hook (X x) y) ((hx.smul v).mono ?_) (((j y).smul (1-v)).mono ?_)
    · rw [abs_of_nonneg he]; exact mul_le_of_le_one_left c hV
    rw [abs_of_nonneg hl]; exact mul_le_of_le_one_left hK (by linarith)
 exact ((G E F x hz (hp y)).mono (le_max_right ..))
lemma star_cost (n:ℕ){K:ℝ}(hK:0≤K)(B:Side):∃ C:ℝ,K≤C ∧∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](m:Side)(U:E→Skin m B)(f:E→Cue m)(x:E),TransK n U x K→ToR n f x K→∀e p:ℝ,0≤e→Guard (U x) e→ZeroF m B (U x) (f x)→ enoughV B e p→ seek (fun t=>starfish m B (U t) (f t)) n x C:=by
 obtain ⟨C,c,H⟩:=breezeT n hK B; obtain ⟨D,d,F⟩:= box_k n c; refine ⟨max K D,le_max_left ..,fun E _ _ m U f x hf g e p u k K h i=>?_⟩
 let v:=stick (0: Row); let y:=fun t=> paint m B (U t) (slot m (f t)) v i
 have ht:v∈Phase.zone {(0:Row)}:= stick_in _ (mem_singleton_self _)
 have hm:= H E m U _ x hf (show arr n (fun t=>slot m (f t)) x _ from fun i=> g i.1) v ht.1 i
 exact ((F E y x hm (prism_nonzero _ ht.1 u k (r:={0}) K ht.2 h.1 i)).mono (le_max_right ..))
end YM.CF.Jet
