import GaugeFieldConstruction.Hurl
/-! # Budget port (additional holes). Affine FI row cost measured with the very same derivative operators -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)

namespace Guide
open Regis ProbabilityTheory
-- one position support expressed in pulled axes
abbrev LightM (r:Ratio c n)(Wa Da:Flaws n)(m:ℕ)(S:Support n) := ∀ y∈S, Brisk r (grid_break r Da) Wa (hallBill m) y
def bayColour (F:Support n)(b:Altar G n):ℝ:=Real.sqrt (∑ x∈Finset.univ.filter (fun (i:Cell n×Bool×G.ColorIndex)=>i.1.1∈ F), (b x)^2)
structure Atlas (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(T:Forest r)(m:ℕ)(X Y:ℝ)(β θ v:ℝ)(b:Support n)(μ:Config G n→ℂ)(F:Altar G n→ℂ) : Prop where
 cost (x:Altar G n): ‖F x‖ ≤ X
 dist (x y): ‖F x-F y‖ ≤ X*bayColour b (x-y)
 diff : ContDiff ℝ 1 F
 mark(Wa Da:Flaws n)(h:LightM r Wa Da m b)(A:T.Slice G) (V D:fieldDir G n 1) : let E:= T.drape A; let X:=grid_break r Da;
           Location_H p θ Wa Da E→CF.Rue.FleetS p.threshold E→ ProbeBox (V+D) (2*v) →abandons_A V r X Wa m→TrustLogs (V+D) E r X v → ‖μ E- F (starOf B P r X Wa m D β V)‖≤ Y
abbrev collectionS (B:Z.Bounds q η C S)(P:Attached H Z)(F:Altar G n→ℂ) := ∫ x, F ((stamen B P n).starProjection x)∂stdGaussian (Altar G n)
variable {W:Flaws n}{θ R' u xK d D:ℝ}{b':Support n}{V:Altar G n→ℂ}{Zκ:Config G n→ℂ}
lemma clouded (A: Atlas B P p T m xK u β θ v b' Zκ V): Integrable (fun x=> V ((stamen B P n).starProjection x)) (stdGaussian (Altar G n)):= (integrable_const xK).mono' ((A.diff.continuous.comp (stamen B P n).starProjection.continuous).aestronglyMeasurable) (Eventually.of_forall fun i=> A.cost _)
lemma tuned_bank (A: Atlas B P p T m xK u β θ v b' Zκ V) : ‖collectionS B P V‖ ≤ xK:= by apply (norm_integral_le_of_norm_le (integrable_const xK) (Eventually.of_forall fun i=>A.cost _)).trans_eq; simp
lemma extinct (τ:ℝ) : MeasurableSet {U:Config G n| CF.Rue.FleetS τ U}:=by
 rw [show {U:Config G n|_}= ⋂ t:Cell n,{U:Config G n|G.chord (faceValue U t) ≠ τ} from ?_]; swap; · ext; simp only [Set.mem_setOf_eq,Set.mem_iInter]
 apply MeasurableSet.iInter; intro i; exact (isOpen_ne_fun (f:=fun U:Config G n=> G.chord (faceValue U i)) (by unfold faceValue; fun_prop) continuous_const).measurableSet
lemma shade_b (q:Support n)(y:Altar G n): 0≤ bayColour q y := Real.sqrt_nonneg _
private abbrev asP (G:Gauge)(X:Support n) := Finset.univ.filter (fun i:Cell n×Bool×G.ColorIndex=>i.1.1∈ X)
variable {J:Type*} (F:Finset J)(K: J→Support n)
lemma bay_earn (p:Set.PairwiseDisjoint ↑F K)(y:Altar G n): ∑ i∈F,bayColour (K i) y ≤ Real.sqrt F.card *‖y‖:=by
 let f(i):= asP G (K i); have hf : Set.PairwiseDisjoint ↑F f :=by intro i hi j hj t; exact Finset.disjoint_left.mpr fun x a v=> Finset.disjoint_left.mp (p hi hj t) (mem_filter.mp a).2 (mem_filter.mp v).2
 apply (sq_le_sq₀ (sum_nonneg (fun i _=> shade_b ..)) (by positivity)).mp; apply (show _ ≤ (F.card:ℝ)*∑ i∈F, bayColour (K i) y ^2 from by simpa using (Finset.sum_mul_sq_le_sq_mul_sq F (fun i=> (1:ℝ)) (fun i=>bayColour (K i) y))).trans -- lair from Flan not imported replace
 rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
 change (∑ j∈F,(Real.sqrt (∑ i∈f j,y i^2))^2) ≤ _; simp_rw [show ∀ j:J,(Real.sqrt (∑ i∈f j,y i^2))^2= _ from fun j=>Real.sq_sqrt (sum_nonneg (fun i (_:i∈f j)=> sq_nonneg (y i)))]
 rw [EuclideanSpace.real_norm_sq_eq]; apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (F.biUnion f)) (fun i _ _=> sq_nonneg (y i))); rw [Finset.sum_biUnion hf]
lemma dispersed (p:Set.PairwiseDisjoint ↑F K) (A:Finset (Site n)) (Q:Finset J)(he:Q⊆F)(hx:∀ i∈Q, ∃ x∈K i,x∈A): Q.card≤ A.card:=by
 classical
 let g:= fun b:↥Q=>(hx b.val b.property).choose; let hg(i:↥Q):= (hx i.val i.property).choose_spec
 have ht:Injective g:= by intro i j h; by_contra f; apply Finset.disjoint_left.mp (p (he i.property) (he j.property) (fun t=> f (Subtype.ext t))) (hg i).1 (by change g i ∈ K ↑j; rw [h]; exact (hg j).1) -- tune
 have hv:= Fintype.card_le_of_injective (fun i:↥Q=> (⟨g i,(hg i).2⟩:↥A)) (fun i j h=> ht (congrArg Subtype.val h)); simp only [Fintype.card_coe] at hv; exact hv
variable {a M z:ℝ}
private abbrev echoP (z:ℂ) (M:Altar G n→ℂ)(w:ℂ) (y:Altar G n):ℝ:= (z*(M y-w)).re
lemma hallChime (u:J→ℂ)(v0:0≤z)(h:∀ i∈F,‖u i‖≤z)(d:0≤xK)(A:J→Altar G n→ℂ)(μ:J→ Config G n→ℂ)(t:∀ i∈F, Atlas B P p T m xK M β θ v (K i) (μ i) (A i))(pA:Set.PairwiseDisjoint ↑F K)(X:J→ℂ) :let f(y:Altar G n):=∑ i∈F,echoP (u i) (A i) (X i) y
 ContDiff ℝ 1 f ∧ ∀ i, ‖fderiv ℝ f i‖≤ z*xK*Real.sqrt F.card:=by
 intro f; refine ⟨ContDiff.sum fun i h=>?_,fun i=>?_⟩
 · exact ContDiff.comp Complex.reCLM.contDiff (ContDiff.mul contDiff_const ((t _ h).diff.sub contDiff_const)) -- tune
 let C:ℝ:= z*xK; have hp : 0 ≤ C:=mul_nonneg v0 d; refine norm_fderiv_le_of_lipschitz ℝ (C:=⟨C*Real.sqrt F.card,by positivity⟩) (LipschitzWith.of_dist_le_mul fun x y=>?_)
 rw [dist_eq_norm,dist_eq_norm, Real.norm_eq_abs]; unfold f; rw [←sum_sub_distrib];
 refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun j=> C*bayColour (K j) (x-y)) (fun j hj=> ?_)).trans ?_)
 · unfold echoP; rw [← Complex.sub_re,←mul_sub,sub_sub_sub_cancel_right]; apply (Complex.abs_re_le_norm _).trans; rw [norm_mul,mul_comm C]; exact (mul_le_mul (h j hj) ((t j hj).dist x y) (norm_nonneg _) v0).trans_eq (by unfold C; ring)
 rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (bay_earn F K pA (x-y)) hp).trans_eq (mul_assoc ..).symm
-- Clarity support toggled at nondefective-threshold sets as bookkeeping; measure estimates use all probes themselves.
def restrictU (p:BudgetPoint)(v:ℝ)(X:Config G n→ℝ)(U:Config G n):= if CF.Rue.FleetS p.threshold U then X U else -v
lemma restrictU_h (P:BudgetPoint)(a:ℝ){W:Config G n→ℝ}(E: Envelope W) : Envelope (restrictU P a W):= Envelope.piece (p:=fun U:Config G n=> CF.Rue.FleetS P.threshold U) (extinct _) E (Envelope.const _)
lemma bill_h (pA:Set.PairwiseDisjoint ↑F K) (pQ:Odd r.count.val)(u:hallBill m≤ r.count.val/2)(Wa Da:Flaws n) : let Y:= F.filter (fun i=>¬LightM r Wa Da m (K i)); Y.card≤wallTax (grid_break r Da) Wa r (hallBill m):=by
 intro Q; refine (dispersed F K pA (Danes (grid_break r Da) Wa r (hallBill m)) Q (filter_subset ..) ?_).trans (Danes.tall pQ u)
 intro i h; have he: ¬ LightM r Wa Da m (K i):=(mem_filter.mp h).2; unfold LightM at he; push Not at he; obtain ⟨j,p,w⟩:=he
 exact ⟨j,p,mem_filter.mpr ⟨mem_univ _,w⟩⟩
lemma HS_B [DecidableEq J](u:J→ℂ)(v0:0≤z)(h:∀ i∈F,‖u i‖≤z)(d:0≤xK)(A:J→Altar G n→ℂ)(μ:J→ Config G n→ℂ)(t:∀ i∈F, Atlas B P p T m xK M β θ v (K i) (μ i) (A i))(pA:Set.PairwiseDisjoint ↑F K)(X:J→ℂ)(Q:ℝ)(hq:∀ i∈F,‖collectionS B P (A i)-X i‖≤Q): let f(y:Altar G n):=∑ i∈F,echoP (u i) (A i) (X i) y
    plumeCost B P f 1 ≤ (F.card:ℝ)*(z*Q):=by
 intro f; unfold plumeCost; rw [one_mul]; let q(x):=(stamen B P n).starProjection x; let δ:=stdGaussian (Altar G n)
 let g(i:J)(x:Altar G n):= u i*(A i (q x)-X i); have hp(i:J)(p:i∈F) :Integrable (g i) δ:= ((clouded B P (t i p)).sub (integrable_const (X i))).const_mul _
 change (∫ x,(∑ i∈F,(g i x).re)∂δ) ≤ _; rw [integral_finsetSum]; swap; · exact fun i b=> Complex.reCLM.integrable_comp (hp i b)
 apply le_trans (Finset.sum_le_sum (g:=fun _=>z*Q) ?_); swap; · intro i w; rw [show (∫ x,(g i x).re ∂δ)= (∫ x,g i x ∂δ).re from (Complex.reCLM.integral_comp_comm (hp i w)), show (∫ x,g i x∂ δ)= u i*(collectionS B P (A i)-X i) from (by unfold g; rw [integral_const_mul,integral_sub (clouded B P (t i w)) (integrable_const _),integral_const, probReal_univ,one_smul])]; apply le_trans (le_abs_self _) ((Complex.abs_re_le_norm _).trans ?_); rw [norm_mul]; exact mul_le_mul (h i w) (hq i w) (norm_nonneg _) v0
 simp
lemma ChimeB [DecidableEq J](u:J→ℂ)(v0:0≤z)(h:∀ i∈F,‖u i‖≤z)(d:0≤xK)(A:J→Altar G n→ℂ)(μ:J→ Config G n→ℂ)(t:∀ i∈F, Atlas B P p T m xK M β θ v (K i) (μ i) (A i))(pA:Set.PairwiseDisjoint ↑F K)(X:J→ℂ)(Q:ℝ)(hq:∀ i∈F,‖collectionS B P (A i)-X i‖≤Q)(uM uT:ℝ)(hM:∀ i∈F,∀ Y,‖μ i Y‖≤uM)(hT:∀ i∈F, ‖X i‖≤uT)(tM:0≤uM)(tT:0≤uT)
 (E c' d₀:ℝ)(bQ:0≤Q)(m0:0 ≤ M) (pQ:Odd r.count.val)(wQ:hallBill m≤r.count.val/2)
 (e:∀ Wa Da:Flaws n,(z*(uM+uT))*wallTax (grid_break r Da) Wa r (hallBill m) ≤ E+c'*Wa.card+d₀*Da.card):
 let W(V:Config G n):=∑ i∈F,(u i*(μ i V-X i)).re; let o:=(F.card:ℝ)*(z*(xK+uT))
 ModerateP B P p T m θ β v ((F.card:ℝ)*(z*(M+Q))+ E + trend*(z*xK)^2*F.card) c' d₀ (restrictU p o W):=by
 intro W o Wa Da; let V:=grid_break r Da; let L:=F.filter (fun i=>LightM r Wa Da m (K i))
 let Ψ:=fun y:Altar G n=>∑ i∈L,echoP (u i) (A i) (X i) y; have hp:L⊆ F:=filter_subset ..
 have hh :Set.PairwiseDisjoint ↑L K:= fun i v j z=> pA (hp v) (hp z)
 have ht': (L.card:ℝ) ≤ F.card:=Nat.cast_le.mpr (card_le_card hp)
 let bK:= z*xK*Real.sqrt F.card
 obtain ⟨hw,l⟩:= hallChime B P L K u v0 (fun i v=> h i (hp v)) d A μ (fun i v=>t i (hp v)) hh X
 let M':=(F.card:ℝ)*(z*M)+(z*(uM+uT))*(wallTax V Wa r (hallBill m):ℝ);
 have hf:0≤M':= add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg v0 m0)) (mul_nonneg (mul_nonneg v0 (add_nonneg tM tT)) (Nat.cast_nonneg _))
 have hz(i:J)(a:ℂ)(t:i∈F)(b:ℝ)(e:‖a‖≤b): |(u i*(a-X i)).re| ≤ z* (b+uT) := (Complex.abs_re_le_norm _).trans (by rw [norm_mul]; exact mul_le_mul (h i t) ((norm_sub_le ..).trans (add_le_add e (hT i t))) (norm_nonneg _) v0)
 have hi(a):|Ψ a|≤o:=by apply (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun i p=>hz i _ (hp p) xK (t i (hp p)|>.cost _))).trans ?_); rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right ht' (mul_nonneg v0 (add_nonneg d tT))
 refine ⟨Ψ,1,M',o,bK,hw,hi,fun x=> (l x).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht') (mul_nonneg v0 d)),?_,?_⟩
 · intro Z ε D U X' c₁ e₁ e₂ e₃
   let z0:= starOf B P r V Wa m D β ε; unfold restrictU; change (if CF.Rue.FleetS p.threshold U then W U else -o) ≤ _
   split
   next iQ =>
     unfold W; let N:= F\L; have hv(i)(v:i∈L): (u i*(μ i U-X i)).re ≤ echoP (u i) (A i) (X i) z0+z*M:=by
        apply sub_le_iff_le_add'.mp -- check orientation
        unfold echoP; rw [← Complex.sub_re,←mul_sub,sub_sub_sub_cancel_right]; refine (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans ?_); rw [norm_mul]; exact mul_le_mul (h i (hp v)) ((t i (hp v)).mark Wa Da ((mem_filter.mp v).2) Z ε D c₁ iQ e₁ e₂ e₃) (norm_nonneg _) v0
     have he : N.card≤wallTax V Wa r (hallBill m):= by
        have hp: N= F.filter fun i=> ¬LightM r Wa Da m (K i):=by ext; simp [N,L]; tauto
        rw [hp]; exact bill_h F K pA pQ wQ Wa Da
     rw [←Finset.sum_sdiff hp]; apply (add_le_add (Finset.sum_le_sum (g:=fun _=> z*(uM+uT)) (fun j k=>by have hx: j∈F:=(mem_sdiff.mp k).1; exact (le_abs_self _).trans (hz j _ hx _ (hM j hx U)))) (Finset.sum_le_sum (fun i p=> hv i p))).trans
     rw [sum_add_distrib,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul]; apply le_trans (add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr he) (by positivity)) (add_le_add_right (mul_le_mul_of_nonneg_right ht' (mul_nonneg v0 m0)) _)); unfold M'
     change _+(Ψ z0+_ ) ≤ 1*Ψ z0+(_+_); linarith -- normalize V
   next k=> exact le_trans (show -o≤ 1*Ψ z0 from (by rw [one_mul]; exact (abs_le.mp (hi z0)).1)) (le_add_of_nonneg_right hf)
 unfold bK; rw [one_pow,mul_one,mul_pow, Real.sq_sqrt (Nat.cast_nonneg _|>.trans le_rfl)]
 let f':= plumeCost B P Ψ 1; have hv:f'≤ (F.card:ℝ)*(z*Q):= (HS_B B P L K u v0 (fun i v=> h _ (hp v)) d A μ (fun i v=>t _ (hp v)) hh X Q fun i v=>hq _ (hp v)).trans (mul_le_mul_of_nonneg_right ht' (mul_nonneg v0 bQ))
 unfold M' V; unfold f' at hv; linarith only [hv, e Wa Da]
end Guide
end YM.Gleam
end
