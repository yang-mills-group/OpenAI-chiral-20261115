import GaugeFieldConstruction.Solstice

/-! # Pay gauge rent under localized aggregate mark perturbation. Adapt Inlets & Danube,
     determinant of unperturbed already licensed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 30000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)


variable {Wa Da:Flaws n}{κ' k f₁ f₂ q':ℝ}{W:Altar G n→ℝ}{τ b Q:ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) (I:TopPrice J R q p r.count.val m β κ k f₁ f₂ v Λ q')
variable (g:0<β)(d:0≤ κ')(l:0≤ C)(j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)


abbrev tailored (T:Forest r)(U:Config G n):= gauge (T.foldAt U) U
lemma tailored_cont (T:Forest r): Continuous (tailored T (G:=G)):= by unfold tailored Lattice.gauge; refine continuous_pi (fun i=> ((Forest.folds T _).mul (continuous_apply i)).mul ((Forest.folds T _).inv))
lemma tall_root (T:Forest r)(x:Site n→G.El)(h:∀ i,x (r.embed i)=1) (U:Config G n) : tailored T (gauge x U)=tailored T U:=by
 unfold tailored; have e(y:Site n): T.foldAt (gauge x U) y * x y=T.foldAt U y:=by
   simp only [Forest.foldAt,travel_gauge,T.hike_root,h,inv_one,mul_one,_root_.mul_inv_rev, _root_.mul_assoc, inv_mul_cancel]
 funext i; let k:= i.1+step i.2; change T.foldAt (Lattice.gauge x U) i.1*(x i.1*U i*(x k)⁻¹)*(T.foldAt (Lattice.gauge x U) k)⁻¹=T.foldAt U i.1*U i*(T.foldAt U k)⁻¹
 rw [←e i.1,← e k]; simp only [_root_.mul_inv_rev, _root_.mul_assoc]
lemma fold_none (T:Forest r)(V:T.Slice G): T.foldAt (T.drape V)=1:=by
 let A:Config G n:=1; rw [T.names (V:=A) _ (fun i h=>(T.on_tree V ⟨i,h⟩))]; funext i; unfold Forest.foldAt; have he (w:Walk)(x: Site n): travel A x w=1:=by
    induction w generalizing x with
    | nil=> rfl
    | cons a w ih=> rw [travel,ih]; simp [Step.read,A]
 rw [he,inv_one]; rfl
lemma tailored_at (T:Forest r)(U:T.Slice G): tailored T (T.drape U)=T.drape U:=by rw [tailored,fold_none]; unfold Lattice.gauge; funext; simp
lemma tailor_cut (T:Forest r)(U:Config G n) : tailored T U=T.drape ((T.seam (tailored T U)).2):=by
 let v:= T.seam (tailored T U); let k:=(v.1,v.2); have h:v.1=1:= funext fun i=>T.compress U i.val i.property; change _ = T.seam.symm (1,v.2); rw [←h]; exact (T.seam.symm_apply_apply (tailored T U)).symm
lemma tagged_union : (∑ W:Flaws n, ∑ D: Flaws n, day_play Z q p W D T β κ k q' φ X) = richBoth Z q p β κ k q' (T.drape X) * Real.exp (φ (T.drape X)):=by
 let A:= T.drape X; rw [sum_eq_single (misdemean p.threshold A),sum_eq_single (misdemean q' A)]
 · unfold day_play; rw [if_pos (show Location_H p q' _ _ _ from ⟨rfl,rfl⟩)]
 · intro d _ x; unfold day_play; rw [if_neg (fun g=>x g.2.symm)]
 · intro z; exact (z (mem_univ _)).elim
 · intro v _ h; apply sum_eq_zero; intro u _; unfold day_play; rw [if_neg (fun g=> h g.1.symm)]
 intro z; exact (z (mem_univ _)).elim
lemma EnvelopeTall {T:Forest r} (E:Envelope φ) : Envelope (fun x:Config G n=> φ (tailored T x)):= ⟨E.meas.comp (tailored_cont T).measurable, E.cost.choose,fun x=> E.cost.choose_spec _⟩
private lemma bits_single(n:Side)(u:ℝ) : (∑ i:Flaws n,Real.exp (u*i.card)) ≤ Real.exp ((Fintype.card (Cell n):ℝ)*Real.exp u):=by
 let a:=Real.exp u; let s:= Fintype.card (Cell n); rw [show (∑ i:Flaws n,Real.exp (u*i.card))=(1+a)^s from ?_]; swap
 · change (∑ i:Flaws n,Real.exp (u*i.card))=(1+a)^s; rw [add_comm,show (a+1)^s=∏ i:Cell n,(a+1) by simp [s], Fintype.prod_add]; simp only [prod_const, one_pow,mul_one]
   refine sum_congr rfl fun i _=>?_ ; rw [mul_comm,Real.exp_nat_mul]
 rw [Real.exp_nat_mul]; apply pow_le_pow_left₀ (by positivity) _ _; rw [add_comm]; exact Real.add_one_le_exp _
abbrev aggregateA (R:PathData G)(p:BudgetPoint)(q:Clip)(β κ k q':ℝ)(T:Forest r)(A:Config G n→ℝ)(U:Config G n):= richBoth R q p β κ k q' U * Real.exp (A (tailored T U))
include B u
lemma aggregateEnv : Envelope (aggregateA Z p q β κ k q' T φ):= (envelopTogether B).mul ((EnvelopeTall u).exp)
lemma fullIntegral (T:Forest r)(wa k' q₀:ℝ):
 (∫ x:Config G n,aggregateA Z p q β wa k' q₀ T φ x∂prior G n) = ∑ Wa:Flaws n, ∑ Da:Flaws n,(∫ x,day_play Z q p Wa Da T β wa k' q₀ φ x∂T.order G):=by
 let X:= aggregateA Z p q β wa k' q₀ T φ; let Y:=T.drape (G:=G)
 change (∫ x:Config G n,X x∂prior G n)= _; rw [T.pack _ ((aggregateEnv B u).integrable _)]; swap; · intro k c U; unfold aggregateA; rw [tall_root T k c,richBoth, malaise_home, richG_inv B]; rfl
 rw [show (fun x:T.Slice G=> X (Y x))= fun x:T.Slice G=> ∑ i:Flaws n, ∑ t:Flaws n, day_play Z q p i t T β wa k' q₀ φ x from funext (fun x=> by unfold X aggregateA; rw [tagged_union]; unfold Y; rw [tailored_at])] -- tune
 rw [integral_finsetSum]; apply sum_congr rfl; intro i _; rw [integral_finsetSum]; exact fun j _=> (env_lease B u i j).integrable _
 intro i _; exact integrable_finsetSum _ fun j _=> (env_lease B u i j).integrable _
variable (g0:2*(r.count.val+1)<n.val) {Wake Weight Dorm:ℝ} -- Wake,Weight charges on day_play, maturity. Dorm any uniform (nonlocal).
-- Simplifying: Stoke accounts all ε over mask summands individually.
def ModerateP (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(T:Forest r)(m:ℕ)(σ β v Q:ℝ)(t u:ℝ)(φ:Config G n→ℝ): Prop:=∀ Wa Da:Flaws n, ∃ (W:Altar G n→ℝ)(t' Q' a b:ℝ),ContDiff ℝ 1 W ∧ (∀ x,|W x|≤ a) ∧ (∀ x,‖fderiv ℝ W x‖≤ b) ∧ Clarity B P p T m Wa Da σ β v Q' t' φ W ∧ Q' + plumeCost B P W t'+trend*b^2*t'^2 ≤ Q + t*Wa.card+u*Da.card
-- need one-sided Clarity assumption excluding exactly-threshold (a.e.). Our above estimates of emblem m_t compare include gates possibly equality; can add all equality mem as defects by > τ/2 and switch charge in P2, or modify Φ on null set. Do latter.
omit u in
lemma moderated_vacuum (v Wake Weight:ℝ)(T:Forest r)(φ:Config G n→ℝ)(U:0≤Wake)(pD:0≤Weight)
 (f:∀ X:T.Slice G,φ (T.drape X)≤ Dorm): ModerateP B P p T m q' β v Dorm Wake Weight φ:=by
   intro Wa Da; refine ⟨fun _=> 0,0,Dorm,0,0,contDiff_const,by simp,by simp,fun X V Y _ _ _ _=> (f X).trans_eq (by ring),?_⟩
   unfold plumeCost; simp only [zero_mul,add_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero]; have hz:0 ≤ Wake*Wa.card:= by positivity
   have hu:0 ≤ Weight*Da.card:=by positivity
   linarith only [hz,hu] -- remove B u issue implicit
abbrev dewCost (n:Side)(τ ψ:ℝ):= (Fintype.card (Cell n):ℝ)*(Real.exp τ+Real.exp ψ)
include B P D I L d g j wH uH u l he g0
lemma at_height (Vk: ModerateP B P p T m q' β v Dorm Wake Weight φ): (∫ x:Config G n, aggregateA Z p q β κ k q' T φ x∂prior G n) ≤ Real.exp (Roof J β n H+cutRate J R q p r m κ' β v Λ η C S+Dorm + dewCost n (reachΔ J R q m β κ'+Wake-f₁) (castΔ J R q r β κ'+Weight-f₂)):=by
 let C₀:= cutRate J R q p r m κ' β v Λ η C S; let E:= Roof J β n H+C₀+Dorm; let L₁:=reachΔ J R q m β κ'; let L₂:=castΔ J R q r β κ'; let τ:= L₁+Wake - f₁; let ψ:= L₂+Weight-f₂
 let R₁(Wa:Flaws n):= τ*Wa.card; let R₂(Wa:Flaws n):= ψ*Wa.card
 let Vap Wa Da := ∫ x,day_play Z q p Wa Da T β κ k q' φ x ∂T.order G
 obtain ⟨F,h⟩:= buttress_uses T
 have hh(Wa Da:Flaws n): Vap Wa Da ≤ Real.exp E * Real.exp (R₁ Wa) * Real.exp (R₂ Da):=by
    obtain ⟨W,t,Q,a,b,o,hx,hy,z,i⟩:= Vk Wa Da
    apply (one_house B P L D u I g d l j wH uH he g0 Wa Da h W t a b Q o hx hy z).trans -- tune order
    rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; change (_ + C₀ + (L₁-f₁)*(Wa.card:ℝ) + (L₂-f₂)*(Da.card:ℝ)+ _ + _ + _)≤ _; unfold R₁ R₂ τ ψ E; linarith only [i]
 rw [fullIntegral B u]; apply le_trans (sum_le_sum (fun i _=> sum_le_sum (fun d _=>hh i d)))
 have ht: 0≤ ∑ t:Flaws n,Real.exp (R₂ t):= sum_nonneg fun x _=> (Real.exp_pos _).le
 let F(Wa:Flaws n):=Real.exp E*Real.exp (R₁ Wa); let M:ℝ:= Fintype.card (Cell n)
 simp_rw [← mul_sum]; rw [← sum_mul, ← mul_sum]; refine (mul_le_mul (mul_le_mul_of_nonneg_left (bits_single n τ) (Real.exp_pos _).le) (bits_single n ψ) ht (by positivity)).trans_eq ?_; rw [← Real.exp_add,← Real.exp_add]; unfold dewCost; congr 1; change E+M*_ + M*_ = E+ M*_; ring
end YM.Gleam
end
