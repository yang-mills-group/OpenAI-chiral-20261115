import ForceSatin.Gentle
import Risa.Photon
import LusterS.Rogue
import YM.SU5.Regis.Trophy
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa.Gentle
open Regis ProbabilityTheory
variable {αu ε χ fuel Q0 b₁ b₂:ℝ}{Φ:Config G n→ℝ}{OT: Support c→Finset (Cell n)→ Altar G n→ℝ}
-- same pressure authority I, one further inclusive bill
variable (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ)(pα:0<αu)(uα:αu≤1)(kα:κ+(χ+ν+ε) ≤ β*(q.linear*p.threshold^2/2))(eD:χ+ν+ε ≤ β*(q.direct*(αu*p.threshold)^2/2))(g0:2*(r.count.val+1)<n.val) (eU:RG.Envelope Φ)(aW:∀ A D,ContDiff ℝ 1 (OT A D))(h1w:∀ A D x, |OT A D x|≤ b₁)(h2w:∀ A D x, ‖fderiv ℝ (OT A D) x‖≤ b₂)
abbrev trip₃ (Z:PathData G)(q:Clip)(p:BudgetPoint) (A:Support c)(D:Finset (Cell n))(T:Forest r)(αu β κ fuel v':ℝ)(U:T.Slice G):ℝ:=if broken r v' (T.drape U)=A ∧ weak (αu*p.threshold) (T.drape U)=D then goods Z q p β κ fuel v' (T.drape U) else 0

abbrev source₃ (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(D:Finset (Cell n))(T:Forest r)(αu β κ fuel v':ℝ)(Φ:Config G n→ℝ)(U:T.Slice G):ℝ:=trip₃ Z q p A D T αu β κ fuel v' U*Real.exp (Φ (T.drape U))
def TreeLease (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint){r:Ratio c n}(T:Forest r)(m:ℕ)(αu β v Q v':ℝ)(A:Support c)(D: Finset (Cell n))(φ:Config G n→ℝ)(W:Altar G n→ℝ):Prop:=
  ∀ (S:T.Slice G),let U:=T.drape S; ∀ (V Y:fieldDir G n 1), A=broken r v' U → D=weak (αu*p.threshold) U → ProbeBox (V+Y) (2*v)→ TrustLogs (V+Y) U r A v→ φ U ≤ W (starFee B P r A D m Y β V) + Q
variable {Q:Support c→Finset (Cell n)→ℝ}(W0:∀ A D,TreeLease B P p T m αu β v (Q A D+ε*D.card) v' A D Φ (OT A D))

private lemma env_form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩
include B in
lemma through_weak (αu:ℝ)(A:Support c)(D:Finset (Cell n)):Envelope (trip₃ Z q p A D T αu β κ fuel v'):=by
 let M:= T.drape (G:=G); have hm:Measurable M:= T.continuous_drape.measurable
 have he:= env_grow (n:=n) (p:=p) (β:=β) (κ:=κ) (v':=v') (fuel:=fuel) B
 exact Envelope.piece (p:=fun x=> broken r v' (M x)=A ∧ weak (αu*p.threshold) (M x)=D) (hm ((malaise_selector A r v').inter (weak_test _))) (env_form _ he _ hm) (Envelope.const 0)
include B eU in
lemma through_source₃(αu:ℝ)(A:Support c)(D:Finset (Cell n)):Envelope (source₃ Z q p A D T αu β κ fuel v' Φ):=(Gentle.through_weak B αu A D).mul ((env_form _ eU _ T.continuous_drape.measurable).exp)
include I g0 D' B P L eU aW h1w h2w pα uα kα eD W0

lemma roundSource (A:Support c)(D:Finset (Cell n))(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ bloom T univ A D m)(Y:LinkArray G (Blip T F)) : let W(w:LinkArray G F):= source₃ Z q p A D T αu β κ fuel v' Φ (deep T F w Y); (∫ x,W x ∂piHaar G (↥F)) ≤ kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)* Real.exp (jewelFee B P (OT A D) 1 b₂ T F (Q A D)):=by
 intro W; let K:=kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card; let u:↥F → G.El:=1; let XE:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • W (release u c); let X:= T.Slice G
 have hU: Envelope W:= env_form _ (through_source₃ B eU αu A D) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J u, W x=0:=by
    intro x vh; unfold W source₃ trip₃; split; swap; · rw [zero_mul]
    next H=>
      exact False.elim <| vh fun i _=>by
         let t:=currency I g0 A (deep T F x Y) H.1 (fun i p=> bloom_sub (hf p)) i; let X:=x i; let b:= G.plog (G.mat X); have ht: deep T F x Y i.val=X:=freeze_held ..; have hX:=t.2.2; simp only [ht] at hX; exact ⟨X,⟨b,hX.2,hX.1⟩,mul_one _⟩
 obtain ⟨hx,he⟩:= release_integral D' u W hU.meas.stronglyMeasurable hp
 let Ω:= OT A D
 let f:=weakWish B P T F A D m (myLog T F Y A) β Ω 1
 obtain ⟨hg',hl⟩:= at_weak (A:=A) (m:=m) B P L D (myLog T F Y A) hg ht Ω (aW A D) (h1w A D) (h2w A D) 1
 let tY:= (taxΔ R q n p β v η C S m - ξ*A.card)-(χ+ν)*D.card; let E(c):= K * Real.exp (Q A D)* f c; let M:= J.scale * Real.exp Λ; have hK :0≤K:=by unfold K kiosk; have h:=D'.scale; positivity
 have hE(c):0≤ E c:=mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
 change (∫ x,W x ∂piHaar G (↥F)) ≤ K*_*_; rw [he]; apply le_trans (b:=∫ x,E x)
 · apply integral_mono (hx.mp (hU.integrable _)) (hg'.const_mul _); intro c'; change XE.indicator G' c'≤ E c'; by_cases h:c'∈XE; swap; · rw [Set.indicator_of_notMem h]; exact hE _
   rw [Set.indicator_of_mem h]; let U:= deep T F (release u c') Y; let V:= T.drape U
   by_cases HR:broken r v' V=A ∧ weak (αu*p.threshold) V=D; swap; · unfold G' W source₃ trip₃; rw [if_neg HR, zero_mul,smul_zero]; exact hE _
   have hd(i:↥F): let z:=release u c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=currency I g0 A U HR.1 (fun _ e=> bloom_sub (hf e)) i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D'.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let pc:= source₃ Z q p A D T αu β κ fuel v' Φ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ (p.threshold_pos.trans_le I.hierarchy)).le.trans I.pale)
   let PP:BudgetPoint:={p with threshold:=v',threshold_pos:=p.threshold_pos.trans_le I.hierarchy,threshold_le:=I.cut}
   obtain ⟨h1,h2,h3,h4⟩:= beyondMake (p:=PP) F (fun _ e=> bloom_sub (hf e)) Y (release u c') HR.1 g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release u c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy: pc = goods Z q p β κ fuel v' V * Real.exp (Φ V):= by unfold pc source₃; rw [trip₃, if_pos HR]
   have ht: pc ≤ (Real.exp tY * Real.exp (Q A D)) * f c':=by
      rw [hy]; let q:=W0 A D U x Y' HR.1.symm HR.2.symm h2 h3
      apply (mul_le_mul (Gentle.weak_grip B pα uα HR.2.symm HR.1.symm I.hierarchy I.light ht h1 h2 h3 h4 (saved hf _) hp I.logo b I.zero_ξ kα eD I.brave) (Real.exp_le_exp.mpr q) (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
      unfold f weakWish scintillate; -- ε reserve cancels Q mark coupon on these D. no loss when combining with pivot
      rw [one_mul]; simp_rw [←Real.exp_add]; apply congrArg Real.exp; unfold tY x Y' Ω; ring
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D'.scale.le (D'.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D'.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*pc ≤ K*Real.exp (Q A D)* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (pow_nonneg (mul_nonneg D'.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); unfold K kiosk; ring
 unfold E; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hl (mul_nonneg hK (Real.exp_pos _).le)).trans_eq ?_
 let q':= (plumeCost B P Ω 1+ trend*b₂^2*(1:ℝ)^2+ ((Module.finrank ℝ (stamen B P n):ℝ)-(Module.finrank ℝ (LinearMap.range (estate B P T F))))/2)
 have hE: jewelFee B P Ω 1 b₂ T F (Q A D)=Q A D+q':=by unfold q' jewelFee; ring
 rw [show OT A D=Ω from rfl,hE, Real.exp_add (Q A D) q']; change K*_*(_*Real.exp q') = K*_ *_; ring
lemma source_inside (A:Support c)(D:Finset (Cell n))(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ bloom T univ A D m) : (∫ x,source₃ Z q p A D T αu β κ fuel v' Φ x ∂T.order G) ≤ kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)* Real.exp (jewelFee B P (OT A D) 1 b₂ T F (Q A D)) :=by
 let X:= Blip T F; let pc:=Held T (fun i=>i∈F); let L':= source₃ Z q p A D T αu β κ fuel v' Φ; let K:=kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)* Real.exp (jewelFee B P (OT A D) 1 b₂ T F (Q A D)); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((through_source₃ B eU αu A D).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundSource B P L D' I pα uα kα eD g0 eU aW h1w h2w W0 A D hg ht b hf i)) (le_of_eq ?_); simp [χ]

#print axioms source_inside
end Risa.Gentle
end YM.Gleam.Luster
