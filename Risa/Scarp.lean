import Risa.Grip
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
namespace Risa
open Regis ProbabilityTheory
variable {χ fuel Q0 b₁ b₂:ℝ}{Φ:Config G n→ℝ}{OT: Support c→Finset (Cell n)→ Altar G n→ℝ}
-- same pressure authority I, one further inclusive bill
variable (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ)(eD:χ+ν ≤ β*(q.direct*p.threshold^2/2))(g0:2*(r.count.val+1)<n.val) (eU:RG.Envelope Φ)(aW:∀ A D,ContDiff ℝ 1 (OT A D))(h1w:∀ A D x, |OT A D x|≤ b₁)(h2w:∀ A D x, ‖fderiv ℝ (OT A D) x‖≤ b₂)
abbrev source₂ (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(D:Finset (Cell n))(T:Forest r)(β κ fuel v':ℝ)(Φ:Config G n→ℝ)(U:T.Slice G):ℝ:=trip₂ Z q p A D T β κ fuel v' U*Real.exp (Φ (T.drape U))
def GradeLease (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(r:Ratio c n)(m:ℕ)(β v Q v':ℝ)(A:Support c)(D: Finset (Cell n))(φ:Config G n→ℝ)(W:Altar G n→ℝ):Prop:=
  ∀ (U:Config G n)(V Y:fieldDir G n 1), A=broken r v' U → D=weak p.threshold U → ProbeBox (V+Y) (2*v)→ TrustLogs (V+Y) U r A v→ φ U ≤ W (starFee B P r A D m Y β V) + Q
variable {Q:Support c→Finset (Cell n)→ℝ}(W0:∀ A D,GradeLease B P p r m β v (Q A D) v' A D Φ (OT A D))

private lemma env_form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩
include B eU in
lemma through_source₂(A:Support c)(D:Finset (Cell n)):Envelope (source₂ Z q p A D T β κ fuel v' Φ):=(through_sharp B A D).mul ((env_form _ eU _ T.continuous_drape.measurable).exp)
include I g0 D' B P L eU aW h1w h2w eD W0

lemma roundSource (A:Support c)(D:Finset (Cell n))(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ bloom T univ A D m)(Y:LinkArray G (Blip T F)) : let W(w:LinkArray G F):= source₂ Z q p A D T β κ fuel v' Φ (deep T F w Y); (∫ x,W x ∂piHaar G (↥F)) ≤ kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)* Real.exp (jewelFee B P (OT A D) 1 b₂ T F (Q A D)):=by
 intro W; let K:=kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card; let u:↥F → G.El:=1; let XE:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • W (release u c); let X:= T.Slice G
 have hU: Envelope W:= env_form _ (through_source₂ B eU A D) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J u, W x=0:=by
    intro x vh; unfold W source₂ trip₂; split; swap; · rw [zero_mul]
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
   by_cases HR:broken r v' V=A ∧ weak p.threshold V=D; swap; · unfold G' W source₂ trip₂; rw [if_neg HR, zero_mul,smul_zero]; exact hE _
   have hd(i:↥F): let z:=release u c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=currency I g0 A U HR.1 (fun _ e=> bloom_sub (hf e)) i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D'.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let pc:= source₂ Z q p A D T β κ fuel v' Φ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ (p.threshold_pos.trans_le I.hierarchy)).le.trans I.pale)
   let PP:BudgetPoint:={p with threshold:=v',threshold_pos:=p.threshold_pos.trans_le I.hierarchy,threshold_le:=I.cut}
   obtain ⟨h1,h2,h3,h4⟩:= beyondMake (p:=PP) F (fun _ e=> bloom_sub (hf e)) Y (release u c') HR.1 g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release u c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy: pc = goods Z q p β κ fuel v' V * Real.exp (Φ V):= by unfold pc source₂; rw [trip₂, if_pos HR]
   have ht: pc ≤ (Real.exp tY * Real.exp (Q A D)) * f c':=by
      rw [hy]; let q:=W0 A D V x Y' HR.1.symm HR.2.symm h2 h3
      apply (mul_le_mul (weak_grip B HR.2.symm HR.1.symm I.hierarchy I.light ht h1 h2 h3 h4 (saved hf _) hp I.logo b I.zero_ξ I.prompt eD I.brave) (Real.exp_le_exp.mpr q) (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
      unfold f weakWish scintillate; rw [one_mul,Real.exp_add,Real.exp_add]; ring
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D'.scale.le (D'.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D'.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*pc ≤ K*Real.exp (Q A D)* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (pow_nonneg (mul_nonneg D'.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); unfold K kiosk; ring
 unfold E; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hl (mul_nonneg hK (Real.exp_pos _).le)).trans_eq ?_
 let q':= (plumeCost B P Ω 1+ trend*b₂^2*(1:ℝ)^2+ ((Module.finrank ℝ (stamen B P n):ℝ)-(Module.finrank ℝ (LinearMap.range (estate B P T F))))/2)
 have hE: jewelFee B P Ω 1 b₂ T F (Q A D)=Q A D+q':=by unfold q' jewelFee; ring
 rw [show OT A D=Ω from rfl,hE, Real.exp_add (Q A D) q']; change K*_*(_*Real.exp q') = K*_ *_; ring
lemma source_inside (A:Support c)(D:Finset (Cell n))(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ bloom T univ A D m) : (∫ x,source₂ Z q p A D T β κ fuel v' Φ x ∂T.order G) ≤ kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)* Real.exp (jewelFee B P (OT A D) 1 b₂ T F (Q A D)) :=by
 let X:= Blip T F; let pc:=Held T (fun i=>i∈F); let L':= source₂ Z q p A D T β κ fuel v' Φ; let K:=kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)* Real.exp (jewelFee B P (OT A D) 1 b₂ T F (Q A D)); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((through_source₂ B eU A D).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundSource B P L D' I eD g0 eU aW h1w h2w W0 A D hg ht b hf i)) (le_of_eq ?_); simp [χ]

#print axioms source_inside
end Risa
end YM.Gleam.Luster
