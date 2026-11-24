import LusterS.Radium
import LusterS.Organ
import Refrain.Shrift
import Refrain.Kernel
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

/-- Dual expense for angular harvest through a mask. Summation needs ν. -/
structure Radiance (J:ChartRatio G)(R:Rules G)(q:Clip)(p:BudgetPoint)(w m:ℕ)(β κ fuel t ξ χ ν v Λ:ℝ) : Prop where
 hierarchy : p.threshold ≤ t
 cut : t≤1
 light : EnoughMark q p m
 pale : suitedFee w t ≤ v
 logo : v ≤ R.c
 chart : 2*v < J.radius
 support : ∀ x:G.Color, ‖x‖ ≤ 2*v → J.J x ≤ Real.exp Λ
 prompt : κ+(χ+ν) ≤ β*(q.linear*p.threshold^2/2)
 brave : fuel+21^4*ξ ≤ β*(q.linear*p.threshold*t/2)
 zero_ξ : 0≤ξ
 green : 0 ≤ Λ
variable {χ fuel:ℝ}
variable (I:Radiance J R q p r.count.val m β κ fuel v' ξ χ ν v Λ) (g0:2*(r.count.val+1)<n.val)
include I g0
lemma currency {F:Finset T.Free} (A:Support c)(X:T.Slice G)(h:broken r v' (T.drape X)=A)(hf:F⊆room T univ A m)(i:↥F): let y:=X (i:T.Free); let b:=G.plog (G.mat y); G.chord y ≤ v ∧ ‖b‖≤2*v ∧ G.lieExp b=y ∧ b∈ ball 0 J.radius:=by
 let U:=T.drape X; have he:U i.val.val=X i.val:=T.off_tree X i.val; have hl: Working r A i.val.val:= kept_freed (T:=T) (m:=m) rfl (⟨i.val,hf i.property⟩: ↥(room T univ A m)); intro y b; have hp: G.chord y≤ v:= by unfold y; rw [←he]; exact (purified (p.threshold_pos.le.trans I.hierarchy) (show _∉ broken r v'  (T.drape X) from (h.symm ▸ hl.1)) g0 hl.2).trans I.pale
 have hv: ‖b‖≤2*v:= (R.sleeve y (hp.trans I.logo)).trans (mul_le_mul_of_nonneg_left hp (by norm_num)); exact ⟨hp,hv,R.records y (hp.trans I.logo),Metric.mem_ball.mpr (dist_zero_right _|>.trans_lt (hv.trans_lt I.chart))⟩
omit g0 I in
private lemma env_form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩
include D' B P L

abbrev kiosk (n:Side) (R:Rules G) (J:ChartRatio G)(q:Clip)(p:BudgetPoint)(β v η C S ξ χ ν Λ:ℝ)(m l d y:ℕ):= (J.scale * Real.exp Λ)^y * Real.exp ((taxΔ R q n p β v η C S m - ξ*l) - (χ+ν)*d)
lemma roundCut (A:Support c)(D:Finset (Cell n))(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ bloom T univ A D m)(Y:LinkArray G (Blip T F)) : let W(w:LinkArray G F):= trip Z q p A D T β κ fuel v' (deep T F w Y); (∫ x,W x ∂piHaar G (↥F)) ≤ kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β):=by
 intro W; let K:=kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card; let u:↥F → G.El:=1; let XE:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • W (release u c); let X:= T.Slice G
 have hU: Envelope W:= env_form _ (through_t B A D) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J u, W x=0:=by
    intro x vh; unfold W trip; split; swap; · rfl
    next H=>
      exact False.elim <| vh fun i _=>by
         let t:=currency I g0 A (deep T F x Y) H.1 (fun i p=> bloom_sub (hf p)) i; let X:=x i; let b:= G.plog (G.mat X); have ht: deep T F x Y i.val=X:=freeze_held ..; have hX:=t.2.2; simp only [ht] at hX; exact ⟨X,⟨b,hX.2,hX.1⟩,mul_one _⟩
 obtain ⟨hx,he⟩:= release_integral D' u W hU.meas.stronglyMeasurable hp
 let f:=scintillate Z q T F D A m (myLog T F Y A) β; obtain ⟨hg',hl⟩:= gleaming (A:=A) (D:=D) (m:=m) B P L (myLog T F Y A) hg ht
 let tY:= (taxΔ R q n p β v η C S m - ξ*A.card)-(χ+ν)*D.card; let E(c):= K * f c; let M:= J.scale * Real.exp Λ; have hK :0≤K:=by unfold K kiosk; have h:=D'.scale; positivity
 have hE(c):0≤ E c:=mul_nonneg hK (Real.exp_pos _).le
 change (∫ x,W x ∂piHaar G (↥F)) ≤ K*_; rw [he]; apply le_trans (b:=∫ x,E x)
 · apply integral_mono (hx.mp (hU.integrable _)) (hg'.const_mul K); intro c'; change XE.indicator G' c'≤ E c'; by_cases h:c'∈XE; swap; · rw [Set.indicator_of_notMem h]; exact hE _
   rw [Set.indicator_of_mem h]; let U:= deep T F (release u c') Y; let V:= T.drape U
   by_cases HR:broken r v' V=A ∧ misdemean p.threshold V=D; swap; · unfold G' W trip; rw [if_neg HR, smul_zero]; exact hE _
   have hd(i:↥F): let z:=release u c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=currency I g0 A U HR.1 (fun _ e=> bloom_sub (hf e)) i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D'.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let pc:= trip Z q p A D T β κ fuel v' U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ (p.threshold_pos.trans_le I.hierarchy)).le.trans I.pale)
   let PP:BudgetPoint:={p with threshold:=v',threshold_pos:=p.threshold_pos.trans_le I.hierarchy,threshold_le:=I.cut}
   obtain ⟨h1,h2,h3,h4⟩:= beyondMake (p:=PP) F (fun _ e=> bloom_sub (hf e)) Y (release u c') HR.1 g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release u c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy: pc = goods Z q p β κ fuel v' V:= if_pos HR
   have ht: pc ≤ Real.exp tY * f c':=by
      rw [hy]; apply (prism_e B HR.2.symm HR.1.symm I.hierarchy I.light ht.le h1 h2 h3 h4 (saved hf _) hp I.logo b I.zero_ξ I.prompt I.brave).trans_eq; rw [Real.exp_add,mul_comm]; rfl
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D'.scale.le (D'.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D'.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*pc ≤ K* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (Real.exp_pos _).le) (pow_nonneg (mul_nonneg D'.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); change M^_*_ = (M^_*_)*_; ring
 unfold E; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hl hK
lemma sharp_insideBudget (A:Support c)(D:Finset (Cell n))(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ bloom T univ A D m) : (∫ x,trip Z q p A D T β κ fuel v' x ∂T.order G) ≤ kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β) :=by
 let X:= Blip T F; let pc:=Held T (fun i=>i∈F); let L':= trip Z q p A D T β κ fuel v'; let K:=kiosk n R J q p β v η C S ξ χ ν Λ m A.card D.card F.card * chartCost (prism T F H G)⁻¹ (coupling β); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((through_t B A D).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundCut B P L D' I g0 A D hg ht b hf i)) (le_of_eq ?_); simp [χ]
end YM.Gleam.Luster
