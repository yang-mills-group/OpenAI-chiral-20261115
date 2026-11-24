import YM.SU5.Gleam.Shelter
import YM.SU5.Gleam.Elevation
/-!
# Earn before summing. Genuine angular weight, one price at each dirt count.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)
-- assumptions bundled
structure Archive (J:ChartRatio G)(R:Rules G)(q:Clip)(p:BudgetPoint)(w m:ℕ)(β κ ξ v Λ:ℝ) : Prop where
 light : EnoughMark q p m
 pale : suitedFee w p.threshold ≤ v
 logo : v ≤ R.c
 chart : 2*v < J.radius
 support : ∀ x:G.Color, ‖x‖ ≤ 2*v → J.J x ≤ Real.exp Λ
 prompt : κ+21^4*ξ ≤ β*(q.linear*p.threshold^2)
 zero_ξ : 0≤ξ
 green : 0 ≤ Λ

abbrev play (Z:PathData G)(q:Clip)(p:BudgetPoint) (A:Support c)(T:Forest r) (β κ:ℝ)(U:T.Slice G):ℝ:= if broken r p.threshold (T.drape U)=A then richG Z q p β κ (T.drape U) else 0
variable (I:Archive J R q p r.count.val m β κ ξ v Λ) (g0:2*(r.count.val+1)<n.val)
include I g0
lemma current {F:Finset T.Free} (A:Support c)(X:T.Slice G)(h:broken r p.threshold (T.drape X)=A)(hf:F⊆room T univ A m)(i:↥F): let y:=X (i:T.Free); let b:=G.plog (G.mat y); G.chord y ≤ v ∧ ‖b‖≤2*v ∧ G.lieExp b=y ∧ b∈ ball 0 J.radius:=by
 let U:=T.drape X; have he:U i.val.val=X i.val:=T.off_tree X i.val; have hl: Working r A i.val.val:= kept_freed (T:=T) (m:=m) rfl (⟨i.val,hf i.property⟩: ↥(room T univ A m)); intro y b; have hp: G.chord y≤ v:= by unfold y; rw [←he]; exact (purified p.threshold_pos.le (show _∉ broken r p.threshold  (T.drape X) from (h.symm ▸ hl.1)) g0 hl.2).trans I.pale
 have hv: ‖b‖≤2*v:= (R.sleeve y (hp.trans I.logo)).trans (mul_le_mul_of_nonneg_left hp (by norm_num)); exact ⟨hp,hv,R.records y (hp.trans I.logo),Metric.mem_ball.mpr (dist_zero_right _|>.trans_lt (hv.trans_lt I.chart))⟩
omit g0 I in
lemma bistro : Fintype.card (↥F)=F.card := Fintype.card_coe _ -- maybe remove
omit g0 I in
private lemma env_form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩
include D B P L
omit g0 I D P L in
lemma env_play (A:Support c) : Envelope (play Z q p A T β κ):= by
 let M :=T.drape (G:=G); have he:Measurable M:= T.continuous_drape.measurable
 let K:= env_form (richG Z q p β κ (n:=n)) (income_g B) M he
 exact Envelope.piece (p:=fun U=> broken r p.threshold (M U)=A) (he (malaise_selector ..)) K (Envelope.const 0)
variable (N:0<C ∨ C=0) -- prefer use C≥0
abbrev tollFee (n : Side) (Z:ℝ)(p:BudgetPoint) := Real.exp Z
abbrev sealFeet (n:Side) (R:Rules G) (J:ChartRatio G)(q:Clip) (p:BudgetPoint)(β v η C S ξ Λ:ℝ)(m l y:ℕ):= (J.scale * Real.exp Λ)^y * Real.exp (taxΔ R q n p β v η C S m - ξ * l)
lemma roundCut (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ room T univ A m)(Y:LinkArray G (Blip T F)) : let W(w:LinkArray G F):= play Z q p A T β κ (deep T F w Y); (∫ x,W x ∂piHaar G (↥F)) ≤ sealFeet n R J q p β v η C S ξ Λ m A.card F.card * chartCost (prism T F H G)⁻¹ (coupling β):=by
 intro W; let K:=sealFeet n R J q p β v η C S ξ Λ m A.card F.card; let u:↥F → G.El:=1; let δ:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • W (release u c); let X:= T.Slice G
 have hU: Envelope W:= env_form _ (env_play B A) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J u, W x=0:=by
    intro x v; unfold W play; split; swap; · rfl
    next H=>
      exact False.elim <| v fun i _=>by
         let t:=current I g0 A (deep T F x Y) H hf i; let X:=x i; let b:= G.plog (G.mat X); have ht: deep T F x Y i.val=X:=freeze_held ..; have hX:=t.2.2; simp only [ht] at hX; exact ⟨X,⟨b,hX.2,hX.1⟩,mul_one _⟩
 obtain ⟨hx,he⟩:= release_integral D u W hU.meas.stronglyMeasurable hp
 let f:=yieldY Z q T F A m (myLog T F Y A) β; obtain ⟨hg',hl⟩:= roundMeasure (A:=A) (m:=m) B P L (myLog T F Y A) hg ht
 let tY:= taxΔ R q n p β v η C S m - ξ*A.card; let E(c):= K * f c; let M:= J.scale * Real.exp Λ; have hK :0≤K:=by unfold K sealFeet; have h:=D.scale; positivity
 have hE(c):0≤ E c:=mul_nonneg hK (Real.exp_pos _).le
 change (∫ x,W x ∂piHaar G (↥F)) ≤ K*_; rw [he]; apply le_trans (b:=∫ x,E x)
 · apply integral_mono (hx.mp (hU.integrable _)) (hg'.const_mul K); intro c'; change δ.indicator G' c'≤ E c'; by_cases h:c'∈δ; swap; · rw [Set.indicator_of_notMem h]; exact hE _
   rw [Set.indicator_of_mem h]; let U:= deep T F (release u c') Y; let V:= T.drape U
   by_cases H:broken r p.threshold V=A; swap; · unfold G' W play; rw [if_neg H, smul_zero]; exact hE _
   have hd(i:↥F): let z:=release u c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=current I g0 A U H hf i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let D':= play Z q p A T β κ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ p.threshold_pos).le.trans I.pale)
   obtain ⟨h1,h2,h3,h4⟩:= beyondMake F hf Y (release u c') H g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release u c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy: D' = richG Z q p β κ V:= if_pos H
   have ht: D' ≤ Real.exp tY * f c':=by
      rw [hy]; apply (enormous_f B H.symm I.light ht.le h1 h2 h3 h4 hp I.logo b I.zero_ξ I.prompt).trans_eq; rw [Real.exp_add,mul_comm]; rfl
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D.scale.le (D.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*D' ≤ K* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (Real.exp_pos _).le) (pow_nonneg (mul_nonneg D.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); change M^_*_ = (M^_*_)*_; ring
 unfold E; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hl hK
abbrev wingFee (N: Side) (R:Rules G) (J:ChartRatio G)(q:Clip) (p:BudgetPoint)(β v η C S ξ Λ:ℝ)(m l:ℕ)(F:Finset T.Free)(H:Bed):= sealFeet N R J q p β v η C S ξ Λ m l F.card * chartCost (prism T F H G)⁻¹ (coupling β) -- `n` not T n actually replace using new letter
lemma insideBudget (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ room T univ A m) : (∫ x,play Z q p A T β κ x ∂T.order G) ≤ wingFee n R J q p β v η C S ξ Λ m A.card F H :=by
 let X:= Blip T F; let D':=Held T (fun i=>i∈F); let L':= play Z q p A T β κ; let K:=wingFee n R J q p β v η C S ξ Λ m A.card F H; let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((env_play B A).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundCut B P L D I g0 A hg ht b hf i)) (le_of_eq ?_); simp [χ]
end YM.Gleam
#print axioms YM.Gleam.insideBudget
