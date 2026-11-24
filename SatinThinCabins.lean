import SatinThinJoin
import SatinThinAngstrom
import YM.SU5.Regis.Trophy
/-! # Untruncated bill with angular perturbation at CLOAK.
 Two-level defects from different scales, do not assume threshold change in pressure/index.
 Adapt Trophy, and Inlets. -/
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
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)

variable {ε dbκ dbD yQ:ℝ}{Y0:Finset (Cell n)}

def ShelfScene (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(r:Ratio c n)(m:ℕ)(β v ε Q:ℝ)(A:Support c)(Y0: Finset (Cell n)) (t:ℝ)(φ:Config G n→ℝ)(W:Altar G n→ℝ):Prop:=
 ∀ (U:Config G n)(V Y:fieldDir G n 1), A=broken r ε U → Y0=misdemean p.threshold U→ ProbeBox (V+Y) (2*v)→ TrustLogs (V+Y) U r A v→ t*φ U ≤ t*W (starFeed B P r A (face_anchors Y0) m Y β V) + Q
structure Accounts (J:ChartRatio G)(R:Rules G)(q:Clip)(p:BudgetPoint)(w m:ℕ)(β v Λ ε κ dbκ s l:ℝ):Prop where
 light : EnoughMark q p m
 pale : suitedFee w ε ≤ v
 shield : p.threshold≤ε
 logo : v ≤ R.c
 chart : 2*v < J.radius
 support : ∀ x:G.Color, ‖x‖ ≤ 2*v → J.J x ≤ Real.exp Λ
 small : κ + s ≤ β*unitDueS q p
 large : dbκ +21^4*l ≤ β*unitDueL q p ε
 non_neg : 0≤l
 green : 0≤Λ
abbrev facePlay (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(Ω:Finset (Cell n))(T:Forest r)(β κ dbκ ε:ℝ)(U:T.Slice G):ℝ:= if broken r ε (T.drape U)=A ∧ misdemean p.threshold (T.drape U)=Ω then twice_rich Z q p β κ dbκ ε (T.drape U) else 0
abbrev scanWave (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(Ω:Finset (Cell n))(T:Forest r)(β κ dbκ ε t:ℝ)(φ:Config G n→ℝ)(U:T.Slice G): ℝ:= facePlay Z q p A Ω T β κ dbκ ε U * Real.exp (t * φ (T.drape U))
variable (I:Accounts J R q p r.count.val m β v Λ ε κ dbκ dbD yQ) (g0:2*(r.count.val+1)<n.val)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
private lemma env_form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩


lemma scan_selector (A:Finset (Cell n)) (v:ℝ): MeasurableSet {U:Config G n| misdemean v U=A}:=by
 simp only [Finset.ext_iff,Set.setOf_forall]; apply MeasurableSet.iInter; intro j; by_cases h:j∈A; · simp only [h,iff_true]; exact scan ..
 simp only [h,iff_false]; exact (scan ..).compl
include B in
lemma env_face (A:Support c) : Envelope (facePlay Z q p A Y0 T β κ dbκ ε):= by
 let M :=T.drape (G:=G); have he:Measurable M:= T.continuous_drape.measurable
 let K:= env_form (twice_rich Z q p β κ dbκ ε (n:=n)) (income_burs B) M he
 exact Envelope.piece (p:=fun U=> broken r ε (M U)=A ∧ misdemean p.threshold (M U)=Y0) ((he (malaise_selector ..)).inter (he (scan_selector ..))) K (Envelope.const 0)
include B u in
lemma env_scanWave (A:Support c) (t:ℝ) : Envelope (scanWave Z q p A Y0 T β κ dbκ ε t φ):=(env_face B A).mul (env_form _ (expEnv u t) _ (T.continuous_drape.measurable))
include I g0

lemma appearance {F:Finset T.Free} (A:Support c)(X:T.Slice G)(h:broken r ε (T.drape X)=A)(hf:F⊆room T univ A m)(i:↥F): let y:=X (i:T.Free); let b:=G.plog (G.mat y); G.chord y ≤ v ∧ ‖b‖≤2*v ∧ G.lieExp b=y ∧ b∈ ball 0 J.radius:=by
 let U:=T.drape X; have he:U i.val.val=X i.val:=T.off_tree X i.val; have hl: Working r A i.val.val:= kept_freed (T:=T) (m:=m) rfl (⟨i.val,hf i.property⟩: ↥(room T univ A m)); intro y b; have hp: G.chord y≤ v:= by unfold y; rw [←he]; exact (purified (p.threshold_pos.le.trans I.shield) (show _∉ broken r ε  (T.drape X) from (h.symm ▸ hl.1)) g0 hl.2).trans I.pale
 have hv: ‖b‖≤2*v:= (R.sleeve y (hp.trans I.logo)).trans (mul_le_mul_of_nonneg_left hp (by norm_num)); exact ⟨hp,hv,R.records y (hp.trans I.logo),Metric.mem_ball.mpr (dist_zero_right _|>.trans_lt (hv.trans_lt I.chart))⟩

-- separate omission pressure cost at foci. absorb through powers.
abbrev footFile (n:Side) (R:Rules G) (J:ChartRatio G)(q:Clip) (p:BudgetPoint)(β v η C S ξ Λ dbD:ℝ)(m l y d:ℕ):= (J.scale * Real.exp Λ)^y * Real.exp (taxΔ R q n p β v η C S m - dbD*d - ξ * l)
abbrev wingFile (R:Rules G)(J:ChartRatio G)(q:Clip)(p:BudgetPoint)(β v η C S ξ Λ dbD:ℝ)(m l d:ℕ)(F:Finset T.Free)(H:Bed):= footFile n R J q p β v η C S ξ Λ dbD m l F.card d*chartCost (prism T F H G)⁻¹ (coupling β)
include D B P L I g0 u a h1 h2
lemma roundShelf (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ cloak T univ A Y0 m)(Y:LinkArray G (Blip T F))(hxS:ShelfScene B P p r m β v ε Q A Y0 t φ W) : let WW(w:LinkArray G F):= scanWave Z q p A Y0 T β κ dbκ ε t φ (deep T F w Y); (∫ x,WW x ∂piHaar G (↥F)) ≤ footFile n R J q p β v η C S yQ Λ dbD m A.card F.card Y0.card * chartCost (prism T F H G)⁻¹ (coupling β)*Real.exp (jewelFee B P W t b₂ T F Q):=by
 intro WW; let K:=footFile n R J q p β v η C S yQ Λ dbD m A.card F.card Y0.card; let uQ:↥F → G.El:=1; let δ:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • WW (release uQ c); let X:= T.Slice G
 have hU: Envelope WW:= env_form _ (env_scanWave B u A t) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J uQ, WW x=0:=by
    intro x v; unfold WW scanWave facePlay; split; swap; · simp -- zero
    next H=>
      exact False.elim <| v fun i _=>by
         let t:=appearance I g0 A (deep T F x Y) H.1 (hf.trans cover_c) i; let X:=x i; let b:= G.plog (G.mat X); have ht: deep T F x Y i.val=X:=freeze_held ..; have hX:=t.2.2; simp only [ht] at hX; exact ⟨X,⟨b,hX.2,hX.1⟩,mul_one _⟩
 obtain ⟨hx,he⟩:= release_integral D uQ WW hU.meas.stronglyMeasurable hp
 let f:= gradeCross B P T F A (face_anchors Y0) m (myLog T F Y A) β W t; obtain ⟨hg',hl⟩:= cross_source (ΛP:=face_anchors Y0) (A:=A) (m:=m) B P L (myLog T F Y A) hg ht W a h1 h2 t
 let tY:= taxΔ R q n p β v η C S m - dbD*Y0.card -yQ*A.card; let E(c):= K * Real.exp Q * f c; let M:= J.scale * Real.exp Λ; have hK :0≤K:=by unfold K footFile; have h:=D.scale; positivity
 have hE(c):0≤ E c:=mul_nonneg (mul_nonneg hK (Real.exp_pos _|>.le)) (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))
 change (∫ x,WW x ∂piHaar G (↥F)) ≤ K * chartCost (prism T F H G)⁻¹ (coupling β) * _; rw [he]; apply le_trans (b:=∫ x,E x)
 · apply integral_mono (hx.mp (hU.integrable _)) (hg'.const_mul _); intro c'; change δ.indicator G' c'≤ E c'; by_cases h:c'∈δ; swap; · rw [Set.indicator_of_notMem h]; exact hE _
   rw [Set.indicator_of_mem h]; let U:= deep T F (release uQ c') Y; let V:= T.drape U
   by_cases H:broken r ε V=A ∧ misdemean p.threshold V = Y0; swap; · unfold G' WW scanWave facePlay; rw [if_neg H, zero_mul, smul_zero]; exact hE _
   have hd(i:↥F): let z:=release uQ c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=appearance I g0 A U H.1 (hf.trans cover_c) i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let D':= scanWave Z q p A Y0 T β κ dbκ ε t φ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ (p.threshold_pos.trans_le I.shield)).le.trans I.pale)
   obtain ⟨h1,h2,h3,h4⟩:= enterCol F hf Y (release uQ c') (p.threshold_pos.le.trans I.shield) H.1 g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release uQ c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy : D'=twice_rich Z q p β κ dbκ ε V * Real.exp (t * φ V):=by unfold D' scanWave; rw [facePlay, if_pos H]
   have hv : f c'= yield_a Z q T F A (face_anchors Y0) m Y' β c'* Real.exp (t*W (starFeed B P r A (face_anchors Y0) m Y' β x)):= rfl
   have ht: D' ≤ Real.exp tY * Real.exp Q * f c':=by
      rw [hy,hv]; have he:= hxS V x Y' H.1.symm H.2.symm h2 h3; have hz:= at_shelf B I.shield H.1.symm H.2.symm I.light ht.le h1 h2 h3 h4 hp I.logo b I.non_neg I.small I.large; have hg:= Real.exp_monotone he; apply (mul_le_mul hz hg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)).trans_eq; rw [Real.exp_add,Real.exp_add]; unfold yield_a tY; ring
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D.scale.le (D.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*D' ≤ (K* Real.exp Q)* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))) (pow_nonneg (mul_nonneg D.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); unfold K footFile tY M; ring
 unfold E; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hl (mul_nonneg hK (Real.exp_pos Q|>.le))).trans_eq ?_; unfold jewelFee; rw [show Q + (_:ℝ)+_+_= Q+(plumeCost B P W t + trend*b₂^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2) from (by ring), Real.exp_add Q]; ring
lemma sourcedDebt (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ cloak T univ A Y0 m)(V: ShelfScene B P p r m β v ε Q A Y0 t φ W) : (∫ x,scanWave Z q p A Y0 T β κ dbκ ε t φ x ∂T.order G) ≤ wingFile R J q p β v η C S yQ Λ dbD m A.card Y0.card F H * Real.exp (jewelFee B P W t b₂ T F Q) :=by
 let X:= Blip T F; let D':=Held T (fun i=>i∈F); let L':= scanWave Z q p A Y0 T β κ dbκ ε t φ; let K:=wingFile R J q p β v η C S yQ Λ dbD m A.card Y0.card F H * Real.exp (jewelFee B P W t b₂ T F Q); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((env_scanWave B u A t).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundShelf B P L D I g0 u a h1 h2 A hg ht b hf i V)) (le_of_eq ?_); simp [χ]
end YM.Gleam
#print axioms YM.Gleam.sourcedDebt
