import GaugeFieldConstruction.Upstream
import YM.SU5.Regis.Trophy

/-! # Pay gauge rent under localized aggregate mark perturbation. Use additional mask; adapt Inlets & Danube & Trophy,
     determinant of unperturbed already licensed. -/
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



-- tag weights together with their *used* payment. θ² flags are not granted
-- extra power unless behind θ_E per-face.
structure TopPrice (J:ChartRatio G)(R:Rules G)(q:Clip)(p:BudgetPoint)(w m:ℕ)(β κ k f₁ f₂ v Λ T:ℝ): Prop where
 moon : p.threshold ≤ T
 light : EnoughMark q p m
 pale : suitedFee w T ≤ v
 logo : v ≤ R.c
 chart : 2*v < J.radius
 support : ∀ x:G.Color, ‖x‖ ≤ 2*v → J.J x ≤ Real.exp Λ
 leanH : κ+f₁ ≤ β*(q.linear*p.threshold^2/2)
 heavy : k+f₂ ≤ β*(q.linear*p.threshold*T/2)
 green : 0 ≤ Λ
variable {k f₁ f₂ q':ℝ}
variable (I:TopPrice J R q p r.count.val m β κ k f₁ f₂ v Λ q') (g0:2*(r.count.val+1)<n.val)
def Location_H (p:BudgetPoint)(q':ℝ)(W D:Flaws n)(U:Config G n):= misdemean p.threshold U=W ∧ misdemean q' U=D
abbrev grid_break (r:Ratio c n)(W:Flaws n):= halo 10 (W.image fun v=> r.parent v.1)
lemma grid_pays (r:Ratio c n)(W:Flaws n): (grid_break r W).card ≤ W.card*21^4:=(Corona.halo_size ..).trans (Nat.mul_le_mul_right _ (card_image_le))
variable {Wa Da:Flaws n}
lemma aligned_H (h:Location_H p q' Wa Da U): broken r q' U=grid_break r Da:= congrArg (grid_break r) h.2

lemma LocatedM (T:ℝ)(W:Flaws n) : MeasurableSet {U:Config G n| misdemean T U=W}:=by
 simp only [Finset.ext_iff,Set.setOf_forall]; apply MeasurableSet.iInter; intro j; by_cases h:j∈W; · simp only [h,iff_true]; exact scan ..
 simp only [h,iff_false]; exact (scan ..).compl

def day_play (Z:PathData G)(q:Clip)(p:BudgetPoint)(Wa Da:Flaws n)(T:Forest r)(β κ k q':ℝ)(φ:Config G n→ℝ)(U:T.Slice G): ℝ:= if Location_H p q' Wa Da (T.drape U) then richBoth Z q p β κ k q' (T.drape U) * Real.exp (φ (T.drape U)) else 0
-- only on chart bill, reading all colors, dangles allowed.
def Clarity (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(T:Forest r)(m:ℕ)(Wa Da:Flaws n)(σ β v Q:ℝ) (t:ℝ)(φ:Config G n→ℝ)(W:Altar G n→ℝ):Prop:=
 ∀ (X:T.Slice G)(V Y:fieldDir G n 1),let U:=T.drape X; let A:=grid_break r Da;
                   Location_H p σ Wa Da U→ ProbeBox (V+Y) (2*v) → abandons_A V r A Wa m →
                   TrustLogs (V+Y) U r A v→ φ U ≤ t*W (starOf B P r A Wa m Y β V)+Q
abbrev daySeal (n:Side)(R: Rules G)(J:ChartRatio G)(q:Clip)(p:BudgetPoint)(β v η C S Λ:ℝ)(m:ℕ) (L L':Flaws n)(f g:ℝ) (y:ℕ):= (J.scale * Real.exp Λ)^y * Real.exp (billA R q n p β v η C S m L L' f g)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
include B
lemma envelopTogether {wa sa θ:ℝ}: RG.Envelope (richBoth Z q p β wa sa θ (n:=n)):= (income_g B).mul ((conduct ..).exp) -- include
include u in
lemma env_lease (Wa Da:Flaws n): Envelope (day_play Z q p Wa Da T β κ k q' φ):=by
 let X:= richBoth Z q p β κ k q' (n:=n); let EE:Envelope fun U:Config G n=> X U*Real.exp (φ U):=(envelopTogether B).mul u.exp
 let M:= T.drape (G:=G); have he:Measurable M:= T.continuous_drape.measurable
 apply Envelope.piece (p:=fun U=> Location_H p q' Wa Da (T.drape U)); exact he ((LocatedM p.threshold Wa).inter (LocatedM q' Da)); refine ⟨EE.meas.comp he,EE.cost.choose, fun i=> EE.cost.choose_spec _⟩
 exact Envelope.const _

omit B
include I g0
lemma flight_M {F:Finset T.Free} (A:Support c)(X:T.Slice G)(h:broken r q' (T.drape X)=A)(hf:F⊆room T univ A m)(i:↥F): let y:=X (i:T.Free); let b:=G.plog (G.mat y); G.chord y ≤ v ∧ ‖b‖≤2*v ∧ G.lieExp b=y ∧ b∈ ball 0 J.radius:=by
 let U:=T.drape X; have he:U i.val.val=X i.val:=T.off_tree X i.val; have hl: Working r A i.val.val:= kept_freed (T:=T) (m:=m) rfl (⟨i.val,hf i.property⟩: ↥(room T univ A m)); intro y b; have hp: G.chord y≤ v:= by unfold y; rw [←he]; exact (purified (p.threshold_pos.trans_le I.moon).le (show _∉ broken r q'  (T.drape X) from (h.symm ▸ hl.1)) g0 hl.2).trans I.pale
 have hv: ‖b‖≤2*v:= (R.sleeve y (hp.trans I.logo)).trans (mul_le_mul_of_nonneg_left hp (by norm_num)); exact ⟨hp,hv,R.records y (hp.trans I.logo),Metric.mem_ball.mpr (dist_zero_right _|>.trans_lt (hv.trans_lt I.chart))⟩

omit I g0
lemma beyondDream (a:Finset T.Free)(h:a⊆accRoom T univ A Wa m)(Y':LinkArray G (Blip T a))(C: LinkArray G a)(t': broken r q' (T.drape (deep T a C Y')) = A) (h0:0<q')(g0:2*(r.count.val+1)<n.val) (p':suitedFee r.count.val q'≤v)(s:v≤R.c) : let t:= T.drape (deep T a C Y'); let x:=fun b:↥a=> G.plog (G.mat (C b)); let f:= stock T a x; let D:=myLog T a Y' A; ProbeBox f (2*v) ∧ ProbeBox (f+D) (2*v) ∧ TrustLogs (f+D) t r A v ∧ abandons_A f r A Wa m:=by
 intro t x f D
 let log_use (e:Bond n)(u:Working r A e) : G.chord (t e)≤v:= (purified h0.le (show _∉broken r q' t from t'.symm ▸ u.1) g0 u.2).trans p'; -- parse Proof? 
 let norm_use (e:Bond n)(u:Working r A e) : ‖logX t e‖≤2*v:= (R.sleeve _ ((log_use e u).trans s)).trans (mul_le_mul_of_nonneg_left (log_use e u) (by norm_num))
 have hta (b:↥a) : Working r A b.val.val:= kept_freed (A:=A) (m:=m) rfl ⟨b.val,mem_filter.mpr ⟨mem_univ _,((mem_filter.mp (h b.property)).2).1⟩⟩ -- implicit tune
 have hz(e:Bond n): collect G (f+D) e= (if Working r A e then logX t e else 0):=by
    change collect G (stock T a x) e+ collect G (myLog T a Y' A) e= _; rw [myLog_field]
    by_cases G0: ∀ i:↥a,e≠i.val.val
    · rw [stock_shallow x e G0,zero_add]; have hg:logX (T.drape (deep T a 1 Y')) e=logX t e:= by unfold logX t; rw [drape_agrees (X:=C) G0] -- might rewrites left
      rw [hg]; simp [G0]
    push Not at G0; obtain ⟨i,rfl⟩:= G0; rw [if_neg (show ¬(Working r A i.val.val ∧ ∀ j:↥a,i.val.val ≠ j.val.val) from fun p=> p.2 i rfl), stock_clean, add_zero,if_pos (hta _ )]; unfold x logX t; rw [drapeX]
 have v0:0 ≤ v:= ((suitFee_pos _ h0).le.trans p')
 refine ⟨fun j=> ?_,fun j=> ?_,fun i u=> ?_,fun e pH=>?_⟩
 · by_cases t':∀ i:↥a,j≠i.val.val; · unfold f; rw [stock_shallow _ j t',norm_zero]; positivity
   push Not at t'; obtain ⟨b,rfl⟩:=t'; unfold f; rw [stock_clean,show x b=logX t _ from ?_]; exact norm_use b.val.val (hta b)
   unfold logX x t; rw [drapeX]
 · rw [hz]; split_ifs; rename_i he; exact norm_use _ he; rw [norm_zero]; positivity
 · exact ⟨(hz i).trans (if_pos u),log_use _ u⟩
 by_cases G0:∀ i:↥a,e≠i.val.val; · exact False.elim (pH (stock_shallow x e G0))
 push Not at G0; obtain ⟨b,rfl⟩:=G0; exact (mem_filter.mp (h b.property)).2

private lemma post_Form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩
include D B P L I g0 u a h1 h2
lemma roundV (Wa Da:Flaws n)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ accRoom T univ (grid_break r Da) Wa m)(Y:LinkArray G (Blip T F))(hxS:Clarity B P p T m Wa Da q' β v Q t φ W) : let WW(w:LinkArray G F):= day_play Z q p Wa Da T β κ k q' φ (deep T F w Y); (∫ x,WW x ∂piHaar G (↥F)) ≤ daySeal n R J q p β v η C S Λ m Wa Da f₁ f₂ F.card * chartCost (prism T F H G)⁻¹ (coupling β)*Real.exp (jewelFee B P W t b₂ T F Q):=by
 intro WW; let A:=grid_break r Da;
 have rp:F ⊆ room T univ A m:= by
    intro i q; exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp (hf q)).2).1⟩
 let K:=daySeal n R J q p β v η C S Λ m Wa Da f₁ f₂ F.card; let uQ:↥F → G.El:=1; let δ:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • WW (release uQ c); let X:= T.Slice G
 have hU: Envelope WW:= post_Form _ (env_lease B u Wa Da) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J uQ, WW x=0:=by
    intro x v; unfold WW day_play; split; swap; · rfl
    next H=>
      exact False.elim <| v fun i _=>by
         let t:=flight_M I g0 A (deep T F x Y) (aligned_H H) rp i; let X:=x i; let b:= G.plog (G.mat X); have ht: deep T F x Y i.val=X:=freeze_held ..; have hX:=t.2.2; simp only [ht] at hX; exact ⟨X,⟨b,hX.2,hX.1⟩,mul_one _⟩
 obtain ⟨hx,he⟩:= release_integral D uQ WW hU.meas.stronglyMeasurable hp
 let f:= blowFunds B P T F A Wa m (myLog T F Y A) β W t; obtain ⟨hg',hl⟩:= at_stokes (Zx:=Wa) (A:=A) (m:=m) B P L (myLog T F Y A) hg ht W a h1 h2 t
 let tY:= billA R q n p β v η C S m Wa Da f₁ f₂; let E(c):= K * Real.exp Q * f c; let M:= J.scale * Real.exp Λ; have hK :0≤K:=by unfold K daySeal; have h:=D.scale; positivity
 have hE(c):0≤ E c:=mul_nonneg (mul_nonneg hK (Real.exp_pos _|>.le)) (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))
 change (∫ x,WW x ∂piHaar G (↥F)) ≤ K * chartCost (prism T F H G)⁻¹ (coupling β) * _; rw [he]; apply le_trans (b:=∫ x,E x)
 · apply integral_mono (hx.mp (hU.integrable _)) (hg'.const_mul _); intro c'; change δ.indicator G' c'≤ E c'; by_cases h:c'∈δ; swap; · rw [Set.indicator_of_notMem h]; exact hE _
   rw [Set.indicator_of_mem h]; let U:= deep T F (release uQ c') Y; let V:= T.drape U
   by_cases H:Location_H p q' Wa Da V; swap; · unfold G' WW day_play; rw [if_neg H, smul_zero]; exact hE _
   have hd(i:↥F): let z:=release uQ c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=flight_M I g0 A U (aligned_H H) rp i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let D':= day_play Z q p Wa Da T β κ k q' φ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ (p.threshold_pos.trans_le I.moon)).le.trans I.pale)
   obtain ⟨h1,h2,h3,h4⟩:= beyondDream F hf Y (release uQ c') (aligned_H H) (p.threshold_pos.trans_le I.moon) g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release uQ c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy : D'=richBoth Z q p β κ k q' V * Real.exp (φ V):=by unfold D' day_play; rw [if_pos H]
   have hv : f c'= pulseFund Z q T F A Wa m Y' β c'* Real.exp (t*W (starOf B P r A Wa m Y' β x)):= rfl
   have ht: D' ≤ Real.exp tY * Real.exp Q * f c':=by
      rw [hy,hv]; have he:= hxS U x Y' H h2 h4 h3; have hW: abandons_A x r A (misdemean p.threshold V) m:= by rw [H.1]; exact h4
      have hz:= collection_R B q' I.moon hp I.logo I.light ht.le h1 h2 h3 hW b κ k f₁ f₂ I.leanH I.heavy
      change richBoth _ _ _ _ _ _ _ V ≤ Real.exp ((-β*∑ b:Cell n,recruit Z q r A (misdemean p.threshold V) m b x Y') + billA R q n p β v η C S m (misdemean p.threshold V) (misdemean q' V) f₁ f₂) at hz
      rw [H.1,H.2] at hz; have hg:= Real.exp_monotone he; apply (mul_le_mul hz hg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)).trans_eq; rw [Real.exp_add,Real.exp_add]; unfold pulseFund tY; ring
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D.scale.le (D.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*D' ≤ (K* Real.exp Q)* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (mul_nonneg (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le))) (pow_nonneg (mul_nonneg D.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); unfold K daySeal tY M; ring
 unfold E; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hl (mul_nonneg hK (Real.exp_pos Q|>.le))).trans_eq ?_; unfold jewelFee; rw [show Q + (_:ℝ)+_+_= Q+(plumeCost B P W t + trend*b₂^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2) from (by ring), Real.exp_add Q]; ring
lemma dayBudget (Wa Da:Flaws n)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ accRoom T univ (grid_break r Da) Wa m)(V: Clarity B P p T m Wa Da q' β v Q t φ W) : (∫ x,day_play Z q p Wa Da T β κ k q' φ x ∂T.order G) ≤ daySeal n R J q p β v η C S Λ m Wa Da f₁ f₂ F.card * chartCost (prism T F H G)⁻¹ (coupling β) * Real.exp (jewelFee B P W t b₂ T F Q) :=by
 let X:= Blip T F; let D':=Held T (fun i=>i∈F); let L':= day_play Z q p Wa Da T β κ k q' φ; let K:=daySeal n R J q p β v η C S Λ m Wa Da f₁ f₂ F.card * chartCost (prism T F H G)⁻¹ (coupling β) * Real.exp (jewelFee B P W t b₂ T F Q); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((env_lease B u Wa Da).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundV B P L D I g0 u a h1 h2 Wa Da hg ht b hf i V)) (le_of_eq ?_); simp [χ]

end YM.Gleam
end
