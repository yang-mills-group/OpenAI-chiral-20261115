import YM.SU5.WakeInvestment.ThirdShelf
import SatinThinCivil
/-! Re-run `sourcedDebt`, then `harvest_civil` from SatinThinCabins & SatinThinCivil.
Use Third shelf and **same** respective saturated motion, curvature-base & accountant hypotheses.
Stronger harvest with this repeated comparator gains full volume mixed leading estimate also
in LP's classification; note previous G won't suffice for its prefix. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Wake
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D:LocalRatio J)

variable {α αcost ε dbκ dbD yQ:ℝ}{Y0:Finset (Cell n)}

def nearScene (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(r:Ratio c n)(m:ℕ)(β v ε α Q:ℝ)(A:Support c)(Y0: Finset (Cell n)) (t:ℝ)(φ:Config G n→ℝ)(W:Altar G n→ℝ):Prop:=
 ∀ (U:Config G n)(V Y:fieldDir G n 1), A=broken r ε U → Y0=misdemean α U→ ProbeBox (V+Y) (2*v)→ TrustLogs (V+Y) U r A v→ t*φ U ≤ t*W (starFeed B P r A (face_anchors Y0) m Y β V) + Q
abbrev nearPlay (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(Ω:Finset (Cell n))(T:Forest r)(β κ dbκ ε αcost α:ℝ)(U:T.Slice G):ℝ:= if broken r ε (T.drape U)=A ∧ misdemean α (T.drape U)=Ω then nearRich Z q p β κ dbκ ε αcost α (T.drape U) else 0
abbrev nearWave (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(Ω:Finset (Cell n))(T:Forest r)(β κ dbκ ε αcost α t:ℝ)(φ:Config G n→ℝ)(U:T.Slice G): ℝ:= nearPlay Z q p A Ω T β κ dbκ ε αcost α U * Real.exp (t * φ (T.drape U))
variable (I:Accounts J R q p r.count.val m β v Λ ε κ dbκ dbD yQ) (g0:2*(r.count.val+1)<n.val)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
private lemma universal_near {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩


include B in
lemma near_face (A:Support c) : Envelope (nearPlay Z q p A Y0 T β κ dbκ ε αcost α):= by
 let M :=T.drape (G:=G); have he:Measurable M:= T.continuous_drape.measurable
 let K:= universal_near (nearRich Z q p β κ dbκ ε αcost α (n:=n)) (near_burs B) M he
 exact Envelope.piece (p:=fun U=> broken r ε (M U)=A ∧ misdemean α (M U)=Y0) ((he (malaise_selector ..)).inter (he (scan_selector ..))) K (Envelope.const 0)
include B u in
lemma env_nearWave (A:Support c) (t:ℝ) : Envelope (nearWave Z q p A Y0 T β κ dbκ ε αcost α t φ):=(near_face B A).mul (universal_near _ (expEnv u t) _ (T.continuous_drape.measurable))
variable (α0:0≤α)(αt:α≤p.threshold)(αK: κ ≤ β*unitDueS q p/2)(αH:αcost+dbD ≤ β*unitDueN q α)
include α0 αt αK αH D B P L I g0 u a h1 h2
lemma nearRound (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ cloak T univ A Y0 m)(Y:LinkArray G (Blip T F))(hxS:nearScene B P p r m β v ε α Q A Y0 t φ W) : let WW(w:LinkArray G F):= nearWave Z q p A Y0 T β κ dbκ ε αcost α t φ (deep T F w Y); (∫ x,WW x ∂piHaar G (↥F)) ≤ footFile n R J q p β v η C S yQ Λ dbD m A.card F.card Y0.card * chartCost (prism T F H G)⁻¹ (coupling β)*Real.exp (jewelFee B P W t b₂ T F Q):=by
 intro WW; let K:=footFile n R J q p β v η C S yQ Λ dbD m A.card F.card Y0.card; let uQ:↥F → G.El:=1; let δ:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • WW (release uQ c); let X:= T.Slice G
 have hU: Envelope WW:= universal_near _ (env_nearWave B u A t) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J uQ, WW x=0:=by
    intro x v; unfold WW nearWave nearPlay; split; swap; · simp
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
   by_cases H:broken r ε V=A ∧ misdemean α V = Y0; swap; · unfold G' WW nearWave nearPlay; rw [if_neg H, zero_mul, smul_zero]; exact hE _
   have hd(i:↥F): let z:=release uQ c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=appearance I g0 A U H.1 (hf.trans cover_c) i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let D':= nearWave Z q p A Y0 T β κ dbκ ε αcost α t φ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ (p.threshold_pos.trans_le I.shield)).le.trans I.pale)
   obtain ⟨h1,h2,h3,h4⟩:= enterCol F hf Y (release uQ c') (p.threshold_pos.le.trans I.shield) H.1 g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release uQ c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4
   have hy : D'=nearRich Z q p β κ dbκ ε αcost α V * Real.exp (t * φ V):=by unfold D' nearWave; rw [nearPlay, if_pos H]
   have hv : f c'= yield_a Z q T F A (face_anchors Y0) m Y' β c'* Real.exp (t*W (starFeed B P r A (face_anchors Y0) m Y' β x)):= rfl
   have ht: D' ≤ Real.exp tY * Real.exp Q * f c':=by
      rw [hy,hv]; have he:= hxS V x Y' H.1.symm H.2.symm h2 h3; have hz:= near_shelf B α0 αt I.shield H.1.symm H.2.symm I.light ht.le h1 h2 h3 h4 hp I.logo b I.non_neg αK αH I.large; have hg:= Real.exp_monotone he; apply (mul_le_mul hz hg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)).trans_eq; rw [Real.exp_add,Real.exp_add]; unfold yield_a tY; ring
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D.scale.le (D.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*D' ≤ (K* Real.exp Q)* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (mul_nonneg (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le))) (pow_nonneg (mul_nonneg D.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); unfold K footFile tY M; ring
 unfold E; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hl (mul_nonneg hK (Real.exp_pos Q|>.le))).trans_eq ?_; unfold jewelFee; rw [show Q + (_:ℝ)+_+_= Q+(plumeCost B P W t + trend*b₂^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2) from (by ring), Real.exp_add Q]; ring
lemma nearDebt (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ cloak T univ A Y0 m)(V: nearScene B P p r m β v ε α Q A Y0 t φ W) : (∫ x,nearWave Z q p A Y0 T β κ dbκ ε αcost α t φ x ∂T.order G) ≤ wingFile R J q p β v η C S yQ Λ dbD m A.card Y0.card F H * Real.exp (jewelFee B P W t b₂ T F Q) :=by
 let X:= Blip T F; let D':=Held T (fun i=>i∈F); let L':= nearWave Z q p A Y0 T β κ dbκ ε αcost α t φ; let K:=wingFile R J q p β v η C S yQ Λ dbD m A.card Y0.card F H * Real.exp (jewelFee B P W t b₂ T F Q); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)

 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((env_nearWave B u A t).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>nearRound B P L D I g0 u a h1 h2 α0 αt αK αH A hg ht b hf i V)) (le_of_eq ?_); simp [χ]
open Regis.Head
variable {death:ℝ}
variable (Q':0 ≤ z')
variable {κ' : ℝ}
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)
variable (g:0<β)(d:0≤ κ')(l:0≤ C)
include d g j wH uH Q'
include he l
lemma near_civil {μ:ℝ}(Φ:∀ x, rebateB death μ x n) (pH:4*descendCost J β κ' z'*(r.count.val:ℝ)^4 ≤ yQ) (hω:4*descendCost J β κ' z'*(coldBill (hallBill m):ℕ)+death ≤ dbD) (Hx:GaugeInvariant φ) (v':∀ A:Support c, ∀ S:Finset (Cell n), nearScene B P p r m β v ε α (Q+z'*(trap r m A+trap_s m S)) A S t φ W): (∫ U:Config G n,nearRich Z q p β κ dbκ ε αcost α U*Real.exp (t*φ U)∂prior G n) ≤ Real.exp (Roof J β n H + rentRoom r R q m p β v η C S Λ (descendCost J β κ' z') + Q + plumeCost B P W t + trend*b₂^2*t^2 + Real.log 2*(Fintype.card (Site c):ℝ)+ μ*(Fintype.card (Site n):ℝ)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T; let D':= descendCost J β κ' z'
 let X:= fun U:Config G n=> nearRich Z q p β κ dbκ ε αcost α U*Real.exp (t*φ U); change (∫ U,X U∂_) ≤ _; have H1:Envelope X:= (near_burs B).mul (expEnv u _); have h':= near_gauge (αcost:=αcost) (α:=α) (ξ:=dbκ) (ε:=ε) (β:=β) (κ:=κ) (p:=p) (n:=n) B; rw [T.pack _ (H1.integrable _) (fun k y U=> by unfold X; rw [Hx,h' k])]; let U0:= Roof J β n H+rentRoom r R q m p β v η C S Λ D' + Q + plumeCost B P W t + trend*b₂^2*t^2; let F'(A:Support c)(Y0:Finset (Cell n)):= nearWave Z q p A Y0 T β κ dbκ ε αcost α t φ
 have hp(A:Support c)(Y0:Finset (Cell n)) : (∫ x,F' A Y0 x ∂T.order G)≤ Real.exp (U0-death*Y0.card) := by
    let p':=(qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩); have hg:= shelfPrize (W:=W) (Q:=Q) (b₂:=b₂) (t:=t) (K':=p') B P L D I Q' j wH uH g d A Y0 h pH hω; apply le_trans _ hg.2; exact nearDebt B P L D I g0 u a h1 h2 α0 αt αK αH A hg.1 g l (cloak_growth (subset_univ F)) (v' A Y0)
 rw [show (fun x:T.Slice G=> X (T.drape x))=(fun x=>∑ i: Support c,∑ j:Finset (Cell n),F' i j x) from ?_]
 swap
 · funext x; let N:= T.drape x; let i:=broken r ε N; let j:=misdemean α N; let H:= nearRich Z q p β κ dbκ ε αcost α N; have hφ(A:Support c)(B:Finset (Cell n)): F' A B x=(if (i,j)=(A,B) then X N else 0):=by
      unfold F' nearWave nearPlay; split <;> rename_i h; · rw [if_pos (Prod.ext h.1 h.2)]
      rw [if_neg (by intro k; exact h ⟨congrArg Prod.fst k,congrArg Prod.snd k⟩),zero_mul]
   simp_rw [hφ]; rw [← Fintype.sum_prod_type (fun b=> if (i,j)=b then X N else 0)]; simp [N]
 rw [integral_finsetSum]; swap; · exact fun i _=> integrable_finsetSum _ (fun j _=> (env_nearWave B u i t).integrable _)
 have hu:∀ i,(∫ x,(∑ j:Finset (Cell n),F' i j x)∂T.order G)≤ Real.exp (U0+μ*Fintype.card (Site n)):=by
    intro i; rw [integral_finsetSum]; exact (sum_le_sum (fun j _=>hp i j)).trans (Φ _); exact fun j _=> (env_nearWave B u i t).integrable _
 refine (sum_le_sum (fun i _=>hu i)).trans_eq (?_); rw [show Roof _ _ _ _ + _ + _ + _+_+_+_= U0+μ* (Fintype.card (Site n):ℝ) + Real.log 2* (Fintype.card (Site c):ℝ) from (by unfold U0; ring)]; simp only [sum_const,card_univ,nsmul_eq_mul, Real.exp_add (U0+_)]
 rw [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num)]; unfold Support; simp only [Fintype.card_finset]; push_cast; ring

end YM.Gleam.Wake
