import YM.SU5.Regis.Brass

/-! # Pay gauge rent under localized aggregate mark perturbation. Adapt Inlets & Danube,
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

def SceneLease (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(r:Ratio c n)(m:ℕ)(β v Q:ℝ)(A:Support c) (t:ℝ)(φ:Config G n→ℝ)(W:Altar G n→ℝ):Prop:=
  ∀ (U:Config G n)(V Y:fieldDir G n 1), A=broken r p.threshold U → ProbeBox (V+Y) (2*v)→ TrustLogs (V+Y) U r A v→ t*φ U ≤ t*W (starCost B P r A m Y β V) + Q
abbrev playWave (Z:PathData G)(q:Clip)(p:BudgetPoint)(A:Support c)(T:Forest r)(β κ t:ℝ)(φ:Config G n→ℝ)(U:T.Slice G): ℝ:= play Z q p A T β κ U * Real.exp (t * φ (T.drape U))
variable (I:Archive J R q p r.count.val m β κ ξ v Λ) (g0:2*(r.count.val+1)<n.val)
variable {Q b₁ b₂ z':ℝ}{φ:Config G n→ℝ} (u: RG.Envelope φ) {W:Altar G n→ℝ}(a:ContDiff ℝ 1 W) (h1:∀ x, |W x| ≤ b₁)(h2: ∀ x, ‖fderiv ℝ W x‖≤ b₂)
private lemma env_form {X:Type*}[MeasurableSpace X]{Y:Type*}[MeasurableSpace Y](F:X→ℝ)(h:RG.Envelope F)(g:Y→ X)(p:Measurable g): Envelope fun i=> F (g i):=by obtain ⟨c,k⟩:=h.cost; exact ⟨h.meas.comp p,c,fun x=> k _⟩

lemma expEnv {E:Type*} [MeasurableSpace E]{f:E→ℝ}(p:Envelope f)(a:ℝ) : Envelope (fun u => Real.exp (a*f u)):= ((Envelope.const a).mul p).exp
include B u in
lemma env_playWave (A:Support c)(t:ℝ): Envelope (playWave Z q p A T β κ t φ):=(env_play B A).mul (env_form _ (expEnv u t) _ (T.continuous_drape.measurable))
abbrev jewelFee(B:Z.Bounds q η C S)(P:Attached H Z)(W:Altar G n→ℝ)(t b:ℝ) (T:Forest r)(F:Finset T.Free) (Q:ℝ):= Q + plumeCost B P W t + trend*b^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2
include D B P L I g0 u a h1 h2
lemma roundFar (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ room T univ A m)(Y:LinkArray G (Blip T F))(hxS:SceneLease B P p r m β v Q A t φ W) : let WW(w:LinkArray G F):= playWave Z q p A T β κ t φ (deep T F w Y); (∫ x,WW x ∂piHaar G (↥F)) ≤ sealFeet n R J q p β v η C S ξ Λ m A.card F.card * chartCost (prism T F H G)⁻¹ (coupling β)*Real.exp (jewelFee B P W t b₂ T F Q):=by
 intro WW; let K:=sealFeet n R J q p β v η C S ξ Λ m A.card F.card; let uQ:↥F → G.El:=1; let δ:= (mouth (ι:=↥F) J); let G'(c:LogArray G F) := pay J c • WW (release uQ c); let X:= T.Slice G
 have hU: Envelope WW:= env_form _ (env_playWave B u A t) _ (by apply ((freeze_meas T _).comp (f:=fun x:LinkArray G F=> (x,Y)) (measurable_id.prodMk measurable_const)))
 have hp: ∀ x ∉ Next.SectorChange.covered J uQ, WW x=0:=by
    intro x v; unfold WW playWave play; split; swap; · simp -- zero
    next H=>
      exact False.elim <| v fun i _=>by
         let t:=current I g0 A (deep T F x Y) H hf i; let X:=x i; let b:= G.plog (G.mat X); have ht: deep T F x Y i.val=X:=freeze_held ..; have hX:=t.2.2; simp only [ht] at hX; exact ⟨X,⟨b,hX.2,hX.1⟩,mul_one _⟩
 obtain ⟨hx,he⟩:= release_integral D uQ WW hU.meas.stronglyMeasurable hp
 let f:= climbSource B P T F A m (myLog T F Y A) β W t; obtain ⟨hg',hl⟩:= at_source (A:=A) (m:=m) B P L (myLog T F Y A) hg ht W a h1 h2 t
 let tY:= taxΔ R q n p β v η C S m - ξ*A.card; let E(c):= K * Real.exp Q * f c; let M:= J.scale * Real.exp Λ; have hK :0≤K:=by unfold K sealFeet; have h:=D.scale; positivity
 have hE(c):0≤ E c:=mul_nonneg (mul_nonneg hK (Real.exp_pos _|>.le)) (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))
 change (∫ x,WW x ∂piHaar G (↥F)) ≤ K * chartCost (prism T F H G)⁻¹ (coupling β) * _; rw [he]; apply le_trans (b:=∫ x,E x)
 · apply integral_mono (hx.mp (hU.integrable _)) (hg'.const_mul _); intro c'; change δ.indicator G' c'≤ E c'; by_cases h:c'∈δ; swap; · rw [Set.indicator_of_notMem h]; exact hE _
   rw [Set.indicator_of_mem h]; let U:= deep T F (release uQ c') Y; let V:= T.drape U
   by_cases H:broken r p.threshold V=A; swap; · unfold G' WW playWave play; rw [if_neg H, zero_mul, smul_zero]; exact hE _
   have hd(i:↥F): let z:=release uQ c' i; G.plog (G.mat z)= c' i ∧ ‖c' i‖≤2*v:=by
      intro z; let a:=U i.val; let y:=G.plog (G.mat z); obtain ⟨_,k,Tt,l⟩:=current I g0 A U H hf i; rw [show U _= z from freeze_held ..] at k Tt l; have hv:y=c' i:= D.inject l (h i (Set.mem_univ _)) (Tt.trans (mul_one _)); exact ⟨hv,hv ▸ k⟩
   let D':= playWave Z q p A T β κ t φ U; let Y':= myLog T F Y A; let x:= stock T F c'; have hp:0 ≤ v:= ((suitFee_pos _ p.threshold_pos).le.trans I.pale)
   obtain ⟨h1,h2,h3,h4⟩:= beyondMake F hf Y (release uQ c') H g0 I.pale I.logo
   rw [show (fun b:↥F=> G.plog (G.mat (release uQ c' b)))=c' from funext (fun i=>(hd i).1)] at h1 h2 h3 h4 -- doesn't work hole
   have hy : D'=richG Z q p β κ V * Real.exp (t * φ V):=by unfold D' playWave; rw [play, if_pos H]
   have hv : f c'= yieldY Z q T F A m Y' β c'* Real.exp (t*W (starCost B P r A m Y' β x)):= rfl
   have ht: D' ≤ Real.exp tY * Real.exp Q * f c':=by
      rw [hy,hv]; have he:= hxS V x Y' H.symm h2 h3; have hz:= enormous_f B H.symm I.light ht.le h1 h2 h3 h4 hp I.logo b I.zero_ξ I.prompt; have hg:= Real.exp_monotone he; apply (mul_le_mul hz hg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)).trans_eq; rw [Real.exp_add,Real.exp_add]; unfold yieldY tY; ring
   have hw: pay J c' ≤ M^F.card:=by
     refine (Finset.prod_le_prod (s:=univ) (g:=fun _=> M) ?_ ?_).trans_eq ?_; · intro i _; exact mul_nonneg D.scale.le (D.pos _ (h i (Set.mem_univ _))).le
     · intro i _; exact mul_le_mul_of_nonneg_left (I.support _ (hd i).2) D.scale.le
     rw [prod_const,card_univ,Fintype.card_coe]
   change pay J c'*D' ≤ (K* Real.exp Q)* f c'; refine (mul_le_mul hw ht (hy.symm ▸ (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))) (pow_nonneg (mul_nonneg D.scale.le (Real.exp_pos _).le) _)).trans_eq (?_); unfold K sealFeet tY M; ring
 unfold E; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left hl (mul_nonneg hK (Real.exp_pos Q|>.le))).trans_eq ?_; unfold jewelFee; rw [show Q + (_:ℝ)+_+_= Q+(plumeCost B P W t + trend*b₂^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2) from (by ring), Real.exp_add Q]; ring
lemma sourcedBudget (A:Support c)(hg:(cellM T F H).PosDef)(ht:0<β)(b:0 ≤ C)(hf:F ⊆ room T univ A m)(V: SceneLease B P p r m β v Q A t φ W) : (∫ x,playWave Z q p A T β κ t φ x ∂T.order G) ≤ wingFee n R J q p β v η C S ξ Λ m A.card F H * Real.exp (jewelFee B P W t b₂ T F Q) :=by
 let X:= Blip T F; let D':=Held T (fun i=>i∈F); let L':= playWave Z q p A T β κ t φ; let K:=wingFee n R J q p β v η C S ξ Λ m A.card F H * Real.exp (jewelFee B P W t b₂ T F Q); let ν:=T.order G; let μ:=piHaar G (↥F); let χ:=piHaar G (Blip T F)
 have hm: MeasurePreserving (divide (G:=G) T (fun i=>i∈ F)) (T.order G) (μ.prod χ):=by
    convert divided (G:=G) T (fun i=>i∈ F) using 1; unfold μ χ; congr!
 let Y(u:LinkArray G F× LinkArray G X):=L' (deep T F u.1 u.2)
 -- use rotated Fubini, applies difference between Fintype card of `b` as subtype from finset vs Decidable mem
 have h: Integrable Y (μ.prod χ):= hm.symm.integrable_comp_of_integrable ((env_playWave B u A t).integrable _)

 change (∫ x,L' x ∂T.order G) ≤ K; rw [← hm.symm.integral_comp' L']; change (∫ x,Y x∂ μ.prod χ)≤ K; rw [integral_prod_symm Y h]
 refine le_trans (integral_mono h.integral_prod_right (integrable_const (μ:=χ) K) (fun i=>roundFar B P L D I g0 u a h1 h2 A hg ht b hf i V)) (le_of_eq ?_); simp [χ]
variable (Q':0 ≤ z') -- z' reserve coefficient per unit universal wall
variable {κ' : ℝ}
variable (j:Odd r.count.val)(wH:hallBill m ≤ r.count.val/2)(uH:∀ i, (Precision.K (H.metric.acts n)) i i ≤ κ')(he:0 < δ)

-- true payment for bounded witness at ALL classified wall/dirt may be proportional to #sites there + generic Q.
def trap (r:Ratio c n)(m:ℕ)(k:Support c):ℝ:= 4*((Fintype.card (Site c):ℝ)*largerBill r.count.val (hallBill m)+ k.card*(r.count.val:ℝ)^4)
def descendCost (J:ChartRatio G)(β t e:ℝ):= margin J β t + ((Fintype.card G.ColorIndex):ℝ)/2 + e
omit D B P L I g0 u a h1 h2
private lemma wing_purchase (h:(cellM T F H).PosDef)(g:0<β)(D:LocalRatio J) : let M:= wingFee n R J q p β v η C S ξ Λ m A.card F H; 0<M ∧ Real.log M=(F.card:ℝ) * (Real.log (spare J β)+Λ) - (Fintype.card G.ColorIndex:ℝ)/2*Real.log (cellM T F H).det + taxΔ R q n p β v η C S m - ξ*A.card :=by
 intro M; let F':= J.scale ^ F.card * chartCost (prism T F H G)⁻¹ (coupling β)
 let V:= R.C; let E:= taxΔ R q n p β v η C S m - ξ*A.card; let T:= Real.exp (E+Λ*F.card); have hz: 0<F':= mul_pos (pow_pos D.scale _) (chartCost_pos _ (PosDef.kronecker h PosDef.one).inv (coupling_pos g))
 have hT: M=F'*T:=by unfold F' M wingFee sealFeet T; rw [mul_pow,Real.exp_add, mul_comm Λ _,Real.exp_nat_mul]; unfold E; ring
 rw [hT]; refine ⟨mul_pos hz (Real.exp_pos _),?_⟩; rw [Real.log_mul hz.ne' (Real.exp_pos _).ne',show Real.log T= _ from Real.log_exp _, (show Real.log F'= _ from prism_spec J D g h)]; unfold E; ring
variable (g:0<β)(d:0≤ κ')(l:0≤ C)
include B P L D I d g j wH uH Q'
private lemma highPrize {K':(H.metric.acts n).PosDef} (A:Support c)(H':Buttress T F)(pH:4*descendCost J β κ' z'*(r.count.val:ℝ)^4 ≤ ξ): let W0:= room T F A m; let M:=wingFee n R J q p β v η C S ξ Λ m A.card W0 H; (cellM T W0 H).PosDef ∧ M*Real.exp (jewelFee B P W t b₂ T W0 (Q+z'*trap r m A)) ≤ Real.exp (Roof J β n H+rentRoom r R q m p β v η C S Λ (descendCost J β κ' z') + Q + plumeCost B P W t + trend*b₂^2*t^2):=by -- u implicit causing omit param L; make explicit implicit synthesizable?
 intro W0 M
 let d':= descendCost J β κ' z'; let K:=leasePart (H.metric.acts n); let X:= Real.log (spare J β); let Y:ℝ:=(Fintype.card G.ColorIndex:ℝ)/2
 let i:= Real.log K; let Hf:=cellM T W0 H; have hh:W0⊆ F:=inner_part; let Hc:= rentRoom r R q m p β v η C S Λ d'; let D':ℕ:=F.card-W0.card; let f:ℝ:=F.card; let c':ℝ:=W0.card; let a:ℝ:=Fintype.card (Site c); let B₀:ℝ:=Fintype.card (Site n)
 have hm : 1 ≤ Fintype.card (Site n):=Fintype.card_pos; have ht :f=3*(B₀-1):=by unfold f; rw [H'.count,Nat.cast_mul,Nat.cast_sub hm]; push_cast; rfl
 obtain ⟨gH,hZ⟩:= looks H K' uH H' hh; refine ⟨gH,?_⟩; obtain ⟨h1,h2⟩:=wing_purchase (A:=A) (R:=R) (H:=H) (p:=p) (v:=v) (η:=η) (C:=C) (S:=S) (ξ:=ξ) (Λ:=Λ) (m:=m) gH g D; rw [← Real.log_le_log_iff (mul_pos h1 (Real.exp_pos _)) (Real.exp_pos _),Real.log_mul h1.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp];
 let x:= largerBill r.count.val (hallBill m); let y:ℝ:= (r.count.val:ℝ)^4
 have hp : (D':ℝ)=f-c':= Nat.cast_sub (card_le_card hh)
 have hxcard :(D':ℝ) ≤ 4*(a*x+A.card*y):= by
    exact (Nat.cast_le (α:=ℝ).mpr (inner_charge (a:=F) (d:=hallBill m) (A:=A) j wH)).trans (le_of_eq (by unfold a x y; push_cast; rfl))
 have hy:0 ≤ f-c':=hp ▸ Nat.cast_nonneg _
 have h':= mul_le_mul_of_nonneg_left hxcard (show 0≤d' from by unfold d' descendCost; have t' := pays_hall (J:=J) (β:=β) d; positivity)
 -- split I green. t δ etc. absorb
 have hh':Λ*(B₀) ≥ 0:= mul_nonneg I.green (by unfold B₀; positivity)
 have hu:c'*Λ ≤ f*Λ:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hh)) I.green
 have hq:= mul_le_mul_of_nonneg_left pH (Nat.cast_nonneg (α:=ℝ) A.card)
 have hk:= mul_le_mul_of_nonneg_right (neg_le_abs X) hy
 change Real.log M=_ at h2; rw [h2]; unfold Roof rentRoom
 change i ≤ Real.log (Hf.det) + κ'*D' at hZ; rw [hp] at h' hZ
 change c'*(X+Λ) - Y*_ + _ -_ + jewelFee B P W t b₂ T W0 (Q+z'*trap r m A) ≤ 3*(B₀-1)*X-Y*i +( _ + 4*Λ*B₀ +4*d'*a*x)+_+_+_
 have hz:0≤Y:=by unfold Y; positivity
 change d'*(f-c') ≤ d'*(4*(a*x+A.card*y)) at h'; change _ * (4*d'*y) ≤ _ at hq; change i≤ Real.log (cellM T W0 H).det+ _ at hZ; rw [←ht]; unfold jewelFee trap; let Z0:= trap r m A
 have uT: (cellM T F H).PosDef:= (H'.precision K').1
 have hF:=at_rank B P L uT; have hw:=at_rank B P L gH; rw [← garden_equiv B P L H',hF,hw]; push_cast
 have hx : |Real.log (spare J β)|=d'-Y*κ'-Y-z':=by unfold d' Y descendCost margin; ring
 have hv : f-c' ≤ Z0:= by rwa [hp] at hxcard
 change d'*(f-c') ≤ d'*Z0 at h'
 change 0 ≤ z' at Q'
 let C' := Fintype.card G.ColorIndex
 rw [show |X| = _ from hx] at hk
 have hv': (d'-z')*(f-c') ≤ (d'-z')*Z0:=mul_le_mul_of_nonneg_left hv (by unfold d' descendCost; have hz:=pays_hall (J:=J) (β:=β) d; have he:0 ≤ (Fintype.card G.ColorIndex:ℝ):=Nat.cast_nonneg _; linarith only [hz,he])
 change (d'-z')*(f-c') ≤ (d'-z')*(4*(a*x + A.card*y)) at hv'
 change z' ≥ 0 at Q'; change (_ :ℝ) + (Q + z'*(4*(a*x + A.card*y))+_ +_ + ((f*(C':ℝ)-c'*(C':ℝ))/2)) ≤ _  -- adjust assoc
 have hw : (C':ℝ) = 2*Y:= by unfold Y C'; ring
 linarith only [hk,hh',ht,hu,hq,mul_le_mul_of_nonneg_left hZ hz,hv', I.green,mul_le_mul_of_nonneg_right ht.le I.green,mul_le_mul_of_nonneg_right hw.ge (show 0≤f-c' from hy),mul_le_mul_of_nonneg_right hw.le hy]
include u h1 h2 a he g0 l
lemma harvest_slate (pH:4*descendCost J β κ' z'*(r.count.val:ℝ)^4 ≤ ξ) (Hx:GaugeInvariant φ) (v':∀ A:Support c, SceneLease B P p r m β v (Q+z'*trap r m A) A t φ W): (∫ U:Config G n,richG Z q p β κ U*Real.exp (t*φ U)∂prior G n) ≤ Real.exp (Roof J β n H + rentRoom r R q m p β v η C S Λ (descendCost J β κ' z') + Q + plumeCost B P W t + trend*b₂^2*t^2 + Real.log 2*(Fintype.card (Site c):ℝ)):=by
 obtain ⟨T⟩:=Tree.select r j; obtain ⟨F,h⟩:= buttress_uses T; let D':= descendCost J β κ' z'
 let X:= fun U:Config G n=> richG Z q p β κ U*Real.exp (t*φ U); change (∫ U,X U∂_) ≤ _; have H1:Envelope X:= (income_g B).mul (expEnv u _); have h':= richG_inv (β:=β) (κ:=κ) (p:=p) (n:=n) B; rw [T.pack _ (H1.integrable _) (fun k y U=> by unfold X; rw [Hx,h' k])]; let U0:= Roof J β n H+rentRoom r R q m p β v η C S Λ D' + Q + plumeCost B P W t + trend*b₂^2*t^2; let F'(A:Support c):= playWave Z q p A T β κ t φ
 have hp(A:Support c) : (∫ x,F' A x ∂T.order G)≤ Real.exp U0 := by
    let p':=(qpos he L.symmetric.1 ⟨fun x=> (L.uniform.1 x).1⟩); have hg:= highPrize (W:=W) (Q:=Q) (b₂:=b₂) (t:=t) (K':=p') B P L D I Q' j wH uH g d A h pH; apply le_trans _ hg.2; exact sourcedBudget B P L D I g0 u a h1 h2 A hg.1 g l (filter_subset_filter _ (subset_univ F)) (v' A)
 rw [show (fun x:T.Slice G=> X (T.drape x))=(fun x=>∑ i: Support c,F' i x) from ?_]
 swap; · funext x; unfold F' playWave; rw [← sum_mul]; simp [play,X]
 rw [integral_finsetSum]; swap; · exact fun i _=> (env_playWave B u _ _).integrable _
 refine (sum_le_sum (fun i _=> hp i)).trans_eq (?_); change (∑ _: Support c, Real.exp U0)=Real.exp (U0+_); simp only [sum_const,card_univ,nsmul_eq_mul,Real.exp_add]; rw [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log (by norm_num)]; unfold Support; simp only [Fintype.card_finset]; push_cast; ring
end YM.Gleam
#print axioms YM.Gleam.harvest_slate
