import YM.SU5.Relativistic.BlueBox
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
local notation "J"=> Link N
local notation "O"=> Face (Per N)
local notation "V"=> Site C
variable (G: Gauge)(p:Clip){σ a b:ℝ}(B:PathData G)
open scoped Classical
local notation "S"=> Config G N
lemma crunch (i:O): (touched i).card ≤ 5:=by
 unfold touched; apply le_trans (List.toFinset_card_le _); rfl -- tune
lemma mush (s:ℝ)(U:S)(v:0≤ s) : (flags s U).card*(p.linear*s^2) ≤ 5*tollD G p s U:=by
 let F:= (univ:Finset O).filter (fun i=>s<girth G U i); have he: flags s U⊆ F.biUnion touched:=by
    intro i v; obtain ⟨k,t,u⟩:= (flags_spec ..).1 v; exact mem_biUnion.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,u⟩,t⟩
 have hs: (flags s U).card ≤ 5*F.card:= (card_le_card he).trans (card_biUnion_le.trans ((sum_le_sum (g:=fun _=> 5) (fun i _=> crunch i)).trans_eq (by rw [sum_const,nsmul_eq_mul,mul_comm] <;> rfl)))
 have hm(i:O)(t:i∈ F): p.linear*s^2≤ clipped p s (G.chord (faceValue U i)):=by
    have hz:= show s < G.chord (faceValue U i) from (mem_filter.mp t).2; unfold clipped; rw [if_neg hz.not_ge,sq,←mul_assoc]; exact mul_le_mul_of_nonneg_left hz.le (mul_nonneg p.tail_pos.le v)
 have ht:= sum_le_sum (s:=F) hm; rw [sum_const,nsmul_eq_mul] at ht; have hv : F.card*(p.linear*s^2)≤ tollD G p s U:=ht.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> clip_pos _ v (G.chord_nonneg _)))
 calc _ ≤ (5*F.card)*(p.linear*s^2):=mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (mul_nonneg p.tail_pos.le (by positivity))
      _= 5*(F.card*(p.linear*s^2)):=by rw [mul_assoc]
      _ ≤ 5*tollD G p s U:=mul_le_mul_of_nonneg_left hv (by norm_num)
open Pressure (radiusB temp)
open Next.SectorChange
variable {T: BudgetPoint}{r k β x t f ξ:ℝ} (X:B.Bounds p σ a b)
abbrev solar (U:S)(s f:ℝ):= f*(flags s U).card

def brine (B:PathData G)(p:Clip)(T:BudgetPoint)(β f:ℝ)(U:S):=Real.exp (solar G U T.threshold f-B.principal p T β U)
def grain (B:PathData G)(p:Clip)(T:BudgetPoint)(β f:ℝ)(U:S):=Real.exp (solar G U T.threshold f-B.inChannels p T β U)
lemma salt_env (s f:ℝ) : Envelope (fun U:S=>solar G U s f):=by
 have he:Envelope (fun U:S=>∑ i:Site N,if i∈flags s U then f else 0):= Envelope.sum _ _ fun i=> Envelope.piece ((flags_open i s).measurableSet) (Envelope.const _) (Envelope.const _)
 convert he using 1; funext i; unfold solar; rw [← sum_filter]; simp [mul_comm] -- tune
include X
lemma brine_int : Integrable (brine G B p T β f) (prior G N):= ((((salt_env G _ _).add (principal_env X T β).neg).exp).integrable _).congr (Eventually.of_forall (fun i=> congrArg Real.exp (sub_eq_add_neg ..).symm)) -- tune implicit N
lemma grain_int : Integrable (grain G B p T β f) (prior G N):= ((((salt_env G _ _).add (channels_env X T β).neg).exp).integrable _).congr (Eventually.of_forall (fun i=>congrArg Real.exp (sub_eq_add_neg ..).symm))
omit X in
lemma yearning (U:S) : grain G B p T β f U ≤ ∑ i:Signed, brine G B p T β f (pull i 0 U):=by
 let A(i:Signed):=pull i 0 U
 have he(i:Signed):solar G (A i) T.threshold f=solar G U T.threshold f:=by
    unfold solar; rw [← Work.H03.flags_send i 0 _ U]; rw [card_image_of_injective]; intro j k e; exact ((Signed.actEquiv i).injective (add_right_cancel e))
 let n:ℝ:= Fintype.card Signed; let v(i:Signed):= B.principal p T β (A i)
 obtain ⟨z,u,t⟩:= exists_min_image univ v (Finset.univ_nonempty)
 have ht: v z ≤ B.inChannels p T β U:=by
    have hh:= sum_le_sum (s:=univ) fun j hj=> t j hj; rw [sum_const,card_univ,nsmul_eq_mul] at hh; have hp:0<n:=Nat.cast_pos.mpr Fintype.card_pos
    change _≤ n⁻¹ * (∑ i,v i); rw [← div_eq_inv_mul,le_div_iff₀ hp,mul_comm]; exact hh
 have hm:grain G B p T β f U≤ brine G B p T β f (A z):=by unfold brine grain; rw [he]; exact Real.exp_le_exp.mpr (sub_le_sub_left ht _)
 exact hm.trans (single_le_sum (f:=fun i=>brine G B p T β f (A i)) (fun i _=>(Real.exp_pos _).le) (mem_univ z))
lemma request (T:BudgetPoint)(β f:ℝ) : (∫ i:S,grain G B p T β f i∂prior G N) ≤ Fintype.card Signed * ∫ i:S, brine G B p T β f i∂prior G N:=by
 let A:= brine (N:=N) G B p T β f; let g:=grain (N:=N) G B p T β f; let pri:= prior G N; have ht:Integrable A pri:= brine_int G p B X
 have hv (s:Signed) : Integrable (fun v=>A (pull s 0 v)) pri:= (prior_pull ..).integrable_comp_of_integrable ht
 have he(s:Signed): (∫ v:S,A (pull s 0 v)∂pri)= ∫ v:S,A v ∂pri:=by exact (BPress.Law.restore pri pri _ (prior_pull ..) A ht).symm
 apply le_trans (integral_mono (grain_int G p B X) (integrable_finsetSum univ fun i _=> hv i) (fun i=> yearning ..)); change (∫ v,∑ s,A (pull s 0 v)∂pri)≤_; rw [integral_finsetSum _ (fun i _=> hv i)]; simp_rw [he,sum_const,card_univ,nsmul_eq_mul]; rfl
variable {D:ℕ}(h:2≤ C.val)
def fillB (β k r t f:ℝ)(T:BudgetPoint)(D:ℕ)(A: Finset (Site C))(x:S):= Real.exp (-t*A.card)*(∏ j∈meter L A,husk G β k (parties L h G x j))*glory L G B D Aᶜ p T.threshold ((1-4*r)*β) x -- f not needed
omit X in
lemma fillP(A:Finset (Site C))(U:S) : 0 ≤ fillB L G p B h β k r t f T D A U:=by unfold fillB; exact mul_nonneg (mul_nonneg (Real.exp_pos _|>.le) (prod_nonneg fun _ _=> (Real.exp_pos _).le)) (prod_nonneg fun _ _=> payP ..)
lemma fillQ (ht:0<β)(hp:r<1/4)(A:Finset (Site C)) : Integrable (fillB L G p B h β k r t f T D A) (prior G N):=by
 let s:=(1-4*r)*β; let Y:= glory L G B D Aᶜ p T.threshold s; let F(x:S):= Real.exp (-t*A.card)*(∏ j∈meter L A,husk G β k (parties L h G x j)); have he: Continuous F:=by unfold F husk parties faceValue; fun_prop
 have hv := (show Integrable F (prior G N) from he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)).norm
 have hs:0<s:=mul_pos (by linarith) ht
 apply Integrable.mono' hv ((he.measurable.mul (goldMeas L G B D X _ _ _)).aestronglyMeasurable); refine Eventually.of_forall (fun i=>?_)
 change ‖fillB L G p B h β k r t f T D A i‖ ≤ _; rw [Real.norm_of_nonneg (fillP L G p B h A i)]; change F i*Y i≤‖F i‖; apply le_trans _ (le_abs_self (F i)); apply mul_le_of_le_one_right (show 0≤F i from mul_nonneg (Real.exp_pos _|>.le) (Finset.prod_nonneg fun _ _=> (Real.exp_pos _|>.le))) (Finset.prod_le_one (fun _ _=>payP ..) (fun _ _=> patS G B D _ _ _ _ hs.le)) -- tune

lemma buzz (z:T.threshold=temp x)(ha:1≤p.relaxation*σ)(hr:0<r)(hf:0≤ f)(hq:0≤ t)(wt:(1+1/r)*vane σ a D≤r*p.linear)(g:r<1/4)(hk:0<k)(βp:0<β)(h0:5*(f+t*hose x)≤ r*β*(p.linear*T.threshold^2))(hk0:k≤ (r*β)*(p.direct*(coupling β)^2/2))(hk1:k≤(r*β)*(p.linear*T.threshold*coupling β))(sickB:∀ x':S,(Beat L G p (temp x) x').card≤(flags (temp x) x').card*hose x) (U:S): brine G B p T β f U≤ Real.exp (Graph.taxY N β T.threshold a b) *∑ i:Finset V, fillB L G p B h β k r t f T D i U:=by
 let V':= Beat L G p T.threshold U; let s:=T.threshold; let Z:=solar G U s f; let E:= tollD G p s U
 have ht:= beats_cost (T:=T) L G p B D U X ha r hr wt g
 let W(i:T_):= boxE G B D p (tray L G i U); let η:= 1-4*r
 let F:= fun i:Link N=> k*(G.chord (parties L h G U i)/(coupling β))-k
 have he: (∑ i∈ meter L V',F i) ≤ r*β*E:=by
    let A:= meter L V'; let Wz:= tradeH L h; let Q:= A.image Wz
    let K(i:Face (Per N)):= clipped p s (G.chord (faceValue U i)); refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (f:=K) (subset_univ Q) fun _ _ _=> clip_pos _ T.threshold_pos.le (G.chord_nonneg _)) (show 0≤r*β by positivity)); unfold Q; rw [sum_image, mul_sum]; swap; · exact fun i t j p e=> trading L h (meter_ss L V' t) (meter_ss L V' p) e
    exact sum_le_sum (fun i _=> Fixed.Extensive.local_slot T.threshold_pos.le (show 0≤ r*β by positivity) (coupling_pos βp) hk0 hk1 hk.le _ (G.chord_nonneg _))
 have hx: Z+t*V'.card≤ r*β*E:=by
    have ht: (V'.card:ℝ) ≤ (flags s U).card*(hose x:ℝ):=by have he:=sickB U; rw [←z] at he; exact_mod_cast he
    let P':ℝ:=(flags T.threshold U).card
    have hu:0≤P':=by unfold P'; positivity
    have hh:= mush G p s U T.threshold_pos.le; have he:=mul_le_mul_of_nonneg_left hh (show 0≤r*β by positivity); unfold Z solar; change r*β*(P'*_)≤r*β*(5*E) at he
    nlinarith only [mul_le_mul_of_nonneg_right h0 hu,mul_le_mul_of_nonneg_left ht hq,he]
 apply le_trans _ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i=>fillB L G p B h β k r t f T D i U) (fun i _=> fillP L G p B h i U) (mem_univ V')) (Real.exp_pos _|>.le))
 unfold fillB; rw [show glory L G B D V'ᶜ p T.threshold (η*β) U = Real.exp (-(η*β)/2*∑ i∈V'ᶜ,W i) from ?_]; swap
 · unfold glory; rw [mul_sum,Real.exp_sum]; refine prod_congr rfl fun i g=> ?_; unfold localPay; rw [Set.indicator_of_mem (beat_guard L G p _ U i g)]; exact congrArg _ (by unfold W; ring)
 rw [show (∏ j∈meter L V', husk G β k (parties L h G U j))= Real.exp (-(∑ j∈meter L V',F j)) from ?_, ←Real.exp_add,← Real.exp_add,← Real.exp_add]; swap
 · unfold husk; rw [←sum_neg_distrib,Real.exp_sum]; exact Finset.prod_congr rfl fun i a=> congrArg _ (by unfold F coupling; rw [div_inv_eq_mul]; ring)
 apply Real.exp_le_exp.mpr; unfold Graph.taxY RG.PathData.principal; obtain ⟨u,v⟩:= Graph.oath X T U
 change 2*r*E+η/2* ∑ i∈ V'ᶜ,W i≤ _ at ht
 linarith only [mul_le_mul_of_nonneg_left ht βp.le,neg_le_of_abs_le v, mul_le_mul_of_nonneg_left (neg_le_of_abs_le u) βp.le,hx,he] -- tune
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.buzz
