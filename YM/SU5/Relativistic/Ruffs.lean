import YM.SU5.Relativistic.Brooms
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
open Pressure (temp radiusB)
open Precision Next.SectorChange
variable (D:ℕ)(Λ:ChartRatio G)(l:LocalRatio Λ)(X:B.Bounds p σ a b)(h:2≤ C.val)
local notation "δ"=> Fintype.card G.ColorIndex
-- absorb bad fee per bad brick. choose t before x
omit l h in
lemma floorFee (Ω:Side) (R:ℝ)(β θ:ℝ)(t:0<β)(e:0<θ) : (DueQ G B D X Ω).det ≤ (Ufee p a)^ Fintype.card (Fresco G Ω):=by
 let Q:=DueQ G B D X Ω; let V':= (Ufee p a) • (1 : Matrix (Fresco G Ω) (Fresco G Ω) ℝ); have hp:=p.quadratic_pos; have hx:0<Ufee p a:=by unfold Ufee; positivity
 refine (det_hike (screenP G B D X Ω).1 ((Matrix.PosDef.one).smul hx) (Q:=V') ?_).trans_eq (by unfold V'; rw [Matrix.det_smul,Matrix.det_one,mul_one]); intro x; unfold V'; rw [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]; have hv := vogue G p D B X 1 zero_lt_one x; simpa using hv
-- explicit λ charge for rest
include l
lemma payment (m:Side)(σ a b k θ:ℝ)(v:1≤ k)(w:0<θ):∃ F:ℝ,0≤ F ∧ ∀ (β:ℝ),0<β→ ∀ (Z:PathData G)(B:Z.Bounds p σ a b),
 Real.exp (-F)*(k*spare Λ β)^(livelies m).card≤ fee G m β Λ θ (DueQ G Z D B m).det:=by
 let n:=Fintype.card (Fresco G m); let z:= (θ*Ufee p a)^n; have hx:=p.quadratic_pos; have hp:0<z:=pow_pos (mul_pos w (show 0< Ufee p a by unfold Ufee; positivity)) _
 let v':= Real.sqrt z; let L:= k^(livelies m).card; have he:L*v'>0:= mul_pos (pow_pos (zero_lt_one.trans_le v) _) (Real.sqrt_pos.mpr hp)
 obtain ⟨F,g,t⟩:= ((Real.tendsto_exp_atTop.eventually_ge_atTop (L*v')).and (eventually_ge_atTop 0)).exists; refine ⟨F,t,fun β t Z B=>?_⟩
 let f:= (DueQ G Z D B m).det; have hh:0<f:=(screenP G Z D B m).1.det_pos
 have hq: θ^n*f≤ z:= (mul_le_mul_of_nonneg_left (floorFee G p Z D B m k β θ t w) (pow_pos w n).le).trans_eq (mul_pow .. |>.symm)
 let f':=Real.sqrt (θ^n*f); have ht:0<f':= Real.sqrt_pos.mpr (mul_pos (pow_pos w _) hh)
 have hk:Real.exp (-F)*L ≤ f'⁻¹:=by
    rw [Real.exp_neg,inv_mul_eq_div,div_le_iff₀ (Real.exp_pos _),← div_eq_inv_mul,le_div_iff₀ ht]; exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hq) (pow_pos (zero_lt_one.trans_le v) _).le).trans g
 let W:=spare Λ β; unfold fee; rw [mul_pow,show Fintype.card (Lo m)= _ from Fintype.card_coe _]; exact le_trans (le_of_eq (show Real.exp (-F)*(L*W^(livelies m).card)= W^(livelies m).card*(Real.exp (-F)*L) from by ring)) (mul_le_mul_of_nonneg_left hk (pow_nonneg (spare_pos _ l t).le _))

lemma lampine {A:Finset V} {T:BudgetPoint}{F r k f K β:ℝ} (pN:2≤ N.val)(s:0<β)(q:0≤ K)(g:0<1-4*r)
 (a:(∫ i:G.El,husk G β k i∂G.probHaar)≤ K*spare Λ β)
 (z:(∫ i:Config G W_,localPay G B D p T.threshold ((1-4*r)*β) i ∂prior G W_)≤2*fee G W_ β Λ (1-4*r) (DueQ G B D X W_).det)
 (v:Real.exp (-F)*(K*spare Λ β)^(livelies W_).card≤ fee G W_ β Λ (1-4*r) (DueQ G B D X W_).det):
 (∫ i:S,fillB L G p B h β k r F f T D A i∂ prior G N) ≤ (K*spare Λ β)^(wires L).card * (2*fee G W_ β Λ (1-4*r) (DueQ G B D X W_).det)^(C.val^4):=by
 let Q:=K*spare Λ β; let W:= fee G W_ β Λ (1-4*r) (DueQ G B D X W_).det; have ht:0≤Q:=mul_nonneg q (spare_pos _ l s).le
 have hv:=pow_nonneg ht (livelies W_).card; have hs:0 ≤ W:= (mul_nonneg (Real.exp_pos _|>.le) hv).trans v; let V':=2*W
 let U(i:S):=(∏ j∈ meter L A,husk G β k (parties L h G i j))*glory L G B D Aᶜ p T.threshold ((1-4*r)*β) i; rw [show fillB L G p B h β k r F f T D A=(fun x=> Real.exp (-F*A.card)*U x) from funext fun i=> mul_assoc ..,integral_const_mul]; unfold U; rw [wheelBill L h G B D X A T.threshold _ _ (by unfold husk; fun_prop) pN]
 apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (integral_nonneg fun x=> (Real.exp_pos _|>.le)) a _) (pow_le_pow_left₀ (integral_nonneg (fun x=> payP ..)) z _) (pow_nonneg (integral_nonneg fun _=>payP ..) _) (pow_nonneg ht _)) (Real.exp_nonneg _));
 have he:A.card+Aᶜ.card=C.val^4:=by rw [add_comm,card_compl_add_card A,Lattice.site_card]
 change Real.exp (-F*A.card)*(Q^(meter L A).card*V'^Aᶜ.card) ≤ Q^(wires L).card*V'^(C.val^4)
 rw [meter_card,pow_add,pow_mul',←he,pow_add,mul_comm (-F) _,Real.exp_nat_mul]
 refine le_trans (le_of_eq (b:=Q^(wires L).card*((Real.exp (-F)* Q^(livelies W_).card)^A.card*V'^Aᶜ.card)) ?_) ?_; · rw [mul_pow]; ring
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _|>.le) hv) (v.trans (show W≤ 2*W by linarith)) _) (pow_nonneg (by unfold V'; positivity) _)) (pow_nonneg ht _) -- tune le args

def pubB (K β r:ℝ) := Fintype.card Signed * ((2:ℝ)^(C.val^4) * (K*spare Λ β)^(wires L).card) * (2*fee G W_ β Λ (1-4*r) (DueQ G B D X W_).det)^(C.val^4)

-- W property awkward L exact count eq. choose F(p,θ,W') may coe
lemma firstM (Ω:Side)(σ a b f k K r z:ℝ)(hk:0<k)(he:0<r)(hf:0≤f)(w:r<1/4)(hZ:0≤a)(hx:0≤b) (pK:1≤K)(s:1≤ p.relaxation*σ)(hs:(1+1/r)*vane σ a D ≤ r*p.linear)(ht:k≤r*p.linear/2)(cK:∀ᶠ β:ℝ in atTop, ∫ i:G.El,husk G β k i∂G.probHaar ≤ K*spare Λ β)(e:0<z):∀ᶠ x:ℝ in atTop,∀ β∈ Set.Icc (x/2) (2*x),∀ (p':BudgetPoint),p'.threshold=temp x→ ∀ {N C:Side}(L:Ratio C N),2≤ N.val → 2≤ C.val → L.count=Ω →∀ (V':PathData G)(B:V'.Bounds p σ a b),
    (∫ i:Config G N, grain G V' p p' β f i ∂prior G N)≤ Real.exp (z*(N.val:ℝ)^4)*pubB L G p V' D Λ B K β r :=by
 let θ:=1-4*r; have hθ:0<θ:=by unfold θ; linarith
 obtain ⟨F,hF,g⟩:= payment G p D Λ l Ω σ a b K θ pK hθ
 obtain ⟨t,u,q⟩:= purseH G p Λ D l Ω σ a b θ hθ 1 zero_lt_one
 obtain ⟨L,h⟩:= eventually_atTop.mp (cK.and q)
 filter_upwards [fuelGauge p a b r f F z k he hk ht hf hF (lt_or_eq_of_le hZ|>.imp id Eq.symm) hx e,eventually_ge_atTop (2*L),proof_t.eventually (ge_mem_nhds u), beat_budget G p] with x hcZ r2 P v β kx p' pT N C L' e1 e2 Wz S' y; -- r shadow use names
 obtain ⟨a₀,b₀,h₀,hc,hb,hh,hD⟩:=hcZ β kx; have ha:=h β (by linarith [kx.1]); let Q(A:Finset (Site C)):=fillB L' G p S' e2 β k r F f p' D A; let pri:= prior G N; have hI(A): Integrable (Q A) pri:= fillQ L' G p S' y e2 b₀ w A
 let t':= Real.exp (Graph.taxY N β p'.threshold a b)
 have hΨ: (∫ i, brine G S' p p' β f i ∂pri) ≤ t'*∑ A:Finset (Site C),∫ i,Q A i ∂pri:=by
    rw [← integral_finsetSum _ (fun A _=>hI A),← integral_const_mul]; apply integral_mono (brine_int G p S' y) ((integrable_finsetSum _ (fun i _=> hI i)).const_mul t'); intro i; rw [←pT] at hc hh; exact buzz L' G p S' y e2 pT s he hf hF hs w hk b₀ hc hb hh (v L') i -- tune
 have hr(A): (∫ i,Q A i ∂pri) ≤ (K*spare Λ β)^(wires L').card*(2*fee G L'.count β Λ θ (DueQ G S' D y L'.count).det)^(C.val^4):=by
    apply lampine L' G p S' D Λ l y e2 e1 b₀ (zero_le_one.trans pK) hθ ha.1; · rw [Wz,pT]; apply (ha.2 _ y _ ⟨h₀.le,P⟩).trans; norm_num; exact le_rfl
    rw [Wz]; exact g _ b₀ S' y
 apply le_trans (request G p S' y p' β f); apply le_trans (mul_le_mul_of_nonneg_left (hΨ.trans (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> hr i)) (Real.exp_nonneg _))) (by positivity)); unfold pubB; rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_finset,site_card]; push_cast
 have hv: t'≤Real.exp (z*(N.val:ℝ)^4):=by unfold t'; rw [pT]; exact Real.exp_le_exp.mpr (hD N)
 have hm : 0 ≤ fee G L'.count β Λ θ (DueQ G S' D y L'.count).det:=by unfold fee; exact mul_nonneg (pow_nonneg (spare_pos _ l b₀).le _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
 let X':=(K*spare Λ β)^(wires L').card; let y':=(2*fee G L'.count β Λ θ (DueQ G S' D y L'.count).det)^(C.val^4); have hX:0≤ X':=pow_nonneg (mul_nonneg (zero_le_one.trans pK) (spare_pos _ l b₀).le) _
 have hy:0 ≤ y':=by unfold y'; positivity
 let n:ℝ:= Fintype.card Signed; let m:ℝ:= (2:ℝ)^(C.val^4)
 change n*(t'*(m*(X'*y'))) ≤ _*(n*(m*X')*y'); nlinarith only [mul_le_mul_of_nonneg_right hv (show 0≤ n*(m*X')*y' by unfold n m; positivity)]
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.firstM
