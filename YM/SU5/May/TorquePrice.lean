import YM.SU5.May.TorqueHearth
import YM.SU5.May.TorqueTreat
import YM.SU5.May.FloeMix
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (m t s R:ℕ) (P:Ramp)
variable {v:ℝ} (h:0<v) (C c:ℝ)
local notation "Rₘ" m:max=> ((↑(Y.ir m).val):ℝ)
noncomputable def resist (A:Preparation)(s:ℕ):ℝ:=2*A.block.val * (A.R.L.val:ℝ)^s
lemma size_t (a:ℕ): ((↑(Journey.side Y m (s+a)).val):ℝ) = resist Λ s * ((↑(Y.ir m).val):ℝ)*(Λ.R.L.val:ℝ)^a:=by
 unfold resist; unfold Journey.side; unfold Ctor cell CSide; change ((↑(((Y.ir m).val*(Λ.R.L^(s+a) : Side).val)*2*Λ.block.val)):ℝ)= _; simp [pow_add] -- tune
 ring
structure Bud (v:ℝ) (V:ℝ→ℝ) : Prop where
 mono:∀ᶠ x in atTop,0≤V x
 priced(c:ℝ)(p:0<c):∀ᶠ x in atTop,V x≤ Real.exp (c*x^v)
variable {F G':ℝ→ℝ}{z:ℝ} (hu:Bud v F)(pu:Bud v G')
lemma Bud.pit (v:ℝ)(h:0<v)(p:0 ≤ C): Bud v fun _=>C:= ⟨Eventually.of_forall fun _=>p, fun c g=>(Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop h).const_mul_atTop g)).eventually_ge_atTop _⟩
include hu in
lemma Bud.up (p:∀ᶠ i in atTop,0≤ G' i∧G' i ≤ F i): Bud v G':= ⟨p.mono fun _ h=>h.1, fun c g=>(p.and (hu.priced c g)).mono fun i h=>h.1.2.trans h.2⟩ -- include hu
lemma Bud.mul (hu:Bud v F)(pu:Bud v G'): Bud v (fun x=> F x*G' x):=by
 constructor; · exact (hu.mono.and pu.mono).mono fun _ h=> mul_nonneg h.1 h.2
 intro c h; filter_upwards [hu.priced (c/2) (half_pos h),pu.priced (c/2) (half_pos h),pu.mono] with x t v u; exact (mul_le_mul t v u (Real.exp_nonneg _)).trans_eq (by rw [←Real.exp_add,←add_mul,add_halves])
include h
lemma Bud.plus (hu:Bud v F)(pu:Bud v G'): Bud v (fun x=> F x+G' x):=by
 constructor; · exact (hu.mono.and pu.mono).mono fun _ h=> add_nonneg h.1 h.2
 intro c hp; filter_upwards [hu.priced (c/2) (half_pos hp),pu.priced (c/2) (half_pos hp),(Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop h).const_mul_atTop (half_pos hp))).eventually_ge_atTop 2] with x t u e; let A:= Real.exp (c/2*x^v); apply (add_le_add t u).trans; rw [show Real.exp (c*x^v)=A*A from (by unfold A; rw [←Real.exp_add,←add_mul,add_halves])]; change 2 ≤ A at e; change A+A≤A*A; nlinarith
lemma Bud.pow (hu:Bud v F)(n:ℕ):Bud v (fun x=>F x^n):=by induction n with
 | zero=>simp_rw [pow_zero]; exact Bud.pit _ _ h zero_le_one
 | succ n ih=> simp_rw [pow_succ]; exact ih.mul hu
lemma Bud.serial: Bud v id:=by
 refine ⟨eventually_ge_atTop _,fun c g=>?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ),(tendsto_rpow_atTop h).eventually ((isLittleO_rpow_exp_pos_mul_atTop v⁻¹ g).bound zero_lt_one)] with x t u
 rw [Real.norm_of_nonneg (by positivity :0 ≤ (x^v)^v⁻¹),Real.rpow_rpow_inv t.le h.ne',Real.norm_of_nonneg (Real.exp_nonneg _),one_mul] at u; exact u
lemma Bud.puff {c:ℝ}: Bud v (fun x:ℝ=> Real.exp (c*x^(v/2))):=by
 refine ⟨Eventually.of_forall fun i=> Real.exp_nonneg _,fun d hd=>?_⟩
 apply ((Sleigh.Paddled.scale (F:=fun x:ℝ=> x^(v/2)) (Sleigh.Paddled.park _) c).discounts (half_lt_self h) hd).mono fun t e=> Real.exp_monotone ((le_abs_self _).trans e)
include hu in
lemma Bud.funded : Tendsto (fun x:ℝ=>Real.exp (- x^v)*F x) atTop (𝓝 0):=by
 apply squeeze_zero' (hu.mono.mono fun i h=>mul_nonneg (Real.exp_nonneg _) h) ?_ (Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_rpow_atTop h).const_mul_atTop (show (0:ℝ)<1/2 from by norm_num)))
 filter_upwards [hu.priced (1/2) (by norm_num)] with x t; exact (mul_le_mul_of_nonneg_left t (Real.exp_nonneg _)).trans_eq (by rw [←Real.exp_add]; unfold Function.comp; ring_nf)
-- $(B+Delta)*N *ρ² ≤ (C+1)*(resist(A)/L^s) · m*exp(...) ...$ then price ≤ rime cost. Uniform EVEN not contour
noncomputable def gentle (Y:Course Λ (VolumeCape.Dream.Nimbus l))(v:ℝ) (m s:ℕ):= ((↑(Journey.side Y m s).val):ℝ) * Real.exp (-((↑(Y.ir m).val):ℝ)^v)
noncomputable def scrutiny (D δ:ℝ) (Y:Course Λ (VolumeCape.Dream.Nimbus l))(v:ℝ)(κ m s a:ℕ):= rimeCost κ (1+(D*(↑(Journey.side Y m (s+a)).val:ℝ)+gentle Y v m (s+a))*price_leg Λ s a^2) * (gentle Y v m (s+a)*price_leg Λ s a^2)*δ^2
include h
lemma booked_charge (p:0≤ C)(ε:ℝ)(p₁:0<ε):∃ γ:ℝ, 0<γ ∧∀ᶠ m in atTop,∀ a:ℕ,s+a ≤ turnUp Y m → scrutiny C c Y v κ m s a ≤ ε*Real.exp (-( (Rₘ m)^γ)):=by
 obtain ⟨A,g,hG⟩:= leg_shelter Y (half_pos h); let y (x:ℝ):= Real.exp (A*x^(v/2)); let W(x:ℝ):ℝ:= resist Λ s*x*y x^2; let F(x:ℝ):ℝ:= rimeCost κ (1+(C+1)*W x)*W x*(Real.exp (x^(v/2))*c^2)
 have ht: Bud v W:= ((Bud.pit _ v h (by unfold resist; positivity)).mul (Bud.serial h)).mul (Bud.pow h (Bud.puff h) _) -- args tune
 have hp: Bud v F:=by
    have he: Bud v (fun x:ℝ=> (1:ℝ)+(C+1)*W x):=Bud.plus h (Bud.pit _ v h zero_le_one) ((Bud.pit _ v h (add_nonneg p zero_le_one)).mul ht)
    have hg: Bud v (fun x:ℝ=>Real.exp (x^(v/2))):=by simpa only [one_mul] using Bud.puff (c:=1) h
    unfold F rimeCost; refine ((Bud.mul (F:=fun _=>(↑(2*κ+1:ℕ):ℝ)^(2*κ)*((2*κ:ℕ):ℝ)) (Bud.pit _ v h (by positivity)) (Bud.pow h he _)).mul ht).mul (hg.mul (Bud.pit _ v h (sq_nonneg _)))
 refine ⟨v/2,half_pos h,?_⟩; filter_upwards [(tendsto_natCast_atTop_atTop.comp Y.ir_grows.tendsto_atTop).eventually ((Bud.funded h hp).eventually (ge_mem_nhds p₁))] with m p' a v₀ -- p shadow!
 let x:= (↑(Y.ir m).val:ℝ); let N:= (↑(Journey.side Y m (s+a)).val:ℝ); let r:= price_leg Λ s a; let η:= Real.exp (-x^v); let Q:=gentle Y v m (s+a); have he:η ≤ 1:= (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (by unfold x; positivity)); have he':0≤ η:=Real.exp_nonneg _; have hN:0≤ N:=by unfold N; positivity
 let L':ℝ:= Λ.R.L.val; have ht: N*r^2 ≤ W x:=by
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤ r from (by unfold r price_leg; positivity)) (hG m s a v₀) 2) hN).trans_eq ?_
    change N*( (Real.sqrt L')⁻¹^a * y x)^2 = _; unfold N; rw [size_t (Y:=Y)]; have hv: ((Real.sqrt L')⁻¹^a)^ (2:ℕ) = (L'⁻¹)^a := by rw [pow_right_comm,inv_pow,Real.sq_sqrt (by positivity)];
    rw [mul_pow,hv]; unfold W y; unfold x L'; rw [inv_pow, mul_assoc _ _ ((↑(Λ.R.L.val):ℝ)^a), mul_assoc (resist Λ s)]; field_simp -- tune
 let D:= Real.exp (x^(v/2)); let D₀:= Real.exp (-x^v)* rimeCost κ (1+(C+1)*W x)*W x
 change rimeCost κ (1+(C*N+Q)*r^2)*(Q*r^2)*c^2 ≤ ε*Real.exp (-(x^(v/2))); rw [Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]; refine le_trans ?_ (show η * F x≤ ε from p')
 have hv:Q ≤ N:= (mul_le_mul_of_nonneg_left he hN).trans_eq (mul_one _)
 have hx: rimeCost κ (1+(C*N+Q)*r^2) ≤ rimeCost κ (1+(C+1)*W x):=by
    unfold rimeCost; apply mul_le_mul_of_nonneg_left _ (by positivity); refine pow_le_pow_left₀ (by unfold r Q gentle; positivity) ?_ _; apply add_le_add_right; refine (mul_le_mul_of_nonneg_right (add_le_add_right hv _) (sq_nonneg _)).trans ?_
    rw [show C*N+N=(C+1)*N from (by ring),mul_assoc]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
 let U:=rimeCost κ (1+(C+1)*W x); let Z':= rimeCost κ (1+(C*N+Q)*r^2);
 have hZ:0 ≤ Z':=by unfold Z' Q r gentle rimeCost; positivity
 have hq: Q*r^2 ≤ η*W x:=by change N*η*_≤_; rw [mul_comm N η,mul_assoc]; exact mul_le_mul_of_nonneg_left ht he'
 exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul hx hq (by unfold Q gentle; positivity) (hZ.trans hx)) (sq_nonneg _)) (Real.exp_nonneg _)).trans_eq (by unfold F η; ring) -- tune
#print axioms booked_charge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
