import YM.SU5.Same.TemperWarrant
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
/-! # Geometric estimate for fixed apparatus quote norm cost, on full set of characters.
    See the construction notes. Window s+1, ordering reflected first. -/
local notation "θ" => hat P.par.R.L P.par.x
local notation "p∞" => P.pillars 3
local notation "T⋆" => P.visitLedger
local notation "B₁" j:max X:max => twinTrip (opposeQ j X) X
local notation "T₁" j:max s:max f:max l:max => twinTrip (opposeQ j (P.windowCenter s f l)) (P.windowCenter s f l)

abbrev sillNote (f s:ℕ)(l:List Axis): P.naturalVox j (s+1):= P.quoteBill j s (s+1) (P.rootSpace f s l) (P.rent_honors j f s l)

abbrev sillView (f s:ℕ)(l:List Axis)(x:P.Spectrum0 3):= P.quoteRay j x s (s+1) (P.rootSpace f s l) (P.rent_honors j f s l)
lemma sill_norm (f s:ℕ)(l:List Axis)(x:P.Spectrum0 3) : ‖P.sillView j f s l x‖=‖P.stateVox j (P.advocate 3 x j) (s+1) (P.sillNote j f s l).val‖:=by
 rw [← P.coincides j (P.advocate 3 x j),LinearIsometry.norm_map]
abbrev sillSquared (f s:ℕ)(l:List Axis)(x:P.Spectrum0 3):= ‖P.sillView j f s l x‖^2
lemma continuous_sillSquared (f s:ℕ)(l:List Axis) : Continuous (P.sillSquared j f s l):=by
 have he:P.sillSquared j f s l=(fun x=>‖P.stateVox j (P.advocate 3 x j) (s+1) (P.sillNote j f s l).val‖^2):=funext fun x=> congrArg (fun t:ℝ=>t^2) (P.sill_norm ..)
 rw [he]; exact (P.state_cont_cost _ _).comp (P.otherSpectrum 3 j).continuous
lemma avg_sillSquared (f s:ℕ)(l:List Axis): (∫ x, P.sillSquared j f s l x ∂p∞)= ‖P.piece j (s+1) (P.sillNote j f s l).val‖^2:=by
 simp_rw [sillSquared,P.sill_norm]; exact P.heartfelt_q ..
lemma cost_reflected (s:ℕ)(V:Cover) : P.eReadL s (P.reflectTest j (P.visitOne s V) * (P.visitOne s V))= (P.tallWorth s:ℂ)^2 * P.eReadL s (T⋆ z' (B₁ j V) s):=by
 rw [P.reflect_visit,P.visit_unit_pair]; let W₁:= opposeQ j V; unfold visitOne; rw [smul_mul_assoc, mul_smul_comm, map_smul,map_smul]; simp only [smul_eq_mul]; ring
lemma eval_note_sill (f s:ℕ)(l:List Axis):
 (↑(‖P.piece j (s+1) (P.sillNote j f s l).val‖^2):ℂ)=(P.tallWorth (s+1):ℂ)^2 * P.eReadL (s+1) (P.visitLedger witnessZ (T₁ j s f l) (s+1)):= by
 rw [Complex.ofReal_pow,← show inner ℂ (P.piece j (s+1) (P.sillNote j f s l).val) (P.piece j (s+1) (P.sillNote j f s l).val)=((‖P.piece j (s+1) (P.sillNote j f s l).val‖:ℝ):ℂ)^2 from inner_self_eq_norm_sq_to_K _, P.seed_pairing]
 exact P.cost_reflected j (s+1) (P.windowCenter s f l) -- argument implicit s?
open Regis.Head.Brecht
local notation "D" => 1+Yoke.pairedN (P:=P.par) witnessZ
variable {C:ℝ} (Ξ:∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k→ Yoke.ShelterCost C P.run s i k)
include Ξ
lemma next_cost_le (f:ℕ)(l:List Axis): ∀ᶠ s:ℕ in atTop, ‖P.eReadL (s+1) (P.visitLedger witnessZ (T₁ j s f l) (s+1))‖ ≤ D:=by
 let A:ℝ:=20
 let g:=trek (I:=Bool) P.run witnessZ P.large P.law Ξ (v:=0) (A:=A) (by unfold A; norm_num) le_rfl (P.tollP 2 (by norm_num)) -- check trek ambiguous
 filter_upwards [(show Tendsto (fun n:ℕ=>n+1) atTop atTop from tendsto_add_atTop_nat 1).eventually g,P.covered_window j f l] with s p t
 let U₁:= T₁ j s f l
 let k:= scout P.par 2 (s+1)
 obtain ⟨W₁,u,v,h⟩:= tile_budget U₁ k t
 have he: Lamour.Bridge.Celeste.breadth 0 W₁*2 ≤ P.debt_length k k:=v.trans (by unfold debt_length; omega)
 let L₁:= P.visitLedger witnessZ U₁ (s+1); let c:= P.parish z' U₁ (s+1) A
 have ht: ‖P.eReadL (s+1) L₁ - (c:ℂ)‖≤1:=by
    have hf := p U₁ W₁ u he h; rw [neg_zero, show trailℓ 0 (hat P.par.R.L P.par.x _)=(1:ℝ) from coin_zero _] at hf; exact hf
 have hx: ‖(c:ℂ)‖ ≤ Yoke.pairedN (P:=P.par) witnessZ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; apply lift_priceΩ P.run z' P.large A P.law
 exact (norm_le_norm_sub_add (P.eReadL (s+1) L₁) (c:ℂ)).trans (add_le_add ht hx)

lemma averaged_note (f:ℕ)(l:List Axis) : ∀ᶠ s:ℕ in atTop,(∫ x, P.sillSquared j f s l x ∂(P.pillars 3)) ≤ D:=by
 let h:Tendsto (fun i:ℕ=> i+1) atTop atTop:=tendsto_add_atTop_nat 1
 filter_upwards [h.eventually P.reward_positive,h.eventually P.tall_units,P.next_cost_le j Ξ f l] with s p q t
 let L₁:= P.piece j (s+1) (P.sillNote j f s l).val
 have he: ‖L₁‖^2 = ‖(P.tallWorth (s+1):ℂ)‖^2 * ‖P.eReadL (s+1) (P.visitLedger witnessZ (T₁ j s f l) (s+1))‖:=by
    rw [← norm_pow, ← norm_mul, ← P.eval_note_sill,Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
 rw [P.avg_sillSquared,he]; apply le_trans ?_ t; refine mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ?_); rw [Complex.norm_real,Real.norm_of_nonneg (show 0< P.tallWorth (s+1) from p.1).le]; exact q
omit Ξ
-- Borel-Cantelli for the very same character chosen later. orientation j from 3.
def FullSills (x:P.Spectrum0 3): Prop:=∀ (j:Axis)(f:ℕ)(l:List Axis), ∀ᶠ s:ℕ in atTop, ‖P.sillView j f s l x‖ ≤ 2^s
-- usable on any part of this course choosing each Character but keep same one.
include Ξ
lemma sill_tend_measure (f:ℕ)(l:List Axis) : ∀ᵐ x∂(P.pillars 3), ∀ᶠ s:ℕ in atTop, ‖P.sillView j f s l x‖ ≤ 2^s:=by
 let K:= P.pillars 3
 let v(s:ℕ):ℝ:=2^s; have hv(s): 0≤v s:=by unfold v; positivity
 have hv'(s:ℕ): 0<v s:=by unfold v; positivity
 let S₁(n):= {x:P.Spectrum0 3| v n ^2 ≤ P.sillSquared j f n l x}
 have he: Summable (fun n:ℕ=>K.real (S₁ n)):=by
    let b:ℝ:=4
    have hb : Summable (fun n:ℕ=> (D)*(1/4:ℝ)^n):= (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (D)
    refine Summable.of_norm_bounded_eventually_nat hb ?_; filter_upwards [P.averaged_note j Ξ f l] with n p
    let g:= P.sillSquared j f n l; have h0: Integrable g K:= (P.continuous_sillSquared ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [Real.norm_of_nonneg (show 0≤K.real (S₁ n) from ENNReal.toReal_nonneg)]; refine le_trans ((le_div_iff₀ (pow_pos (hv' n) 2)).2 (?_ : K.real (S₁ n)*v n^2 ≤ D)) ?_
    · rw [mul_comm]; exact (mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun i=> (show 0≤g i from sq_nonneg _)) h0 _).trans p
    rw [show (v n)^2= (4:ℝ)^n from ?_,div_eq_mul_inv,div_pow,one_pow,one_div]; unfold v; rw [← pow_mul,Nat.mul_comm n 2,pow_mul]; norm_num
 have ht: ∀ n:ℕ, ENNReal.ofReal (K.real (S₁ n)) = K (S₁ n):= fun _=> ENNReal.ofReal_toReal (measure_ne_top K _)
 have h:(∑' n, K (S₁ n))≠⊤:=by simp_rw [← ht,← ENNReal.ofReal_tsum_of_nonneg (fun n=> (show 0≤K.real (S₁ n) from ENNReal.toReal_nonneg)) he]; exact ENNReal.ofReal_ne_top
 exact (ae_eventually_notMem h).mono fun x p=>p.mono fun n w=> (le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (hv n) (le_of_lt ( lt_of_not_ge (show ¬ v n^2 ≤ P.sillSquared j f n l x from w))))
lemma ae_full_sills : ∀ᵐ x∂(P.pillars 3), P.FullSills x:= by
 unfold FullSills; simp_rw [ae_all_iff]; exact fun j f l=> P.sill_tend_measure j Ξ f l
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.ae_full_sills
