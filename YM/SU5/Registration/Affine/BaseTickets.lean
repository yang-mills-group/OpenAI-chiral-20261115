import YM.SU5.Registration.Affine.BaseSpending
import YM.SU5.Registration.Rise.PitPrices
import YM.SU5.Registration.Rise.FarAnchor
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
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
open Worth Pays CF.BProof

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)

/-! # Operator at ANY heated presentation

Maps from fields at a fixed anchor into a taller stage (ruler-overlap fixed) are
in H and are contractive; can pass to ALL matter-free clock leaves in one
norm estimate. When the allowance is spent at both ends the opening line is
operator-norm priced; the screenings at nonaligned points depend on mesh, but
transfer out of mesh on MANY-F via its spatial continuity. Then get Strong Star Cauchy
on the sequence of managed granules.
-/
open Germ Alliance
open _root_.YM.SatinRegistration
variable (xY x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x j
local notation "X'"=> P.ColorHil j ξ
local notation "G"=> P.ManyF j ξ
local notation "U"=> P.truck j ξ
local notation "E"=> (P.physicalEnergy j ξ).E
local notation "S"=> P.seasons j ξ
local notation "E'" => (S).E
local notation "T'"=>timeMesh P.par
local notation "α" s:max n:max => whenly (timeMesh P.par) s n
local notation "π" => P.toStageG j ξ
variable (g h:ℕ)(l:List Axis) (a:ℕ→(ℕ×ℕ)→ℝ)(v':ℕ→ℕ)
local notation "s!"=> P.rootSpace g f l
local notation "p!" n:max=> P.quoteSpot g f l n
local notation "O" f:max=>P.rowClock j g f l
local notation "π'" n:max=> P.basePlay xY g n
local notation "D" n:max=> (P.basePlay xY g n).pivot P l
local notation "c₀"=>ℕ -- remove
local notation "z₀" v:max=> (Z f v (O f))
local notation "Z'" v:max=> P.bedCase j (P.rootSpace g f l) xY (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) v
local notation "Cκ" v:max=> (Z' v).charges ξ (P.calendarZ v f (O f) (Nat.succ_pos _))
local notation "κ" => P.cartage j ξ
local notation "ℓ₁" v:max=> ((p! v) j).toNat -- parser ℓ! not p! max!!
local notation "λκ" v:max=> (p! v)
local notation "ζ" t:max i:max=> P.tenderH j xY x g h l a v' t i
local notation "p₀" f:max r:max t:max i:max => P.approxCane j xY x g h l a v' f r t i
local notation "M" s:max=> mill (timeMesh P.par) s
local notation "D₀" s:max=> tiltBase P.par A s
local notation "C₀" v:max=> (P.bedCase j (P.rootSpace g f l) xY (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) v).charges ξ (P.calendarZ v f (O f) (Nat.succ_pos _)) -- already `Cκ`

variable (S₁:P.NightCop)(L':Odd P.par.R.L.val) (u:Earnings P A C g h v' a)
include S₁ L' u
variable (Tq:∀ᶠ s:ℕ in atTop, treasury A C P s (s+1) (s+1))
private lemma record_cane (i₀:ℕ)(p:h≤ i₀)(t:ℝ≥0)(u₀:treasury A C P i₀ (i₀+1) (i₀+1))(w:P.ColumnBill (O i₀) i₀) : ∀ᶠ i:ℕ in atTop, ‖(p₀ i₀ (i₀+1) t i)‖≤ avail (L) h (i₀+1)*(4*(3*tiltBase P.par A i₀*fareMin (L) 1)):=by
 let f:= i₀; let U':= P.rootSpace g i₀ l; let d: (P.ColorHil j (P.advocate 3 x j)).Op:= (P.bedCase j U' xY (O i₀) (P.rent_honors j g i₀ l) (Nat.le_add_right _ 1) (f+1)).charges ξ (P.calendarZ (f+1) f (O i₀) (Nat.succ_pos _))
 have ht:‖d‖≤4*(3*tiltBase P.par A i₀*fareMin (L) 1):=by
   refine (P.raw_detent j U' xY x (O i₀) (P.rent_honors j g i₀ l) (Nat.le_add_right _ 1) (Nat.succ_pos _) w S₁ u₀).trans_eq ?_ -- binder w implicit? get from solver
   rw [Nat.add_sub_cancel_left]
 filter_upwards [u.fast.tendsto_atTop.eventually_ge_atTop (i₀+1)] with i h
 have he:=u.gift (u.earlier.le.trans p) (Nat.lt_succ_self i₀) p h; unfold approxCane; rw [norm_smul, Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul he.1 ((P.pit_pay ..).trans ht) (norm_nonneg _) ((abs_nonneg _).trans he.1)

include Tq
lemma tender_ticket : ∀ᶠ k:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ‖ζ (M k) i‖≤ avail P.par.R.L h (k+k+1) * rackR P.par.R.L A:=by
 let f(k:ℕ):=k+k; let X(t:ℕ):= tiltBase P.par A t; let q:=(Real.exp (8*A+1)); let K:= zoomM P.par.R.L; let d:=fareMin P.par.R.L 1; have hd:0≤d:=by unfold d fareMin; positivity
 filter_upwards [tendsto_double_page.eventually_ge_atTop h,tendsto_double_page.eventually (P.row_paid j),P.angle_half_row j g l, tendsto_double_page.eventually Tq, tendsto_double_page.eventually P.slot_le_unit] with k p t r v a₀; let s:=f k
 let B:= avail P.par.R.L h (f k+1); have he:0≤B:=(P.fee_pos).le
 have hx: X (f k) ≤ q:= mul_le_of_le_one_left (Real.exp_pos _|>.le) a₀
 filter_upwards [P.record_cane j xY x g h l a v' S₁ L' u _ p (M k) v (t g l),P.zone_tender j xY g h l a v' S₁ L' u (f:=s) p (Nat.lt_succ_self s) (t g l) (M k) r] with i w h
 have hk:= (zoomM_p P.par.R.L).le; have hz:B*(2*(6*X s/K)) + B*(4*(3* X s*d)) ≤ B*(rackR P.par.R.L A):=by rw [←mul_add]; unfold rackR; change _ ≤ B*(2*(6*q/K)+4*(3*q*d)); gcongr
 apply (norm_le_norm_sub_add (ζ (M k) i) (p₀ s (s+1) (M k) i)).trans ((add_le_add (h x) w).trans ?_); unfold skyLoss; rw [show s.succ - s=1 from by omega, pow_one]; exact hz
lemma spending : ∃ C:ℝ, 0≤C ∧ ∃ K:ℝ, 1≤K ∧ ∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ in atTop, ‖ζ (M k) i‖ ≤ C*K^k:=by
 let k:= zoomC P.par.R.L; let c:= rackR P.par.R.L A; have he:1≤k:= zoomC_p _; have hv:0≤ c:= P.rackR_positive; have hp:0≤4*k*c:=by positivity
 refine ⟨_,hp,k*k,one_le_mul_of_one_le_of_one_le he he,(P.tender_ticket j xY x g h l a v' S₁ L' u Tq).mono fun i v=> v.mono fun q t=> t.trans ?_⟩
 refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (Nat.sub_le (i+i+1) h)) (show 0 ≤ (4:ℝ) by norm_num)) hv|>.trans_eq ?_
 rw [pow_add k (i+i), pow_one,pow_add k,mul_pow]; ring

lemma tender_power : RisePrice (P.tenderH j xY x g h l a v'):=by
 obtain ⟨K,p,D₁,q,y⟩:= P.spending j xY x g h l a v' S₁ L' u Tq
 refine P.clock_to_power _ K D₁ p q y ?_
 intro s t q' r'; filter_upwards [(P.granule_thin j xY g h l a v' u).eventually (gt_mem_nhds q')] with i p
 exact P.stage_cheaper j ξ _ (show (D (v' i)).allowance P j ≤ s from (show _<_ from p).le) r' (show (D (v' i)).allowance P j ≤ s from (show _<_ from p).le) r' _
omit S₁ L' u Tq
open Swatch
-- each fixed stamp bounded on G across the spectrum (include weight). no movement issue.
lemma fixed_cap_eng (A:P.Apron) : ∃ C≥(0:ℝ),∀ x:P.Spectrum0 j,‖A.engine P j x‖≤C:=by
 let V:= P.door j A.s (A.u j+A.u j) (add_pos (A.pos _) (A.pos _)) (A.cardB P j) (A.color P j); exact ⟨‖V‖,norm_nonneg _,fun x=> NonUnitalStarAlgHom.norm_apply_le (P.colorSpace j x) V⟩
lemma fixed_offer (A:P.Swatch)(t:ℝ≥0)(i:ℕ) : ∃ C≥(0:ℝ),∀ x:P.Spectrum0 3,‖A.Wstage x j t t i‖≤C:=by
 obtain ⟨C,v,h⟩:= P.fixed_cap_eng j (A.fieldA i)
 let x:= ‖A.rate i‖; have he:0≤x:=norm_nonneg _; refine ⟨x*C,mul_nonneg he v,fun x' =>?_⟩; unfold Wstage stageG stageH; rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((P.toG_cost ..).trans ((P.heater_norm ..).trans (h (P.advocate 3 x' j)))) he

lemma ModSpaces.funds (A:P.Swatch)(p:P.ModSpaces j A) : P.ThresholdPrice j A := by
 intro t h; obtain ⟨l,d,v₀' ,k⟩:= p.2 t h 1 zero_lt_one
 let F (i:ℕ)(x):= A.Wstage x j t t i; let X(i:ℕ)(x):= P.cane x j (F i x) (l i); let D':=fun (_:ℕ) x=> d x
 obtain ⟨N,h⟩:=eventually_atTop.mp k; obtain ⟨B,v',p⟩:= P.fixed_offer j A t N
 refine ⟨1+B+1,by linarith,?_⟩
 filter_upwards [k] with i u y
 let Y₁:= d y
 let k':=F N y; let f:=F i y; have hp:‖X N y‖ ≤ B:= (P.cane_norm ..).trans (p y)
 have ht:‖Y₁‖≤ 1+B:=by have t:dist k' k'=0:=dist_self _; refine (norm_le_norm_sub_add Y₁ (X N y)).trans (add_le_add ?_ hp); rw [←dist_eq_norm,dist_comm]; exact h N le_rfl y
 change ‖f‖≤_
 calc
  _ = ‖P.cane y j (X i y) (-(l i))‖:=by unfold X; rw [P.cane_join,neg_add_cancel,P.cane_ofZero]
  _ ≤ ‖X i y‖:= P.cane_norm ..
  _ ≤ 1+B+1 := by
    have he: dist (X i y) Y₁ ≤ 1:= u y; exact (norm_le_norm_sub_add (X i y) Y₁).trans ((add_le_add ((dist_eq_norm ..).ge.trans he) ht).trans_eq (add_comm ..)) -- seminorm stuck

noncomputable abbrev baseFlight : P.Swatch:= { fieldA := fun i=> (P.basePlay xY g (v' i)).pivot P l, rate:= fun i=> (a i (g,h):ℂ) }
local notation "Qy"=> P.baseFlight xY g h l a v'
lemma base_ride (s:ℝ≥0)(i:ℕ) : (Qy).Wstage x j s s i=π (ζ s i):= (map_smul _ _ _).symm

local notation "HΓ" x:max => P.ManyF j (P.advocate 3 x j)
include S₁ L' u
lemma base_motion (x':PaidSubsidy g h a) : P.ModSpaces j (P.baseFlight xY g h l a v'):=by
 refine ⟨fun j=> P.granule_thin j xY g h l a v' u,?_⟩
 intro t v r d; let q:=r/2; have h':0<q:=half_pos d
 -- from M6 argument (obtained AFTER fixing pad) and uniform gamma stilt-corrected comparison above
 obtain ⟨i₀,h₁,Sv,hV,hR⟩:= ((P.angle_half_row j g l).and ((tendsto_double_page.eventually (P.row_paid j)).and (((vanishes T').eventually (gt_mem_nhds v)).and (tendsto_double_page.eventually_ge_atTop h)))).exists
 let f:= i₀+i₀; have hp:h≤ f:= hR
 have hx: α f (O f)≤t:= h₁.trans (show M i₀ < t from hV).le
 obtain ⟨k,ht⟩:= ((P.sky_zero h A hp).eventually (gt_mem_nhds h')).exists; let r':= f+(k+1); have hr:f<r':= by unfold r'; omega
 let a'(i:ℕ):=(subsidy g h f r' i a:ℂ)
 obtain ⟨c,hc⟩:= cauchySeq_tendsto_of_complete (x' f r' (u.earlier.le.trans hp) hp hr);
 have hz:Tendsto a' atTop (𝓝 (c:ℂ)):= Complex.continuous_ofReal.continuousAt.tendsto.comp hc
 -- `σ` binds anchor f used implicitly across x inst; careful not capture original {f}
 let X:= fun j:Axis=>P.pinTime j g f l; let p'(i:ℕ):= P.laysM (P.vtile (v' i) (P.quoteSpot g f l (v' i))); let p(i):=p' i-X
 have hv: Tendsto p' atTop (𝓝 X) := (P.quote_moving g l (u.earlier.le.trans hp) L').comp u.fast.tendsto_atTop
 let t₀:=P.price_in_space j xY g h l a v' S₁ L' u hp hr hz t hx
 refine ⟨p,(fun γ=>P.ticketsInSpace j xY γ g l (f:=f) t r' (c:ℂ)),?_, (add_halves r) ▸ UpTo.chain ?_ (t₀ q h')⟩
 · simpa [p] using (hv.sub_const X)
 filter_upwards [P.zone_tender j xY g h l a v' S₁ L' u hp hr (Sv g l) t hx] with i u γ
 refine (P.cane_distance ..).trans ?_
 rw [P.base_ride,dist_eq_norm,←map_sub]; exact (P.toG_cost ..).trans ((u γ).trans (show skyLoss P A f r' h < q from ht).le)
include Tq
lemma base_grant (p:PaidSubsidy g h a) : P.ThresholdPrice j (Qy) ∧ P.ModSpaces j (Qy) ∧ (∀ x:P.Spectrum0 3,(P.baseFlight xY g h l a v').WPermit x j):=by
 have u':= P.base_motion j xY g h l a v' S₁ L' u p
 refine ⟨u'.funds P j (Qy),u',fun z=> ⟨u'.1,?_,fun t h=> u'.starts P z j (Qy) t h⟩⟩ -- arg order for Rated lemma! actual P x a A
 obtain ⟨k,C',e,h⟩:= P.tender_power j xY z g h l a v' S₁ L' u Tq
 refine ⟨k,C',e,fun t p q=>?_⟩; simp_rw [P.base_ride]; exact (h t p q).mono fun i t=> (mul_le_mul_of_nonneg_left (P.toG_cost ..) (by positivity)).trans t
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms base_grant
#print axioms base_motion
#print axioms tender_power
#print axioms ModSpaces.funds
