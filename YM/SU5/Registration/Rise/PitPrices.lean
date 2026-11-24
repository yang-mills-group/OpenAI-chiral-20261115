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
local notation "N" s:max i:max => Journey.side P.run i s
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
variable (x:P.Spectrum0 3)
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
local notation "π'" n:max=> P.basePlay x g n
local notation "D" n:max=> (P.basePlay x g n).pivot P l
local notation "c₀"=>ℕ -- remove
local notation "z₀" v:max=> (Z f v (O f))
local notation "Z'" v:max=> P.bedCase j (P.rootSpace g f l) x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) v
local notation "Cκ" v:max=> (Z' v).charges ξ (P.calendarZ v f (O f) (Nat.succ_pos _))
local notation "κ" => P.cartage j ξ
local notation "ℓ₁" v:max=> ((p! v) j).toNat -- parser ℓ! not p! max!!
local notation "λκ" v:max=> (p! v)
local notation "ζ" t:max i:max=> P.subsidizedH j x g h l a v' t i
local notation "p₀" f:max r:max t:max i:max => P.approxCab j x g h l a v' f r t i
local notation "M" s:max=> mill (timeMesh P.par) s
local notation "D₀" s:max=> tiltBase P.par A s
local notation "C₀" v:max=> (P.bedCase j (P.rootSpace g f l) x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) v).charges ξ (P.calendarZ v f (O f) (Nat.succ_pos _)) -- already `Cκ`

variable (S₁:P.NightCop)(L':Odd P.par.R.L.val) (u:Earnings P A C g h v' a)
lemma angle_half_row : ∀ᶠ k:ℕ in atTop, whenly T' (k+k) (O (k+k)) ≤ M k :=by
 filter_upwards [P.row_beat j zero_lt_one] with i p
 apply NNReal.coe_le_coe.mp; unfold whenly; rw [NNReal.coe_mul,NNReal.coe_natCast]; apply (p g l).le.trans (by rw [one_mul]; exact le_rfl) -- f parameter? .row_beat j
include S₁ L' u
-- no treasury_plot needed for convergence
lemma site_travels (p:PaidSubsidy g h a) (t:ℝ≥0)(q:0<t) : Travels (H:=G) (fun i=> P.toStageG j ξ (ζ t i)) :=by
 apply Flying.via; intro d y
 obtain ⟨i₀,h₁,Sv,hV,hR⟩:= ((P.angle_half_row j g l).and ((tendsto_double_page.eventually (P.row_paid j)).and (((vanishes T').eventually (gt_mem_nhds q)).and (tendsto_double_page.eventually_ge_atTop h)))).exists -- S notation conflict
 let f:= i₀+i₀; have hp:h≤ f:= hR
 have hx: α f (O f)≤t:= h₁.trans (show M i₀ < t from hV).le
 obtain ⟨k,ht⟩:= ((P.sky_zero h A hp).eventually (gt_mem_nhds y)).exists; let r:= f+(k+1); have hr:f<r:= by unfold r; omega
 let F':= P.approxCab j x g h l a v' f r t; refine ⟨fun i=> π (F' i), P.approxFlies j x g h l a v' L' u hp hr p t, ?_⟩
 filter_upwards [P.relative_pit j x g h l a v' S₁ L' u hp hr (Sv g l) t hx] with i p
 rw [←map_sub]; refine (P.toG_cost j ξ _).trans (p.trans (show P.skyLoss A f r h < d from ht).le) -- .sky_loss notation P

/- For polynomial cap, price at s+1 curvature shaft including relative cost. -/
variable (Tq:∀ᶠ s:ℕ in atTop, treasury A C P s (s+1) (s+1))
private lemma record_approx (i₀:ℕ)(p:h≤ i₀)(t:ℝ≥0)(u₀:treasury A C P i₀ (i₀+1) (i₀+1))(w:P.ColumnBill (O i₀) i₀) : ∀ᶠ i:ℕ in atTop, ‖(p₀ i₀ (i₀+1) t i)‖≤ avail (L) h (i₀+1)*(4*(3*tiltBase P.par A i₀*fareMin (L) 1)):=by
 let f:= i₀; let U':= P.rootSpace g i₀ l; let d: (P.ColorHil j (P.advocate 3 x j)).Op:= (P.bedCase j U' x (O i₀) (P.rent_honors j g i₀ l) (Nat.le_add_right _ 1) (f+1)).charges ξ (P.calendarZ (f+1) f (O i₀) (Nat.succ_pos _))
 have ht:‖d‖≤4*(3*tiltBase P.par A i₀*fareMin (L) 1):=by
   refine (P.raw_center j U' x (O i₀) (P.rent_honors j g i₀ l) (Nat.le_add_right _ 1) (Nat.succ_pos _) w S₁ u₀).trans_eq ?_ -- binder w implicit? get from solver
   rw [Nat.add_sub_cancel_left]
 filter_upwards [u.fast.tendsto_atTop.eventually_ge_atTop (i₀+1)] with i h
 have he:=u.gift (u.earlier.le.trans p) (Nat.lt_succ_self i₀) p h; unfold approxCab; rw [norm_smul, Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul he.1 ((P.pit_pay ..).trans ht) (norm_nonneg _) ((abs_nonneg _).trans he.1)

include Tq
noncomputable abbrev rackR (L'':Lattice.Side) (A:ℝ) :ℝ:=2*(6*Real.exp (8*A+1)/zoomM L'')+4*(3*Real.exp (8*A+1)*fareMin L'' 1)
omit S₁ L' u Tq in
lemma rackR_positive : 0≤ rackR (P.par.R.L) A:=by unfold rackR; have h:= zoomM_p P.par.R.L; unfold fareMin; positivity
lemma milestone_price : ∀ᶠ k:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ‖ζ (M k) i‖≤ avail P.par.R.L h (k+k+1) * rackR P.par.R.L A:=by
 let f(k:ℕ):=k+k; let X(t:ℕ):= tiltBase P.par A t; let q:=(Real.exp (8*A+1)); let K:= zoomM P.par.R.L; let d:=fareMin P.par.R.L 1; have hd:0≤d:=by unfold d fareMin; positivity
 filter_upwards [tendsto_double_page.eventually_ge_atTop h,tendsto_double_page.eventually (P.row_paid j),P.angle_half_row j g l, tendsto_double_page.eventually Tq, tendsto_double_page.eventually P.slot_le_unit] with k p t r v a₀; let s:=f k
 let B:= avail P.par.R.L h (f k+1); have he:0≤B:=(P.fee_pos).le
 have hx: X (f k) ≤ q:= mul_le_of_le_one_left (Real.exp_pos _|>.le) a₀
 filter_upwards [P.record_approx j x g h l a v' S₁ L' u _ p (M k) v (t g l),P.relative_pit j x g h l a v' S₁ L' u (f:=s) p (Nat.lt_succ_self s) (t g l) (M k) r] with i w h
 have hk:= (zoomM_p P.par.R.L).le; have hz:B*(2*(6*X s/K)) + B*(4*(3* X s*d)) ≤ B*(rackR P.par.R.L A):=by rw [←mul_add]; unfold rackR; change _ ≤ B*(2*(6*q/K)+4*(3*q*d)); gcongr
 apply (norm_le_norm_sub_add (ζ (M k) i) (p₀ s (s+1) (M k) i)).trans ((add_le_add h w).trans ?_); unfold skyLoss; rw [show s.succ - s=1 from by omega, pow_one]; exact hz
lemma buy_geometric : ∃ C:ℝ, 0≤C ∧ ∃ K:ℝ, 1≤K ∧ ∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ in atTop, ‖ζ (M k) i‖ ≤ C*K^k:=by
 let k:= zoomC P.par.R.L; let c:= rackR P.par.R.L A; have he:1≤k:= zoomC_p _; have hv:0≤ c:= P.rackR_positive; have hp:0≤4*k*c:=by positivity
 refine ⟨_,hp,k*k,one_le_mul_of_one_le_of_one_le he he,(P.milestone_price j x g h l a v' S₁ L' u Tq).mono fun i v=> v.mono fun q t=> t.trans ?_⟩
 refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (Nat.sub_le (i+i+1) h)) (show 0 ≤ (4:ℝ) by norm_num)) hv|>.trans_eq ?_
 rw [pow_add k (i+i), pow_one,pow_add k,mul_pow]; ring

-- retain named polynomial norm estimate at fixed t. need at t for any all stamps. reusable generic lemma using geometric and eventually antitonic, adapt from `TemperGalaxy`
omit S₁ L' u Tq
private lemma book_small_t (s:ℕ)(e:ℝ)(u:0<e)(t:e≤P.macroStep s): ∃ k:ℕ, s ≤ k ∧ P.macroStep k ≤ e ∧ e ≤ (P.par.R.L.val:ℝ)* P.macroStep k:=by
 obtain ⟨n,h,p⟩:= ((eventually_ge_atTop s).and (P.macroStep_zero.eventually (gt_mem_nhds u))).exists
 have he: ∃ d:ℕ, P.macroStep (s+d) ≤ e:= ⟨n-s,by rw [Nat.add_sub_of_le h]; exact (show _<_ from p).le⟩
 let a:= Nat.find he
 have hp:P.macroStep (s+a) ≤ e:= Nat.find_spec he
 refine ⟨s+a,Nat.le_add_right ..,hp,?_⟩
 by_cases b:a=0
 · rw [b, add_zero]; exact t.trans (le_mul_of_one_le_left (P.macroStep_pos s|>.le) (le_of_lt (by exact_mod_cast ((timeMesh P.par).Llarge))))
 obtain ⟨y,hy⟩:=Nat.exists_eq_succ_of_ne_zero b
 have hb:y < Nat.find he:=show y<a from by rw [hy]; omega
 have ht:e< P.macroStep (s+y):=lt_of_not_ge (Nat.find_min he hb)
 rw [hy, show s+y.succ=s+y+1 by omega]; exact ht.le.trans_eq ((show (P.par.R.L.val:ℝ)*P.macroStep (s+y+1)=P.macroStep (s+y) by simpa only [Nat.add_sub_cancel_left,pow_one] using P.daysF (s+y+1) (s+y) (Nat.le_succ _)).symm)


abbrev RisePrice {H₁:Type*}[Norm H₁] (F:ℝ≥0 → ℕ→ H₁) : Prop:=∃ k:ℕ,∃ C≥ (0:ℝ), ∀ t:ℝ≥0,0<t→t≤1→∀ᶠ i:ℕ in atTop,(t:ℝ)^k *‖F t i‖≤C
local notation "Lℝ"=> (P.par.R.L.val:ℝ)
-- geometric to RisePrice. threshold depends on t.
lemma clock_to_power {H₁:Type*}[SeminormedAddCommGroup H₁] (Y':ℝ≥0→ℕ→H₁) (K B₀:ℝ)(p:0≤K)(q:1≤B₀)
 (d:∀ᶠ n:ℕ in atTop,∀ᶠ i:ℕ in atTop, ‖Y' (mill (timeMesh P.par) n) i‖≤ K*B₀^n) (e:∀ s t:ℝ≥0, 0<s→s≤t→∀ᶠ i:ℕ in atTop, ‖Y' t i‖≤‖Y' s i‖): RisePrice Y':=by
 obtain ⟨s,v⟩:=eventually_atTop.mp d; have he:1<Lℝ:= by exact_mod_cast (timeMesh P.par).Llarge
 let a:=P.macroStep 0
 obtain ⟨m,u'⟩:= ((tendsto_pow_atTop_atTop_of_one_lt he).eventually_ge_atTop B₀).exists
 let B₁:ℝ≥0:= M s; let c₁:= K*(Lℝ*a)^m; let C':=K*B₀^s
 have hp:0≤c₁:=mul_nonneg p (pow_nonneg (mul_nonneg (zero_le_one.trans he.le) (P.macroStep_pos _|>.le)) _)
 refine ⟨m,max c₁ C',hp.trans (le_max_left ..),fun t z r=>?_⟩; rcases le_or_gt t B₁ with ht|hv
 · obtain ⟨k,hk,f,y⟩:= P.book_small_t s (t:ℝ) z ht
   let L':ℝ:=P.macroStep k; have hL:0 < L':=P.macroStep_pos k
   have hv: (Lℝ*L')^m * (Lℝ^m)^k=(Lℝ*a)^m:=by
      have hf: L'*Lℝ^k=a:=by rw [mul_comm]; simpa only [Nat.sub_zero] using P.daysF k 0 (Nat.zero_le k)
      rw [←pow_mul, Nat.mul_comm m k,pow_mul,← mul_pow,mul_assoc,hf]
   filter_upwards [e (M k) t hL f, v _ hk] with i w T
   refine le_trans (mul_le_mul (pow_le_pow_left₀ (show (0:ℝ)≤(t:ℝ) from z.le) y m)
                  (w.trans (T.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans q) (show B₀≤ Lℝ^m from u') _) p))) (norm_nonneg _) (pow_nonneg (by positivity) _)) ?_
   change (Lℝ*L')^m*(K*(Lℝ^m)^k) ≤ _; rw [mul_left_comm,hv]; exact le_max_left ..
 filter_upwards [v s le_rfl,e B₁ t (mill_pos ..) hv.le] with i u v; exact le_trans ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (show (0:ℝ)≤(t:ℝ) from z.le) (show (t:ℝ)≤1 from r))).trans (v.trans u)) (le_max_right ..)

include u in
lemma granule_thin : Tendsto (fun i=> ((P.basePlay x g (v' i)).pivot P l).allowance P j) atTop (𝓝 0):=by
 simp_rw [P.allowance_pivot]; unfold whenly; simpa only [mul_zero, Function.comp_def] using ((vanishes T').comp u.fast.tendsto_atTop|>.const_mul (P.roomy:ℝ≥0))
include S₁ L' u Tq
lemma granule_rise_price : RisePrice (P.subsidizedH j x g h l a v'):=by
 obtain ⟨K,p,D₁,q,y⟩:= P.buy_geometric j x g h l a v' S₁ L' u Tq
 refine P.clock_to_power _ K D₁ p q y ?_
 intro s t q' r'; filter_upwards [(P.granule_thin j x g h l a v' u).eventually (gt_mem_nhds q')] with i p
 exact P.stage_cheaper j ξ _ (show (D (v' i)).allowance P j ≤ s from (show _<_ from p).le) r' (show (D (v' i)).allowance P j ≤ s from (show _<_ from p).le) r' _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.site_travels
#print axioms Spine.granule_rise_price
