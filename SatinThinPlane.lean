import SatinThinMill
import SatinThinPool
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
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "κ"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
local notation "B"=> P.basePlay x f r
local notation "K" f:max r:max=> P.megaK f r
local notation "W'" => P.tallWorth r
local notation "q!" i:max s:max=> P.runP f r i s
local notation "p!" i:max s:max=> P.meshPose r (q! i s)
local notation "O"=> P.charmF
local notation "oQ"=> opposeQ 3
local notation "oR"=> opposeR 3
open Regis.Circuit SatinJets
local notation "r!" f:max r:max=> ((P.rewardK f r):ℝ)
local notation "Cσ"=> Yoke.canonWeight
local notation "H!" i:max b:max=> P.strollQ x f r i b
local notation "Hu" i:max b:max=> P.strollV x f r i b
/-! # Purchase & projection simultaneously on exactly elected R-m&parting. 
-/
local notation "Φ"=> P.Spectrum0 3
local notation "χ"=> P.pillars 3
local notation "cwd" f:max=> slotFee P.par f

local notation "Tier"=> ℕ × ℕ
/-! # Pull a persistent campaign to all of countable future calendar. -/
variable {l:List Axis}
local notation "Q'" s:max l:max => P.rootSpace f s l -- f fixed
/-- always exist -/
structure ForecastCard(P:Spine)(f r:ℕ)(j:Axis)(l:List Axis)(e:ℝ) where
 stage:ℕ
 up:f ≤ stage
 down:r ≤ stage
 doorway:P.pinTime j f stage l< e
 bill:P.repeatBill (twiceT (P.rootSpace f stage l) j) stage
 book:0 < slotFee P.par stage
noncomputable abbrev pedal_ξ (j:Axis){e:ℝ}(V:ForecastCard P f r j l e) : Pedal P f:= ⟨j,(V.stage,V.stage+1),P.rootSpace f (V.stage) l,V.bill,V.up,P.rent_honors j f (V.stage) l,lt_add_one _,V.book⟩ -- namespace
lemma forever_quote (f r:ℕ)(l:List Axis)(e:ℝ)(e0:0<e) : Nonempty (ForecastCard P f r j l e):=by
 obtain ⟨s,v,h,p,u,t,y⟩:= ((eventually_ge_atTop f).and ((eventually_ge_atTop r).and (((P.pin_approach j f l).eventually (gt_mem_nhds e0)).and ((P.offers_plans j 1 zero_lt_one).and ((P.earns_newsprint j 1 zero_lt_one).and P.size_honors))))).exists
 exact ⟨s,v,h,p,u.1 _ (t f l), y.1⟩ -- Nonempty?
-- elementary navy
variable {e A b C:ℝ}
variable (V:ForecastCard P f r j l e)
local notation "Sᵗ"=> V.stage
local notation "Dᵗ"=> P.pedal_ξ j V
local notation "Cᵗ"=> P.rootSpace f (V.stage) l
local notation "pᵗ"=> P.rent_honors j f (V.stage) l
local notation "■" u:max=> P.quoteRay j x V.stage u (P.rootSpace f (V.stage) l) (P.rent_honors j f (V.stage) l)
abbrev quotaSize (A:ℝ) (n:ℕ) := navy n * P.lensForm A V.stage
noncomputable abbrev cardPrice (A:ℝ)(n:ℕ):ℝ:= 2*(4*zoomC P.par.R.L^(V.stage+1-r))*(‖■ (V.stage+1)‖+ P.quotaSize j V A n/ zoomM P.par.R.L^((V.stage+1)-V.stage))
-- comparable requests
include V
lemma account_due (q:f < r)(p: Odd P.par.R.L.val)(n:ℕ)(A C:ℝ): ∀ᶠ v:ℕ in atTop,∀ (a: Tier→ℝ) {c:ℕ→Tier→ℝ}{w:ℕ→ℕ}, Workforce A C f v P c a w→ P.reachP x (Dᵗ) v a A ≤ navy n→ ‖(a (f,r):ℂ) • P.beamWatch j x f v l e‖ ≤ P.cardPrice j x V A n:=by
 filter_upwards [P.quote_time j l V.up V.doorway p,eventually_ge_atTop (V.stage+1)] with v H₀ y a c w t h; obtain ⟨v',X,hx,e',d⟩:=H₀; let Z:= P.quotaSize j V A n; have hN:0≤ Z:=by exact mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (lensBasis _|>.le) V.book.le)
 have hz:0 ≤ 4* zoomC P.par.R.L^(V.stage+1-r):=mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans (zoomC_p _)) _)
 have hr:= V.down.trans (Nat.le_add_right V.stage 1); have hv':=(show chargeSpan f v (f,r) from ⟨le_rfl,q,hr.trans y⟩); have hb:= (show chargeSpan f v (Dᵗ).s from ⟨(Dᵗ).grows, (Dᵗ).depth,y⟩)
 exact P.cap_travel j x (Cᵗ) (pᵗ) l X hx e e'.le d y (Nat.le_succ _) (a (f,r)) (a (Dᵗ).s) _ hz (t.career (f,r) (Dᵗ).s hv' hb hr) hN (P.charge_p x Dᵗ v a A y n h) -- V.stage+1 syntax F card shadow
omit V
-- campaign earned at every index WHILE preparing root rank.
structure AtMile (P:Spine)(A C:ℝ)(f r:ℕ)(x:P.Spectrum0 3)(b:ℝ)(u:ℕ→ℕ)(a:ℕ→Tier→ℝ) (R:ℕ→Pedal P f):Prop where
 fast:StrictMono u
 up:∀ i, r ≤ u i
 cruise:∀ i,∃ c w, Workforce A C f (u i) P c (a i) w
 price:P.lantern x f r ≤ min7/4
 main:∀ i, dist (P.invoiceV x f r (u i) (a i (f,r):ℂ)) (P.invoiceV x f r r 1) ≤ b/16
 extra:∀ n:ℕ,∀ᶠ i:ℕ in atTop,P.reachP x (R n) (u i) (a i) A ≤ navy n
variable (G₀:P.NightCop)(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)(F₀:f<r)(P0:∀ v:ℕ,r ≤ v→∃ c a w, Workforce A C f v P c a w)(Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(u:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ b/16)
include G₀ Book F₀ P0 Q0 u S D Z0
lemma appearance (Rv:ℕ→Pedal P f)(D₀:P.Spectrum0 3→Prop)(p0:∀ᵐ x∂χ,D₀ x) :∃ (x:Φ), D₀ x ∧ ∃ v a, AtMile P A C f r x b v a Rv:=by
 let v(i:ℕ):= r+i; have hv(i): r ≤ v i:= Nat.le_add_right r i; choose c a w t using fun i=> P0 (v i) (hv i); let yS: Pedal P f:=⟨3,(f,r),P.baseRoot f,Book,le_rfl,P.lent_anchor f,F₀,S⟩
 let s:= P.lensForm A f; let m₀:= min7 /4; let c':=s^2; let g(i:ℕ)(x:Φ):= P.lantern x f r /m₀; let h(i:ℕ)(x:Φ):= P.reachP x yS (v i) (a i) A; let k(i n:ℕ)(x:Φ):=P.reachP x (Rv n) (v i) (a i) A
 have hcc:0<c':=pow_pos (mul_pos (lensBasis _) S) _; have hmn:0 < m₀:=div_pos min_positive (by norm_num); have ht(i): (∫ x:Φ, g i x ∂χ)≤ 1/4:=by unfold g; rw [integral_div]; exact ((div_le_iff₀ hmn).2 (Q0.trans_eq (show m₀/4=(1/4)*m₀ by ring)))
 obtain ⟨x,p,q⟩:=P.budgetFor g h k (fun i=> (P.lantern_cont ..).div_const _) (fun i=> P.reach_cont ..) (fun i n=> P.reach_cont ..) (fun i x=> div_nonneg ( (show 0≤ P.glareF f r 1 1 0 x from norm_nonneg _).trans (P.lantern_available x f r).1) hmn.le) (fun i x=>P.reach_zero ..) (fun i n x=> P.reach_zero ..) ht (fun i=>P.reach_window yS (v i) (a i) (t i) G₀) (fun i n=> P.reach_window (Rv n) (v i) (a i) (t i) G₀) p0
 obtain ⟨k₀,g0,x0⟩:= extraction_of_frequently_atTop q; refine ⟨x,p,v∘k₀,a∘k₀, ( (show StrictMono v from fun i l u=> by unfold v; omega).comp g0), fun i=>hv _, fun i=> ⟨_,_,t (k₀ i)⟩,(div_le_one hmn).1 ((x0 0).1),fun i=>?_,fun n=>(g0.tendsto_atTop.eventually (eventually_gt_atTop n)).mono fun i y=>(x0 i).2.2 n y⟩
 have he:= (x0 i).2.1; let j:= k₀ i; let v₁:= v j; unfold h reachP at he; rw [dif_pos (show (yS.s.2) ≤ v (k₀ i) from hv ..)] at he
 let C':= a j; have he' := (div_le_one hcc).mp he; unfold reachF at he'; change ‖P.stateVox 3 (P.advocate 3 x 3) v₁ (P.cameo 3 (P.baseRoot f) (C' (f,r)) F₀.le (hv j) (P.lent_anchor f))‖^2≤ c' at he'; rw [P.price_caps x] at he'; exact le_trans (P.compare_distance x (hv j) F₀.le _ (lensValue A) (lensBasis A) D u he' S) Z0
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.account_due
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.appearance
