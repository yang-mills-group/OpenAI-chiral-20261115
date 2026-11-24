import YM.SU5.Assay.Medal
import YM.SU5.Assay.Belt
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
open Ballad Glaze
variable {P}
local notation "𝔏"=>Lead.Clan
local notation "τ"=>P.tock
local notation "δ"=>P.macroStep
/-! Certificate of the purchasing chamber in the spare room. All tags fit at one rate.
 For x-compatible costs take e.g. the four axis advocates of that very x; such purchase
 doesn't require any other trajectory or voter. -/
abbrev Court (P:Spine):= (j:Axis) × P.Spectrum0 j
abbrev Menagerie (P:Spine):= (Z:𝔏) → P.Medal Z
lemma Menagerie.available {r:P.Register}{w:Supplier}{u v:ℝ}(h:uniform P r w u v)(q:Tasting.Paid P.par):Nonempty (P.Menagerie):=⟨fun Z=>(Medal.available h q Z).some⟩

variable (P)(A:ℕ→P.Glaze)
local notation "β"=>P.rawBase j x
local notation "η"=>P.rawUnit j x
local notation "D" s:max=>Glaze.serial A s
def Notches :Prop:= ∀ a>0,∃C≥0,∀ᶠ s in atTop,‖β (D s) a a‖≤C
variable {P j x A}
lemma RawNormal.notches {g:ℕ→P.VMark}{p:Vantage}{T:P.RawLag j x}(w:P.RawNormal j x (serial A) g p T):P.Notches j x A:=by
 intro a h
 let c:=‖T a a‖+1
 refine ⟨c,by positivity,(((w.showAt a h a h).norm).eventually (gt_mem_nhds (lt_add_one _))).mono (fun i v=>?_ )⟩
 rw [←P.charter_cost j x (g i)]
 exact v.le
lemma Notches.bright {Z:𝔏}{a:ℝ}(e:P.Notches j x A)(p:0<a)(m:P.Medal Z):
   ∀ᶠ s in atTop, Real.exp ‖β (D s) a a‖ * ‖β (D s) a a‖*‖β (m.bright.apron s) a a-η a a‖≤a:=by
 obtain ⟨c,u,w⟩:=e _ p
 have h:= tendsto_iff_norm_sub_tendsto_zero.mp ((Medal.gained x m).showAt a p a p)
 have ht:= h.const_mul (Real.exp c*c)
 rw [mul_zero] at ht
 filter_upwards [w,ht.eventually (gt_mem_nhds p)] with s v y
 unfold align at y; rw [P.charter_zero] at y
 exact (mul_le_mul_of_nonneg_right (mul_le_mul (Real.exp_le_exp.mpr v) v (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)).trans y.le

variable (P) in
def Clutch (I:Set P.Court)(A:ℕ→P.Glaze):Prop:=Tiny A ∧ ∀ a>0,∃C≥0,∀ᶠ s in atTop,∀i:P.Court,i∈I→
  ‖P.rawBase i.1 i.2 (Glaze.serial A s) a a‖≤C
-- Super-algebraic tolerance in any positive billed width no smaller than lag r.
def prismGap (a:ℝ):ℝ:=a*Real.exp (-(a⁻¹))
lemma prismGap_pos {a:ℝ}(p:0<a):0<prismGap a:=mul_pos p (Real.exp_pos _)
lemma prismGap_mono {a b:ℝ}(p:0<a)(h:a≤b):prismGap a≤prismGap b:=mul_le_mul h (Real.exp_le_exp.mpr (neg_le_neg (inv_anti₀ p h))) (Real.exp_pos _).le (p.le.trans h)
lemma prismGap_le {a:ℝ}(p:0<a):prismGap a ≤a:= mul_le_of_le_one_right p.le (by rw [←Real.exp_zero,Real.exp_le_exp];exact neg_nonpos.mpr (by positivity))

-- Check stage s at level m; m=0 default.
variable (P) in
def Punch (I:Set P.Court)(M:P.Menagerie)(A:ℕ→P.Glaze)(s:ℕ)(r:ℝ):Prop:=
  τ s (A s).w≤r ∧
  ∀Z:𝔏, τ s (M Z).bright.w≤r ∧
   ∀ i:P.Court,i∈I→
   Real.exp ‖P.rawBase i.1 i.2 (Glaze.serial A s) r r‖ * ‖P.rawBase i.1 i.2 (Glaze.serial A s) r r‖ *
     ‖P.rawBase i.1 i.2 ((M Z).bright.apron s) r r - P.rawUnit i.1 i.2 r r‖≤prismGap r

variable (M:P.Menagerie){I:Set P.Court}
lemma Clutch.specialize {I J:Set P.Court}(h:P.Clutch I A)(p:J⊆I):P.Clutch J A:=by
 refine ⟨h.1, fun a w=>?_⟩
 obtain ⟨c,t,v⟩:=h.2 a w
 exact ⟨c,t,v.mono fun s r i y=>r i (p y)⟩
lemma Clutch.finite {I:Set P.Court}(p:Tiny A)(q:I.Finite)(h:∀ i∈I,P.Notches i.1 i.2 A):P.Clutch I A:=by
 classical
 letI := q.fintype
 refine ⟨p,fun a w=>?_⟩
 choose c t v using fun i:I=>h i i.2 a w
 refine ⟨∑i,c i,sum_nonneg (fun i _=>t i),?_⟩
 filter_upwards [eventually_all.mpr v] with s u
 intro i r
 let j:I:=⟨i,r⟩
 exact (u j).trans (Finset.single_le_sum (f:=c) (fun i _=>t i) (Finset.mem_univ j))
lemma Clutch.ready (h:P.Clutch I A){a:ℝ}(u:0<a):∀ᶠ s in atTop,P.Punch I M A s a:=by
 refine (h.1.early u).and ?_ 
 apply eventually_all.mpr
 intro Z
 refine (P.tock_small _ u).and ?_
 obtain ⟨c,t,v⟩:=h.2 _ u
 have g:=Real.exp_pos c
 let d:=Real.exp c*c+1
 have w:0<d:=by positivity
 filter_upwards [(M Z).simultaneously u u (div_pos (prismGap_pos u) w),v] with s e b
 intro i r
 specialize b i r
 have u':=(mul_le_mul (Real.exp_le_exp.mpr b) b (norm_nonneg _) g.le).trans (le_add_of_nonneg_right zero_le_one)
 exact (mul_le_mul_of_nonneg_right u' (norm_nonneg _)).trans ((lt_div_iff₀' w).mp (e i.1 i.2)).le

-- target lags are 1/(1+m)
def slat (m:ℕ):ℝ:=((m:ℝ)+1)⁻¹
lemma slat_limit:Tendsto slat atTop (𝓝 0):=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (1:ℝ) tendsto_natCast_atTop_atTop)
lemma slat_pos (m:ℕ):0<slat m:=by unfold slat; positivity
variable (P I A)
-- Decide all checks 0..s. These are formulae with norms on *actual* stage s in selected Hilberts,
-- not claiming computability or algorithmic rigor for evaluating the certificate.
def punched (s:ℕ):Finset ℕ:= (range (s+1)).filter (fun m=>m=0∨P.Punch I M A s (slat m))

local notation "Υ"=> P.punched A M I
lemma plugged(s:ℕ): (Υ s).Nonempty:=by refine ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),Or.inl rfl⟩⟩
def needle (s:ℕ):ℕ:=(Υ s).max' (P.plugged A M I s)
local notation "k"=> P.needle A M I
def scrap (s:ℕ):ℝ:=slat (k s)
variable {P I A}
lemma Clutch.ace (h:P.Clutch I A):Tendsto (k) atTop atTop:=by
 rw [Filter.tendsto_atTop];intro b
 filter_upwards [h.ready M (slat_pos b),eventually_ge_atTop b] with s v p
 exact (Υ s).le_max' b (mem_filter.mpr ⟨mem_range.mpr (by omega),Or.inr v⟩)
lemma Clutch.punches (h:P.Clutch I A):∀ᶠ s in atTop, P.Punch I M A s (P.scrap A M I s):=by
 filter_upwards [(h.ace M).eventually_ge_atTop 1] with s u
 have y:=(mem_filter.mp ((Υ s).max'_mem (P.plugged A M I s))).2
 change k s=0∨_ at y
 exact y.resolve_left (by omega)
lemma Clutch.scraps (h:P.Clutch I A): Tendsto (P.scrap A M I) atTop (𝓝 0):=slat_limit.comp (h.ace M)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
