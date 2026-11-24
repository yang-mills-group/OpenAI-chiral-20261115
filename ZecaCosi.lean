import ZecaRuby
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

local notation "ξ"=> P.advocate 3 x j
local notation "EH"=>P.physicalEnergy j ξ
local notation "M"=> P.ColorHil j ξ
local notation "Ω"=> P.colorZero j ξ
local notation "Μ"=> timeMesh P.par



local notation "G"=>P.ManyF j ξ

section general
variable {T:Type*} [NormedAddCommGroup T][NormedSpace ℂ T]
lemma price_brush_general {L':Side}{s r:ℕ}{A:ℝ}
    (x y:T)(a d z h:ℝ) (B:(a:ℂ)=(d:ℂ)*(z:ℂ))
    (w:‖(d:ℂ)‖≤ h)
    (g:‖ (↑(zoomM L' ^(r-s)):ℂ) • ((z:ℂ) • x-y)‖≤A):
    dist ((a:ℂ) • x) ((d:ℂ) • y) ≤ h*A/zoomM L'^(r-s):= by
 have p:=pow_pos (zoomM_p L') (r-s)
 rw [B,←smul_smul,dist_eq_norm, ← smul_sub, norm_smul,
      le_div_iff₀ p,mul_assoc,mul_comm (‖(z:ℂ) • x-y‖)]
 have t:= norm_nonneg (d:ℂ)
 rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg p.le] at g
 exact mul_le_mul w g (mul_nonneg p.le (norm_nonneg _)) (t.trans w)
end general

def peakPrice (A:ℝ):= Real.exp (8*A+1)
lemma violet_cheaper {A C:ℝ}(h:treasury A C P s r v):
 violet P.par s A≤peakPrice A:=by
 obtain ⟨i,g,a⟩:=h.room.exists
 have y:=a.load.health
 exact mul_le_of_le_one_left (Real.exp_pos _).le
   (y.2.2.2.1.trans y.2.2.2.2)
def prismRate (c A:ℝ)(s r:ℕ):=
 orbitRent c P r * (4 * peakPrice A) / zoomM P.par.R.L^(r-s)
lemma prism_to_zero (c A:ℝ)(s:ℕ): Tendsto (fun r=> prismRate P c A s r) atTop (𝓝 0):=by
 let d:=(|c|+1)*4*zoomM L^s*(4 * peakPrice A)
 have h:Tendsto (fun r:ℕ=>d*(1/8:ℝ)^r) atTop (𝓝 0):=by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
       (by norm_num:(1:ℝ)/8<1)).const_mul d
 have t: (zoomC L) = (1/8:ℝ)*zoomM L:= by unfold zoomC zoomM; ring
 apply h.congr'
 filter_upwards [eventually_ge_atTop s] with r p
 have i:zoomM L^(r-s)*zoomM L^s=zoomM L^r:=by rw [←pow_add,Nat.sub_add_cancel p]
 unfold d prismRate orbitRent
 rw [t, mul_pow, ←i]
 exact (eq_div_iff (pow_pos (zoomM_p ..) ..).ne').mpr (by ring)
variable {c A C a b:ℝ}(l:List Axis)
   {u:ℕ→ℕ}{y:ℕ→ℕ × ℕ→ℝ}

local notation "Pad"=>P.rosePad j s
local notation "Town"=>Odessa j (P.roseRoot f s l) s (P.roseWide j s) P
local notation "χ" t:max=>P.crop j x f t l a b
local notation "δ" i:max r:max=>rateQR f k c (u i) (y i) (s,r)
local notation "α" i:max=>c*y i (f,k)
variable (p:Skyways P f k A C c u y)(e:P.NightCop)
include p e
lemma violet_bows(h:k≤ s)(O:Town)(m:Pad≤ a)(n:Pad≤ b)(t:s<r)(q:r≤u i):
    dist ((↑(c*y i (f,k):ℝ):ℂ) • χ (u i)) ((δ i r:ℂ) • χ r) ≤
       P.prismRate c A s r ∧
    ‖χ r‖ ≤4*(fareMin P.par.R.L (r-s)*peakPrice A):=by
 obtain ⟨sc,fee,z,zp,g⟩:= (p.toEngaged.wages (c:=c) h t q)
 have gap:=P.crop_buy j x l g (p.early.le.trans h) O e m n
 have gr:=P.violet_cheaper g.treasury
 constructor
 · refine price_brush_general (s:=s) (r:=r) (L':=L) (χ (u i)) (χ r)
        (α i) (δ i r) (y i (s,r)) (orbitRent c P r)
        (congrArg ((↑) : ℝ→ℂ) sc|>.trans (Complex.ofReal_mul ..))
        (by rw [Complex.norm_real,Real.norm_eq_abs];exact fee)
        (gap.2.trans (mul_le_mul_of_nonneg_left gr (by norm_num)))
 exact gap.1.trans (by
    have x': 0<(P.par.R.L.val:ℝ):=by exact_mod_cast P.par.R.L.property
    unfold fareMin
    gcongr)

omit p e in
private lemma pearl_pay {T:Type*}[MetricSpace T](z:ℕ→T)
  (h:∀ d:ℝ,0<d→∃ b':T, ∀ᶠ i in atTop, dist (z i) b' < d): CauchySeq z:=by
 apply Metric.cauchySeq_iff.mpr
 intro d hd
 obtain ⟨b',hb⟩:=h _ (half_pos hd)
 obtain ⟨i,j⟩:=eventually_atTop.mp hb -- deprecated
 refine ⟨i, fun m s n y=> lt_of_le_of_lt (dist_triangle _ b' _) ?_⟩
 rw [dist_comm b']
 exact ((add_lt_add (j _ s) (j _ y))).trans_eq (add_halves d)

lemma violet_joins(h:k≤ s)(O:Town)(m:Pad≤ a)(n:Pad≤ b):
 ∃ V,Tendsto (fun i=>(↑(c*y i (f,k):ℝ):ℂ) • χ (u i)) atTop (𝓝 V):=by
 refine cauchySeq_tendsto_of_complete (pearl_pay _ ?_)
 intro d hd
 have hg:=P.prism_to_zero c A s
 obtain ⟨r,v,t⟩:= ((eventually_gt_atTop s).and (hg.eventually (gt_mem_nhds (half_pos hd)))).exists
 have t':P.prismRate c A s r < d/2:=t
 obtain ⟨z,he⟩:=p.sold (s,r)
 have y':Tendsto (fun i=>(δ i r:ℂ) • χ r) atTop (𝓝 ((z:ℂ) • χ r)):=
     (Complex.continuous_ofReal.continuousAt.tendsto.comp he).smul_const _

 refine ⟨(z:ℂ) • χ r,?_⟩
 -- placeholder explicit
 filter_upwards [p.post.tendsto_atTop.eventually (eventually_ge_atTop r),
    Metric.tendsto_nhds.mp y' (d/2) (half_pos hd)] with i hx hs
 have hi:=P.violet_bows j x l p e h O m n v hx
 exact (dist_triangle _ ((δ i r:ℂ) • χ r) _).trans_lt
      ((add_lt_add (hi.1.trans_lt t') hs).trans_eq (add_halves d))

def scaleCosy(P:Spine)(A:ℝ):= 4*(fareMin P.par.R.L 1*peakPrice A)+
  (4*peakPrice A)/zoomM P.par.R.L
omit p e
lemma scaleCosy_p:0<scaleCosy P A:=by
 have hz:=zoomM_p L;have x': 0<(P.par.R.L.val:ℝ):=by exact_mod_cast P.par.R.L.property
 unfold scaleCosy fareMin peakPrice; positivity
include p e
lemma violet_norm (h:k≤ s)(O:Town)(m:Pad≤ a)(n:Pad≤ b)(d:s< u i):
 ‖(↑(c*y i (f,k):ℝ):ℂ) • χ (u i)‖≤ orbitRent c P (s+1)*scaleCosy P A:=by
 obtain ⟨hv,g⟩:=P.violet_bows j x l p e h O m n (show s<s+1 from Nat.lt_succ_self s) (Nat.succ_le_of_lt d)
 rw [Nat.add_sub_cancel_left] at g

 let U:=(↑(c*y i (f,k):ℝ):ℂ) • χ (u i)
 let V:=(δ i (s+1):ℂ) • χ (s+1)
 have hp:‖U‖≤‖V‖+dist U V:=by
    rw [add_comm]; simpa only [dist_eq_norm,sub_zero] using (dist_triangle U V 0)
 apply hp.trans
 unfold scaleCosy
 rw [mul_add]; refine add_le_add ?_ (hv.trans_eq ?_)
 · unfold V
   rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
   exact mul_le_mul (p.toEngaged.wages_cap) g (norm_nonneg _) (orbitRent_pos ..).le
 unfold prismRate
 rw [Nat.add_sub_cancel_left,pow_one,mul_div_assoc]


end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
