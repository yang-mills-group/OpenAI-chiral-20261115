import YM.SU5.LoomForce.Meter
import YM.SU5.LoomForce.Board
import YM.SU5.WakeInvestment.FoldPower

/-!
# Maturity/inequality clearing for multi-staff aperture. No powers on clover
cost beyond the rents of Turbine -- asking at combined polynomial color
receipt needs Holder prices at higher orders now. Keep arity *fixed*, still before
any estimates with it taking torus path. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Phase SU Rush Mir Reflect Lifted Vale
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Jewel
open Pressure BProof Worth Worth.Pays WakeInvestment
open EmberWind
open scoped Topology ContDiff BigOperators ENNReal InnerProductSpace Classical
section salaries
-- costs as real functions of hat
private def loose (f : ℝ→ℝ) := ∃ J, Worth.Pays 0 J 0 f
private lemma loose_const (a:ℝ) : loose (fun _=> a) := ⟨0,constant a⟩
private lemma loose_coin (b:ℝ) : loose (fun x=> coin x 0 b 0) := ⟨b,whole 0 b 0⟩
variable {f g : ℝ → ℝ}
private lemma loose_plus (h:loose f) (v:loose g) : loose (fun x=> f x + g x) := by
  obtain ⟨a,h⟩ := h; obtain ⟨b,v⟩ := v
  refine ⟨max a b + 1, plus (Worth.Pays.merit h (Or.inr (Or.inl ⟨rfl,?_⟩)))
    (Worth.Pays.merit v (Or.inr (Or.inl ⟨rfl,?_⟩)))⟩
  · linarith [le_max_left a b]
  linarith [le_max_right a b]
private lemma loose_scale (a:ℝ) (h:loose f) : loose (fun x=> a*f x) := by obtain ⟨b,h⟩:=h; exact ⟨b,Pays.scale a h⟩
private lemma loose_mul (h:loose f) (v:loose g) : loose (fun x=> f x * g x) := by
  obtain ⟨a,h⟩ := h; obtain ⟨b,v⟩ := v; exact ⟨a+b,by simpa only [zero_add] using times h v⟩
private lemma loose_pow (h:loose f) (n:ℕ) : loose (fun x=> f x ^ n) := by
  obtain ⟨a,h⟩ := h; exact ⟨a*n,by simpa only [zero_mul] using Pays.pot h n⟩
private lemma loose_launch (h:loose f) : ∀ᶠ I in atTop, ∀ᶠ x in atTop, f x ≤ coin x 0 I 0 := by
  obtain ⟨a,h⟩ := h; exact (eventually_gt_atTop a).mono fun I p=> leap h (Or.inr (Or.inl ⟨rfl,p⟩))

private def meter_cap (x:ℝ) := 2*Real.sqrt x * temp x
private lemma loose_cap : loose meter_cap := by
  refine ⟨1,Pays.fix (Pays.scale 2 (whole 0 1 0)) ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; unfold meter_cap
  rw [Regis.Head.Garland.era x p,←BProof.thresh_eq p,BProof.thresh,mul_assoc,BProof.coin_mul]; norm_num
private lemma cap_non (x:ℝ) : 0 ≤ meter_cap x := by unfold meter_cap; have ht:=Work.E04.temp_nonneg x; positivity

variable (P:Preparation) (n U m : ℕ) (C K A : ℝ) (h:0 ≤ C) (hK: 0<K) (hA:0<A)
local notation "θ" s:max => hat P.R.L P.x s
def glow (P:Preparation)(A:ℝ)(s:ℕ) : ℝ := sPow P s A ^ 2

structure Office (P:Preparation)(T K A C:ℝ)(n U m s:ℕ) : Prop where
  circus : CircusPrice P 0 K s
  cells : sPow P s (grass K) ≤ sPow P s T
  seats : (m:ℝ) ≤ sPow P s T
  metered (ρ:ℝ)(p:|ρ| ≤ 2*bornQ P s) :
    let x := hat P.R.L P.x s
    let S := sPow P s T
    let D := |ρ| * temp x
    let q := glow P A s
    let c := tollMeter C q n U
    let a := sPow P s K
    capBill (zoomR P A s) q ρ (temp x) ^ n ≤ S ∧
      c ≤ S ∧ c*(1+D)^n ≤ S ∧ c*(1+D)^n*Staff.armRent a (skyline x) D a ≤ scratch x
include h hA hK
lemma office_opens : ∃ T, 0<T ∧ ∀ᶠ s in atTop, Office P T K A C n U m s := by
  let R(x:ℝ):= coin x 0 A 0
  let y(x:ℝ):= meter_cap x
  let b(x):= coin x 0 K 0
  let a(x:ℝ) := R x^3*R x^2*(Staff.regiment*y x)+R x^3*(Fintype.card SU.Slot:ℝ)
  let V(x:ℝ) := tollMeter C (R x^2) n U
  let e(x:ℝ) := V x*(1+y x)^n
  let o(x:ℝ) := e x*(2*SU.group.colorScale*(b x+4*b x)*y x)
  have hc : loose a := by
    have he:= loose_pow (loose_coin A) 3; apply loose_plus (loose_mul (loose_mul he (loose_pow (loose_coin A) 2)) (loose_scale _ loose_cap)) (loose_mul he (loose_const _)) -- apply vs defeq
  have hv:loose V:=loose_scale _ (loose_scale _ (loose_pow (loose_scale 2 (loose_plus (loose_const 1)
    (loose_pow (loose_coin _) 2))) _))
  have he:loose e:=loose_mul hv (loose_pow (loose_plus (loose_const 1) loose_cap) n)
  have hx:loose o:=loose_mul he (loose_mul (loose_scale (2*SU.group.colorScale) (loose_plus (loose_coin K) (loose_scale 4 (loose_coin K)))) loose_cap)
  obtain ⟨T,t,hg,hz,hm,hS⟩ := ((eventually_gt_atTop (0:ℝ)).and ((eventually_gt_atTop (grass K)).and
    ((loose_launch (loose_pow hc n)).and ((loose_launch hv).and (loose_launch he))))).exists
  obtain ⟨w,pW⟩ := hx
  have hg' : ∀ᶠ x:ℝ in atTop, o x*skyline x ≤ scratch x:=
    leap (times pW (whole (-120000/400000) 0 0)) (Or.inl (by norm_num):(Earlier _ _ _ (-7/400000) 0 0)) -- syntax
  refine ⟨T,t,?_⟩
  filter_upwards [CircusPrice.ready P 0 K (by norm_num) hK, grow_e A 2 hA P,
    grow_e T (m:ℝ) t P, (turnover P).eventually (leap (whole 0 (grass K) 0) (p:=T) (q:=0)
        (Or.inr (Or.inl ⟨rfl,hg⟩))), (turnover P).eventually hz, (turnover P).eventually hm,
    (turnover P).eventually hS, (turnover P).eventually hg'] with s hI t gm ht l y0 hv hq
  refine ⟨hI,ht,gm,fun ρ p0=>?_⟩
  let X:=θ s
  intro x S D q c b'
  have hu : 0 ≤ temp x:= Work.E04.temp_nonneg _
  have hh : D ≤ y X:= mul_le_mul_of_nonneg_right p0 hu
  have hp : 0 ≤ D:= mul_nonneg (abs_nonneg _) hu
  have hQ : 0 ≤ q := sq_nonneg _
  have hc0 : 0 ≤ c:= by unfold c tollMeter; positivity
  have hR:(zoomR P A s:ℝ) ≤ R X:=by
    have hv: (zoomR P A s:ℝ) < (R X)/2+1:=Nat.ceil_lt_add_one (by have he:0<R X:=BProof.coin_pos ..; positivity)
    change 2 ≤ R X at t; linarith only [hv,t]
  have hD : c*(1+D)^n ≤ e X:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith only [hh]) _) hc0
  refine ⟨le_trans (pow_le_pow_left₀ (show 0≤capBill (zoomR P A s) q ρ (temp x) from capBill_pos (τ:=temp x) _ _ hQ hu) (show capBill (zoomR P A s) q ρ (temp x) ≤ a X from ?_) _) l, y0, hD.trans hv,?_⟩
  · have hr:0≤Staff.regiment:=Staff.regge
    change (_ * q*(Staff.regiment* D) + _) ≤ (R X^3 * q*(Staff.regiment*y X) + R X^3*(Fintype.card SU.Slot:ℝ)); gcongr
  apply hq.trans'; unfold Staff.armRent; change c*(1 + D)^n*( _*(b X+4*b X)*skyline X* D) ≤ o X*skyline X; unfold o
  have h0:0≤ skyline X:=(WakeInvestment.chip_pos ..).le; have hy:0≤b X:=BProof.coin_pos ..|>.le
  have hr:=SU.group.colorScale_pos; have hO:0≤ e X:= (mul_nonneg hc0 (by positivity)).trans hD
  calc _ ≤ e X*(2*SU.group.colorScale*(b X+4*b X)*skyline X* y X) := by gcongr
       _ = _:= by ring
#print axioms office_opens
end salaries
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
