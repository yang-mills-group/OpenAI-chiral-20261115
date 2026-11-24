import YM.SU5.Thin.Press.Loom
import YM.SU5.Fineness.Stitch
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
open Pitching.Focus AnalyticBridge.Annulus1AD
local notation "H'"=> Pannier.halfLie SU.group
variable {P}
open Sleigh
private lemma logEngine (M:ℝ)(z:ℝ)(p:0<z)(h:0<M): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2≤a→x/2≤b→ |a-b| ≤ M → |Real.log a-Real.log b|≤ z*x^(-(1/4:ℝ)) := by
 filter_upwards [eventually_gt_atTop (0:ℝ), ((Paddled.park (-(1:ℝ))).scale (2*M)).discounts (b:=-(1/4:ℝ)) (by norm_num) p] with x hx he a b ha hb hh
 exact (log_swing (half_pos hx) ha hb).trans ((mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (x/2)⁻¹)).trans (( (le_abs_self _).trans he).trans' (le_of_eq (by rw [Real.rpow_neg_one]; field_simp))))
lemma engineFuel (Q : Grace K R L)(H: LocalRatio L) (M:ℝ)(z:ℝ)(p:z>0)(t: M>0): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2≤a → x/2≤b →|a-b| ≤ M → ∀ i n F,|entryFin Q i n F a - entryFin Q i n F b|≤ (z*x^(-(1/4:ℝ)))*sites n:=by
 let f:=H'+1; have hf : 0≤ H':=Pannier.pen_log_nonneg _; have he:0<f:= add_pos_of_nonneg_of_pos hf zero_lt_one; let e₁:= z/(3*f)
 filter_upwards [eventually_gt_atTop (0:ℝ), logEngine M e₁ (div_pos p (by positivity)) t] with x ht hx a b ha hb hΔ i n F
 have hh:=hx a b ha hb hΔ; let e:=e₁*x^(-(1/4:ℝ)); have hc:e>0:=mul_pos (div_pos p (by positivity)) (by positivity); let W:=sites n; have hw:1 ≤ W:=sites_pos n
 have hp: entryFin Q i n F a-entryFin Q i n F b= -(H'*(Real.log a-Real.log b)* (3*(W-1))):=by
    unfold entryFin Fineness.gaugedBase; rw [spare_formula _ H.scale ((half_pos ht).trans_le ha),spare_formula _ H.scale ((half_pos ht).trans_le hb),Pannier.shadowLie, sites_as_price]; unfold W; ring
 rw [hp, abs_neg,abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg (show 0≤3*(W-1) by linarith only [hw])]; calc
    _ ≤ (H'*e)*(3*W):=by change _ ≤ e at hh; gcongr <;> linarith
    _ ≤ (f*e)*(3*W):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hc.le) (by positivity)
    _ = _:= (by change _=(z*x^(-(1/4:ℝ)))*W; unfold e e₁; field_simp)
lemma head_geo {r:ℝ}(p:1<r)(L:Side)(x:ℝ)(b:ℕ): Tendsto (fun i:ℕ=> hat L x (b+i)/ r^i) atTop (𝓝 0):= by
 have he:Tendsto (fun i:ℕ=>(x+b*billX L)/ r^i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt p)
 have h₀:= (he.add ((tendsto_pow_const_div_const_pow_of_one_lt 1 p).mul_const (billX L))); simp only [pow_one,zero_mul, add_zero] at h₀; apply h₀.congr; intro i; unfold hat; push_cast; ring
lemma heightFuel (Q: Grace K R L)(B:Side) (x:ℝ) (C q:ℝ) (h:0 < q): ∀ᶠ i in (atTop :Filter ℕ), ∀ m, C ≤ (q*(hat R.L x i)^(-(1/4:ℝ)))*sites (cell m B R.L i):=by
 let a:ℝ:= R.L.val; have hp:a>1:=by unfold a; exact_mod_cast (show 1 < R.L.val by have ht:= Q.tallX; omega)
 let X:=hat R.L x; let g:=|C|+1; have hg:0<g:=by unfold g; positivity
 have hv: Tendsto (fun i:ℕ=> X i / a^i) atTop (𝓝 0):=by simpa only [zero_add] using (head_geo hp R.L x 0)
 filter_upwards [(stage_slope Q x).eventually_ge_atTop 1, hv.eventually (ge_mem_nhds (div_pos h hg))] with i p ht m
 change 1≤X i at p; have ht':0<X i:= zero_lt_one.trans_le p
 have hw:g≤ q*(X i)^(-(1:ℝ))* a^i:=by
    rw [Real.rpow_neg_one]; change X i/a^i ≤ _ at ht; field_simp at ht ⊢; linarith only [ht]
 let Z:=mesh m R.L i; have hh:1 ≤ ((More (cell m B R.L i)).val:ℝ):= by exact_mod_cast ((More (cell m B R.L i)).property)
 have tx:a^i ≤ sites (cell m B R.L i):= by
    apply (le_self_pow₀ hh (by decide: (4:ℕ)≠0)).trans'; have he:R.L.val^i ≤ Z.val:= Nat.le_mul_of_pos_left _ m.property
    have hx:Z.val ≤ (More (cell m B R.L i)).val:= (Nat.le_mul_of_pos_right (Z.val) Nat.zero_lt_two|>.trans (Nat.le_mul_of_pos_right _ B.property))|>.trans (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)
    change (↑R.L.val:ℝ)^i≤ ((More (cell m B R.L i)).val:ℝ); exact_mod_cast he.trans hx
 apply hw.trans' (show C≤g from le_trans (le_abs_self _) (le_add_of_nonneg_right zero_le_one)) |>.trans; apply mul_le_mul _ tx (by positivity) (mul_nonneg h.le (Real.rpow_nonneg ht'.le _)); apply mul_le_mul_of_nonneg_left _ h.le; exact Real.rpow_le_rpow_of_exponent_le p (by norm_num)

open Fineness
namespace Branch
local notation "X"=> hat R.L x
variable {A:Branch W m k x N0}
variable {i:ℕ}{α:ℝ}(p:Cistern J q h P N0) (a:Bon J q h D delay A)(H:Service V U W J q h D C R0 P N0 delay)
local notation "ζ" n:max=> sites (cell m B R.L n)
include p H
lemma brake_power (E:LocalRatio L)(s:ℝ)(hv:s>0):∀ᶠ i in atTop,∀ (m:Side)(k:ℕ)(A:Branch W m k x N0)(b:Bet k), Bon J q h D delay A → Solved P A α b→ A.last.music W.z → i<k →
 let G: ℕ→ℝ := fun n=>entryFin V (k-n) (cell m B R.L n) (A.gram P b n).J ((A.gram P b n).beta); let Z(n):=(A.gram P b n).v.re; |(Z i-Z (i+1))-(G (i+1)-G i)| ≤ (s*(X i)^(-(1/4:ℝ)))*sites (cell m B R.L i):=by
 let C':= 8* H'*Real.log R.L.val; let d:= s/3; have ht:d>0:= div_pos hv (by norm_num); let M:=guardFee (W:=W); let T':=1+|M|
 filter_upwards [(stage_slope V x).eventually (p.toll d ht), heightFuel V B x |C'| d ht, (stage_slope V x).eventually (engineFuel V E T' d ht (by unfold T'; positivity))] with i u h ξ m k A b t c a e G Z
 let X₀:=A.toSpine.address i; let F:=A.gram P b; let v:= (b.read (i+1)).re; let Hφ:=A.active P b i; let w:=A.corr P b (i+1); let U₀:= A.offset P b (i+1); let P':=A.op P i
 obtain ⟨hu,hκ,hA⟩:= yearFit t H c e a; let G':= entryFin V (k-i) _ (F i).J v
 have hpV:|G' - G i| ≤ (d*(X i)^(-(1/4:ℝ)))*sites (cell m B R.L i):=ξ v (F i).beta hu hκ ((by rw [abs_sub_comm]; exact hA.trans ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))) : |v-(F i).beta| ≤ T') _ _ _
 have H₀: Heed V X₀ (d*(X i)^(-(1/4:ℝ))) v U₀ (F i).v :=by
    have hr:=u _ _ _ _ _ (t.request i e) v w.1 (hat_step i ▸ (t.beta_ok H c.toRealQ (i+1) e).2) (t.flow (t.charged H c.toRealQ (i+1) e)) U₀; change Heed V X₀ (d*(X i)^(-(1/4:ℝ))) v U₀ (A.offset P b i); rw [offset.eq_1 P A b i,dif_pos e]; exact hr
 have hR:crestDue V X₀ v= G (i+1)-G'-C':=by unfold crestDue; change entryFin V (k-1-i) _ _ _-entryFin V (k-1-i+1) _ _ _-_= _; rw [show k-1-i+1=k-i from by omega,show k-1-i=k-(i+1) from by omega]; rfl
 unfold Heed at H₀; rw [hR] at H₀
 have he:=abs_le.mp (h m); change -_ ≤ C'∧C' ≤ (d*(X i)^(-(1/4:ℝ)))*sites (cell m B R.L i) at he
 change |Z i-Z (i+1)-(G (i+1)-G'-C')| ≤ (d*(X i)^(-(1/4:ℝ)))*sites (cell m B R.L i) at H₀; rw [abs_le] at hpV H₀ ⊢; unfold d at *; constructor <;> linarith only [he.1,he.2,H₀.1,H₀.2,hpV.1,hpV.2]

end Branch
end YM.CF.Py.Rate
