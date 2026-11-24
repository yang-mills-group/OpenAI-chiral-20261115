import GaugeFieldConstruction.WheelPress
import YM.SU5.Fineness.Driving
-- P1 calibration, sharpening Driving.lean
set_option autoImplicit false
set_option maxHeartbeats 164000
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
private lemma driveX (M:ℝ)(z:ℝ)(p:z>0)(h:0<M): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2 ≤ a→ x/2≤b → |a-b| ≤ M → |Real.log a-Real.log b| ≤ z*fourthDeck x:=by
 have H:Tendsto (fun x:ℝ=>x^(3/4:ℝ)*z) atTop atTop:= (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).atTop_mul_const p
 filter_upwards [H.eventually_ge_atTop (M*2),eventually_gt_atTop (0:ℝ)] with x hx hp a b hA hB H; rw [abs_le] at H ⊢
 have he{a b:ℝ}(hA:x/2≤a)(hB:x/2≤b)(t:a-b≤M): Real.log a-Real.log b≤z*fourthDeck x:=by
    have ha:0<a:= lt_of_lt_of_le (half_pos hp) hA; have hb:0<b:=lt_of_lt_of_le (half_pos hp) hB
    rw [← Real.log_div ha.ne' hb.ne']; refine (Real.log_le_sub_one_of_pos (div_pos ha hb)).trans (sub_le_iff_le_add.mpr ((div_le_iff₀ hb).mpr ?_));
    let v:=z*fourthDeck x; have hv:0<v:=mul_pos p (inv_pos.mpr (Real.sqrt_pos_of_pos (Real.sqrt_pos_of_pos hp)))
    change a ≤ (v+_)*_
    have hV:M*2≤x*v:=le_trans hx (le_of_eq (by
      rw [show x*v=x*fourthDeck x*z from by unfold v; ring, fourthDeck_price x hp.le]; congr 1
      rw [show (3/4:ℝ)=1+ -(1/4) by norm_num,Real.rpow_add hp]; simp))
    nlinarith only [t,hV, mul_le_mul_of_nonneg_right hB hv.le]
 refine ⟨neg_le.mp ?_,he hA hB H.2⟩; rw [neg_sub]; exact he hB hA (by linarith only [H.1])
lemma entryDeck (Q : Grace K R L)(H: LocalRatio L) (M:ℝ)(z:ℝ)(p:z>0)(t: M>0): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2≤a → x/2≤b →|a-b| ≤ M → ∀ i n F,|entryFin Q i n F a - entryFin Q i n F b|≤ z*fourthDeck x*sites n:=by
 let f:=H'+1; have hf : 0≤ H':=Pannier.pen_log_nonneg _; have he:0<f:= add_pos_of_nonneg_of_pos hf zero_lt_one; let e:= z/(3*f)
 filter_upwards [eventually_gt_atTop (0:ℝ), driveX M e (div_pos p (by positivity)) t] with x ht hx a b ha hb hΔ i n F
 have hh:=hx a b ha hb hΔ; let W:=sites n; have hw:1 ≤ W:=sites_pos n
 have hp: entryFin Q i n F a-entryFin Q i n F b= -(H'*(Real.log a-Real.log b)* (3*(W-1))):=by
    unfold entryFin Fineness.gaugedBase; rw [spare_formula _ H.scale ((half_pos ht).trans_le ha),spare_formula _ H.scale ((half_pos ht).trans_le hb),Pannier.shadowLie, sites_as_price]; unfold W; ring
 rw [hp, abs_neg,abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg (show 0≤3*(W-1) by linarith only [hw])]; calc
    _ ≤ (H'*(e*fourthDeck x))*(3*W):=by gcongr <;> linarith
    _ ≤ (f*(e*fourthDeck x))*(3*W):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (mul_nonneg (div_nonneg p.le (by positivity)) (show 0 ≤ fourthDeck x from inv_nonneg.mpr (Real.sqrt_nonneg _)))) (by positivity)
    _ = _:= (by change _=z*fourthDeck x*W; unfold e; field_simp)
variable {β:ℝ}{c:ℂ}

private lemma growPitch (Q: Grace K R L)(B:Side)(x:ℝ)(C:ℝ):∀ᶠ i in atTop,∀ m,C ≤ 3*fourthDeck (hat R.L x i) * sites (cell m B R.L i):=by
 let a:ℝ:= R.L.val; have hp:a>1:=by unfold a; exact_mod_cast (show 1 < R.L.val by have ht:= Q.tallX; omega)
 have h₀:Tendsto (fun n:ℕ=> x/a^n) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hp)
 have h₁:Tendsto (fun n:ℕ=> (n:ℝ)/a^n) atTop (𝓝 0):=by
    have v:=tendsto_pow_const_mul_const_pow_of_lt_one 1 (inv_nonneg.mpr (zero_lt_one.trans hp).le) ((inv_lt_one₀ (zero_lt_one.trans hp)).2 hp) -- fix name
    simpa [inv_pow,div_eq_mul_inv] using v
 have g:Tendsto (fun i:ℕ=>|C| *(hat R.L x i/a^i)) atTop (𝓝 0):=by
   simpa [hat,div_eq_mul_inv,add_mul,mul_right_comm _ (Vale.billX R.L)] using ((h₀.add (h₁.mul_const (billX R.L))).const_mul |C|)
 filter_upwards [g.eventually (ge_mem_nhds zero_lt_one),(stage_slope Q x).eventually_ge_atTop 1] with i s hx m
 let N:=mesh m R.L i; have hh:1 ≤ ((More (cell m B R.L i)).val:ℝ):= by exact_mod_cast ((More (cell m B R.L i)).property)
 have q:a^i≤ sites (cell m B R.L i):=by
  apply (le_self_pow₀ hh (by decide: (4:ℕ)≠0)).trans'
  have he:R.L.val^i ≤ N.val:= Nat.le_mul_of_pos_left _ m.property
  have hx:N.val ≤ (More (cell m B R.L i)).val:= (Nat.le_mul_of_pos_right (N.val) Nat.zero_lt_two|>.trans (Nat.le_mul_of_pos_right _ B.property))|>.trans (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)
  change (↑R.L.val:ℝ)^i≤ ((More (cell m B R.L i)).val:ℝ); exact_mod_cast he.trans hx
 let T:=hat R.L x i
 have hx':1≤T:=hx; have hX:0<T:=zero_lt_one.trans_le hx'
 have hY: fourthDeck T * T ≥ 1:=by
   rw [fourthDeck_price T hX.le];
   calc _=T^(-(1/4)+1:ℝ):=by rw [Real.rpow_add hX,Real.rpow_one]
        _≥1:=Real.one_le_rpow hx' (by norm_num)
 have hb: |C| *T≤ a^i:=by
   change |C| * (T/a^i)≤1 at s; rw [← mul_div_assoc,div_le_one (by positivity)] at s; exact s
 calc
 C≤|C|:=le_abs_self _
 _ ≤ 3*fourthDeck T*(|C| *T):=by nlinarith only [mul_le_mul_of_nonneg_right hY (abs_nonneg C),abs_nonneg C]
 _ ≤ _:= mul_le_mul_of_nonneg_left (hb.trans q) (mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg _)))

open Fineness
namespace Branch
local notation "X"=> hat R.L x
variable {A:Branch W m k x N0}
variable {i:ℕ}{α:ℝ}(p:SpiceWay J q h P N0) (a:Bon J q h D delay A)(H:Service V U W J q h D C R0 P N0 delay)
local notation "ζ" n:max=> sites (cell m B R.L n)
local notation "dL"=> 8* H'*Real.log R.L.val
include p H
lemma cycleYearsX (E:LocalRatio L):∀ᶠ i in atTop,∀ (m:Side)(k:ℕ)(A:Branch W m k x N0)(b:Bet k), Bon J q h D delay A → Solved P A α b→ A.last.music W.z → i<k →
 let G: ℕ→ℝ := fun n=>entryFin V (k-n) (cell m B R.L n) (A.gram P b n).J ((A.gram P b n).beta); let Z(n):=(A.gram P b n).v.re; |(Z i-Z (i+1))-(G (i+1)-G i)| ≤9*fourthDeck (hat R.L x i)*sites (cell m B R.L i):=by
 let C':= dL; let M:=guardFee (W:=W); let T':=1+|M|
 filter_upwards [(stage_slope V x).eventually p.toll, growPitch V B x |dL|, (stage_slope V x).eventually (entryDeck V E T' 3 (by norm_num) (by unfold T'; positivity))] with i u h ξ m k A b t c a e G Z
 let d:=3*fourthDeck (hat R.L x i)
 let X₀:=A.toSpine.address i; let F:=A.gram P b; let v:= (b.read (i+1)).re; let Hφ:=A.active P b i; let w:=A.corr P b (i+1); let U₀:= A.offset P b (i+1); let P':=A.op P i
 obtain ⟨hu,hκ,hA⟩:= yearFit t H c e a; let G':= entryFin V (k-i) _ (F i).J v
 have hpV:|G' - G i| ≤ d*sites (cell m B R.L i):=ξ v (F i).beta hu hκ ((by rw [abs_sub_comm]; exact hA.trans ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))) : |v-(F i).beta| ≤ T') _ _ _
 have H₀: Heed V X₀ d v U₀ (F i).v :=by
    have hr:=u _ _ _ _ _ (t.request i e) v w.1 (hat_step i ▸ (t.beta_ok H c.toRealQ (i+1) e).2) (t.flow (t.charged H c.toRealQ (i+1) e)) U₀; change Heed V X₀ d v U₀ (A.offset P b i); rw [offset.eq_1 P A b i,dif_pos e]; exact hr
 have hR:crestDue V X₀ v= G (i+1)-G'-C':=by unfold crestDue; change entryFin V (k-1-i) _ _ _-entryFin V (k-1-i+1) _ _ _-_= _; rw [show k-1-i+1=k-i from by omega,show k-1-i=k-(i+1) from by omega]; rfl
 unfold Heed at H₀; rw [hR] at H₀
 have he:=abs_le.mp (h m); change -_ ≤ C'∧C' ≤ d*sites (cell m B R.L i) at he
 change |Z i-Z (i+1)-(G (i+1)-G'-C')| ≤ d*sites (cell m B R.L i) at H₀; rw [abs_le] at hpV H₀ ⊢; unfold d at *; constructor <;> linarith only [he.1,he.2,H₀.1,H₀.2,hpV.1,hpV.2]
end Branch
end YM.CF.Py.Rate
end
