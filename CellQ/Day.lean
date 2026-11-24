import CellQ.Projection
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Py.Rate.Pitching.Focus
variable (P:Spine) {U:P.Roster}(M:Morn P.par.K)
-- Qualifying per reference height. Markov on price.Basic threshold ~2^s sqrt(Wx). all suffice vs boost.S
local notation "K"=>P.calibration
open Py.Rate.Pitching.Focus
-- choose 3 axes? team finite. D.At all commands l=(F etc). geometry `cellar`; b both tags to bound vectors.
noncomputable abbrev priceQ (M:Morn P.par.K)(a:ℝ) := Real.exp (2*(|a|+|M.Mult|)+1)
noncomputable abbrev ranch(P:Spine)(M:Morn P.par.K)(a:ℝ)(j:ℕ):ℝ:= payday P j * priceQ (P:=P) M a * Real.exp 1
abbrev hikeV (d:ℕ):ℕ:= 2^(2^d:ℕ)
variable {F:ℕ}{C D:ℕ→ℕ→ℝ}{α:ℝ}
lemma volumeR (j:ℕ): 0<payday P j:=by
 let x:=Vale.hat P.par.R.L P.par.x j -- notation not imported
 have hL:=turn_p P j
 have hv:0≤ (SU.group).slopeConstant:=(Gauge.slopeConstant_pos Thera.yet_one).le
 let q:=(P.par.R.L.val:ℝ)
 have he:1 ≤ q:=Nat.one_le_cast.mpr P.par.R.L.property
 have ht:0 < YM.SectorNext.Remainder.Scales.y SU.group P.par.R.L x:=by
    unfold YM.SectorNext.Remainder.Scales.y YM.Pressure.betaF; have hg:=mul_nonneg hv (Real.log_nonneg he); change 1≤x at hL; linarith
 exact pow_pos (YM.SectorNext.Remainder.Scales.gauge SU.group P.par.R.L ht) _
lemma ranch_p (a:ℝ)(j:ℕ):0<ranch P M a j:=mul_pos (mul_pos (volumeR P j) (Real.exp_pos _)) (Real.exp_pos _)
lemma income_x (j n:ℕ)(t:j≤n)(e:F ≤ j)(V:Accolade P M α F n (C n) (D n))(b:Bool):let B:=dress P n j (cellar P F j) b (C n) (D n);
 (∫ x,readingSq P (n+1) B x ∂ P.pillars 3) ≤ shardRa P M α j (Calico.amount P j) (reachQ P j):=by
 intro B; obtain ⟨R,R'⟩:=recess P F j
 rw [paid_mean]; refine (Complex.re_le_norm _).trans ?_
 let e':((P.calibration.ℓ:ℕ):ℤ)+ Calico.amount P j≤nodeC (cellar P F j) (3:Axis):=by unfold minB at R; push_cast at R; unfold Calico.amount; push_cast; exact R
 unfold B; change ‖P.E (n+1) (mirror K 3 0 (dress P n j (cellar P F j) b _ _).val*(dress P n j (cellar P F j) b _ _).val)‖≤_; rw [dress_val]; exact V.2 j e t 3 _ _ _ e' R'
def Jones(P:Spine)(M:Morn P.par.K)(α:ℝ) (F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3):Prop:= ∀ᶠ d:ℕ in atTop,let j:=hikeV d;∀ k:ℕ, let n:=j+k
          ∀ b:Bool, ‖P.viewF 3 x (n+1) (birthDress P n j (cellar P F j) b (C n) (D n) (fresh P F j))‖≤2^(d+k)*(2*ranch P M α j)
lemma reader_E (A:∀ n,F ≤ n→ Accolade P M α F n (C n) (D n)) : ∀ᵐ x ∂P.pillars 3,Jones P M α F C D x:=by
 have hG:Tendsto hikeV atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℕ) by decide)).comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℕ) by decide))
 obtain ⟨s,H⟩:= Filter.eventually_atTop.mp ((hG.eventually_ge_atTop F).and (hG.eventually (earnings_wafer P M α)))
 let PrC(n):=Fin (n+1) × Bool
 let j(n:ℕ)(i:PrC n):=hikeV (i.1.val+s); let v(n:ℕ)(i:PrC n):=j n i+(n-i.1.val)
 let y(n:ℕ)(i:PrC n):=dress P (v n i) (j n i) (cellar P F (j n i)) i.2 (C (v n i)) (D (v n i))
 let B(n:ℕ)(i:PrC n)(x:P.Spectrum0 3):= readingSq P (v n i+1) (y n i) x
 let p(n:ℕ)(i:PrC n) := ranch P M α (j n i)
 have ht(n:ℕ)(i:PrC n):0<p n i:= ranch_p ..
 let S(n:ℕ)(i:PrC n)(x:P.Spectrum0 3):= ((p n i)^2)⁻¹* B n i x
 have he(n:ℕ)(i:PrC n):Continuous (S n i):=continuous_const.mul (paid_cont ..)
 have hr(n:ℕ)(i:PrC n)(x:P.Spectrum0 3) : B n i x = ‖P.viewF 3 x (v n i+1) (birthDress P (v n i) (j n i) (cellar P F _) i.2 (C (v n i)) (D (v n i)) (fresh P F _))‖^2:= as_paid ..
 have hv(n:ℕ)(i:PrC n)(x):0≤S n i x:=by unfold S; rw [hr]; positivity
 have ha(n:ℕ): (Fintype.card (PrC n):ℝ) ≤4*2^n:=by
    unfold PrC; rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]; push_cast; have he:(n:ℝ)+1≤ 2^n:= by exact_mod_cast (show n+1 ≤ 2^n from Nat.lt_two_pow_self)
    linarith only [he,show 0≤ (2:ℝ)^n by positivity]
 have hu(n i): (∫ x,S n i x∂P.pillars 3)≤ (1:ℝ):=by
    obtain ⟨hd,g⟩:= H (i.1.val+s) (Nat.le_add_left ..)
    have hp:j n i ≤ v n i:=Nat.le_add_right ..
    let q:=hd.trans hp
    have hi:=income_x P M (j n i) (v n i) hp hd (A _ q) i.2; unfold S; rw [integral_const_mul]
    have hP:((p n i)^2)⁻¹≥0:=by positivity
    apply (mul_le_mul_of_nonneg_left (hi.trans g) hP).trans
    have hm:1≤Real.exp 1:=Real.one_le_exp zero_le_one
    change _ * ( _^2 * Real.exp 1) ≤ _
    apply le_trans _ (inv_mul_cancel₀ (pow_pos (ht n i) 2).ne' |>.le)
    unfold p ranch; rw [mul_pow (_*_) (Real.exp 1)]; gcongr -- gap need Real.exp≤ Real.exp²
    first | exact le_self_pow₀ hm (by decide) | skip
 let e(n:ℕ):ℝ:=2^n*2
 have hf(n:ℕ):0<e n:=by unfold e; positivity
 have hm:=prognosis S (fun _=>1) he hv e hf hu fun n=>?_ 
 · filter_upwards [hm] with x hx
   unfold Jones; obtain ⟨n,hn⟩:=Filter.eventually_atTop.mp hx; filter_upwards [eventually_ge_atTop (s+n)] with d hd j' k q b
   let m:=d-s+k; let i:PrC m:=(⟨d-s,by unfold m; omega⟩,b); have hr0:j m i = j':=by unfold j i; simp only; rw [Nat.sub_add_cancel (show s≤d by omega)]
   have ht': v m i=q:=by unfold v q; rw [hr0]; congr 1; change m-(d-s)=k; unfold m; omega
   have hW:= hn m (by unfold m; omega) i; unfold S at hW; rw [hr] at hW
   let V:= ‖P.viewF 3 x (v m i+1) (birthDress P (v m i) (j m i) (cellar P F (j m i)) i.2 (C (v m i)) (D (v m i)) (fresh P F (j m i)))‖
   have hU:V< e m*p m i:=by
      apply (pow_lt_pow_iff_left₀ (norm_nonneg _) ((mul_pos (hf _) (ht ..)).le) (show 2≠(0:ℕ) by omega)).1
      rw [mul_pow]; rw [mul_comm ((p m i)^2)⁻¹,←div_eq_mul_inv] at hW; exact (div_lt_iff₀ (pow_pos (ht ..) 2)).mp hW
   unfold V at hU; rw [ht',hr0] at hU -- dep equality, defeq h?
   -- p m still j m i fold.. rw
   have hQ:p m i=ranch P M α j':=congrArg (ranch P M α) hr0
   refine (show _< _ from hU).le.trans ?_; rw [hQ]; unfold e; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (show m≤d+k by unfold m; omega)) (by have h:=ranch_p P M α j'; positivity)
 · unfold discount e; rw [mul_one,mul_pow (2^( _ :ℕ))]; apply (ha n).trans (le_of_eq ?_); rw [sq,sq,inv_pow]; field_simp; ring -- squaring which? simpler notation
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
