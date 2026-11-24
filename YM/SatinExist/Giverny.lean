import YM.SU5.FiniteGaugeData.Seld.GaugeK
import YM.SatinExist.EdgePrice
/-!
 # Thermal tariffs on both incoming & outgoing axes. Independent-sided progress.
-/
set_option autoImplicit false
set_option maxRecDepth 2200
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "ρ" => volume.restrict (Ioi (0:ℝ))

lemma ticket_sym : StampPower S n=Cache S (n+1):=by
 let z:= OS.Semigroup.duration 1; have h:z∈inside:= dur.mpr zero_lt_one
 let F:=S.F z
 have hF:F=S.E 1 := S.roots_heat zero_lt_one
 have hI: Injective F := by
   intro x y t; apply sub_eq_zero.mp; apply S.heat_faithful 1; rw [← hF,map_sub,t,sub_self]
 let G:= saucer S; let D:=looper S z
 have hD:G*D=F:= dorsal S z h
 induction n with
 | zero=>
    change StampPower S 0=G^1; rw [pow_one]
    ext1 x; rw [meter]; change _=ship S x; unfold ship
    congr 1; funext t; unfold thermalMass; simp only [pow_zero,Nat.factorial_zero, mul_one,Nat.cast_one,div_one]; rfl
 | succ n ih=>
    have he:D*StampPower S (n+1)=F*StampPower S n:=by
       ext1 x; change (F _ - deriv S.F z (StampPower S (n + 1) x))=F (StampPower S n x); rw [interest_higher S n x z h]; exact sub_sub_cancel _ _
    have hh:F*StampPower S (n+1)=F*Cache S (n+1+1):=by
       rw [← hD, mul_assoc,he,hD]; unfold Cache; rw [pow_succ',ih]; change G*(F * G^(n+1))=F*(G*G^(n+1)); rw [←mul_assoc,(show Commute G F from cupF ..)|>.eq,mul_assoc]; assumption
    ext1 x; exact hI (DFunLike.congr_fun hh x)

abbrev elast (t:ℝ):= S.E t.toNNReal
local notation "E" => elast S

def Currency (A:ℝ→H.Op) : Prop:= ∀ s t:ℝ,0<t → t ≤ s → A s=E (s-t)* A t * E (s-t)
lemma elast_comes (s t:ℝ) (p:0 ≤ s)(g:0≤t): E s*E t=E (s+t):=by
 unfold elast; rw [Real.toNNReal_add p g,S.time]; rfl
lemma elast_good {t:ℝ}(h:0<t): ContinuousAt E t:=by
 let F(r:ℝ):=S.F (r:ℂ); have hc:= (S.localHeat _ (show (t:ℂ)∈inside from h)).continuousAt.comp continuous_ofReal.continuousAt
 exact ContinuousAt.congr hc ((show ∀ᶠ x in 𝓝 t, x ∈ Ioi (0:ℝ) from Ioi_mem_nhds h).mono (fun x p=> branch_eq_heat S x p))
variable (A:ℝ→H.Op)(C:Currency S A)
local notation "d" p:max t:max=> min p t

def escrow (p t:ℝ):= E (p - d p t) * A (d p t) * E (t - d p t)
local notation "GW" => escrow S A
include C
lemma cash_out (s p t:ℝ)(q:0 < s)(u:s≤p)(v:s≤t): GW p t= E (p-s)*A s* E (t-s):=by
 let h:=min p t; have hv:s≤h := le_min u v; unfold escrow
 let b:=E (min p t - s); rw [C _ _ q hv, mul_assoc _ _ (E (t - min p t))] -- tune
 change E (p-h)* (E (h-s)*A s * E (h-s)*E (t-h)) = _
 simp only [mul_assoc]
 rw [← mul_assoc (E (p-h)),elast_comes S (p-h) (h-s) (sub_nonneg.mpr (min_le_left ..)) (sub_nonneg.mpr hv),sub_add_sub_cancel,elast_comes S (h-s) (t-h) (sub_nonneg.mpr hv) (sub_nonneg.mpr (min_le_right ..)),add_comm (h-s),sub_add_sub_cancel]
lemma cash_loc {p:ℝ×ℝ}(t:0<p.1)(u:0<p.2): ContinuousAt (uncurry GW) p:=by
 let s:=min p.1 p.2/2; have v:0 < s:=div_pos (lt_min t u) zero_lt_two; have hs:s < min p.1 p.2:= half_lt_self (lt_min t u); have k:= lt_of_lt_of_le hs (min_le_left p.1 p.2); have k':= lt_of_lt_of_le hs (min_le_right p.1 p.2)
 let R(b:ℝ×ℝ):= E (b.1-s)* A s*E (b.2-s); have h:ContinuousAt R p := ((show ContinuousAt (fun b:ℝ×ℝ=>E (b.1-s)) p from (elast_good S (sub_pos.mpr k)).comp (f:=fun b:ℝ×ℝ=>b.1-s) ((continuous_fst.sub continuous_const).continuousAt)).mul continuousAt_const).mul (show ContinuousAt (fun b:ℝ×ℝ=>E (b.2-s)) p from (elast_good S (sub_pos.mpr k')).comp (f:=fun b:ℝ×ℝ=>b.2-s) ((continuous_snd.sub continuous_const).continuousAt))
 apply h.congr; filter_upwards [continuous_fst.continuousAt.eventually (lt_mem_nhds k),continuous_snd.continuousAt.eventually (lt_mem_nhds k')] with g t u; exact (cash_out S A C s _ _ v t.le u.le).symm -- arguments
lemma fortune {v w t:ℝ}(p:0<t)(h:0<v)(q:0<w): E v*A t* E w= E t*GW v w*E t:=by
 calc
  _ = GW (v+t) (w+t):=by rw [cash_out S A C t _ _ p (le_add_of_nonneg_left h.le) (le_add_of_nonneg_left q.le),add_sub_cancel_right,add_sub_cancel_right]
  _= _:=by
    let u:=min v w; have hu:0< u:= lt_min h q
    have hv:u≤ v:=min_le_left ..; have hw:u≤ w:=min_le_right ..
    rw [cash_out S A C u _ _ hu (hv.trans (le_add_of_nonneg_right p.le)) (hw.trans (le_add_of_nonneg_right p.le)),cash_out S A C u _ _ hu hv hw,mul_assoc (E t)] -- tune
    simp only [mul_assoc]
    rw [elast_comes S (w-u) t (sub_nonneg.mpr hw) p.le,show w+t-u=w-u+t from by abel,show v+t-u=t+(v-u) from by abel, ← elast_comes S t _ p.le (sub_nonneg.mpr hv),mul_assoc]
end YM.SatinJets
