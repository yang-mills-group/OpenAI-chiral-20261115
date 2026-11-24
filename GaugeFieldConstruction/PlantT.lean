import GaugeFieldConstruction.Plough
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Heliac
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
open Dial Nacre Ember Fir Fock
open Work.F03 Taxi TableF Bank HushP ModuleB Flot RG Hake
open Layout Fren
local instance(I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance(I:Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
open Module
-- split books. Norm long charge over powers
variable (Y: Flounces n) {h a c v:ℝ}
abbrev pruneF (w:ℕ): Flounces n:= fun i=>if i.card ≤ w then Y i else 0
def partF(w:ℕ): Flounces n:= Y-pruneF Y w
lemma partX(w:ℕ)(i:Hubber n):partF Y w i=if w < i.card then Y i else 0:=by unfold partF; simp only [Pi.sub_apply,pruneF]; split <;> split <;> first | omega|simp
lemma cut_book(w:ℕ)(F: Torches n)(U: LegTax F): LegTax (F.1,pruneF F.2 w)∧ LegTax ((0:Paper n),partF F.2 w):=by
 refine ⟨⟨U.1,fun i=>?_⟩,port_Z,fun i=>?_⟩
 · unfold pruneF; simp only; split; exact U.2 i; exact port_Z
 change portable (partF F.2 w i); rw [partX]; split; exact U.2 i; exact port_Z
lemma cut_price (w:ℕ)(g:TraceD p o h a Y c): TraceD p o h a (pruneF Y w) c:=by
 obtain ⟨U,q,t⟩:=g; refine ⟨U,fun i=>?_,t⟩; unfold pruneF; split
 · exact q i
 exact ⟨track_p track_zero (track_pos (q i).1),fun _=>rfl⟩
lemma long_price (w:ℕ)(b:ℝ)(e:b≤a)(g:TraceD p o h a Y c): TraceD p o h b (partF Y w) (Real.exp ((b-a)*(w:ℝ))* c):=by
 obtain ⟨U,q,t⟩:=g; let R(i:Hubber n):=if w < i.card then U i else 0; refine ⟨R,fun i=>?_,?_⟩
 · rw [partX]; unfold R; split
   · exact q i
   exact ⟨track_zero,fun _=>rfl⟩
 apply le_trans _ (mul_le_mul_of_nonneg_left t (Real.exp_pos _).le); rw [mul_sum]; apply sum_le_sum; intro i _; unfold R; split
 next p=> rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (track_pos (q i).1); unfold Branch.rent; rw [← Real.exp_add]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonpos_left (Nat.cast_le.mpr p.le) (sub_nonpos.mpr e)]
 rw [mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (track_pos (q i).1))
abbrev trunc_T (w:ℕ)(F:Torches n):Torches n:=(F.1,pruneF F.2 w)
abbrev long_T(w:ℕ)(F:Torches n):Torches n:=(0,partF F.2 w)
lemma cabinT (w:ℕ)(F:Torches n){M:Male}{W:Waves}(p':Portage F o p h a W M c v): Portage (trunc_T w F) o p h a W M c v:= ⟨⟨p'.fare.1,cut_price _ _ _ p'.fare.2⟩,(cut_book _ _ p'.legal).1,p'.port,p'.post⟩
lemma driftT(F:Torches n)(w:ℕ)(b:ℝ)(e:b≤a)(M:Male)(u:LegTax F)(t:TraceD p o h a F.2 c):Portage (long_T w F) o p h b 0 M 0 (Real.exp ((b-a)*(w:ℝ))*c):=⟨⟨track_zero,long_price _ _ _ _ e t⟩,(cut_book _ _ u).2,(Blank_z (M:=M) (a:=0)).port,(Blank_z (M:=M) (a:=0) (h:=h) (p:=p) (o:=o)).post⟩
lemma re_J(w:ℕ)(F:Torches n): trunc_T w F+long_T w F=F:=Prod.ext (add_zero _) (by change pruneF _ w+(F.2-_)=_; abel) -- tune
lemma tr_F(w:ℕ)(s:Sweep n)(F:Torches n): tiro s (trunc_T w F)= trunc_T w (tiro s F):=by
 apply Prod.ext; · rfl
 funext i; let K:=nCap s; let Y:=K.symm i; change Barber s (pruneF _ _ Y)=pruneF (tiro s F).2 w i; unfold pruneF; rw [show Y.card=i.card from card_map ..]; split; rfl; exact bornØ s
lemma tr_L(w:ℕ)(s:Sweep n)(F:Torches n):tiro s (long_T w F)=long_T w (tiro s F):=by
 apply add_left_cancel (a:=tiro s (trunc_T w F)); rw [←tiro_add,re_J,tr_F,re_J]
omit o
open Filter
lemma tail_W (L: Side)(p:1<L.val)(a b:ℝ)(e:a < b): ∀ᶠ w:ℕ in atTop, let W:= (L.val:ℝ)^((w:ℝ)/3); Real.exp ((L.val:ℝ)^((w:ℝ)/4)) * Real.exp ((a-b)*(↑(⌊W⌋₊):ℝ)) ≤1:=by
 let Q:ℝ:=L.val; have hQ:1<Q:=by change 1<(L.val:ℝ); exact_mod_cast p
 let A:=(Q ^ ((1:ℝ)/3)); let B:=(Q ^ ((1:ℝ)/4))
 have ha:1<B:=Real.one_lt_rpow hQ (by norm_num)
 have hb:B<A:=Real.rpow_lt_rpow_of_exponent_lt hQ (by norm_num)
 have ht:0<A:= (zero_lt_one.trans ha).trans hb
 let t(w:ℕ):=(B/A)^w; have he:Tendsto t atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (zero_lt_one.trans ha).le ht.le) ((div_lt_one ht).mpr hb)
 filter_upwards [he.eventually (gt_mem_nhds (show 0<(b-a)*(1/2) from mul_pos (sub_pos.mpr e) (by norm_num))), (tendsto_pow_atTop_atTop_of_one_lt (ha.trans hb)).eventually_ge_atTop 2] with w hw hp
 intro Y; have hp' :A^w/2 ≤ (⌊A^w⌋₊:ℝ) :=by have he:=Nat.lt_floor_add_one (A^w); linarith
 have hu(k:ℝ): Q^((w:ℝ)/k)=(Q ^ ((1:ℝ)/k))^w:=by rw [show (w:ℝ)/k=(1/k)*(w:ℝ) from (by ring),Real.rpow_mul (zero_lt_one.trans hQ|>.le),Real.rpow_natCast]
 change Real.exp (Q^((w:ℝ)/4)) * _ ≤ _; rw [← Real.exp_add,Real.exp_le_one_iff,hu 4]; change B^w+_ ≤ _; change t w < _ at hw; have hk:t w=B^w / A^w:= div_pow ..; rw [hk,div_lt_iff₀ (pow_pos ht w)] at hw; rw [show Y=A^w from hu 3]; linarith only [hw,mul_le_mul_of_nonneg_left hp' (sub_nonneg.mpr e.le)]
end MastTin
end YM.CF.XGarden
end
