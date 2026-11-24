import GaugeFieldConstruction.Nandin
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
open Rush
-- anchor costs on this chart.
open QuadClock Vault
variable (p)(M:Male) (h) (o: Skye.Seat n)
abbrev buoyB(s:Sweep n)(p:BudgetPoint)(M:Male)(h:ℝ)(o:Skye.Seat n)(f:Waves):= αPress (sh s⁻¹ o) M p (Mason s⁻¹ f) h
abbrev facetW(s:Sweep n)(p:BudgetPoint)(M:Male)(h:ℝ)(o:Skye.Seat n)(f:Waves):= WakeQ s (buoyB s p M h o f) -- binder order tune
-- pay uniform bank pre-L.
abbrev EarlyP_0:= {mindChart with power:= 2, power_ge:=le_rfl : BudgetPoint}
abbrev earlyBank:ℝ:=max |Turnp mindChart| |Turnp EarlyP_0|
lemma EBZ:0 ≤ earlyBank := (abs_nonneg _).trans (le_max_left ..)
lemma retention (v:p.power≤3)(w:p.order≤6):Turnp p ≤ earlyBank:=by
 have ht:p.power=2∨p.power=3:=by have he:=p.power_ge; omega
 unfold earlyBank; have he:p.order=6:=le_antisymm w p.order_ge;
 rcases ht with x|x
 · rw [show Turnp p=Turnp EarlyP_0 from (by unfold Turnp; rw [x,he]; try rfl)]; exact (le_abs_self _).trans (le_max_right ..)
 rw [show Turnp p=Turnp mindChart from (by unfold Turnp; rw [x,he])]; exact (le_abs_self _).trans (le_max_left ..)
lemma payY_a (u:Waves)(t:ℂ): Mason s (t • u)=payZ s t • Mason s u:= sheen_p ..
lemma azimuth(t:Sweep n): sh t (sh s o)=sh (s*t) o:=congrArg (fun X:Scree.Hub n=>X.val.1) (push_sum (X:=Zhub o) s t).symm
lemma azBack : sh s (sh s⁻¹ o)=o:=by nth_rw 1 [← inv_inv s]; exact shiftback ..
lemma stryde (t:Sweep n)(F:InkD n): WakeQ t (WakeQ s F)= WakeQ (s*t) F:= T_uni (s*t) (T_comp s t (Wake_acts ..) (Wake_acts ..))
lemma sh_Pi(t:Sweep n)(V:Waves):Mason (s*t)⁻¹ (Mason t V)= Mason s⁻¹ V:=by rw [lands_t, mul_inv_rev]; simp
lemma mete(t:Sweep n)(f:Waves):Turns t (facetW s p M h o f) (facetW (s*t) p M h (sh t o) (Mason t f)):=by
 have he: sh (s*t)⁻¹ (sh t o)=sh s⁻¹ o:=by rw [azimuth,mul_inv_rev, ← mul_assoc,mul_inv_cancel,one_mul]
 suffices H: WakeQ t (facetW s p M h o f)=facetW (s*t) p M h (sh t o) (Mason t f) by rw [←H]; exact Wake_acts ..
 unfold facetW; rw [stryde]; unfold buoyB; rw [he, sh_Pi]
abbrev Hcost:=earlyBank*tilos
variable {o p M h}
lemma HC_pos : 0≤Hcost:= mul_nonneg EBZ (abs_nonneg _)
set_option maxHeartbeats 180000 in
lemma paidW (f:Waves)(u:300<n.val)(v:0<h)(hP:p.power≤3)(e:p.order ≤6): PressB p (Zhub o) (facetW s p M h o f) h (Hcost*‖f‖) ∧ MetaB o M f (facetW s p M h o f) p h∧ lifeH (facetW s p M h o f) 1=0:=by
 let z:= sh s⁻¹ o; let X:= Mason s⁻¹ f; let T:= αPress z M p X h; let Y:= WakeQ s T;
 have ht:= dose_E s M z X u v hP e; have hp:= rent_μ z s X M (lt_trans (by norm_num) u) hP e v; have hy:sh s z=o:= azBack s o; rw [hy] at ht hp;
 have hg: Mason s X=f:=by unfold X; rw [lands_t,inv_mul_cancel,lands_o]; -- tune
 refine ⟨?_,?_,?_⟩
 · apply lift_PV hp; exact (mul_le_mul (retention p hP e) (sheen_norm s⁻¹.s s⁻¹.charge f) (norm_nonneg X) EBZ).trans_eq (mul_assoc ..|>.symm)
 · rw [hg] at ht; exact ht
 -- Thoughts also Eq unit from Laws . 
 let Z:= (Wake_acts s T).turns 1; rw [Facet.glacial] at Z
 change Pastry.pane (Y 1)=0; rw [show Y 1= _ from Z,HoldS]; change cast_B (wageZ s) (lifeH T 1)=0; rw [show lifeH T 1=_ from skin_C z M p X h,map_zero]
lemma prism_a (x y:Waves)(v:20<n.val)(w:0<h)(hP:p.power≤3)(e:p.order≤6): facetW s p M h o (x+y)=facetW s p M h o x+facetW s p M h o y:=by
 have he: Mason s⁻¹ (x+y)= Mason s⁻¹ x+ Mason s⁻¹ y:= sheen_plus ..; unfold facetW buoyB; rw [he]; let L:= hatchP (sh s⁻¹ o) M w hP e v; rw [← hatch_v _ _ w hP e v (Mason s⁻¹ x + Mason s⁻¹ y), map_add, Wake_add]; rfl -- binder
lemma prism_l (x:Waves)(a:ℂ)(v:20<n.val)(w:0<h)(hP:p.power≤3)(e:p.order≤6): facetW s p M h o (a • x) = a • facetW s p M h o x:=by
 unfold facetW buoyB; rw [payY_a]; let T:=Mason s⁻¹ x; let z:=payZ s⁻¹ a; rw [←hatch_v _ _ w hP e v, map_smul,Wake_smul, warX, mul_inv_cancel, ride_one]; rfl
variable (p M h o)
def shoulder(o:Skye.Seat n)(p:BudgetPoint)(M:Male)(h:ℝ)(f:Waves): InkD n:= ((Fintype.card (Sweep n):ℂ)⁻¹) • ∑ i:Sweep n, facetW i p M h o f
variable {p h o}
lemma mimic {J:Type}(T:Finset J)(V:J→Waves)(C:J→ InkD n)(a:J→ℝ)(P:∀ i∈T, MetaB o M (V i) (C i) p h)(g:∀ i∈T,PressB p (Zhub o) (C i) h (a i))(u:0≤h) : MetaB o M (∑ i∈T,V i) (∑ i∈T,C i) p h:=by
 classical
 induction T using Finset.induction_on with
 | empty=>simp only [sum_empty]; have he: (0:InkD n)=fun _=> hollow 0:=funext fun i=> Subtype.ext (show 0=(0:ℂ) • (1:FC _) from (zero_smul ℂ (1:FC _)).symm); rw [he]; exact linearØ o M _
 | @insert i T v ih=> rw [sum_insert v,sum_insert v]; let k:= fun i (h:i∈T)=>g i (mem_insert_of_mem h); exact linearHU _ _ (P i (mem_insert_self ..)) (ih (fun i t=> P i (mem_insert_of_mem t)) k) u (g i (mem_insert_self ..)) (Larch.prop_sum T C a p h _ k)
lemma mag_h : 0<(Fintype.card (Sweep n):ℝ):= Nat.cast_pos.mpr Fintype.card_pos
lemma mag_c : (Fintype.card (Sweep n):ℂ) ≠ 0:= Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
set_option maxHeartbeats 180000 in
lemma stronghold(v:300<n.val)(w:0<h)(hP:p.power ≤3)(e:p.order ≤6)(f: Waves): MetaB o M f (shoulder o p M h f) p h∧ lifeH (shoulder o p M h f) 1=0∧ PressB p (Zhub o) (shoulder o p M h f) h (Hcost* ‖f‖):=by -- binder order shoulder originally?
 let F(i:Sweep n):= facetW i p M h o f; let V:=∑ i:Sweep n,F i; let h₀:=Hcost*‖f‖; let r(i:Sweep n):=paidW (o:=o) (M:=M) i f v w hP e; let K: PressB p (Zhub o) V h (∑ _i:Sweep n,h₀):= Larch.prop_sum univ F (fun _=>h₀) p h (Zhub o) fun i _=> (r i).1
 let a:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹; let x:=mimic M univ (fun i:Sweep n=> f) F (fun _=> h₀) (fun i _=> (r i).2.1) (fun i _=> (r i).1) w.le; refine ⟨?_, ?_,?_ ⟩
 · have he:= linearHE o M (F:=∑ _i:Sweep n,f) (T:=V) (a:=∑ _i:Sweep n,h₀) x K a w.le
   have hh:a • (∑ _i:Sweep n,f)=f:=by
      exact (show ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](k:E),a • (∑ _i:Sweep n,k)=k from fun {_} _ _ v=> by rw [sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, show a*_ = 1 from inv_mul_cancel₀ mag_c, one_smul]) f
   rw [hh] at he; exact he
 · change lifeH (a • V) 1=0; rw [life_smul]; have he: lifeH V 1=0:=by unfold V; rw [lifeSum,Finset.sum_apply]; exact sum_eq_zero (fun i _=> (r i).2.2)
   simp [Pi.smul_apply,he]
 apply lift_PV (Roots.súe _ V K a)
 apply le_of_eq; unfold a; rw [norm_inv, show (Fintype.card (Sweep n):ℂ)= ↑(Fintype.card (Sweep n):ℝ) from (by push_cast; rfl),Complex.norm_real, Real.norm_of_nonneg mag_h.le,sum_const,card_univ,nsmul_eq_mul]; unfold h₀; rw [←mul_assoc,inv_mul_cancel₀ mag_h.ne',one_mul]
variable (o)
lemma TsV(f:Waves)(p:BudgetPoint)(h:ℝ): Turns s (shoulder o p M h f) (shoulder (sh s o) p M h (Mason s f)):=by
 constructor; intro W; unfold shoulder; simp only [Pi.smul_apply,Finset.sum_apply, scar_y, map_sum]
 let a:ℂ:=(Fintype.card (Sweep n):ℂ)⁻¹; rw [show payZ s a=a from ?_]; swap; · unfold payZ; cases wageZ s; rfl; change (starRingEnd ℂ) a=a; simp [a]
 apply congrArg (a • ·); symm; let L:= facetW (n:=n); exact Fintype.sum_equiv (Equiv.mulRight s) _ _ fun i=> (Turns.turns (show Turns s (L i p M h o f) (L (i*s) p M h (sh s o) (Mason s f)) from mete ..) W).symm
variable (v:20<n.val)(u:0<h)(w:p.power≤3)(e:p.order ≤6)
set_option maxHeartbeats 220000 in
def incumb : Waves→ₗ[ℂ] InkD n where
 toFun f:= shoulder o p M h f
 map_add' x y:=by unfold shoulder; simp_rw [prism_a _ _ _ v u w e, Finset.sum_add_distrib,smul_add] -- tune
 map_smul' t x:=by unfold shoulder; simp_rw [prism_l _ _ _ v u w e,←smul_sum]; rw [RingHom.id_apply]; exact smul_comm ..
include v u w e
set_option maxHeartbeats 220000 in
lemma IncPay(t:300<n.val)(f:Waves): let Q:= incumb M o v u w e f
 PressB p (Zhub o) Q h (Hcost*‖f‖)∧ MetaB o M f Q p h∧ lifeH Q 1=0:=by
 intro Q; have hp:= stronghold (o:=o) M t u w e f; exact ⟨hp.2.2,hp.1,hp.2.1⟩ -- tune
set_option maxHeartbeats 220000 in
lemma IncMove (f: Waves) : Turns s (incumb M o v u w e f) (incumb M (sh s o) v u w e (Mason s f)):= TsV .. -- tune
lemma Preservation {Q T: InkD n}{c d:ℝ}{F Z:Waves}(e' :PressB p X Q h c)(μ:PressB p (moveHub s X) T h d)(l:100<n.val)(m:Nonwrapping X.val.2 X.val.1) (V: Turns s Q T) (hx:MetaB X.val.1 M F Q p h)(hz:MetaB (sh s X.val.1) M Z T p h): Z=Mason s F:=metaUnique (sh s X.val.1) M T p h Z _ hz (fℓies s M _ e' μ V u.le _ hx l m)
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
