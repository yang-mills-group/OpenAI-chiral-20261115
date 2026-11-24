import Bay.D.Quavers
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
local notation "T4"=>SU.group
open Buffered Py Py.Rate LocalLimit Preparation Buffered.Afterglow
open Tower VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

open SlabMark MeshClock

open Journey Papal
variable (P:VacuumSelection.Spine)
local notation "K" => P.calibration

structure Row (i k:ℕ→ℕ): Prop where
 growing:Tendsto i atTop atTop
 cooling:Tendsto k atTop atTop
 rate(s){f}:TestFamily K true f → Tendsto (fun r=>Journey.sharp P.run P.large s (i r) (k r) f) atTop (𝓝 (P.E s f))
 reaches (s):∀ᶠ n:ℕ in atTop,Ferry P.run s (i n) (k n)

lemma row_shifts {i k p:ℕ→ℕ}(h:Row P i k)(g:Tendsto p atTop atTop):
 Row P (i∘p) (k∘p):=⟨h.growing.comp g,h.cooling.comp g,fun s _ a=>(h.rate s a).comp g,fun s=>g.eventually (h.reaches s)⟩

lemma firstRow (π:ℕ→ℕ)(p:Tendsto π atTop atTop)
 (h:∀ᶠ r in atTop, legacy P.run (P.period r) (P.cutoff (π r))) :
 Row P P.period (P.cutoff∘π):=by
 refine ⟨P.law.pick.grow_i.tendsto_atTop, P.law.pick.grow_k.tendsto_atTop.comp p, fun s f t=>
    (P.law.together s f t).paths π h,fun s=>?_⟩
 filter_upwards [floor_pays _ _ P.law s, h] with i f r
 exact f _ r

lemma therapist {m n:Side}(e:m=n){M:Mark m}{a:ℝ}
 (h:Envelope M)(u:∀x,‖M x‖≤a): let f:Mark n:= e ▸ M; Envelope f ∧ ∀x,‖f x‖ ≤a:=by subst n; exact ⟨h,u⟩

variable (s:ℕ){i k:ℕ→ℕ}
lemma strength (p:Row P i k) (S:Finset Cover):
 ∃C> (0:ℝ),∀ᶠ n:ℕ in atTop, ∀ (x:Buffered.Family K),InTest K true S false x →
    ∀a,Tower.pay x a → ‖Journey.sharp P.run P.large s (i n) (k n) x‖≤C*a:=by
 obtain ⟨d,v⟩:=Tower.sizes S
 let Y:=P.run
 let B:=Tower.Grip Y P.large s d
 have h:0<B:=Real.exp_pos _
 refine ⟨1+B,by positivity,?_⟩
 filter_upwards [p.growing.eventually (Tower.tandem _ _ s d),p.cooling.eventually (thaw_plot Y 1 one_pos s),p.reaches s]
    with n b g q x y a r
 have e:‖hot P.run P.large s (i n) (k n) x‖ ≤ B*a:=by
    have u:= b (k n) q y (show InTest K true ∅ false 1 from InTest.one) v
      (fun t=>⟨0,by simp⟩) a 1 r Tower.pay_unit
    simpa only [mul_one,B,Y] using u
 have w:‖ Journey.sharp P.run P.large s (i n) (k n) x - hot P.run P.large s (i n) (k n) x‖ ≤a:=by
    rw[hot,dif_pos q.depth]

    obtain ⟨I,R⟩:= therapist (Journey.terrain Y P.large (Y.ir (i n)) s)
       (y.support (momentm Y (i n) s)).env (r _)
    exact le_trans (g _ q.depth _ a I R) (one_mul a).le
 rw [add_mul,one_mul]
 exact le_trans (norm_le_norm_sub_add ..) (add_le_add w e)

lemma quickens {S:Finset Cover} {f:ℕ→ Buffered.Family K} {g:Buffered.Family K}
 (p:Row P i k) (t:BQueue S f g): Tendsto
   (fun r=> Journey.sharp P.run P.large s (i r) (k r) (f r)) atTop (𝓝 (P.E s g)):=by
 obtain ⟨C,h,v⟩:=strength P s p S
 let e:=p.rate s (aux_test t.landing)
 rw [Metric.tendsto_nhds]
 intro ε hε
 filter_upwards [t.saved (ε/2/C) (by positivity),v,p.reaches s, Metric.tendsto_nhds.mp e (ε/2) (by positivity)] with n w u j l
 have q:=u _ (Tower.InTest.subOp (t.whereTo n) t.landing) _ w
 rw [sharp_sub _ _ _ (aux_test (t.whereTo n)) (aux_test t.landing) j,
     mul_div_cancel₀ _ h.ne'] at q
 refine lt_of_le_of_lt (dist_triangle _ (Journey.sharp P.run P.large s (i n) (k n) g) _) ?_

 exact lt_of_le_of_lt
   (add_le_add ((dist_eq_norm ..).le.trans q) le_rfl) (by linarith only [l])

lemma songqueue
   {K': Calibration} {S:Finset Cover}
   {G:ℕ→ Buffered.Family K'} {f:Buffered.Family K'} (j:Axis) (r:ℕ)
   (h:BQueue S G f) (n:ℕ):
 ∃ T,BQueue T (fun i=>singing K' j r (G i) n) (singing K' j r f n):=by
 induction n with
 | zero=>simp only[singing];exact ⟨_,h⟩
 | succ n ih=>
   obtain ⟨T,u⟩:=ih
   simp only[singing,bow]
   exact ⟨_,BQueue.station j _ (BQueue.multiply (u.revolve j _) u)⟩
