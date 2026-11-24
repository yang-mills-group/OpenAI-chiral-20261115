import Quarry.Jet
import Zephyr.Bed
import Quarry.Kernel

set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology CF Tulip Cube Lat Tenant Drapes Branch Buffered
open Swell StressExchange Fock Finset Skye Scree
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

variable {N : Side}
local notation "Ω" => Single N

lemma millTr (x : Cover)(P : Op (Single N)) : (P*millQ (wrap N x)).trace = ∑ i:IS, P (tag N x i) (tag N x i) := by
  rw [mill_house]; unfold houseW Matrix.trace cutM inhabit
  change (∑ i:Ω,(P * cutM (inhabit (wrap N x))) i i) = _
  simp_rw [cutM,Matrix.mul_diagonal]
  change (∑ i:(Site N × SpinIdx) × SU.Slot, _ )= _
  -- sum choose row represented by exact wrap
  simp only [Fintype.sum_prod_type, tag,IS]
  rw [sum_comm (s:=(univ:Finset (Site N))) (t:=(univ:Finset SpinIdx))]
  apply sum_congr rfl; intro i _
  rw [Finset.sum_eq_single_of_mem (wrap N x) (mem_univ _)]
  · apply sum_congr rfl; intro b _; simp [inhabit]
  intro b p t; simp [inhabit,t]

variable (P : Afterglow.Tower.VacuumSelection.Spine)
open Py Py.Rate LocalLimit Preparation Afterglow.Tower.VacuumSelection Vow

/-- Variant of the SprigFee interface prepared to sum over this block, NOT losing
    post-purchases. This is on the exact per-site jet, even before Tape use. -/
def prismChip (i k s : ℕ) (z : Cover) (m : ℕ) (L : List Axis) (t : ℝ) : ℂ :=
  let N := age P.run i s
  let M := Dial.spar P.par.K.j (blood P.run i k s) (petals (stream N) t)
  let B := squareSum millQ m L (wrap N z)
  ((M-Dial.tickA N)*B).trace
local notation "Pr" => P.par

lemma prism_nil (m i k s : ℕ) (x : Cover) : prismChip P i k s x m [] =
    sparSite (N:=age P.run i s) P.par.K.j (blood P.run i k s) x +
      Function.const _ (- ((Dial.tickA _)*millQ (wrap (age P.run i s) x)).trace) := by
  funext v
  dsimp only [prismChip]; rw [sub_mul,Matrix.trace_sub, sub_eq_add_neg]
  exact congrArg (fun h:ℂ => h+_) (millTr x _)

abbrev walkUp (z : Cover) (m : ℕ) (a : Axis) (n : ℕ) : Cover := z - m • step a + (n+1) • step a
lemma prism_cons (i k s : ℕ) (m : ℕ) (a : Axis) (L : List Axis) (x : Cover) (r : ℝ) :
    prismChip P i k s x m (a::L) r = ∑ n∈range (2*m), prismChip P i k s (walkUp x m a n) m L r := by
  dsimp only [prismChip]
  rw [squareSum,stripSum, mul_sum, Matrix.trace_sum]; apply sum_congr rfl; intro i _
  simp only [walkUp,map_add,map_sub,map_nsmul,wrap_step,moveSite]

/-- Pay the actual top-bill at this Pose. -/
theorem harvestFull (SP : SprigFee P)(z : Cover)(m : ℕ)(t : 0 < m)(L : List Axis) :
    ∃ d:ℝ, 0<d ∧ ∀ᶠ s:ℕ in atTop, ∀ i k : ℕ, let f := prismChip P i k s z m L;
                                              Bud f ∧ d < (bud f 2).re := by
  induction L generalizing z with
  | nil=>
    obtain ⟨d,h,p⟩ := SP.actual z; refine ⟨d,h,?_⟩
    filter_upwards [p] with s p i k
    dsimp only
    rw [prism_nil]; exact p i k _
  | cons a L IH =>
    choose d e F using fun j : ℕ => IH (walkUp z m a j)
    have hz : 0∈range (2*m) := by simp [t]
    refine ⟨d 0,e 0,?_⟩
    filter_upwards [(eventually_all_finset (range (2*m))).mpr (fun n _=> F n)] with s hs i k
    dsimp only
    rw [funext (prism_cons P i k s m a L z)]
    let B(n:ℕ) := bud (prismChip P i k s (walkUp z m a n) m L)
    have b := Bloom.sum _ (fun n v => ((hs n v i k).1).bloom)
    rw [b.bud_eq, Finset.sum_apply, Complex.re_sum]; refine ⟨b.1,(hs 0 hz i k).2.trans_le ?_⟩
    exact single_le_sum (f:=fun n => (B n 2).re) (fun i w => (le_of_lt ((e i).trans (hs i w _ _|>.2)))) hz

open RG Vale
local notation "N" i:max s:max => cell (P.run.ir i) (Pr).block (Pr).R.L s
local notation "BIG" i:max k:max s:max => RootBook P.run i k s
local notation "poses" => List.ofFn (id:Axis→Axis)

variable (z : Cover) (i k s : ℕ) (m : ℕ)

abbrev colorsTest (X : SOp (cell (P.run.ir i) P.par.block P.par.R.L s)) : ℝ → ℂ :=
  let R := RootBook P.run i k s
  (topChip R.p ((P.run.voyage i).CapeT s) (wrap (N i s) z) X) ∘ petals (stream _)

lemma lightProbe {a c u v : ℝ}{J T X Z V}(p : Counterfoil P.run s i k m a c u v (wrap (age P.run i s) z) J T X Z V) :
    prismChip P i k s z m poses =ᶠ[𝓝 0]
      fun x => colorsTest P z i k s X x + turn Z (stream _) x := by
  obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,hp,p',u,v,q,S,T,X0,g,k_,z',t,Q⟩ := p.study
  have dP := (Pr).dpos
  let N' := age P.run i s; let K := (P.run.voyage i).CapeT s
  let Q' := BIG i k s; let R := Q'.p; let y := wrap N' z; let Nν := stream N'
  have pX : colorsTest P z i k s X =ᶠ[𝓝 0] turn X Nν := germ_turn R Nν y X hp p'
  filter_upwards [petals_open dP Nν,pX] with x h H
  let V := profile (petals Nν x); let P' := funde P.par.K.j Q'.J.M N'
  have e: (P' V-Dial.tickA _)*windmill y m=X V+Z V := t ⟨V,h⟩
  change Matrix.trace ((P' V- _)*windmill y m)=colorsTest P z i _ s X x + Matrix.trace (Z V)
  rw [e,Matrix.trace_add, H]; rfl

lemma CounterRun {a c u v : ℝ}{J T X Z V}(p : Counterfoil P.run s i k m a c u v (wrap (age P.run i s) z) J T X Z V) :
    let w:= (BIG i k s).p.B/10
    Bud (colorsTest P z i k s X) ∧ Bud (turn Z (stream _)) ∧
        bud (prismChip P i k s z m poses)=bud (colorsTest P z i k s X) + bud (turn Z (stream _)) ∧
        ∀ (W:ℝ) (_:Oily a P.par.d (breadth z) W) (k:Fin 3), ‖bud (turn Z (stream _)) k‖ ≤ W*(Real.exp (-a*(w:ℝ))*c) := by
  have H := lightProbe P z i k s m p
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,B,l,b,c',h,d,F,J,Pz,q,-⟩ := p.study
  let N' := age P.run i s; let x := stream N'; let y := wrap N' z
  have t : Bud (colorsTest P z i k s X) := ((turn_sol (soak_sole Pz.pay) (Pr).dpos x).congr (germ_turn _ x y X B l)).1
  have hz := (turn_sol (soak_sole q) (Pr).dpos x).1
  exact ⟨t,hz,((t.bloom.add hz.bloom).congr H).bud_eq,fun W w k=>turn_bound q (deep_grace z) w k⟩
-- make eventual uniform at all volumes for actual X

local notation "ξ" s:max => Vale.hat (Pr).R.L (Pr).x s

lemma small_chip (a c W d:ℝ)(h:0<a)(g:0<d):
    ∀ᶠ s:ℕ in atTop, W*(Real.exp (-a*((Pressure.radiusB (ξ s) /10 : ℕ):ℝ))*c) < d := by
  have T : Tendsto (fun s:ℕ => Pressure.radiusB (ξ s) / 10) atTop atTop := by
    refine tendsto_atTop.mpr fun i : ℕ => ?_
    filter_upwards [(Work.E01.radiusB_tendsto.comp (turnover (Pr))).eventually_ge_atTop (i*10)] with k p
    change i*10≤Pressure.radiusB (ξ k) at p; omega
  have U := (((Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop h
    (tendsto_natCast_atTop_atTop.comp T))).mul_const c).const_mul W)
  simpa only [Function.comp_def, neg_mul, mul_zero, zero_mul, eventually_map] using U.eventually (gt_mem_nhds (by simpa using g))

theorem paid_turn (SP : SprigFee P) (t : 0 < m)(a c : ℝ)(h : 0<a) :
    ∃ d : ℝ, 0<d ∧ ∀ᶠ s:ℕ in atTop, ∀ (i k : ℕ) {u v : ℝ} {J T X Z V},
      Counterfoil P.run s i k m a c u v (wrap (age P.run i s) z) J T X Z V →
      Bud (colorsTest P z i k s X) ∧ d < (bud (colorsTest P z i k s X) 2).re := by
  obtain ⟨d,e,L⟩ := harvestFull P SP z m t (List.ofFn (id:Axis→Axis))
  obtain ⟨W,⟨w⟩⟩ := oily h P.par.dpos (breadth z)
  refine ⟨d/2, half_pos e,?_⟩
  filter_upwards [L, small_chip P a c W _ h (half_pos e)] with s M p i k u v J T X Z V q
  obtain ⟨q₁,q₂,t,F⟩ := CounterRun P z i k s m q
  refine ⟨q₁,?_⟩
  have ht := ((Complex.re_le_norm _).trans (F W w 2))
  have B := (M i k).2; have H : (BIG i k s).p.B=Pressure.radiusB (ξ s) := q.study.2.2.1
  rw [H] at ht; rw [t,Pi.add_apply,Complex.add_re] at B; linarith only [B, ht, p]
end Zephyr.Chern
