import WakeRoad.Marigold
import WakeRoad.Dipole
/-! # Seed Hessian of the actual GarlandBook stencil through mask. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke
namespace Spine.Gingham
namespace VoyageB
open Diary CF.Gingham.Ruff GarlandBook Drapes
open Dial
open YM.WakeRoad _root_.Zephyr.Chern
open scoped ContDiff
variable {N:Side}
private lemma beamCart (X:Op (Single N))(o:Site N):
 Matrix.trace (X * WW o) = ∑ j:IS, X ((o,j.1),j.2) ((o,j.1),j.2):=by
 unfold Matrix.trace Matrix.diag
 simp_rw [WWj]
 change (∑ p:(Site N× SpinIdx)×SU.Slot, if p.1.1=o then X p p else 0)=_
 simp only [Fintype.sum_prod_type_right]
 simp

variable (P:Spine)
local notation "R" s:max i:max k:max=>RootBook P.run i k s
local notation "N'" s:max i:max=> Journey.side P.run i s
local notation "Kₜ" s:max i:max k:max=> Gingham.Ruff.prince P.par.K.j (R s i k)
lemma beam_case (i s k:ℕ)(y:Cover):
 (fun t:ℝ=> Matrix.trace (breast (Kₜ s i k) (0+Lattice.wrap (N' s i) y) (profile (petals (_root_.Zephyr.Chern.stream (N' s i)) t))))=
  sparSite P.par.K.j (N:=N' s i) (R s i k).J.M y + Function.const _ (-Matrix.trace (tickA (N' s i)* WW (Lattice.wrap _ y))) :=by
 funext t; rw [zero_add,breast,_root_.sub_mul,Matrix.trace_sub,beamCart,(plume_den ..).1]
 rfl

-- eventually through all purchased tori even since Gram, no s> cutoff needed for this
lemma beam_replies : ∃ d:ℝ,0<d ∧ ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,
   let n:=Journey.side P.run i s
   let f:=fun t:ℝ=>Matrix.trace (yoke (Gingham.Ruff.prince P.par.K.j (RootBook P.run i k s)) (underlay P.par) 0 (profile (petals (_root_.Zephyr.Chern.stream n) t)))
   Bud f ∧ d < (bud f 2).re := by
 choose d hd r using (SprigFee.paid P).actual
 let u:=underlay P.par
 have hx:(0:Cover) ∈ CF.Gingham.Ruff.apron u:= apron_spec.mpr fun i=>by simp;
 refine ⟨d 0,hd 0,?_⟩
 filter_upwards [(Filter.eventually_all_finset (CF.Gingham.Ruff.apron u)).mpr (fun i _=> r i)] with s h i k
 let n:=N' s i
 let K:=Kₜ s i k
 let f:= fun t:ℝ=> Matrix.trace (yoke K u 0 (profile (petals (_root_.Zephyr.Chern.stream n) t)))
 let f₀(x:Cover):=fun t:ℝ=> Matrix.trace (breast K (0+wrap n x) (profile (petals (_root_.Zephyr.Chern.stream n) t)))
 have hf:f=(fun v=>∑ x∈CF.Gingham.Ruff.apron u,f₀ x v):=funext fun v=>by unfold f; rw [yoke_sum, Matrix.trace_sum]
 have he (v:Cover)(p:v∈CF.Gingham.Ruff.apron u): Bud (f₀ v) ∧ d v < (bud (f₀ v) 2).re:=by
    have he:= beam_case P i s k v
    unfold f₀; rw [he]; exact h v p i k _
 let Y:= Bloom.sum (CF.Gingham.Ruff.apron u) (fun i v=> (he i v).1.bloom)
 change Bud f ∧ d 0 < (bud f 2).re
 rw [hf]
 refine ⟨Y.1,?_⟩; rw [Y.bud_eq, Finset.sum_apply,Complex.re_sum]
 exact (he 0 hx).2.trans_le (single_le_sum (fun i v=> ((hd i).trans (he i v).2).le) hx)

variable (a c μ E₀:ℝ)(r₀:ℕ){δ t:ℝ}(X:Rialto 6 P.par.d δ t)(hδ:0<δ)
abbrev auprix(s i k:ℕ)(_p:Scene P a c μ r₀ s i k):Doub (Journey.side P.run i s) → ℂ:= Gingham.Ruff.hum X (fun z=>yoke (Gingham.Ruff.prince P.par.K.j (RootBook P.run i k s)) (underlay P.par) 0 z.val)
local notation "α" p:max=> auprix P a c μ r₀ X _ _ _ p
include hδ

omit hδ in
lemma auprix_top {s i k:ℕ}(p:Scene P a c μ r₀ s i k)(v:Doub (side P.run i s)): Bloom (fun j:ℝ=> (α p) (j • v)) ![(α p) 0, 0,quadraticChi (α p) v]:=by
 have h:0≤a/4:=(div_pos p.gears.tag.1 (by norm_num)).le
 exact bloomLine _ ((Shells.sing X p.gb.pump h) 0 (by simp)).smooth (Shells.sing_flat X p.gb.pump h (by omega)) v

lemma quadratic_burst : ∃ d> (0:ℝ), ∀ᶠ s:ℕ in atTop,∀ i k,∀ p:Scene P a c μ r₀ s i k,
 d < (quadraticChi (auprix P a c μ r₀ X s i k p) (jetColor (side P.run i s) δ)).re:=by
 obtain ⟨d,v,h⟩:=beam_replies P
 refine ⟨d,v,h.mono fun s l i k p=>?_⟩
 specialize l i k
 let y:=jetColor (N' s i) δ
 have t':∀ᶠ b:ℝ in 𝓝 0, ‖b • y‖ < 1:= ((show Continuous (fun b:ℝ=> b • y) from continuous_id.smul continuous_const).norm.tendsto 0).eventually (gt_mem_nhds (by simp))
 have he: (fun t:ℝ=>Matrix.trace (yoke (Kₜ s i k) (underlay P.par) 0 (profile (petals (_root_.Zephyr.Chern.stream (N' s i)) t)))) =ᶠ[𝓝 0] (fun t=> (α p) (t • y)):=by
   filter_upwards [t'] with j v
   change _= Matrix.trace (yoke (Kₜ s i k) (underlay P.par) 0 (profile (dabble δ (j • y))))
   rw [dabble,if_pos (show ‖j • y‖ < 1 from v),cart_pencil j hδ.ne']
 let A:= (auprix_top P a c μ r₀ X p y).congr he
 let f:=fun t:ℝ=> Matrix.trace (yoke (Kₜ s i k) (underlay P.par) 0 (profile (petals (_root_.Zephyr.Chern.stream (N' s i)) t)))
 exact lt_of_lt_of_eq l.2 (congrArg (fun c':_root_.Zephyr.Chern.Three ℂ=> (c' 2).re) A.bud_eq) -- l.2 has HE of Aux? inspect

open Pike
omit hδ in
lemma trunc_paid {a:ℝ}(p:0<a)(c t:ℝ)(u:Side)(B:ℕ→ℕ)(q:Tendsto B atTop atTop): Tendsto (fun s=> Shells.Interest u (a/8) (Pike.waist a c (tenderb (B s))) 2*t^2) atTop (𝓝 0):=by
 have he:Tendsto (fun s=> tenderb (B s)) atTop atTop:= by
   refine tendsto_atTop_atTop.mpr (fun k=>?_); obtain ⟨i,h⟩:= eventually_atTop.mp (q.eventually_ge_atTop (k*200)); exact ⟨i,fun b v=>by have t:=h b v; unfold tenderb; omega⟩
 have h:(0:ℝ)<a/4-a/8:=by linarith
 have H:=(((Real.tendsto_exp_neg_atTop_nhds_zero.comp
   (Tendsto.const_mul_atTop h ( (show Tendsto ((↑):ℕ→ℝ) atTop atTop from tendsto_natCast_atTop_atTop) |>.comp he))).mul_const c).const_mul (Fan.price u (a/8) 2)).mul_const (t^2)
 simpa only [zero_mul,mul_zero,Pike.waist,Shells.Interest, Function.comp_def,neg_mul] using H
variable (V:Anthem P a c μ r₀ δ t X)
local notation "π" s:max=> P.run.meter.a s
abbrev burningF {s i k:ℕ}(p:Scene P a c μ r₀ s i k) := musicA X p.gb.pump (RootBook P.run i k s).p -- try name
lemma reportCard (ha:0<a) (pL: Anthem P a c μ r₀ δ t X): ∃ d> (0:ℝ), ∀ᶠ s:ℕ in atTop,∀ i k,∀ p:Scene P a c μ r₀ s i k,
  let Q:=quadraticChi (burningF P a c μ r₀ X p)
  let n:=Journey.side P.run i s
  d < (Q (jetColor n δ)).re ∧ Bud (p.gb.fountainQ p.bre ∘ _root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream n)) ∧
    d < (bud (p.gb.fountainQ p.bre ∘ _root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream n)) 2).re:=by
 obtain ⟨d,v,H⟩:= quadratic_burst P a c μ r₀ X hδ
 obtain ⟨b,bill⟩:= jetMist δ hδ
 let B (s:ℕ):=(π s).B
 let u:=underlay P.par
 let c':=pepCharge u a c
 have he:Tendsto B atTop atTop:=by
    have h : B = fun s=> Pressure.radiusB (hat P.par.R.L P.par.x s) := funext fun s=> (P.run.meter.boot s).2.1
    rw [h]; exact Work.E01.radiusB_tendsto.comp (turnover P.par)
 refine ⟨d/2,half_pos v,?_⟩
 filter_upwards [pL,H,(trunc_paid ha c' b u B he).eventually (gt_mem_nhds (half_pos v))] with s w h l i k p
 intro Q n
 have t:= (w i k p).1
 have vh:=h i k p
 let q:=burningF P _ c μ r₀ X p
 let V:=jetColor n δ
 have e : (R s i k).p=P.run.meter.a s:= (((P.run.voyage i).X (P.run.uv k)).pull.owns s p.ok.le).width.symm
 have hz: d/2 < (Q V).re :=by
    have yr : ‖quadraticChi (α p) V-Q V‖ ≤ Shells.Interest u (a/8) (Pike.waist a c' (tenderb (R s i k).p.B)) 2*b^2:= by rw [norm_sub_rev]; exact (t.growth V b (bill n)).restK
    have y:= (Complex.re_le_norm (quadraticChi (α p) V-Q V)).trans yr
    rw [e,Complex.sub_re] at y
    change d < (quadraticChi (α p) V).re at vh
    linarith
 let f(t:ℝ) := p.gb.fountainQ p.bre (_root_.Zephyr.Chern.petals (_root_.Zephyr.Chern.stream n) t)
 have eq : f =ᶠ[𝓝 0] (fun t:ℝ=> q (t • V)) := by
    have ht := (t.emerges (fun _=>dustId n));
    have h: Tendsto (fun t:ℝ=>t • V) (𝓝 0) (𝓝 0):= by simpa using (show Continuous (fun t:ℝ=>t • V) from continuous_id.smul continuous_const).tendsto (0:ℝ)
    filter_upwards [h.eventually ht] with t z
    rw [cart_pencil t hδ.ne'] at z
    exact z
 let H':= (bloomLine q (t.gallery 0 (by simp)).smooth t.linear V).congr eq
 exact ⟨hz,H'.1,hz.trans_le (le_of_eq (congrArg (fun c':_root_.Zephyr.Chern.Three ℂ=> (c' 2).re) H'.bud_eq.symm))⟩ -- H'.bud_eq : bud f = ...; symm. 
#print axioms reportCard
