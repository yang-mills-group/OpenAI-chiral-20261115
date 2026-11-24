import SatinPP.Roll

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid

noncomputable abbrev pageB := (∑ i:Axis,frameRadius i) + P.sidesPerTick+1
noncomputable abbrev pageChoice(f:ℕ):= P.pageB * P.baseK f
theorem choice_pos (f:ℕ): 0<P.pageChoice f:=Nat.mul_pos (Nat.succ_pos _) (P.payment_pos _)
noncomputable abbrev gaugeHead:= (16*P.par.block.val)*P.pageB
theorem width_choice(f:ℕ):
    P.pageWidth (P.pageChoice f)=P.gaugeHead * P.baseK f:=
  (Nat.mul_assoc ..).symm

theorem bound_form (s f:ℕ)(l:List Axis):
    let x:=P.rootSpace s f l
    (rural (P.thresholdF f):ℤ) < nodeC x j ∧
     nodeC x j+rural (P.thresholdF f) < P.pageWidth (P.pageChoice f) ∧
     (P.calibration.ℓ:ℤ)+ frameRadius j ≤ nodeC x j ∧
     nodeC x j+ frameRadius j+P.calibration.ℓ ≤ P.pageWidth (P.pageChoice f):= by
  intro x
  let b:=P.baseK f
  have HB: 1≤b:=P.payment_pos _
  have HB' : 1≤P.par.block.val:= P.par.block.property
  let n:=P.pageChoice f
  have hP: P.pageB ≤ n:= Nat.le_mul_of_pos_right _ HB
  have hB: b≤n:=Nat.le_mul_of_pos_left _ (show 0<P.pageB from Nat.succ_pos _)

  have hq:16*n ≤ P.pageWidth n:= by
    unfold pageWidth; rw [Nat.mul_assoc]; gcongr; exact Nat.le_mul_of_pos_left _ HB'
  have he: nodeC x j ≤ (b:ℤ)+(↑(2*frameRadius j+2*P.sidesPerTick:ℕ):ℤ):=P.node_ceiling j f s _
  have ht:= P.broadly j f s l|>.1
  change (↑(P.axleQ j (P.thresholdF f)):ℤ) ≤ x j at ht
  have hy: frameRadius j ≤ ∑ i:Axis, frameRadius i:= Finset.single_le_sum (f:=fun i=>frameRadius i) (fun i _=>Nat.zero_le _) (Finset.mem_univ j)
  have hee: reserve P.par P.width = P.calibration.ℓ:=rfl
  change _∧_∧_∧_
  have hb':= show (16*n:ℕ) ≤ P.pageWidth (P.pageChoice f) from hq
  unfold pageB at hP; unfold b baseK axleQ repeatD at hB; unfold axleQ repeatD at ht
  simp only [nodeC,two_smul,Pi.add_apply,Pi.one_apply]
  simp only [nodeC,two_smul,Pi.add_apply,Pi.one_apply] at he
  have hN: b≤n:=hB
  omega
theorem page_form (s f v:ℕ)(l:List Axis):
    Between P.calibration j 0 (ruler P.par.block * (↑(P.tierScale f v* P.pageChoice f):ℤ))
        (frameOne (P.clockPlate f v (P.rootSpace s f l))) := by
  intro i h
  let X:=P.rootSpace s f l; let u:=P.clockPlate f v X
  obtain ⟨g,_,tκ⟩:= mem_biUnion.mp h; obtain ⟨t,w,rfl⟩:=mem_image.mp tκ
  have ht:(t j).natAbs≤ frameRadius j:= Finset.le_sup (f:=fun x:Cover=> (x j).natAbs) w
  let a:=P.pageWidth (P.pageChoice f)
  let q:ℤ:=P.tierScale f v
  have hq:1≤q:=by
    have t':1≤P.tierScale f v:=pow_pos (P.par.R.L.property) _
    unfold q;exact_mod_cast t'
  have e:u j=q*nodeC X j:=by unfold u clockPlate; rw [Pi.smul_apply,nsmul_eq_mul]
  have e': ruler P.par.block * (↑(P.tierScale f v* P.pageChoice f):ℤ)=q*a:=by
    unfold q a pageWidth ruler; push_cast; ring
  rw [e']
  change 0+_ ≤ t j+u j ∧ t j+u j+_ ≤ _
  obtain ⟨hb,r⟩:= (P.bound_form j s f l).2.2

  change _≤ nodeC X j at hb
  change nodeC X j+_+_ ≤ (a:ℤ) at r
  have h₀: nodeC X j ≤ u j:=by rw [e];exact le_mul_of_one_le_left (by omega) hq
  have h1: (a:ℤ)-nodeC X j≤q*a-u j:=by
    rw [e,←_root_.mul_sub]
    exact le_mul_of_one_le_left (by omega) hq
  omega
local notation "hat!" s:max=>hat P.par.R.L P.par.x s
lemma choice_late :
   ∀ᶠ f in atTop, ∀ s l,
     P.Clearance f (P.pageChoice f) (P.rootSpace s f l) := by
 have h: Worth.Pays 0 0 6 (fun x:ℝ=> ↑P.gaugeHead*(2*(P.axleQ 3 (radiusB x):ℝ)+1)):= Pays.scale _ (plus (Pays.scale 2 (P.width_ledger 3)) (Worth.Pays.merit (constant _) (by norm_num [Worth.Earlier])))
 filter_upwards [P.weather_bill 1 zero_lt_one, (turnover P.par).eventually (leap (w:=0) (p:=1) (q:=0) h (by norm_num [Worth.Earlier]))] with f e g s l
 refine ⟨P.choice_pos f,fun j=>⟨(P.bound_form j s f l).1,(P.bound_form j s f l).2.1⟩,
     P.repeat_shrink e ?_⟩
 rw [P.width_choice,baseK,show P.thresholdF f=radiusB (hat! f) from (P.run.meter.boot f).2.1]
 have t:=g.trans (Nat.le_ceil (trailℓ 1 (hat! f)))
 unfold scout; exact_mod_cast t
/-!
### Sharp enough page pricing for a fifth-power energy estimate
-/

lemma planned_linear :
    ∃ b:ℝ,0<b ∧ ∀ᶠ r:ℕ in atTop,(P.plannedK r:ℝ)≤ b*r:=by
 let L:ℝ:= P.par.R.L.val; have hL:0<L:=by unfold L; exact_mod_cast P.par.R.L.property
 let v:=billX P.par.R.L; have hv:0<v:=P.arc_price; have hx:0<P.par.x:= (Real.exp_pos _).trans_le P.large
 have h: Worth.Pays 0 (P.depthCap) 0 (fun x:ℝ=>L*trailℓ P.depthCap x):= Pays.scale _ (Pays.whole _ _ _)
 refine ⟨P.par.x+v,by linarith,?_⟩
 filter_upwards [P.planned_ceiling,(turnover P.par).eventually (leap (w:=1) (p:=0) (q:=0) h (Or.inl zero_lt_one)), eventually_ge_atTop 1] with r t e g
 rw [coinY (P.f_here r)] at e
 have hr:(1:ℝ) ≤ r:= by exact_mod_cast g
 exact (t.trans e).trans (show P.par.x+r*v ≤ _ from by nlinarith only [mul_le_mul_of_nonneg_left hr hx.le])

noncomputable abbrev menuSize (A:ℝ)(r:ℕ) :=
    let f:=P.pointEra r
    A * P.pageWidth (P.pageChoice f)/ (P.par.R.L.val:ℝ)^f
lemma menu_unfold (A:ℝ)(r:ℕ):
    P.menuSize A r = (A * P.gaugeHead) * (P.plannedK r:ℝ)* ((P.par.R.L.val:ℝ)⁻¹)^r:=by
 let L:ℝ:=P.par.R.L.val; have h:0<L:=by unfold L;exact_mod_cast P.par.R.L.property
 let s:=P.pointEra r
 have hp:s≤r:=Nat.sub_le ..
 have e:L^r=L^(r-s)*L^s:= by rw [←pow_add,Nat.sub_add_cancel hp]
 unfold menuSize plannedK megaK; dsimp -iota only
 rw [P.width_choice,inv_pow]
 push_cast
 change _= _; rw [show (P.par.R.L.val:ℝ)^r=L^_ *L^s from e]
 field_simp -- L coerces both sides unify?

 unfold L s; ring
lemma menu_ceiling (A:ℝ)(u:0<A):
    ∃ b:ℝ,0<b ∧ ∀ᶠ r:ℕ in atTop,0≤P.menuSize A r ∧ P.menuSize A r ≤ b* r*((P.par.R.L.val:ℝ)⁻¹)^r:=by
 obtain ⟨B,t,p⟩:=P.planned_linear
 let c :ℝ:= A * P.gaugeHead
 have hc:0<c:= mul_pos u (Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos (by decide) P.par.block.property) (Nat.succ_pos _)))
 refine ⟨c*B,mul_pos hc t,?_⟩
 filter_upwards [p] with r hr
 rw [P.menu_unfold]
 constructor
 · positivity
 have he:=mul_le_mul_of_nonneg_left hr hc.le
 rw [←mul_assoc] at he
 exact mul_le_mul_of_nonneg_right he (by positivity)

lemma menu_zero {A:ℝ}(u:0<A): Tendsto (P.menuSize A) atTop (𝓝 0):=by
 obtain ⟨B,t,p⟩:=P.menu_ceiling _ u
 let a:ℝ:= (P.par.R.L.val:ℝ)
 have h:1<a:= by unfold a;exact_mod_cast (timeMesh P.par).Llarge
 have t₁:|a⁻¹| < 1:=by simpa [abs_of_nonneg ((show (0:ℝ)<a by linarith only [h]).le)] using inv_lt_one_of_one_lt₀ h
 apply squeeze_zero' (p.mono fun r h=>h.1) (p.mono fun r h=>h.2)
 have ht:= (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 t₁).const_mul B
 simpa only [mul_zero,pow_one,←mul_assoc] using ht
lemma menu_cheap (h:64<P.par.R.L.val){A:ℝ}(u:0<A):
    ∀ᶠ r:ℕ in atTop, (P.menuSize A r)^5 * (zoomC P.par.R.L)^r ≤ 1:=by
 obtain ⟨b,t,p⟩:=P.menu_ceiling _ u
 let L:ℝ:= P.par.R.L.val; have h₁ : 64<L:= by unfold L;exact_mod_cast h
 have h₀:0<L:=by linarith only [h₁]
 have hq:|(L⁻¹)^5 * zoomC P.par.R.L| < 1:=by
    rw [abs_of_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (zoomC_p _)))]
    calc
     _=64/L:=by change ((L⁻¹)^5*(64*L^4))=_;field_simp
     _< 1 := (div_lt_one h₀).mpr h₁
 have ht:= (tendsto_pow_const_mul_const_pow_of_abs_lt_one 5 hq).const_mul (b^5)
 rw [mul_zero] at ht
 filter_upwards [p,ht.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r H0 t
 apply le_trans ?_ t
 refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ H0.1 H0.2 5) (pow_nonneg (zero_le_one.trans (zoomC_p _)) _)).trans_eq ?_
 show ((b*_*L⁻¹^r)^5)*_=_
 ring

/-- Buy any page with thermal half-budget below t, and with zoom amplification
at most B/t^5. Works with any extra cofinite short-height conditions. -/
lemma menu_fifth (h:64<P.par.R.L.val){A:ℝ}(u:0<A)
    {q:ℕ→Prop}(p:∀ᶠ r in atTop,q r) :
    ∃ B:ℝ, 0<B ∧ ∀ t:ℝ,0<t→t≤1→ ∃ r, q r ∧ P.menuSize A r < t ∧
        zoomC P.par.R.L^r ≤ B/t^5:=by
 obtain ⟨s,g⟩:=eventually_atTop.mp (p.and (P.menu_cheap h u))
 let z:=zoomC P.par.R.L; have hz:0<z:= lt_of_lt_of_le zero_lt_one (zoomC_p _)
 refine ⟨z^s+z,by positivity,?_⟩
 intro t t₀ t₁
 have hp:∃r:ℕ,P.menuSize A (s+r)<t:=by
   obtain ⟨i,e,v⟩:= ((P.menu_zero u).eventually (gt_mem_nhds t₀)|>.and (eventually_ge_atTop s)).exists
   exact ⟨i-s,by rw [Nat.add_sub_cancel' v]; exact e⟩
 refine ⟨s+Nat.find hp,(g _ (Nat.le_add_right ..)).1,Nat.find_spec hp,(le_div_iff₀ (by positivity)).mpr ?_⟩
 change z^(s+Nat.find hp)*_ ≤ _
 generalize e:Nat.find hp=n
 cases n with
 | zero=>
    rw [add_zero]
    exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ t₀.le t₁)).trans (le_add_of_nonneg_right hz.le)
 | succ n=>
    have e':=Nat.find_min hp (show n<Nat.find hp from by omega)
    have ht:t≤ P.menuSize A (s+n):= le_of_not_gt e'
    have R: z^(s+n)*t^5 ≤ 1:=by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ t₀.le ht 5) (by positivity)).trans ((g _ (Nat.le_add_right _ n)).2)
    rw [Nat.add_succ,pow_succ',mul_assoc]
    exact (mul_le_of_le_one_right hz.le R).trans (le_add_of_nonneg_left (by positivity))

lemma price_base (h:15∣P.par.R.L.val) (v:P.par.R.L.val % 16=1) :
    64<P.par.R.L.val:= by omega

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
