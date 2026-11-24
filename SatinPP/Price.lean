import SatinPP.Jacket
import SatinPP.Menu
import SatinPP.EveryParts
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
local notation "W"=>P.calibration
local notation "Q"=>P.par.block
variable (x:P.Spectrum0 3)
local notation "ξ"=>P.advocate 3 x j
local notation "Y"=>P.physicalEnergy j ξ
local notation "L"=>P.par.R.L.val
local notation "Υ"=>timeMesh P.par


lemma box_stock {w:ℕ} (F:P.Test)(hw:0<w)
    (S:Finset Cover)(b:F∈bay W S true)(t:Between W j 0 (ruler Q*w) S)
    (e:F∈enclave W) (p:P.PaidRolls v w F.val):
    ∃ A:(P.ColorHil j (P.advocate 3 x j)).Op, P.Stock j ξ v w F A ∧ ‖A‖ ≤ 1 ∧
       inner ℂ (P.colorZero j ξ) (A (P.colorZero j ξ)) = P.singleState j v ξ F:=by
 let g:=P.positiveVox j v S F b (fun i h=>(t i h).1)
 let h:P.Card j v w:=⟨g,S,b,t⟩
 let G:=P.door j v w hw h (show P.voxTest j v h.val∈enclave W from e)
 refine ⟨(P.colorSpace j ξ G),stock_door hw h (show P.voxTest j v h.val∈enclave W from e),?_,?_⟩
 · apply (NonUnitalStarAlgHom.norm_apply_le (P.colorSpace j ξ) G).trans
   change ‖P.Box j v w hw h‖ ≤ 1
   exact SlabMark.Bankroll.gets_box _ _ P.law v P.projection j w hw h p _
 rw [show G=_ from rfl, P.attended]
 exact P.view_scalar .. 


/-- Center in this same chosen reading. -/
lemma paid_center {w:ℕ}(F:P.Test)(hw:0<w)
    (S:Finset Cover)(b:F∈bay W S true)(t:Between W j 0 (ruler Q*w) S)
    (e:F∈enclave W) (p:P.PaidRolls v w F.val):
    ∃ A, P.Stock j ξ v w (P.dewy F (P.singleState 3 v x F)) A ∧ ‖A‖ ≤ 2:=by
 obtain ⟨G,u,g,H⟩:=P.box_stock j x F hw S b t e p
 let z:=P.singleState 3 v x F
 let ω:=P.colorZero j ξ
 have h:‖z‖ ≤ 1:=by
    have hw:‖ω‖=1:=by exact P.norms_color ..
    have hy:‖G ω‖≤1:= (G.le_opNorm ω).trans (by rw [hw,mul_one]; exact g)
    unfold z; rw [←P.single_agrees 3 j,← H]
    exact (norm_inner_le_norm _ _).trans (by rw [show ‖P.colorZero j ξ‖=1 from hw,one_mul]; exact hy)
 let T:=(Y).E (whenly Υ v w)
 rw [dewy,sub_eq_add_neg, ←neg_smul]
 change ∃ A, P.Stock j ξ v w (F+(-z) • 1) A ∧ _
 exact ⟨G+(-z) • T,u.plus ((P.stock_one j ξ v w).smul _), (norm_add_le ..).trans (by
    rw [norm_smul,norm_neg]
    exact (add_le_add g (mul_le_one₀ h (norm_nonneg _) ((Y).shrinks _))).trans (le_of_eq (by norm_num)))⟩



lemma localized {A:P.Apron} {w k l:ℕ}{c:ℂ} {d:Cover} (h:A.s=v)(wk:w=l+k)
    (du:d j=(l:ℤ))(hl:A.zoom P v j ≤ l)(hk:A.zoom P v j ≤ k)
    (p:∃ T,P.Stock j ξ v w (c • P.chartAll d (A.full P v)) T ∧ ‖T‖  ≤  2)
    (e:ℝ)(g:bell Υ v w ≤ e):
    ‖c • P.locket j ξ A e e‖  ≤  2:= by
 subst w
 let b:=bell Υ v l
 let a:=bell Υ v k
 have ha:0  ≤  a:=by rw [show a=_ from natural_time ..]; exact NNReal.coe_nonneg _
 have hb:0  ≤  b:=by rw [show b=_ from natural_time ..]; exact NNReal.coe_nonneg _
 have he:b + a  ≤  e:=by simpa [a,b,bell,_root_.add_mul] using g
 have hbk:A.realWidth P j ≤ b:=by
    rw [←A.zoom_bell P j v h.le]; exact (bell_le Υ v _ _).mpr (by exact_mod_cast hl)
 have hak:A.realWidth P j ≤ a:=by
    rw [←A.zoom_bell P j v h.le]; exact (bell_le Υ v _ _).mpr (by exact_mod_cast hk)
 let A₀:=P.locket j ξ A b a
 rw [P.widen_locket j ξ A hbk hak (le_trans (by linarith only [ha]) he) (le_trans (by linarith only [hb]) he),←map_smul]
 apply (jacket_cost ..).trans
 refine (P.charter_ge j ξ (P.vtile v d) _).trans ?_
 obtain ⟨T,hT,u⟩:=p

 have ht:= (P.transport_stock j ξ A v d h.le hl hk).smul c
 rw [du, sub_self,P.shifts_zero] at ht
 change ‖P.charter j ξ (P.vtile v d) (c • A₀)‖ ≤ _
 have hs: P.charter j ξ (P.vtile v d) (c • A₀)= c • P.charter j ξ (P.vtile v d) A₀:=by
    apply ContinuousLinearMap.ext; intro y; unfold charter; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_smul]
 rwa [hs,P.stock_unique j ξ ht hT]



noncomputable abbrev pageFull (f:ℕ):ℝ:=bell (timeMesh P.par) f (P.pageChoice f)
noncomputable abbrev printW (f v:ℕ):ℕ:= P.tierScale f v * P.pageChoice f
noncomputable abbrev printSpot (g f v:ℕ)(l:List Axis):Cover:=P.clockPlate f v (P.rootSpace g f l)

lemma page_menu (r:ℕ): P.menuSize (1/2) r=P.pageFull (P.pointEra r):=by
 unfold menuSize pageWidth pageFull
 change _ = ((↑(↑(P.pageChoice (P.pointEra r)):ℤ)):ℝ)*↑(((8:ℝ≥0)*P.par.block.val)/ (↑P.par.R.L.val:ℝ≥0)^(P.pointEra r))
 push_cast; ring
lemma pin_cheaper (g f:ℕ)(l:List Axis): P.pinTime j g f l<P.pageFull f:=by
 let t:= (nodeC (P.rootSpace g f l) j)
 let s:=P.sidesPerTick
 have h:= (P.bound_form j g f l).2.1
 have hx:t<(↑(P.pageWidth (P.pageChoice f)):ℤ):=by unfold t; omega
 have hy:(t:ℝ)<(P.pageChoice f:ℝ)*s:=by
    have h: t< (↑(P.pageChoice f*s):ℤ):=hx.trans_eq (congrArg _ (mul_comm _ _))
    exact_mod_cast h
 unfold pinTime pageFull
 change (t:ℝ)*P.macroStep f/s < (↑(↑(P.pageChoice f):ℤ):ℝ)*P.macroStep f
 rw [Int.cast_natCast]
 exact (div_lt_iff₀ (show 0 < (s:ℝ) by exact_mod_cast P.sides_pos)).mpr ((mul_lt_mul_of_pos_right hy (P.macroStep_pos _)).trans_eq (by ring))

lemma page_bell (h:f ≤ v): bell Υ v (P.printW f v) = P.pageFull f:=by
 calc 
   _=((whenly Υ v _):ℝ) := natural_time ..
   _= _:= (congrArg _ (P.when_eq f v (P.pageChoice f) h)).trans (natural_time Υ f _).symm

/-- Relative recentering poise costs. Arbitrary pivot of original probe. -/
structure PagePose (g f v:ℕ)(l:List Axis)(d:Cover)(m k:ℕ) : Prop where
 spot: P.printSpot g f v l = pivotQ (P.granule (P.megaK g v)) l + P.sidesPerTick • d
 split: P.printW f v=m+k
 first:d j=(m:ℤ)
 left:((P.basePlay x g v).pivot P l).realWidth P j ≤ bell (timeMesh P.par) v m
 right:((P.basePlay x g v).pivot P l).realWidth P j ≤ bell (timeMesh P.par) v k

lemma pose_earned (g f:ℕ)(hg:g≤f)(hu:Odd P.par.R.L.val)(l:List Axis):
    ∀ᶠ v:ℕ in atTop, ∃ d m k,P.PagePose j x g f v l d m k:=by
 let a:=P.pageFull f; let e:=(P.pinTime j g f l+a)/2
 have h':P.pinTime j g f l < a:= P.pin_cheaper ..
 have h₁:P.pinTime j g f l < e:= by unfold e;linarith only [h']
 have h₂:0< a-e:=by unfold e;linarith only [h']
 have ht:Tendsto (fun v=> (P.roomy:ℝ)*P.macroStep v) atTop (𝓝 0):=by simpa only [mul_zero] using P.macroStep_zero.const_mul (P.roomy:ℝ)

 filter_upwards [ht.eventually (ge_mem_nhds h₂),P.quote_time j l hg h₁ hu] with v t b
 obtain ⟨v₀,d,g₀,H,U⟩:=b
 let w:=P.printW f v
 let h:=bell Υ v (d j)
 let B:=(P.basePlay x g v).pivot P l
 have hr:B.realWidth P j=(P.roomy:ℝ)*P.macroStep v:= by unfold B; rw [Apron.pivot_w]; exact congrArg (·*P.macroStep v) (Int.cast_natCast ..)
 have hp:0<h:=(B.real_width_pos P j).trans (lt_of_eq_of_lt hr H)
 have hm:d j ≥ 0:= (bell_le Υ v _ (d j)).mp (by simpa [bell,h] using hp.le)
 let m:=(d j).toNat; have he:d j=(m:ℤ):=(Int.toNat_of_nonneg hm).symm
 have hv:d j ≤ (w:ℤ):=(bell_le Υ v _ _).mp (U.trans (by rw [P.page_bell v₀]; linarith only [h₂]))
 let k:=w-m
 have hw:m+k=w:= Nat.add_sub_of_le (by omega)
 refine ⟨d,m,k,g₀,hw.symm,he,lt_of_eq_of_lt hr (H.trans_eq (congrArg (bell Υ v) he)) |>.le,?_⟩
 rw [hr]
 have ha:a=h+bell Υ v k:=by
    rw [show a=bell Υ v w from (P.page_bell v₀).symm,←hw]; unfold h
    rw [he]; simp [bell,_root_.add_mul]
 exact t.trans (by change h≤e at U; linarith only [U,ha])


variable {A C a:ℝ}{α:ℕ→ℝ}{g u m:ℕ}{τ:ℕ→ℕ}{l:List Axis}
lemma pose_cost (h: P.NightCop)(Lc:lender A C f r v α a τ P)
 (cl:P.Clearance f (P.pageChoice f) (P.rootSpace g f l))
 (ct:P.CloseRates A C f r v)
 (n0:fareMin P.par.R.L (r-f)≤1)
 {d:Cover}(z:P.PagePose j x g f v l d m k)
 {e:ℝ}(y:P.pageFull f≤e) :
    ‖((roomFee A*a:ℝ):ℂ) • P.locket j ξ ((P.basePlay x g v).pivot P l) e e‖ ≤ 2:=by
 let F:=P.printSpot g f v l
 let H:ℂ:=(roomFee A*a:ℝ)
 let G:P.Test:=H • P.visitOne v F
 let B:=(P.basePlay x g v).pivot P l
 have hb:B.s=v:=Apron.pivot_s ..
 let w:=P.printW f v
 refine P.localized j x (c:=H) hb z.split z.first
   ((P.zoom_check j v m B hb.le).mpr z.left)
   ((P.zoom_check j v k B hb.le).mpr z.right) ?_ e ((P.page_bell (Lc.treasury.price.le.trans Lc.treasury.step)).trans_le y)
 have hh:0<P.tierScale f v:=pow_pos P.par.R.L.property _
 have b:G∈ bay W (frameOne F) true:= (Tapestry.locates ..).mpr (InTest.smul _ P.basesT)
 have a': G∈enclave W:=Subalgebra.smul_mem _ (P.clock_colors F) _
 obtain ⟨T,t,vT⟩:=P.paid_center j x G (Nat.mul_pos hh (P.choice_pos _)) (frameOne F) b (P.page_form j g f v l) a'
   (P.clearance_roll _ Lc h ct n0 cl)

 have e₀: P.chartAll d (B.full P v)=P.chartAll d B.F:= hb ▸ P.issuing_here B d
 have h₁:H • P.chartAll d (B.full P v)=P.dewy G (P.singleState 3 v x G):=by
    rw [e₀]; unfold B G
    rw [P.baseP_F, P.chart_center, ←z.spot]
    unfold centeredQ dewy; generalize P.visitOne v (P.printSpot g f v l)=z
    rw [map_smul,smul_sub,smul_eq_mul,smul_smul]; -- tune rfl
 rw [h₁]
 exact ⟨T,t,vT⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pose_cost
