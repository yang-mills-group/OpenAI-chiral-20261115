import YM.SU5.FiniteGaugeData.Tower.Hours
import YM.SU5.FiniteGaugeData.Tower.CompactFlight
/-!
# Transverse lattice representation, assembles and projects canonical continuous part

Here form one spectral H for the continuous part and connect real-time on it.
Diagnostic use / comparison and full-H question in other modules.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)(strict:Bool)
variable (C:Arena Y H Q j z strict)
local notation "F" s:max=> Tower.Field Y H s j z strict
local notation "κ" s:max=>actor Y H s Q j z strict C
local notation "A"=> Ark.Ht Y H Q j z strict C
local notation "w"=>floorV Y H Q j z strict C
abbrev Trans (a:Axis):= {i:Axis // i≠a}
open MeshClock Germ
local notation "M"=>timeMesh Λ
-- use same even step as time (double amounts)
noncomputable def courseU (b:Trans j): Lunation (timeMesh Λ) A where
 nav s x:= sailV Y H V s Q j z strict _ b.property C (2*x)
 zero s:=by rw [mul_zero]; exact sailV_source Y H V s Q j z strict b.val _ C
 limited s i:=sailV_small Y H V s Q j z strict b.val _ C _
 sums s i j':=by rw [sailV_sum,mul_add]
 changeover s r i' p:=by -- wrong args order
    rw [sailV_high Y H V s Q j z strict _ b.property C _ r i']; unfold MeshClock.castor smill; change _=sailV _ _ _ _ _ _ _ _ _ _ _ (2*((Λ.R.L.val:ℤ)^(r-s)*p)); congr 1; ring

noncomputable def ladder : Alliance (Trans j) (marks (timeMesh Λ)) A where
 crew b:= (courseU Y H V Q j z strict C b).plays
 cCom b a x y:=by
    obtain ⟨s,i,h⟩:=notch_exists M x; obtain ⟨t,k,hp⟩:=notch_exists M y
    let mm:=max s t; let ha:s ≤ mm:=le_max_left ..; let ht:t ≤ mm:=le_max_right ..
    change (Lunation.ship (courseU Y H V Q j z strict C b) _).comp (Lunation.ship (courseU Y H V Q j z strict C a) _)=(Lunation.ship (courseU Y H V Q j z strict C a) _).comp (Lunation.ship (courseU Y H V Q j z strict C b) _)
    rw [←h,←hp,← notch_up M s mm ha,← notch_up M t mm ht, Lunation.navZ,Lunation.navZ]
    exact sailV_commutes Y H V mm Q j z strict b.val b.property C a.val a.property _ _
local notation "L₀"=>ladder Y H V Q j z strict C
local notation "V₀" a:max=> ((L₀).crew a).play
local notation "u" t:max=> advance Y H V Q j z strict C t

lemma on_ladder(a:Trans j)(i':ℤ):(V₀ a) (notch M s i')=sailV Y H V s Q j z strict _ a.property C (2*i'):= Lunation.navZ (courseU Y H V Q j z strict C a) ..
lemma ladder_time(a:Trans j)(t:ℝ≥0)(x:marks M):((V₀ a) x).comp (u t)=(u t).comp ((V₀ a) x):=by
 obtain ⟨s,i,rfl⟩:=notch_exists _ x; rw [on_ladder,sailV_time]

-- enumerate transverse axes without duplicates. positions mesh finite comparisons later
noncomputable def look (j:Axis):List (Trans j):= Finset.sort (α:=Trans j) univ (· ≤ ·)
lemma look_all (a:Trans j):a∈look j:=by simp [look]
lemma look_one(j:Axis):(look j).Nodup :=by apply Finset.sort_nodup
local notation "δ"=> daylight M
local notation "X"=> look j
local notation "T₀"=> (L₀).Realm X

local notation "τ" t:max=> (L₀).lame X (u t) (fun i _ v=> ladder_time Y H V Q j z strict C i t v)
noncomputable def stages : OS.Semigroup ((ladder Y H V Q j z strict C).Realm (look j)) j where
 E t:= (L₀).lame X (u t) (fun i _ v=> ladder_time Y H V Q j z strict C i t v)
 U x:= (L₀).aviation (daylight M) (look j) (fun a => x.val a.val)
 eZero:=by ext1 x; apply Subtype.ext; rw [Alliance.grating,advance_source]; rfl
 time t b:=by ext1 x; apply Subtype.ext; change (u (t+b)) (x.val:A)= (u t) ((u b) x.val); rw [advance_smag]; rfl
 shrinks t:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by rw [one_mul]; have h:=ContinuousLinearMap.le_opNorm (u t) x.val |>.trans (mul_le_of_le_one_left (norm_nonneg _) (advance_small Y H V Q j z strict C t)); exact h)
 sym t:=by
    change ContinuousLinearMap.adjoint (τ t)=(τ t)
    ext1 x; apply ext_inner_left ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ ((u t) y.val) (x.val:A) =inner ℂ (y.val:A) ((u t) x.val)
    rw [← ContinuousLinearMap.adjoint_inner_right (u t),advance_adjoint]
 uZero:=by
    have hv:(fun (a: Trans j)=> (0:E4) (a:Axis))=0:=by ext1; rfl
    rw [show ((0:OS.Cross j).val)=(0:E4) from rfl,hv,Alliance.aviation_zero]
 space x y:=by
    have he:(fun a:Trans j=>(x+y).val (a:Axis))=(fun a:Trans j=> x.val (a:Axis)) + (fun a:Trans j=> y.val (a:Axis)):=rfl
    rw [he,← Alliance.aviation_group]
 independent t x:=by
    ext1 i; apply Subtype.ext
    change (u t) ((L₀).flight δ X (fun a=>x.val a.val) i.val)=(L₀).flight δ X _ ((u t) i.val)
    rw [←ContinuousLinearMap.comp_apply _ (u t),Alliance.fluid _ _ _ _ (fun i _ v=> ladder_time Y H V Q j z strict C i t v)]; rfl
 unitary t x:=Alliance.aviation_unit ..
 continuousE x:=by
    change Continuous (fun t=> ((τ t) x:(L₀).aviator X))
    exact Continuous.subtype_mk (show Continuous (fun i=> (u i) (x.val:A)) from (advance_strong ..).continuous) _
 continuousU x:=Alliance.aviation_cont _ _ _ _ (fun (i:Trans j) _=>show Continuous (fun v:OS.Cross j=>(v.val:E4) i.val) by fun_prop) x
noncomputable def landing (x:A): (T₀):=(⟨((L₀).stackS X) x,(L₀).planted X x⟩ : ↥((L₀).aviator X))
local notation "b₀"=>landing Y H V Q j z strict C
local notation "F₀" => stages Y H V Q j z strict C
lemma landing_early(t:ℝ≥0)(x:A): b₀ ((u t) x)=(F₀).E t (b₀ x):=by
 let Q':= (L₀).stackS X
 apply Subtype.ext
 change Q' ((u t) x)=(u t) (Q' x)
 rw [←ContinuousLinearMap.comp_apply (u t), Alliance.ground _ _ _ (fun i _ v=>ladder_time Y H V Q j z strict C i t v)]; rfl
lemma landing_vac: (b₀ w: (L₀).aviator X).val= (w:A) :=by
 apply Alliance.grounded _ X; rw [Alliance.assembled]; intro a _
 have ht: (fun i=> (V₀ a) i w)=fun _=>w:=by
    funext i; obtain ⟨s,x,rfl⟩:=notch_exists M i; rw [on_ladder,sailV_vac]
 change ContinuousAt (fun i=> (V₀ a) i w) 0; rw [ht]; exact continuousAt_const

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.landing_early
