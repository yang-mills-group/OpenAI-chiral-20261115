import YM.SU5.LoomForce.Condy
import YM.Next.MAXWELL.House
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
namespace Sundial
open LitCurrent LitCurrent.Surplus
open Pressure Worth Worth.Pays BProof
open Next.Rank.Spindle
-- physical-in-microscope timelike here. choose x at 0 (wrapped to every n).
-- tall gauge spacing X=L^-s/(constant) in the emerging tests. The comparator plane
-- is reflection along 3 at height R. Use R **negative**, multiple ruler, so the
-- plan qualifies for SlabMark Between, permits BQueue in subsequent estimate
-- (partial checkpoint DOESN'T yet obtain BQueue). Kept origin on lattice & paid both ends full.
variable {b B:ℕ}{χ:ℝ}(A:ℝ)(R:ℤ)
local notation "z" a:max=> radiusB (hat (Λ).R.L (Λ).x a)
local notation "p" s:max=> sPow Λ s A
local notation "Y"=> P.run
open Maxwell.Free Maxwell
abbrev τx:= -(YM.basis (3:Axis))
abbrev unitReceipt:=4* Maxwell.normal
lemma unit_pos : 0<unitReceipt:= mul_pos (by norm_num) Maxwell.normal_pos -- name
lemma taucost : τx≠0:= neg_ne_zero.mpr (norm_pos_iff.mp (by rw [basis_norm]; exact one_pos))
private lemma easel (i j:Axis): houseM τx i j = (if i=j then if i=3 then (-1:ℝ) else 1 else 0):= by
 by_cases t:i=j; · subst j; by_cases t:i=3 <;> simp [τx,houseM,kr_eq, t]; try ring
 rcases eq_or_ne i 3 with v|v <;> rcases eq_or_ne j 3 with q|q <;> simp_all [τx,houseM,kr_eq,Ne.symm]
lemma taxing (i j:PlaqAxes): (realDir i:ℂ)*specter i j τx= if i=j then (unitReceipt:ℂ) else 0 := by
 unfold specter; rw [bare_formula _ _ _ _ taucost]; unfold Maxwell.Free.wedge Maxwell.Free.house; simp_rw [easel]; have hi:=i.property; have hj:=j.property; have ht: i.val.1 ≠ 3 :=by intro h; rw [h] at hi; exact not_lt_of_ge ((show ∀ x:Axis,x≤3 from by decide) _) hi
 by_cases x:i=j
 · subst j; unfold realDir; split <;> simp [unitReceipt,τx, *,Ne.symm (LT.lt.ne hi),LT.lt.ne hi]
 have hg: i.val.1 ≠ j.val.1 ∨ i.val.2≠j.val.2:= by by_contra! t; exact x (Subtype.ext (Prod.ext t.1 t.2))
 have ht': i.val.1≠ j.val.2∨ i.val.2≠ j.val.1:= by by_contra! k; obtain ⟨y,e⟩:=k; rw [y,e] at hi; exact lt_asymm hi hj
 rcases hg with a|a <;> rcases ht' with b|b <;> simp [x,a,b] -- tune

abbrev φclock (P:Spine)(A:ℝ)(s:ℕ):ℕ:= ⌈sPow P.par s A / (2*(ruler P.par.block:ℝ))⌉₊
def shadowR (P:Spine)(A:ℝ)(s:ℕ):ℤ:= ruler P.par.block * (φclock P A s)
local notation "κr" s:max=> shadowR P A s
local notation "C_"=> (ruler P.par.block :ℝ)
lemma rulerBright : 0< (ruler P.par.block:ℝ):= Int.cast_pos.mpr (ruler_gene P.par.block)
lemma shadow_pay (s:ℕ): (p s) ≤ 2*((κr s):ℝ) ∧ 2*((κr s):ℝ) < (p s) + 2*(ruler P.par.block:ℝ):=by
 unfold shadowR; let f := (2*C_); have hp:0<f:=mul_pos (by norm_num) (rulerBright P); have hμ:0<p s:= BProof.coin_pos ..
 have he:0≤ (p s)/f:= by positivity
 rw [Int.cast_mul, Int.cast_natCast, ←mul_assoc]
 refine ⟨(div_le_iff₀' hp).mp (Nat.le_ceil _),?_⟩; have ht:(φclock P A s:ℝ)< (p s)/f+1:=Nat.ceil_lt_add_one he
 have ht': (φclock P A s:ℝ)-1<(p s)/f:=by linarith
 change f*_<(p s)+f; linarith only [(lt_div_iff₀' hp).1 ht'] -- f not unfolded
lemma shadow_pos (s:ℕ) : 0< κr s:=Int.cast_pos (R:=ℝ)|>.mp (by apply pos_of_mul_pos_right (show 0<2*(κr s:ℝ) from lt_of_lt_of_le (BProof.coin_pos ..) ((shadow_pay P A s).1)) (by norm_num)) -- which
variable (u:0<A)
include u
lemma shadow_revenue : Tendsto (fun s=> 2*((κr s):ℝ)/(p s)) atTop (𝓝 1) :=by
 have hpos s:0<p s:=BProof.coin_pos ..
 have hv:Tendsto (fun s=> (p s)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (sPower_pay Λ u)
 have hx:Tendsto (fun s=> 2*C_*(p s)⁻¹+1) atTop (𝓝 1):=by simpa only [mul_zero,zero_add] using (hv.const_mul (2*C_)).add_const 1
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x:=(1:ℝ))) hx (fun s=>(one_le_div (hpos s)).mpr (shadow_pay P A s).1) (fun s=>?_)
 rw [←div_eq_mul_inv]; rw [show 2*C_/(p s)+1=((p s)+2*C_)/(p s) from ?_]; exact div_le_div_of_nonneg_right ((shadow_pay P A s).2.le) (hpos s).le; field_simp [(hpos s).ne']; ring
lemma radius_down (a b:ℝ): Tendsto (fun s=>(a*(z s:ℝ)+b)/(p s)) atTop (𝓝 0):=by
 let f:=Pays.plus (Pays.scale a Pays.rising) (merit (constant b) (by norm_num [Earlier]))
 let t':= limit (times f (whole 0 (-A) 0)) (Or.inr (Or.inl ⟨zero_add _, by simpa⟩))
 refine (t'.comp (turnover Λ)).congr (fun s=>?_); unfold sPow; simp only [comp_apply, div_eq_mul_inv]; rw [BProof.coin_inv,neg_zero] -- name tune
#check @shadowR

-- uniform about varying collocation AP faces. Pose Sweep must act including reverse shift. Not depending on height smoothing.
omit u
variable (N:Side)
def shadowShift (R:ℤ) (v:Cover) : Cover:= (Buffered.plane 3 R).motion v
local notation "κ"=> wrap (More N)
local notation "Z"=> nodeC (0:Cover)
lemma send_pay (x:Cover): sendSite R (wrap (More N) x) = wrap (More N) (shadowShift R x):=by
 unfold shadowShift; rw [←Shape.anno]; unfold sendSite; unfold Shape.anon; rw [show haul N R= wrap (More N) (2 • (R • (step 3:Cover))) from by unfold haul slipV; rw [mul_smul]; rfl]; unfold plane; push_cast; rfl

def openSeat (b:Bool)(R:ℤ)(u:Sheds B): Cover:=
 let v:= u.1.val.1 + nodeC 0
 if b then if u.1.val.2.val.2=(3:Axis) then shadowShift R v-step 3 else shadowShift R v else v
lemma cost_p (b:Bool)(d:Sheds B): let F:= (readingFob B R (0:Site N)).ua (b,d); (F.1= wrap (More N) (openSeat b R d)) ∧ F.2=d.1.val.2:= by
 intro F
 have hp:node (0:Site N) =wrap (More N) (nodeC 0):= by simpa only [map_zero] using Lifted.node_of N (0:Cover)
 unfold openSeat; simp only; let S:= armFace B (node (0:Site N)) d.1; let T:= d.1.val.1 + Z; have hx:S.1= κ T :=by unfold S armFace T; simp [hp]
 cases b; exact ⟨hx,rfl⟩
 change (sendV R S).1=_ ∧ (sendV R S).2= _; rw [plazas]; change (if d.1.val.2.val.2=3 then sendSite R S.1- step (3:Axis) else sendSite R S.1)=κ (if d.1.val.2.val.2=3 then shadowShift R T-step 3 else shadowShift R T) ∧ S.2=d.1.val.2; rw [hx,send_pay]; split_ifs with h <;> (refine ⟨?_, rfl⟩; try rw [map_sub,wrap_step])
 rfl

private lemma openBounds (u v:Sheds B)(q:Axis): let y:=openSeat true R u-openSeat false R v
   ((y q)-(2*R)* step (3:Axis) q).natAbs ≤ 4*B+8:=by
 intro y; have ht(x:Next.Rank.Spindle.Turn B): -(B:ℤ) ≤ x.val.1 q ∧ x.val.1 q ≤ (B:ℤ):= ⟨(box_test.mp (faceOrigin x)).1 q,(box_test.mp (faceOrigin x)).2 q⟩
 have he:= ht u.1; have hx:= ht v.1; unfold y openSeat nodeC shadowShift; simp only [Bool.false_eq_true,ite_false,ite_true]; split_ifs <;> simp only [Pi.sub_apply,fling_move] <;> by_cases h:q=3 <;> simp_all [Ne.symm] <;> omega

include u
lemma booth_cost (f:ℕ→ℕ)(t:StrictMono f)(a b: ∀ s,Sheds (radiusB (hat P.par.R.L P.par.x (f s)))) :
    Tendsto (fun s=> riseX (sPow P.par (f s) A) (openSeat true (-(shadowR P A (f s))) (a s) - openSeat false (-(shadowR P A (f s))) (b s))) atTop (𝓝 τx) :=by
 let k(s:ℕ) := (p (f s)); let x(s:ℕ):= -(κr (f s)); let L(s:ℕ):= openSeat true (x s) (a s)-openSeat false (x s) (b s)
 have he:Tendsto (fun s=> 2*(x s:ℝ)/k s) atTop (𝓝 (-1 : ℝ)):= ((shadow_revenue P A u).neg.comp t.tendsto_atTop).congr fun i=>by simp [x,k,neg_div]
 have hv:Tendsto (fun i=>(4*((z (f i)):ℝ)+8)/k i) atTop (𝓝 0):=(radius_down P A u 4 8).comp t.tendsto_atTop
 refine (PiLp.continuous_toLp 2 (fun _:Axis=>ℝ)).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ i:Axis,Tendsto (fun s=> (riseX (k s) (L s)) i) atTop (𝓝 (τx i)) from ?_))
 intro i; let t':ℤ:= (step (S:=ℤ) 3 i); let H(s:ℕ):= L s i-(2*x s*t'); have hz:Tendsto (fun s=> (H s:ℝ)/k s) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero (fun _=>norm_nonneg _) _ hv; intro s; rw [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<k s from BProof.coin_pos ..)]
    refine div_le_div_of_nonneg_right ?_ (BProof.coin_pos ..|>.le); rw [←Int.cast_abs, ←Int.natCast_natAbs]; exact_mod_cast openBounds (x s) (a s) (b s) i
 have ht: τx i = (-1:ℝ) * (t':ℝ)+0:=by by_cases t:i=3 <;> simp [τx,t',t]
 rw [ht]; exact ((he.mul_const (t':ℝ)).add hz).congr fun g=> by change _+_= (L g i:ℝ)/k g; unfold H; push_cast; ring -- likely riseX at coord; shadows
#print axioms booth_cost
end Sundial
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
