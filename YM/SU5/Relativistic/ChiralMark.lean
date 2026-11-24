import YM.SU5.Relativistic.MultiMark
import YM.SU5.Selected.Clinic

/-!
# Positive-degree matter test

Together with a nonzero reading, a mark certified by this predicate genuinely uses
chiral letters, not in the scalar-gauge subalgebra. Here this is proved without assuming
faithfulness of any reading. `bannedSeat`: kills the filled reference ket itself;
preserved on pushing to the microscopic horizon. This is a physical statement about
which local Mark is inserted; not pretending this proves any S-matrix result etc.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel
open Tower.Selected Vacancy
open Journey
open Reed (Fine think)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

section farm
variable {I I' : Type*} [LinearOrder I] [Fintype I] [LinearOrder I'] [Fintype I']
variable {s t u : Finset I} {b : Bool} {A B : FC I}
variable {s' : Finset I'}

private abbrev evan (A:FC I)(s:Finset I):Prop:= acts A (basisKet s)=0
lemma grassmann (h:Fine s t b A): ∃ z:ℂ,(b=true → z=0) ∧ acts A (basisKet s)=z • basisKet s:=by
  induction h with
  | empty=> exact ⟨0,fun _=>rfl, (act_zero _).trans (zero_smul _ _).symm⟩
  | one=> exact ⟨1,nofun,(act_one _).trans (one_smul _ _).symm⟩
  | seed i p=>
    refine ⟨0,fun _=>rfl,?_⟩
    rw [zero_smul]; by_cases h:i∈ s
    · rw [show (think s).term i=put i from if_pos h,put_act,if_pos h]
    rw [show (think s).term i = -takeF i from if_neg h,act_neg,take_act,if_neg h,neg_zero]
  | @grow a c x y p q hp hq=>
    -- binder order
    obtain ⟨z,g,e⟩:= hp; obtain ⟨w,v,u⟩:=hq
    refine ⟨w*z,?_,by rw [act_mul,u,map_smul,e,smul_smul]⟩
    intro h
    cases x<;> cases y <;> simp_all
  | add _ _ hp hq=>
    obtain ⟨z,g,e⟩:=hp; obtain ⟨w,v,k⟩:=hq; exact ⟨z+w,fun h=>by rw [g h,v h,add_zero],by rw [act_add,e,k,add_smul]⟩
  | scale _ w hp=>
    obtain ⟨z,g,e⟩:=hp; exact ⟨w*z,fun h=>by rw [g h,mul_zero],by rw [act_smul,e,smul_smul]⟩
lemma grassmann_odd (h:Fine s t true A): acts A (basisKet s)=0:=by
  obtain ⟨z,h,q⟩:=grassmann h; rw [q,h rfl,zero_smul]
lemma matter_course (κ:ℂ→+*ℂ) (P : FC I→ₛₗ[κ] FC I') (p:P 1=1)
    (q:∀ {x y:FC I} {b c},Fine s t b x→ Fine s t c y → P (x*y)=P x * P y)
    (e:∀ i∈t,∃ t':Finset I',Fine s' t' true (P ((think s).term i))) (h:Fine s t b A) :
    ∃ z:ℂ, acts A (basisKet s)=z • basisKet s∧acts (P A) (basisKet s')= κ z • basisKet s':=by
  induction h with
  | empty=> exact ⟨0, by rw [act_zero,zero_smul],by rw [map_zero,map_zero,act_zero,zero_smul]⟩
  | one=>exact ⟨1,by rw [act_one,one_smul],by rw [p,map_one,act_one,one_smul]⟩
  | seed i t=> obtain ⟨X,g⟩:=e i t; exact ⟨0,(grassmann_odd (Fine.seed i t)).trans (zero_smul _ _).symm,by rw [map_zero,zero_smul]; exact grassmann_odd g⟩
  | grow v w i j=>
    obtain ⟨z,h,g⟩:=i; obtain ⟨k,e,x⟩:=j
    exact ⟨k*z,by rw [act_mul,e,map_smul,h,smul_smul],by rw [q v w,map_mul,act_mul,x,map_smul,g,smul_smul]⟩
  | add v w i j=>
    obtain ⟨z,h,g⟩:=i; obtain ⟨k,e,x⟩:=j
    exact ⟨z+k,by rw [act_add,h,e,add_smul],by rw [map_add,map_add,add_smul,act_add,g,x]⟩
  | scale v a i=>
    obtain ⟨z,h,g⟩:=i
    exact ⟨a*z,by rw [act_smul,h,smul_smul],by rw [map_smulₛₗ P,map_mul,act_smul,g,smul_smul]⟩
lemma matter_map (κ:ℂ→+*ℂ) (P : FC I→ₛₗ[κ] FC I') (p:P 1=1)
    (q:∀ {x y:FC I} {b c},Fine s t b x→ Fine s t c y→ P (x*y)=P x * P y)
    (e:∀ i∈t, ∃ t':Finset I', Fine s' t' true (P ((think s).term i))) (h:Fine s t b A)
    (a: acts A (basisKet s)=0) : acts (P A) (basisKet s')=0:=by
  obtain ⟨z,g,k⟩:= matter_course κ P p q e h
  have he:basisKet s ≠ 0:= norm_pos_iff.mp (by simp [basisKet])
  rw [g] at a; rw [k,(smul_eq_zero.mp a).resolve_right he,map_zero, zero_smul]
end farm

section
variable {N M:Side} (T : Ratio N M)
local notation "ρ" N:max => basisKet (Tset N)
lemma before_preserves (j:ℕ) (Q:Op SU.Slot) (m:Male) (h:Odd T.count.val) (z : Nom N M) {F : FC (Single N)} {s:Finset (Single N)} {b:Bool} (p:Fine (Tset N) s b F) (q:acts F (ρ N)=0) :
    acts (Advance.subF T j Q m h z F) (ρ M)=0:=by
  refine matter_map (RingHom.id _) (Advance.subF T j Q m h z) (Advance.sub_one ..) (fun a b=> Advance.sub_mul _ _ _ _ _ _ a b) ?_ p q
  intro i hi; refine ⟨Finset.univ,?_⟩
  by_cases g:i ∈ Tset N
  · rw [show (think _).term i = _ from (if_pos g : (think _).term i=put i), sub_put _ _ _ _ _ _ _ g]
    have h' := Advance.stroke_fine T j Q m h z i
    rw [Advance.stroke,if_pos g] at h'; exact h'
  rw [show (think _).term i = _ from (if_neg g : (think _).term i= -takeF i), map_neg, sub_take _ _ _ _ _ _ _ g]
  have h' := Advance.stroke_fine T j Q m h z i; rw [Advance.stroke,if_neg g] at h'; exact fine_neg h'

/-- `evanescent` = matter constant term absent. -/
def evanescent (f:Mark N):Prop:=∀ x, acts (f x) (basisKet (Tset N))=0

lemma pushed_ev (A: StepData (More N) (More M)) (j:ℕ) (Q:Op SU.Slot) (m:Male) (p: Odd T.count.val) (d:Chi) (w β:ℝ) (l:Loom N)
    {f:Mark N} {b:Bool} {S} (v:AtSupport b S f) (g:evanescent f): evanescent (pushMark T A j Q m p d w β l f):=by
  -- outer integral vanishing cross, no price needed for this statement
  let X:FC (Single M) →ₗ[ℂ] Wave (Single M):={ toFun:=fun x=>acts x (ρ M), map_add':=fun _ _=> act_add .., map_smul':=fun _ _ => act_smul .. }
  let Y:= X.toContinuousLinearMap.restrictScalars ℝ
  intro x
  change Y (pushMark T A j Q m p d w β l f x)=0
  unfold pushMark linkLaw
  apply steady Y
  intro V
  rw [map_smul]
  suffices h:Y (assembled T j Q m p d w l f x V)=0 by rw [h,smul_zero]
  unfold assembled; apply steady Y
  intro k
  unfold gathered avgF; rw [map_smul,map_sum,sum_eq_zero,smul_zero]; intro i _
  exact before_preserves T j Q m p _ (v.allV _) (g _)
where
 steady {H J A:Type} [NormedAddCommGroup H][NormedAddCommGroup J][NormedSpace ℝ H][NormedSpace ℝ J][CompleteSpace J][CompleteSpace H][MeasurableSpace A]
    {f:A→H}{μ:Measure A}(X:H→L[ℝ] J)(s:∀ a,X (f a)=0): X (∫ a,f a∂μ)=0:=by
    by_cases w:Integrable f μ
    · rw [← ContinuousLinearMap.integral_comp_comm X w]; simp_rw [s,integral_zero]
    rw [integral_undef w,map_zero]
lemma only_excited {f:Mark N}(p:evanescent f) (x:Fields N) : acts (f x) (Dial.mateK N)=0:=by
  let a:= ρ N; let q:= Dial.mateK N
  have hs:Sea (cutM (Tset N)) q:= (touchP N) ▸ Dial.tickB N
  have hv:q= (inner ℂ a q) • a:=by nth_rw 1 [←hs.1]; rw [cutLine, cut_oneAct]; unfold a; rw [basis_inner]
  change acts _ q=0; rw [hv,map_smul,p x,smul_zero]
lemma mirror_ev {f:Mark N} {b:Bool} {S} (v:AtSupport b S f) (p:evanescent f) (i:Axis)(z:ℤ):evanescent (reflMark i z f):=by
  let U:=carR i z N
  let P : FC (Single N) →ₗ⋆[ℂ] FC (Single N):=⟨⟨Fock.theta U,theta_add _⟩,fun c x=> theta_smul U x c⟩
  intro x; let y:= reflFields i z x
  change acts (P (f y)) _=_
  refine matter_map _ P (theta_one _) (fun _ _=>theta_mul U _ _) ?_ (v.allV y) (p y)
  intro a t; refine ⟨univ,?_⟩
  apply Reed.Fine.arrive (U:=U) ?_ ?_ (h:=Fine.seed a (Finset.mem_univ a)) -- e `twist U univ = cutM T`
  · have he: cutM (univ:Finset (Single N)) = 1 := by ext x y; by_cases p:x=y <;> simp [cutM,p,Matrix.one_apply]
    rw [he,map_one]
  rw [dim_cut,map_sub,map_one, show twist U (cutM (Tset N))=1-cutM (Tset N) from flatTset i z]; abel
end

section election
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable (s i k:ℕ)
variable {f:Altitude.Cloud (Dome (tent Y H))}

lemma keeps_degree (h:Tapestry.Pay Y s i k)(t:f∈ shorter (Dome K) s)
    (v: evanescent (attire (breathing Y H s i k f))) (n:ℕ) (q: s+n≤Y.uv k) :
    evanescent (attire (breathing Y H (s+n) i k f)):=by
  induction n with
  | zero=> exact v
  | succ n ih=>
    have t': s+n < Y.uv k:=by omega
    rw [←Nat.add_assoc,ascent_actual Y H _ i k (climbs (Dome K) (by omega : s ≤ s+n) t)]
    exact pushed_ev (Vale.apt (Y.ir i) Λ.block Λ.R.L (s+n)) (patternA Y (s+n) i k) Λ.K.j
      (patternQ Y (s+n) i k).val _ Λ.R.odd_side _ _ (patternβ Y (s+n) i k) _ (Ward.signs (breathing Y H (s+n) i k f)) (ih (by omega))
end election
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.keeps_degree
