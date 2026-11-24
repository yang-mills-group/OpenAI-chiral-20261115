import YM.SU5.SatinWard.Resolution.Cholette
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Tapestry
open SlabMark Papal Papal.Moon Papal.Moon.Moonlit SwitchC Garland Terrace Juniper
namespace CasaF
open Swell Sonar Fock Tapestry.StageW LitCurrent LitCurrent.Chamber
open QuadClock Preparation.Tabletop
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)(s:ℕ)(i k:ℕ→ℕ) {r v:ℕ} {a b φ:ℝ} (A:∀ n,s<Y.uv (k n))
variable (X:∀ n,MaskPoint Y r s (i n) (k n) a b)(E:(n:ℕ)→eraτ Y s (i n) (k n) r a φ)
local notation "N" j:max=> side Y (i j) s
local notation "Yt"=> tent Y H
local notation "R"=> (Y.meter.a s)
local notation "S✩"=> pavilion (nodeC (0:Cover)) ((Y.meter.a s).B+12)
local notation "p_" j:max=> RootBook Y (i j) (k j) s
local notation "M✔" j:max=> (Y.voyage (i j)).CapeT s
-- Normalized residue geometry and EOM family statement.
open Vacancy VacuumSelection.VelourWiggle
variable {K:Calibration}{m n:Side} {F G:Family K}{D S:Finset Cover}
lemma cueWords{ι:Type}(B:Finset ι)(F:ι→ℕ→ Family K)(H:ι→ Family K)(p:∀ i∈B,BQueue D (F i) (H i)):BQueue D (fun i=>∑ j∈B, F j i) (∑ j∈B,H j):=by
 classical
 induction B using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; exact BQueue.stay InTest.zero zero_lt_one (fun n v=> (show ‖(0:FC (Single (K.c n)))‖≤1 by simp)) -- norm implicit
 | insert i H t ih=> simp_rw [sum_insert t]; exact cueSum (p i (mem_insert_self ..)) (ih fun k t'=> p k (mem_insert_of_mem t'))
-- station.Ph.E invariant.W λ normalizations given later.No slips ties.
variable {Γ':ℕ} (q:Cover)
structure Domicile (p:ℕ)(F:Cover→Family K) : Prop where
    valid (x): InTest K true (pavilion (nodeC x) p) false (F x)
    neutral :∀ x,Neutral K (F x)
    travel (x j d) : Tower.chime K j d (F x)=F (x+d • step j)
namespace Domicile
variable {q k:ℕ} {F G:Cover→ Family K}
lemma lift (t:Domicile q F)(p:q≤ k): Domicile k F:=⟨fun i=>(t.valid i).mono (inclPav _ _ _ p),t.neutral,t.travel⟩
lemma tinted (x:ℝ)(t:Domicile k F): Domicile k (x • F):=by
 simp_rw [← Complex.coe_smul]; exact ⟨fun i=>(t.valid i).smul _,fun i=> covariant_scale _ (t.neutral i) _, fun i j d=> by simp only [Pi.smul_apply,chime_scale,t.travel i j d]⟩
lemma more (u:Domicile k F)(t:Domicile k G): Domicile k (F+G):=⟨fun i=>(u.valid i).add (t.valid i),fun i=> (covariant_parts K (u.neutral i) (t.neutral i)).1,fun i j d=>by simp only [Pi.add_apply,chime_plus,u.travel i j d,t.travel i j d]⟩
lemma less (u:Domicile k F)(t:Domicile k G): Domicile k (F-G):=by rw [sub_eq_add_neg, ←neg_one_smul ℝ]; exact u.more (t.tinted _)
lemma count {ι:Type}(A: Finset ι)(F:ι→ Cover→Family K)(p:∀ i∈A,Domicile k (F i)): Domicile k (∑ i∈A,F i):=by
 classical
 induction A using Finset.induction_on with
 | empty=> rw [sum_empty]; exact ⟨fun _=> InTest.zero,fun i=>covariant_zero _,fun i j d=> by simp only [Tower.chime,Pi.zero_apply]; funext m; funext x; simp only [mirror,reflMark,Pi.zero_apply, theta_zero]⟩
 | insert i S t ih=> rw [sum_insert t]; exact (p _ (mem_insert_self ..)).more (ih (fun j hj=>p j (mem_insert_of_mem hj)))
-- outside clock.TH wrap.Want housing B=2r.U.prime
lemma pavLord (x:Cover)(u:Cover)(v:∀ i:Axis,(u i).natAbs ≤ l)(q:ℕ) : pavilion (nodeC (x+u)) q⊆ pavilion (nodeC x) (q+2*l):=by
 intro i t; rw [pav_v] at *; intro j; specialize t j; specialize v j;
 simp only [nodeC,Pi.add_apply,Pi.mul_apply,nsmul_eq_mul,Pi.one_apply,Nat.cast_ofNat, show ∀(x:Axis),(2:Cover) x = 2 from fun _=>rfl] at t ⊢; omega
lemma flow_d (u:Cover)(p:∀ i:Axis,(u i).natAbs≤ l)(t:Domicile k F): Domicile (k+2*l) (fun x=>F (x+u)):=⟨fun x=>(t.valid _).mono (pavLord _ _ p k),fun x=> t.neutral _,fun x i j=> by rw [t.travel (x+u), add_right_comm]⟩
lemma solo {x:Family K}(t:InTest K true (pavilion (nodeC (0:Cover)) k) false x)(g:Neutral K x): Domicile k (fun v=>carriage v x):= by refine ⟨fun i=>?_,fun i=>moving_color ordinate _ t g,fun i j d=> reach_clock t i j d⟩; simpa only [zero_add] using carriage_test i t
lemma oriented {x:ℕ}(F: Cover→Family K)(p:Domicile x F)(i j:Cover): carriage i (F j)= F (j+i):=travel_carriage _ (fun j x=> p.travel x j) i j
end Domicile
end CasaF
end YM.CF.Buffered.Afterglow.Tower
