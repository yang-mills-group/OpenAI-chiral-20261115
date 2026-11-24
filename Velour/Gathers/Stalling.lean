import Velour.Gathers.Slacken
import Velour.Crepe.Blanket
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour


def stall (d:ℕ)(A:Coalition):Coalition where
 voters:= A.voters.image (d+·)
 w:=fun i=>A.w (i-d)
 pledges:=by rw [Finset.sum_image]; swap; exact fun _ _ _ _ h=>Nat.add_left_cancel h
             simpa using A.pledges
 signed:=by intro j c
            obtain ⟨i,t,rfl⟩:=Finset.mem_image.mp c
            simpa using A.signed i t

variable (P:Spine)(x:P.Spectrum0 3) (v:ℕ→ℕ)(u:StrictMono v)
   (a:ℕ→ℝ)(f r:ℕ) (s:ℕ → Coalition)
local notation "ξ" j:max=>P.advocate 3 x j
local notation:max "T!" h:max i:max=>P.pleading x f r i (h i) v a u

def waiting (s:ℕ → Coalition)(n:ℕ→ℕ):ℕ → Coalition:=
   fun i=>stall (n i-i) (s (n i))

lemma waiting_long (n:ℕ→ℕ)(h:∀i,i ≤ n i)(j:Axis)(l:List Axis):
    Slower (ξ j) (fun i=>(T! s i).pivot P l)
       (fun i=>(T! (waiting s n) i).pivot P l) n
    ∧ ∀i, P.macroStep (v i) ≤ ((T! (waiting s n) i).pivot P l).realWidth P j:= by


 simp_rw [Apron.pivot_w,P.pleading_w]
 -- simp_rw only changes second
 refine ⟨⟨?_,tendsto_atTop_mono h tendsto_id,?_⟩,fun i=>?_⟩
 · simp_rw [Apron.pivot_w,P.pleading_w]; exact P.narrowQuorum v u
 · intro i d w
   rw [Apron.pivot_w,P.pleading_w] at w
   rw [P.pleading_velour _ _ _ _ _ _ _ _ _ _ _ w,P.pleading_velour]
   swap
   · apply le_trans _ w
     exact mul_le_mul_of_nonneg_left (P.hem_time (u.monotone (h i))) (Nat.cast_nonneg _)
   dsimp only [waiting,stall]
   rw [Finset.sum_image]; swap; exact fun _ _ _ _ g=>Nat.add_left_cancel g
   refine Finset.sum_congr rfl fun k _=>?_
   rw [Nat.add_sub_cancel_left,show i+(n i-i+k)=n i+k by have := h i; omega]
 exact le_mul_of_one_le_left (P.macroStep_pos _|>.le) (by
     exact_mod_cast Nat.succ_le_of_lt (P.roomy_p))



variable (pay:ℕ→(ℕ×ℕ)→ℝ){A C b:ℝ}
local notation "a₀"=> fun i=> pay i (f,r)
local notation "X" j:max=> P.ColorHil j (P.advocate 3 x j)
local notation "T♯" s:max => fun i=>P.pleading x f r i (s i) v a₀ u
theorem totty_radiated (K:P.Register)(w:ScoutAnthem P x A C f r b v pay)
 (g:P.NightCop)(p:f<r)(o:Odd P.par.R.L.val):
 ∃ (s:ℕ → Coalition)(Y:∀ j:Axis,List Axis→ℝ→ X j),
   Radiates P x (T♯ s) Y ∧ P.VelvetCup x (T♯ s) ∧ P.TottyCup x (T♯ s):=by
 obtain ⟨s,h⟩:=P.velvet_council x v u pay f r K w g p o
 obtain ⟨n,t,q⟩:=P.slow_cup x (T♯ s) v
    (fun n=> T♯ (waiting s n)) h u.tendsto_atTop
    (P.waiting_long x v u a₀ f r s)
 exact ⟨waiting s n,_,t.cinema_raw,t,q⟩
#check totty_radiated
#print axioms totty_radiated
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
