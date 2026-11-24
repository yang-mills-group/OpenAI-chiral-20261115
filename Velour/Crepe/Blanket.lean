import Velour.Crepe.Caring
import Velour.Crepe.Assemble
/-! # Strengthen convex plebiscite once. -/
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


open QuadClock TopologicalSpace
variable {ι : Type}

private lemma pledgesLate [Nonempty ι][Countable ι](J:ι→Hilbert)
   [∀i, SeparableSpace (J i).space]
   (T:ℕ→∀i:ι, ℕ→(J i).Op)(B:ℕ→ℝ)
   (b:∀ᶠ k in atTop, ∀i:ι, ∀ᶠ n:ℕ in atTop, ‖T k i n‖≤ B k):
   ∃q:ℕ → Coalition,
      ∀ᶠ k in atTop, ∀ i, (∀ᶠ n in atTop, ‖pool q (T k i) n‖ ≤ B k) ∧
                    ∃ Y:(J i).Op, Gleams (J i) (pool q (T k i)) Y :=by
 obtain ⟨r,u⟩:=eventually_atTop.mp b
 have h(z:ℕ×ι):∃a:ℝ,∀ᶠ n in atTop, ‖T (z.1+r) z.2 n‖≤ a:= ⟨_,u _ (by omega : r≤z.1+r) _⟩
 obtain ⟨q,y⟩:=pooled (fun z:ℕ×ι=>J z.2) (fun z=>T (z.1+r) z.2) h
 refine ⟨q,(eventually_ge_atTop r).mono fun k e i=> ⟨pool_exp q _ (u k e i),?_⟩⟩
 rw [←Nat.sub_add_cancel e]
 exact y (k-r,i)


variable (P:Spine)(x:P.Spectrum0 3)(v:ℕ→ℕ)(u:StrictMono v)(a:ℕ→ (ℕ×ℕ)→ℝ){A C b:ℝ}(f r:ℕ)

local notation "a₀" => fun i=> a i (f,r)
local notation "R₀"=> P.rewardK f r
local notation "y" j:max=>P.advocate 3 x j
local notation "τ"=> P.macroStep
local notation "T♯" s:max => fun i=>P.pleading x f r i (s i) v a₀ u
local notation "X" j:max=> P.ColorHil j (P.advocate 3 x j)
local notation "I!"=>Axis × List Axis

private def tickets (k:ℕ)(d: Axis × List Axis)(i:ℕ): (X d.1).Op:=
 (R₀:ℂ) • (a i (f,r):ℂ) •
 (((P.basePlay x f (v i)).pivot P d.2).velour P d.1 (y d.1) (τ k))
private def tokenB(A:ℝ):=max (‖(R₀:ℂ)‖ * P.flourish A) 1
local notation "D!"=>zoomC P.par.R.L^2



local notation "Y!"=>tickets P x v a f r
local notation "B!"=>tokenB P f r

include u in
private lemma safeCaps (w:ScoutAnthem P x A C f r b v a) (g:P.NightCop)(p:f<r)
   (o:Odd P.par.R.L.val):∀ᶠ k in atTop, ∀ d:I!, ∀ᶠ i:ℕ in atTop, ‖Y! k d i‖≤
       (B! A) * D!^k:=by
 obtain ⟨r',z⟩:=w.station
 filter_upwards [P.clover_cap g p o A C] with k h d
 have t:= h d.1 d.2
 filter_upwards [u.tendsto_atTop.eventually t] with i h
 obtain ⟨_,_,w⟩:=z.cruise i; have ht:=(h w x).2
 unfold tickets; rw [norm_smul]
 refine (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans ?_
 rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg (sq_nonneg _) _)
lemma narrowQuorum : StrictMono v → Tendsto (fun i=> (P.roomy:ℝ) * P.macroStep (v i)) atTop (𝓝 0):= by
 intro p; simpa only [mul_zero,Function.comp] using (P.macroStep_zero.comp p.tendsto_atTop).const_mul (P.roomy:ℝ)


private lemma exactTickets (s:ℕ → Coalition)(k:ℕ)(j:Axis)(l:List Axis):
   pool s (Y! k (j,l)) =ᶠ[atTop] (fun i=> (((T♯ s) i).pivot P l).velour P j (y j) (τ k)):=by
 filter_upwards [(P.narrowQuorum v u).eventually (gt_mem_nhds (P.macroStep_pos k))] with i h
 have e: (P.roomy:ℝ) * P.macroStep (v i) ≤ τ k:= (le_of_lt h)
 rw [P.pleading_velour x j f r i (s i) v u ..]; swap; exact e
 unfold pool; refine Finset.sum_congr rfl fun n w=>?_
 rw [Complex.ofReal_mul,Complex.ofReal_mul,mul_smul,mul_smul]; rfl

theorem velvet_council
 (K:P.Register)
 (w:ScoutAnthem P x A C f r b v a)
 (g:P.NightCop)(p:f<r)(o:Odd P.par.R.L.val):
 ∃s:ℕ → Coalition, P.VelvetCup x (T♯ s):=by
 let J(d:I!):=X d.1
 haveI(d:I!): SeparableSpace (J d).space:=P.colorPopulation d.1 _ K
 obtain ⟨s,h⟩:=pledgesLate J _ _ (safeCaps P x v u a f r w g p o)
 refine ⟨s, fun j l=>?_⟩
 let Q(n:ℕ):= ((T♯ s) n).pivot P l
 have z: Tendsto (fun i=>(Q i).realWidth P j) atTop (𝓝 0):=by
    unfold Q; simp_rw [Apron.pivot_w,P.pleading_w]; exact P.narrowQuorum v u


 refine ⟨z,macro_tender z ?_,
    B! A, D!, le_max_right _ _,one_le_pow₀ (zoomC_p P.par.R.L),?_⟩
 · refine h.mono fun k e=>?_
   obtain ⟨U,v'⟩:= (e (j,l)).2
   exact ⟨U,v'.agree (exactTickets P x v u a f r s k j l)⟩
 refine h.mono fun k e=> (((e (j,l)).1).and (exactTickets P x v u a f r s k j l)).mono fun n g=>?_
 exact le_of_eq_of_le (congrArg (‖·‖) g.2.symm) g.1

theorem velvet_radiated (K:P.Register)(w:ScoutAnthem P x A C f r b v a)
 (g:P.NightCop)(p:f<r)(o:Odd P.par.R.L.val):
 ∃ (s:ℕ → Coalition)(Y:∀ j:Axis,List Axis→ℝ→ X j),
   Radiates P x (T♯ s) Y ∧ P.VelvetCup x (T♯ s):=by
   obtain ⟨s,h⟩:=P.velvet_council x v u a f r K w g p o
   exact ⟨s,_, h.cinema_raw,h⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.velvet_radiated

