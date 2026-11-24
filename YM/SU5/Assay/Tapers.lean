import YM.SU5.Assay.WrapMix
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Meaning of negligible reimbursement (`Tapers`). Positive sequence
 absorbs *any* fixed exponential in the mark index. Partners need only
 `Inflates`. Both describe upper budgets, not convergence of marks.
-/
variable {d e:ℕ→ℝ}
def Inflates (d:ℕ→ℝ):Prop:= (∀s,0≤d s) ∧ ∃C:ℝ,0≤C ∧ ∃D:ℝ,0≤D ∧ ∀ᶠs in atTop,d s≤C*D^s
def Tapers (d:ℕ→ℝ):Prop:= (∀s,0≤d s) ∧∀D:ℝ,0≤D→ Tendsto (fun s=>d s*D^s) atTop (𝓝 0)
lemma Tapers.off (h:Tapers d):Tendsto d atTop (𝓝 0):=by simpa only [one_pow,mul_one] using (h.2 _ zero_le_one)
lemma Inflates.constant {c:ℝ}(u:0≤c): Inflates (fun _=>c):=⟨fun _=>u,_,u,_,zero_le_one,Eventually.of_forall fun n=>by simp⟩
lemma Tapers.inflates (h:Tapers d):Inflates d:=⟨h.1,_,zero_le_one,_,zero_le_one,by
 simpa only [one_pow,one_mul] using (Tapers.off h).eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))⟩
lemma Tapers.product (h:Tapers d)(v:Inflates e): Tapers (fun s=>d s*e s):=by
 obtain ⟨b,C,w,B',u,i⟩:=v
 refine ⟨fun s=> mul_nonneg (h.1 s) (b s),fun L t=> squeeze_zero' (Eventually.of_forall fun s=>mul_nonneg (mul_nonneg (h.1 s) (b s)) (pow_nonneg t _))
    (f:=fun n=>d n*e n*L^n) (g:=fun n=>C*(d n*(B'*L)^n)) ?_ ?_⟩
 · filter_upwards [i] with s a
   exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a (h.1 s)) (pow_nonneg t s)).trans_eq (by rw [mul_pow]; ring)
 simpa only [mul_zero] using (h.2 _ (mul_nonneg u t)).const_mul C
lemma Inflates.product (h:Inflates e)(v:Inflates d):Inflates (fun s=>e s*d s):=by
 obtain ⟨b,C,w,B',u,i⟩:=h;obtain ⟨a,E',p,L,t,k⟩:=v
 refine ⟨fun s=>mul_nonneg (b s) (a s),_,mul_nonneg w p,_,mul_nonneg u t,(i.and k).mono fun s z=>?_⟩
 exact (mul_le_mul z.1 z.2 (a s) (mul_nonneg w (pow_nonneg u _))).trans_eq (by rw [mul_pow];ring)
lemma Tapers.add (h:Tapers d)(u:Tapers e): Tapers (fun s=>d s+e s):=by
 refine ⟨fun s=> add_nonneg (h.1 s) (u.1 s),fun L t=>?_⟩
 simpa only [add_mul,zero_add] using (h.2 L t).add (u.2 L t)
variable {P j}{Z:Ballad.Lead.Clan}{A:ℕ→P.Glaze}
lemma Glaze.expands (h:Glaze.Grows j A): Inflates (fun s=>‖(A s).tile j s‖):=⟨fun s=>norm_nonneg _,h⟩

/-- Strengthening `Reel.shadow_vanish`. -/
lemma Reel.faded (r:P.Reel j Z)(h:Glaze.Grows j A): Tapers (fun s=> ‖(r.dusk (A s) (ply s)).tile j s‖):=by
 refine ⟨fun s=>norm_nonneg _,?_⟩
 obtain ⟨C,c,L,l,w⟩:=h
 intro B' v
 let D:=r.c
 have d:0≤D:=r.paid.2.2.1
 have e:D<1:=r.paid.2.2.2.1
 have hy:Tendsto (fun N:ℕ=> L*B'*D^N) atTop (𝓝 0):=by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one d e).const_mul (L*B')
 obtain ⟨N,g⟩:=(hy.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))).exists
 let q:= L*B'*D^N; have ht: 0≤q:=by unfold q; positivity
 have hk : Tendsto (fun s:ℕ=> C*q^s) atTop (𝓝 0):=by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht (show q<1 from g)).const_mul C
 apply squeeze_zero' (Eventually.of_forall fun _=>mul_nonneg (norm_nonneg _) (pow_nonneg v _)) _ hk
 filter_upwards [w,r.history,eventually_ge_atTop N] with s h u y
 have hp:N*s≤ply s:=le_trans (Nat.mul_le_mul_right s y) (by unfold ply; rw [pow_two]; omega)
 have hD:= (u (A s) (ply s)).trans (mul_le_mul h (pow_le_pow_of_le_one d e.le hp) (pow_nonneg d _) (mul_nonneg c (pow_nonneg l _)))
 refine (mul_le_mul_of_nonneg_right hD (pow_nonneg v _)).trans_eq ?_
 unfold q; rw [mul_pow,mul_pow,←pow_mul]; ring
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
