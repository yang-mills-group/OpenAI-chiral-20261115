import YM.SU5.Relativistic.OddTrace2
import YM.CF.Buffered.Microscopic
import YM.CF.Buffered.Transfer

/-! # Marked Donor eyes with grading. Does not change the partner. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open YM.CF.Buffered.Heat
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra

private lemma seeded_even {n:Type*} [LinearOrder n] [Fintype n] (s:Finset n)(x:Op n): Sector univ false (seedR s x):=by
 unfold seedR; refine Sector.scale (Sector.add ?_ ?_) _
 · exact Sector.sumS _ _ fun i _=> Sector.sumS _ _ fun j _=> ((Sector.down i (mem_univ _)).mul (Sector.down j (mem_univ _))).scale _
 exact Sector.sumS _ _ fun i _=> Sector.sumS _ _ fun j _=> ((Sector.up i (mem_univ _)).mul (Sector.up j (mem_univ _))).scale _

variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : GramM (CSide m B)) (R : Loom (CSide m B)) (p : Pinning m B)
   (W : Scroll m B (Brace.northZ m B)) (clip : Clip) (u : ℝ)
local notation "c₀" => CSide m B
local notation "f₀" => Brace.northZ m B
variable (eyes : Eyes P X R p W clip u) {a D b : ℝ} (k : ScaleK a D W) (v : Budget B e b) {d' b' : ℝ} {n : ℕ} (T : Roof (CSide m B) b' d' n R) (h : X.p.threshold ≤ b') (U : Rue.IsleB SU.group X.p.threshold)
variable (i : Axis) (s : ℤ) (f : Mark (CSide m B))
local notation "μ" => gaugeShift B s
local notation "E" => Buffered.band c₀ i (gaugeShift B s) 0
include eyes k v T h U
lemma summitOdd (x : AtSupport true E f) (hu : 0 ≤ u) : 0 ≤ Complex.I * markedRead (reflMark i μ f*f) R (denZ X P R) := by
  rw [← mark_smul, summit_num P X R p W clip u eyes k v T h U]; swap
  · exact Girt.pole_w _ (fun x:FC (Single c₀) => Complex.I • x) (by fun_prop) (env_mult (x.refl i μ).env x.env)
  exact top_Fermi i s p W clip _ _ u v k hu (both f) (Env.along x.env (measurable_id.prodMk measurable_id)) (fun u v t=> x.dep _ _ t t) (fun a=> (x.allV (a,a)).sector)

include i s
lemma summonZero {S} (x:AtSupport true S f) : markedRead f R (denZ X P R) = 0 :=by
 rw [summit_num P X R p W clip u eyes k v T h U x.env,rephased_eq i s p W]
 unfold heatNum; rw [heatTerm_slab p W clip X.beta X.p.threshold u v]
 apply integral_eq_zero_of_ae
 apply Eventually.of_forall
 intro y
 -- multiply by the EVEN seeds and evolution.
 let Y' := actualEvol i f₀ u
 let F:= rephased i s (both f)
 let ν:= upperP c₀
 have he{J:Type}[LinearOrder J][Fintype J]: cutM (univ:Finset J)=1:= by ext i j; by_cases k:i=j<;>simp [cutM,k,Matrix.one_apply]
 have hy : Sector univ false (Y' y):= sector_exp (sector_real u (pair_charge (by rw [he,one_mul,mul_one])))
 have hY:(modesIn c₀ univ)=univ:= by ext t; simp [modes_at]
 have hz : Sector univ true (F y):= by
    apply Window.twist_sector -- ? arguments
    case p=> simp [he]
    apply Window.cross_sector (S:=univ) _ _
    swap; · intro i; simp
    unfold liftShift both
    have hp(a): Sector univ true (f a):= hY ▸ ((x.mono (subset_univ _)).allV a).sector
    apply north_sector _ _ _ (hp _)
    rw [he,map_one] -- maybe `_`
 have hv:= (hz.mul hy).mul (sector_exp (seeded_even ν (seedArg e y)))
 unfold slabTerm; change _ * (F y * Y' y * _ ) ν ν=0; rw [(show Sector univ true (F y*Y' y*seedOp e y) from hv).odd_lost, mul_zero]
end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.summonZero
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.summitOdd
