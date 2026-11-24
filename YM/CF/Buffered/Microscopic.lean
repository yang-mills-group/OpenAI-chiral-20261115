import YM.CF.Buffered.StepIdentity
import YM.CF.Buffered.Place
import YM.CF.Chaff.Diet

/-! # Recover the actual microscopic HEAT numerator from a gaugeM push

Apply the startup identification off the given threshold ties. Its treshold
and beta must be those of the Gram history. Use generalized **eyes** with the
pin choice as in VolumeBurn proof, not a coarser stub assertion about bare
numerator or positivity. (In standard pin case use Chaff Lives_B as-is.)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Heat
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : GramM (CSide m B)) (R : Loom (CSide m B)) (p : Pinning m B)
   (W : Scroll m B (Brace.northZ m B)) (clip : Clip) (u : ℝ)
local notation "c₀" => CSide m B
local notation "f₀" => Brace.northZ m B
def Eyes : Prop := ∀ i:Orbit c₀, Rue.FleetS X.p.threshold i.1 → ∀ T:FC (Single c₀), inner ℂ (mateK c₀) (acts T (denZ X P R i))= ∫ z, heatTerm p W clip X.beta X.p.threshold e u f₀ (fun _=>Spark.crossL (helix _).symm T) (i.1,z) ∂rains m
variable (eyes : Eyes P X R p W clip u) {a D b : ℝ} (k : ScaleK a D W) (v : Budget B e b) {d' b' : ℝ} {n : ℕ} (T : Roof (CSide m B) b' d' n R) (h : X.p.threshold ≤ b') (U : Rue.IsleB SU.group X.p.threshold)
def both {n : Side} (f : Mark n) : Evaluation n := fun x=> f (x,x)
lemma term_hit (f g : RP.Test m B) (x : Pack m B) (a : f x=g x) (β t : ℝ) : heatTerm p W clip β t e u f₀ f x = heatTerm p W clip β t e u f₀ g x := by
  unfold heatTerm; by_cases h:x∈ TallyR m B e 0
  · rw [Set.indicator_of_mem h,Set.indicator_of_mem h,a]
  rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h]
include eyes k v T h U
lemma summit_num {A : Mark (CSide m B)} (y : Envelope A) : markedRead A R (denZ X P R) = heatNum p W clip X.beta X.p.threshold e u f₀ (insertTop (both A)) := by
  let f := insertTop (both A); let Y' := heatTerm p W clip X.beta X.p.threshold e u f₀ f
  have ht := Girt.pole_w _ (Spark.crossL (helix _).symm) (cxC _) (Env.along (g:=fun x:Pack m B=>(x.1,x.1)) y (measurable_fst.prodMk measurable_fst))
  apply Chaff.feastL (m:=m) X.p U _ Y' (Env.integrableX (heatTerm_env p W clip X.beta X.p.threshold u v k f₀ f ht) (RP.wheel m B))
  intro i t; change letterRead (A (i.1,R i)) _= _; rw [show letterRead (A (i.1,R i)) _= _ from eyes i t (A (i.1,R i))]
  refine integral_congr_ae (Eventually.of_forall fun z=> ?_)
  by_cases m' : i.1∈ Nova.Calm SU.group _ X.p.threshold
  · refine term_hit p W clip u _ f _ ?_ X.beta X.p.threshold; rw [Vale.Grace.Robes.solar i _ T _ h m']; rfl
  unfold Y' heatTerm; simp only [show Nova.primal clip (Domain m B) X.beta X.p.threshold i.1=0 from Set.indicator_of_notMem m' _, Complex.ofReal_zero,zero_mul]
omit eyes k v T h U
lemma both_north (f : Mark (CSide m B)) {i : Axis} {s : ℤ} (h : AtSupport false (Buffered.band (CSide m B) i s 0) f) :
    Envelope (both f) ∧ LocalOn (Buffered.band c₀ i s 0) (both f) ∧ ∀ x, Sector (modesIn c₀ (Buffered.band c₀ i s 0)) false (both f x) := ⟨Env.along h.env (measurable_id.prodMk measurable_id), fun x y v=> h.dep _ _ v v, fun x=> (h.allV (x,x)).sector⟩
include eyes k v T h U
variable (i : Axis) (s : ℤ) (f g : Mark (CSide m B))
local notation "μ" => gaugeShift B s
local notation "E" => Buffered.band c₀ i (gaugeShift B s) 0
-- trace limit on exactly the top mark obtained, reflection simultaneously peeled
lemma summit_trace (a : AtSupport false E f) (b : AtSupport false E g) (hu : 0≤u) :
    let l := fun n => transfer p W clip X.beta X.p.threshold u e i f₀ n
    Tendsto (fun n => kernelTrace (n+1) (l n (rephased i s (both g))) (kernelStar (n+1) (l n (rephased i s (both f))))) atTop
      (𝓝 (markedRead (reflMark i μ f * g) R (denZ X P R))) := by
  intro l; rw [summit_num P X R p W clip u eyes k v T h U]; swap; · exact env_mult ((a.refl i μ).env) b.env
  obtain ⟨p0,p1,p2⟩:= both_north f a; obtain ⟨q0,q1,q2⟩:= both_north g b
  exact displaced_limit i s p W clip X.beta X.p.threshold u v k hu (both f) (both g) p0 q0 p1 q1 p2 q2
lemma summit_gram (x : AtSupport false E f) (hu : 0 ≤ u) : 0 ≤ markedRead (reflMark i μ f*f) R (denZ X P R) := by
  rw [summit_num P X R p W clip u eyes k v T h U]; swap; · exact env_mult (x.refl i μ).env x.env
  obtain ⟨p0,p1,p2⟩:= both_north f x; exact top_nonnegative i s p W clip X.beta X.p.threshold u v k hu (both f) p0 p1 p2
end YM.CF.Buffered.Heat
