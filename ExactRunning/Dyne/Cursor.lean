import ExactRunning.Dyne.Cable
/-!
# Changing legs without changing the second coefficient

A lemma used both in transport of the fine Hessian and in changing the
external V. Fourth polarization issues here can matter: we don't assume
that *every* mixed entry with the fourth polarization is O(p²).
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Asymptotics

abbrev Cost (f : ℝ → ℂ) :=
  f =O[cutRay] (fun t : ℝ => t^2)

lemma Cost.small {f} (h : Cost f) : Tendsto f cutRay (𝓝 0) :=
  (isLittleO_one_iff ℝ).mp (h.trans_isLittleO ((isLittleO_one_iff ℝ).mpr (by
     simpa using ((tendsto_id (x:=𝓝 (0:ℝ))).pow 2).mono_left
       (nhdsWithin_le_nhds (s:={0}ᶜ)))))

lemma Touch.on_cut {f g : ℝ → ℂ} (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (h : (fun t=> f t - g t) =o[cutRay] fun t:ℝ => t^2) : Touch f g := by
  have h0 := tendsto_nhds_unique ((hf.tendsto.sub hg.tendsto).mono_left nhdsWithin_le_nhds)
    (Cost.small h.isBigO)
  refine ⟨hf,hg,?_⟩
  rw [← nhdsWithin_univ,
    show (Set.univ:Set ℝ)={0}ᶜ ∪ {0} from (Set.compl_union_self _).symm,nhdsWithin_union]
  exact h.sup ((isLittleO_zero _ _).congr'
    (show (fun _=>0)=ᶠ[𝓝[{0}] 0] (fun t=> f t-g t) by
      filter_upwards [self_mem_nhdsWithin] with _ (e : _ =0);rw [e];exact h0.symm)
    EventuallyEq.rfl)

section shake
variable {p : Momentum} {x₀ y₀ : Phase ι} {x y u v : ℝ → Phase ι} {K : Kin ι} {M : ℝ → Momentum}
variable {a b : ℝ → ℂ}
lemma soft_change (ha : Cost a) (hb : Tendsto b cutRay (𝓝 0)) :
    (fun t=> a t * b t) =o[cutRay] (fun t:ℝ=> t^2) :=
  (ha.mul_isLittleO ((isLittleO_one_iff ℝ).mpr hb)).congr_right (fun _=> mul_one _)

theorem shake (h : ContinuousAt (fun t=> K (M t)) 0)
    (sx : Tendsto x cutRay (𝓝 x₀)) (sy : Tendsto y cutRay (𝓝 y₀))
    (d : ∀i, Cost (fun t=> u t i))
    (e : ∀i, Cost (fun t=> v t i))
    (hi : Inert K (M 0) x₀ y₀) :
    (fun t =>
      (x t+u t) ⬝ᵥ K (M t) *ᵥ (y t+v t) - x t ⬝ᵥ K (M t) *ᵥ y t)
    =o[cutRay] (fun t:ℝ=> t^2) := by
  have th := h.tendsto.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
  have yy := sy.add (show Tendsto v cutRay (𝓝 0) from tendsto_pi_nhds.mpr fun i => (e i).small)
  rw [add_zero] at yy
  have r : Tendsto (fun t => K (M t) *ᵥ (y t+v t)) cutRay (𝓝 0) := by
    suffices K (M 0) *ᵥ y₀ = 0 from this ▸
      ((continuous_fst.matrix_mulVec continuous_snd).tendsto _).comp (th.prodMk_nhds yy)
    funext i;simpa using (hi (Pi.single i 1)).2
  have z : Tendsto (fun t => x t ᵥ* K (M t)) cutRay (𝓝 0) := by
    suffices x₀ ᵥ* K (M 0) = 0 from this ▸
      ((continuous_snd.matrix_vecMul continuous_fst).tendsto _).comp (th.prodMk_nhds sx)
    funext i
    simpa only [dotProduct_mulVec, dotProduct_single, mul_one] using! (hi (Pi.single i 1)).1

  have i := IsLittleO.sum (s:=Finset.univ) fun i _ => soft_change (d i) (tendsto_pi_nhds.mp r i)
  have j := IsLittleO.sum (s:=Finset.univ) fun i _ => soft_change (e i) (tendsto_pi_nhds.mp z i)
  refine (i.add j).congr_left fun t => ?_
  change u t ⬝ᵥ K (M t) *ᵥ (y t+v t) + v t ⬝ᵥ x t ᵥ* K (M t) = _
  rw [dotProduct_comm (v t), ← dotProduct_mulVec, add_dotProduct]
  rw [mulVec_add,dotProduct_add (x t)]
  abel

lemma Inert.minus {a₀ b₀ : Phase ι} (hx : Inert K p (x₀ - a₀) (y₀ - b₀)) :
    x₀ ⬝ᵥ K p *ᵥ y₀ = a₀ ⬝ᵥ K p *ᵥ b₀ := by
  have i := (hx y₀).1
  have j := (hx a₀).2
  rw [sub_dotProduct,sub_eq_zero] at i
  rw [mulVec_sub,dotProduct_sub,sub_eq_zero] at j
  rw [i,j]

end shake
end ExactRunning
