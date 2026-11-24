import YM.SU5.FiniteGaugeData.Poin.Celadon
import YM.SU5.FiniteGaugeData.Poin.Starley
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
variable (t u:M'.Token)(chip:M'.Chip)(g:Test4)(w:List M'.Token)
local notation "D"=>Bench S
local notation "F"=> M'.Model S Ω
local notation "L"=> M'.lens S Ω
local notation "D₀"=> Bench S
local notation "H₀"=> Hatch M' S Ω
local notation "K"=> Cache S
local notation "R"=> saucer S
open Submodule
variable (n:ℕ)
def crowd: F→ₗ[ℂ] H:= (hall S n).comp (M'.Model S Ω).subtype
abbrev Xroad := (LinearMap.range (crowd M' S Ω n)).topologicalClosure
local instance : CompleteSpace (Xroad M' S Ω n):= isClosed_closure.completeSpace_coe
local notation "U"=>Xroad M' S Ω n
variable (x:H)
include hΩ
lemma ride (p:E4)(e:x∈ Xroad M' S Ω n) : M S p x∈U:=by
 apply Set.MapsTo.closure (s:=Set.range (crowd M' S Ω n)) (t:=Set.range (crowd M' S Ω n)) ?_ (M S p).continuous e; rintro _ ⟨y,rfl⟩; exact ⟨ ⟨ usher S p y.val,fleet M' S Ω hΩ y.val p y.property⟩,ush_pre S p n _ ⟩ -- order ush.
lemma project_K: Commute (Cache S n) (Xroad M' S Ω n).starProjection:=
 (co_reg S (U).starProjection (fun p => ((align (S.edge p) U (timeslot S p ▸ fun x q=> ride M' S Ω hΩ n x (p • basis tt) q) (by
    intro t w; apply mem_orthogonal .. |>.2; intro x p'; rw [← timeslot S p,tboth]; exact w _ (ride M' S Ω hΩ n x (-(p • basis tt)) p') ))).symm)).pow_left n -- parens
lemma crowd_dense(p:M'.Climb S Ω=⊤): DenseRange (fun x:M'.Model S Ω=> hall S n x.val):=by
 intro x; refine (show x∈(U:Set H) from closure_minimal (s:=Set.range (L)) (t:=(U:Set H)) ?_ isClosed_closure ((Model_foot M' S Ω p) x))
 rintro _ ⟨y,rfl⟩; let t:= hall S n y.val; let P:=(U).starProjection; have ht:t∈U:= (le_topologicalClosure (LinearMap.range (crowd M' S Ω n))) ⟨y,rfl⟩; apply (starProjection_eq_self_iff).mp; change P (L y)= L y; rw [← show (K n) t=L y from releases S n y.val]; rw [show P (K n t)=K n (P t) from DFunLike.congr_fun (project_K M' S Ω hΩ n).eq.symm t]; rw [show P t=t from starProjection_eq_self_iff.mpr ht]
#print axioms project_K
-- any charge. determines inverse-energy operator uniquely at that charge.
variable (A B:H.Op)(PX:M'.Climb S Ω=⊤)
include PX
lemma encase (h:∀ (f:Test4)(x y:M'.Model S Ω), inner ℂ (L x) (ℑ S A f n y.val).val= inner ℂ (L x) (ℑ S B f n y.val).val): A=B:=by
 let Qc(x:M'.Model S Ω):= hall S n x.val; have he:=crowd_dense M' S Ω hΩ n PX; apply DFunLike.coe_injective; apply he.equalizer A.continuous B.continuous; funext x; apply he.eq_of_inner_right ℂ; intro y; -- `inner ...`
 let F'(p:E4):= lucent S (Qc y) (Qc x) A p-lucent S (Qc y) (Qc x) B p
 have hx(V:H.Op): Continuous (lucent S (Qc y) (Qc x) V):= continuous_const.inner (village S (Qc x) V)
 have hv:F'=fun _=>0:= Canopy.oracle _ ((hx A).sub (hx B)) (fun g=>by unfold F'; simp_rw [mul_sub]; rw [integral_sub (sell ..) (sell ..)]; apply sub_eq_zero.mpr; exact Eq.trans (assizes S A g y.val x.val n).symm ((h g y x).trans (assizes S B g y.val x.val n))) -- order assizes =? p? check
 have hh: F' 0=0:= congrFun hv 0; unfold F' lucent at hh; rw [vroot,vroot] at hh; exact sub_eq_zero.mp hh
#print axioms encase
lemma priority (P':H.Op)(h:∀ x:M'.Model S Ω, ∀ g:Test4, L (M'.operator S Ω chip g x)=(ℑ S P' g (M'.grade chip) x.val).val) : M'.dep chip=P':= encase M' S Ω hΩ (M'.grade chip) _ _ PX (fun f x y=>congrArg (inner ℂ (L x)) (h y f))
#print axioms priority
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
