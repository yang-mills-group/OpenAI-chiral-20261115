import YM.SU5.FiniteGaugeData.Poin.Lykos
import YM.SU5.FiniteGaugeData.Poin.BrightT
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
local notation "L"=>M'.Ticket S Ω
abbrev Model := Submodule.span ℂ (Set.range (M'.bud S Ω))
def Strand : Submodule ℂ H:= (M'.Model S Ω).map (Bench S).subtype
abbrev Climb := (M'.Strand S Ω).topologicalClosure
local notation "B"=> Model M' S Ω
local notation "D₀"=> Strand M' S Ω
local notation "P"=> M'.Climb S Ω
local notation "L₁"=> M'.bud S Ω
open Submodule
variable (x z:Bench S)(A:H.Op)(Y:H)
lemma models : M'.Strand S Ω= span ℂ (Set.range (L)):=by unfold Strand Model; rw [map_span,← Set.range_comp]; rfl
lemma Mmem : (M'.bud S Ω w)∈ M'.Model S Ω := subset_span ⟨w,rfl⟩
lemma omegaW : Ω ∈ M'.Model S Ω:= Mmem M' S Ω []
lemma membrane (p:x∈ M'.Model S Ω): x.val∈ Strand M' S Ω:= mem_map_of_mem p
lemma memberS (p:x∈(Strand M' S Ω).comap (Bench S).subtype): x∈ Model M' S Ω:=by
 obtain ⟨y,h,t⟩:= (show x.val∈D₀ from p); exact (Subtype.ext t : y=x) ▸ h
lemma wardown : (M'.bud S Ω w).val∈M'.Climb S Ω:= le_topologicalClosure _ (membrane M' S Ω _ (Mmem M' S Ω w)) -- s name
lemma OmegaP: Ω.val∈ M'.Climb S Ω:= wardown M' S Ω []
-- eval on Model: actual invariant domain
lemma advance (p:x∈ Model M' S Ω): M'.horizon S t x∈ Model M' S Ω:=by
 let V:= horizon M' S t; apply (show B≤ (B).comap V from span_le.mpr ?_) p; rintro _ ⟨w,rfl⟩; exact Mmem M' S Ω (t::w)
lemma twoface : reve M' (reve M' t)=t:=Prod.ext (Lduo M' _) (Probe.bar_twice t.2)
-- mapZ proof.Q.
lemma respects (p:z.val∈ (M'.Climb S Ω)ᗮ): (M'.horizon S t z).val∈ (M'.Climb S Ω)ᗮ:=by
 rw [Climb, orthogonal_closure] at p ⊢; apply (mem_orthogonal _ _).2; rintro x ⟨u,v,rfl⟩; change inner ℂ u.val _=_; rw [← show M'.reve (M'.reve t)=t from twoface ..,← legPaid]; exact p _ (membrane M' S Ω _ (advance M' S Ω _ _ v)) -- t repeated definition in legPaid maybe.
variable (u:E4)
local notation "U"=> M S
local notation "K"=> saucer S
local instance zProj : CompleteSpace (M'.Climb S Ω):= isClosed_closure.completeSpace_coe
-- public definitions cannot use private instance in result? cod.Restrict.S
include hΩ
lemma fleet (p:x∈M'.Model S Ω): usher S u x ∈ B := by
 let G:=usher S u; apply (show B≤ (B).comap G from span_le.mpr ?_) p; rintro _ ⟨w,rfl⟩; change G (M'.bud S Ω w) ∈ B; rw [show G (M'.bud S Ω w)=_ from bring M' S Ω hΩ w u]; exact Mmem M' S Ω _
lemma calm (p:Y∈ M'.Strand S Ω): M S u Y∈ M'.Strand S Ω:=by rcases p with ⟨y,t,rfl⟩; exact membrane M' S Ω _ (fleet M' S Ω hΩ _ _ t)
lemma pureM (p:Y∈M'.Climb S Ω): M S u Y ∈ M'.Climb S Ω:= MapsTo.closure (s:=(D₀:Set H)) (t:=(D₀:Set H)) (fun x p=> calm M' S Ω hΩ x u p) (U u).continuous p
lemma tailing(y:H) (v:y∈ (M'.Climb S Ω)ᗮ): U u y∈ Pᗮ:=by
 apply (mem_orthogonal _ _).mpr; intro x p; rw [tboth]; exact v _ (pureM M' S Ω hΩ x (-u) p)
-- Proj.price
omit hΩ
abbrev Hatch:H.Op:=(M'.Climb S Ω).starProjection
local notation "J"=> Hatch M' S Ω
lemma carp : Hatch M' S Ω Ω.val=Ω.val:= starProjection_eq_self_iff.mpr (OmegaP M' S Ω)
lemma align (UU:Submodule ℂ H.space)[CompleteSpace UU](p:MapsTo A (UU:Set H.space) UU)(h:MapsTo A (UUᗮ:Set H.space) UUᗮ): Commute A UU.starProjection:= by
 ext1 x; apply Eq.symm; apply eq_starProjection_of_mem_orthogonal (p (UU.starProjection_apply_mem x)); change A x-A (UU.starProjection x) ∈ UUᗮ; rw [←map_sub]; exact h (sub_starProjection_mem_orthogonal x)
include hΩ
lemma stock : Commute (M S u) (J) := align (U u) (P) (fun _ p=> pureM M' S Ω hΩ _ u p) (fun _ p=> tailing M' S Ω hΩ u _ p)
lemma r_cap : Commute (saucer S) (Hatch M' S Ω) := co_reg S (J) (fun t=> by rw [← timeslot]; exact (stock M' S Ω hΩ _).symm)
lemma heat_P(u:ℝ≥0): Commute (S.E u) (J):=by
 rcases eq_zero_or_pos u with rfl|k; · rw [S.eZero]; exact Commute.one_left _
 exact dielectric S (J) u (r_cap M' S Ω hΩ) k
#print axioms r_cap
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
