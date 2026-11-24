import YM.CF.Continuum.Sten

/-!
# Compute the price of point currents in the Emu Wick window

List order convention starts each matched pair with a **down** letter, then an
up letter. Tracings separate, no Haar factors left. Distinct bilinears use
arbitrary common ordering after each contributes the same Cool component to a
family of momenta. Valuation in the free comparison uses the left block of
`pencil`; the i in the spatial weights is retained (not Hermitianizing with its
conjugate). We first compute the target before making any limiting claim.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter Metric Finset Fock Lattice Lat Rush Cube SU Scroll Spire Tulip Mir Mir.Trip Phase RP
open Onyx Flare Emu Dial Ember Kea Jill
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
open YM.Stationary (Gaia)

section tall
variable {R : ℕ→ℝ} {I : Type*}
/-- A recorded spacetime/flavor with separate route bookkeeping. -/
abbrev Glyph (I : Type*) := I × Wing
def marked (u : I→Gaia) (z : ℕ→I→Cover)
    (v : ∀ i, Tendsto (fun k=>riseX (R k) (z k i)) atTop (𝓝 (u i)))
    (t : ∀ i j, u i=u j → ∀ᶠ k in atTop, z k i=z k j) : Plot (Glyph I) R:= ⟨fun k x=>z k x.1, Prod.snd, u∘Prod.fst, fun a=>v a.1, fun i j=> t i.1 j.1⟩
-- port tracing with l=1
abbrev dst(x : I)(c : Slot)(a : Component) : Glyph I:= (x,⟨a.down,c,1⟩)
abbrev src(x : I)(c : Slot)(a : Component) : Glyph I:= (x,⟨a.up,c,1⟩)
def letters (x : I)(a : Component)(c : Slot) : List (Glyph I) := [dst x c a, src x c a]
variable {u : I→Gaia} {z : ℕ→ I → Cover} (v : ∀ i, Tendsto (fun k=>riseX (R k) (z k i)) atTop (𝓝 (u i))) (t : ∀ i j, u i=u j → ∀ᶠ k in atTop, z k i=z k j)
local notation "ρ" => Plot.rho (marked u z v t)

lemma rho_same (b : Glyph I) (s : Glyph I) (h : signW b.2 = signW s.2) : ρ b s = 0 := if_pos h
lemma rho_up_up (x y : I) (a b : Component)(c d : Slot) : ρ (src x c a) (src y d b) = 0 := by apply rho_same; change decide (a.up ∉ _) = decide (b.up ∉ _); simp [a.hu,b.hu]
lemma rho_down_down (x y : I) (a b : Component)(c d : Slot) : ρ (dst x c a) (dst y d b) = 0 := by apply rho_same; change decide (a.down ∉ _) = decide (b.down ∉ _); simp [a.hd,b.hd]
lemma rho_hit (x y : I) (a b : Component)(c d : Slot) : ρ (dst x c a) (src y d b) = if c=d then pencil (u x-u y) a.down b.up else 0 := by
  simp [Plot.rho,marked, Function.comp, signW,a.hd,b.hu, frank]
lemma rho_flip (x y : I) (a b : Component)(c d : Slot) : ρ (src x c a) (dst y d b) = -ρ (dst y d b) (src x c a) := by
  simp [Plot.rho,marked, Function.comp, signW,a.hu,b.hd]
lemma rho_side (x : I) (a b : Component)(c d : Slot) : ρ (dst x c a) (src x d b) = 0 := by rw [rho_hit]; simp [pencil]

lemma two_letters (x : I)(a : Component)(c : Slot) : runes ρ (letters x a c)=0:=by
  simp [letters,runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,rho_side]

private lemma wick₂ {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

-- lists may repeat points
private lemma wick₃ {T : Type*}(d : T→T→ℂ)(p q r s t u : T) : runes d [p,q,r,s,t,u]=
    d p q*runes d [r,s,t,u]- d p r*runes d [q,s,t,u]+ d p s*runes d [q,r,t,u]- d p t*runes d [q,r,s,u]+d p u*runes d [q,r,s,t]:=by
  simp_rw [wick₂]
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

theorem four_letters(x y : I)(c d : Slot)(a b : Component) : runes ρ ((letters x a c) ++ (letters y b d)) = (if c=d then -(pencil (u x-u y) a.down b.up * pencil (u y-u x) b.down a.up) else 0) := by
  change runes ρ [dst x c a, src x c a,dst y d b,src y d b]=_
  rw [wick₂,rho_side,rho_side, rho_flip, rho_up_up,rho_down_down,rho_hit,rho_hit]
  by_cases h:c=d<;> simp [h,Eq.comm]

def sixM (x y z : Gaia)(a b e : Component) := pencil (x-y) a.down b.up*pencil (y-z) b.down e.up*pencil (z-x) e.down a.up+pencil (x-z) a.down e.up*pencil (y-x) b.down a.up*pencil (z-y) e.down b.up

theorem six_letters(x y k : I)(c d f : Slot)(a b e : Component) : runes ρ ((letters x a c) ++ (letters y b d) ++ (letters k e f)) = (if c=d ∧ d=f then sixM (u x) (u y) (u k) a b e else 0) := by
  change runes ρ [dst x c a, src x c a,dst y d b,src y d b,dst k f e, src k f e] = _
  rw [wick₃]; simp only [rho_side, rho_down_down, zero_mul,sub_zero, zero_sub, wick₂, rho_up_up]; simp only [rho_flip]; simp only [rho_hit]
  by_cases h:c=d <;> by_cases t:d=f
  · subst c; subst d; simp [sixM]; ring
  · subst c; simp [t,Ne.symm t]
  · subst f; simp [h,Ne.symm h]
  simp [h,t,Ne.symm h,Ne.symm t]

lemma two_trace (x y : I)(a b : Component) : (∑ c∈colors a.fam,∑ d∈ colors b.fam,runes ρ ((letters x a c)++ letters y b d))= if a.fam=b.fam then dimf a.fam • -(pencil (u x-u y) a.down b.up * pencil (u y-u x) b.down a.up) else 0 := by
  simp_rw [four_letters]
  split_ifs with h
  · simp [←h,colors_card]
  apply sum_eq_zero; intro c p; apply sum_eq_zero; intro d q; refine if_neg ?_; rintro rfl; exact h ((mem_filter.mp p).2.symm.trans (mem_filter.mp q).2)

def threeTrace (u : I→Gaia)(z : ℕ→I→Cover)(v : ∀ i, Tendsto (fun k=>riseX (R k) (z k i)) atTop (𝓝 (u i)))
    (t : ∀ i j,u i=u j→ ∀ᶠ k in atTop,z k i=z k j)(x y l : I)(a b e : Component) : ℂ :=
    ∑ c∈colors a.fam,∑ d∈colors b.fam,∑ f∈colors e.fam,runes (Plot.rho (marked u z v t)) (letters x a c++letters y b d++letters l e f)
lemma three_trace (x y l : I)(a b e : Component)(h : b.fam=a.fam)(g : e.fam=a.fam) : threeTrace u z v t x y l a b e=dimf a.fam • sixM (u x) (u y) (u l) a b e := by
  unfold threeTrace; simp_rw [six_letters,h,g]
  rw [← colors_card, ←sum_const]; refine sum_congr rfl fun i k=>?_; rw [sum_eq_single_of_mem i k]; · simp [k];
  intro j e h; simp [Ne.symm h]
end tall
end YM.CF.Window
