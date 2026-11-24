import YM.CF.DPress.Wagon.Touch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Race
structure Reward (T:Race n L) (A:Style T) where
 fee: Bool→ℝ
 p(i):0<fee i
namespace Reward
variable {T:Race n L}{A:Style T}(μ:Reward T A)(X: List Bool)
def cost := (X.map μ.fee).prod
lemma cost_p : 0 < μ.cost X:=by
 induction X with|nil=> exact zero_lt_one|cons i X ih=> exact mul_pos (μ.p i) ih
lemma dual : μ.cost X.reverse= μ.cost X:=by simp [cost,List.map_reverse]
lemma adds (Y: List Bool): μ.cost (X++Y)= μ.cost X*μ.cost Y:=by simp [cost]
lemma constant (i:Bool)(k:ℕ):μ.cost (List.replicate k i)= μ.fee i^k:=by simp [cost]
end Reward
namespace Credit
variable {T:Race n L}(A:Style T)(μ:Reward T A){ℒ:Fixed.Test n→ℝ}(p:Bound T ℒ) (B: List Bool)
def tab (ℒ:Fixed.Test n→ℝ) : Set ℝ:= { t |∃ (a:ℤ)(b:Bool)(X:Fixed.Test n), Credit A a b B X ∧ ℒ X/μ.cost B=t}
def tariff (ℒ:Fixed.Test n→ℝ)(B: List Bool):= sSup (tab A μ B ℒ) -- binder order
lemma t_tar : ℒ 1/μ.cost B∈ tab A μ B ℒ:=⟨0,true,1,Credit.unitP ..,rfl⟩
include p
lemma roof : BddAbove (tab A μ B ℒ) :=by obtain ⟨k,h⟩:= p.cap (A.V^B.length); refine ⟨k/μ.cost B,?_⟩; rintro x ⟨a,b,v,hv,rfl⟩; exact div_le_div_of_nonneg_right (h v hv.tag.cost hv.tag.borel) (μ.cost_p _).le
lemma hard(a:ℤ)(b: Bool)(x)(h:Credit A a b B x): ℒ x/μ.cost B≤ tariff A μ ℒ B:=le_csSup (roof A μ p B) (⟨a,b,x,h,rfl⟩)
lemma f_income : 0 ≤ tariff A μ ℒ B:= (div_nonneg (p.light 1) (μ.cost_p _).le).trans (hard A μ p B 0 true 1 (Credit.unitP ..))
omit p
lemma rotate_N (P:List Bool)(v:(B.length+P.length)*A.w=T.η)(q: Even (B.length+P.length)): tab A μ (B++P) ℒ= tab A μ (P++B) ℒ:=by
 have he(B P: List Bool)(u:(B.length+P.length)*A.w=T.η)(q:Even (B.length+P.length)):tab A μ (B++P) ℒ⊆tab A μ (P++B) ℒ:= fun x ⟨w,b,v,h,t⟩=> ⟨_,_,v,rotate_Q h (by simp only [blockP,List.length_append,u]) (List.length_append ▸ q), (by rw [←t, μ.adds, μ.adds,mul_comm (μ.cost P)])⟩
 exact Set.Subset.antisymm (he B P v q) (he P B (by rw [Nat.add_comm]; exact v) (by rw [Nat.add_comm]; exact q))
include p
lemma duplicateD {X:Fixed.Test n}(a:ℤ)(b:Bool)(P:List Bool)(h:Credit A a b (B++P) X)(v:B.length=P.length)(q:(B.length+P.length)*A.w=T.η): (ℒ X / μ.cost (B++P))^2 ≤ tariff A μ ℒ (B++B.reverse)*tariff A μ ℒ (P.reverse++P):=by
 obtain ⟨Y,Z,y,z,t⟩:= duplicate A p b h v (by rw [←add_mul]; exact q); let Q:=ℒ X; have he:0 ≤ ℒ Y / μ.cost (B++B.reverse):=div_nonneg (p.light _) (μ.cost_p _).le; refine le_trans ?_ (mul_le_mul (hard A μ p _ a b _ y) (hard A μ p _ a b _ z) (div_nonneg (p.light _) (μ.cost_p _).le) (he.trans (hard A μ p _ a b _ y))); rw [div_pow,div_mul_div_comm]; rw [show μ.cost (B++B.reverse)*μ.cost (P.reverse++P)=(μ.cost (B++P))^2 from ?_]; · exact div_le_div_of_nonneg_right t (sq_nonneg _)
 rw [μ.adds, μ.adds,μ.adds,μ.dual,μ.dual]; ring -- tune rule term inference
lemma highTop (P: List Bool)(v:B.length=P.length)(q:(B.length+P.length)*A.w=T.η): tariff A μ ℒ (B++P)^2 ≤ tariff A μ ℒ (B++B.reverse)*tariff A μ ℒ (P.reverse++P):=by
 let R:= tariff A μ ℒ (B++B.reverse)*tariff A μ ℒ (P.reverse++P); have hr:0≤R:=mul_nonneg (f_income A μ p _) (f_income A μ p _); let U:=tariff A μ ℒ (B++P); have hu:U≤Real.sqrt R:=by
    refine csSup_le (Set.nonempty_of_mem (t_tar A μ (B++P))) ?_; rintro i ⟨a,b,x,y,rfl⟩; have he:= Real.sq_sqrt hr; have hp:(ℒ x/μ.cost (B++P))^2≤R:=duplicateD A μ p B a b P y v q; nlinarith [Real.sqrt_nonneg R]
 exact le_trans (pow_le_pow_left₀ (f_income A μ p _) hu 2) (Real.sq_sqrt hr).le
end Credit
end Race
end YM.CF.DPress.Wagon
