import YM.SatinExist.Toast
import YM.SU5.FiniteGaugeData.Seld.Murmur
-- Defeat of gauge-only interpretation needs presentations equiv on unpadded read. Derivative exactly smear.
set_option autoImplicit false
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H:Hilbert}{j:Axis}(S: OS.Semigroup H j) (r:ℕ)
local notation "U"=> S.E
local notation "K"=> Cache S
local notation "R"=> saucer S
variable (A:H.Op)(f:Test4)
-- movement in eu clock positive ⇒ transfer derivative; check any spin mark
lemma eventScalar : ℑ S (oneJet S A) f (r+1) = ℑ S A (-(εpref j f)) r:=by
 let F:= valise S A f; let g:= εpref j f; let G:=valise S A (-g)
 have hp : valise S (oneJet S A) f=R*G* R:=by
    have he:=orion S A f; have t(p:E4): Commute (M S p) R:=(tread S p).symm
    unfold oneJet; rw [sub_eq_add_neg,← neg_one_smul ℂ (_ * R), vadd,vscale,neg_one_smul, overlap _ _ _ _ t, overlap_R _ _ _ _ t,he]; rw [show G= -valise S A (εpref j f) from map_neg (barren S A) _]; simp
 ext1 x; apply Subtype.ext; apply cache_I S (r+1)
 let k:=hall S (r+1) x;
 rw [native, hp, show Cache S (r+1) = R* (Cache S r) from pow_succ' .. ]; change R (G (R k))= R (Cache S r _); rw [show R k= hall S r x from ?_,native];
 rw [←downstairs S 1 r]; simp only [Cache,pow_one]; rfl
end YM.SatinJets
