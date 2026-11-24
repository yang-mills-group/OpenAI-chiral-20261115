import YM.CF.BProof.Oasis.Fee
/-! The extended Wick domain & billing against the actual bra/ket. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums Civic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P:Spin.Ready j a b l r}{F: Core j a b l r N}{H:Honor P F δ}(x:Loft F δ c v η)
lemma leanA : IsStarProjection (coreA x):= (show Ride .. from x.property).breeze.1
lemma coreSkew:(coreB x)ᵀ= -coreB x:= ((show Ride .. from x.property).pores 1 Wick.walk1).3
abbrev owner := F.θ (carried x.val.1) 1
def valid (u:Phys N) := Wick.Task (owner x) u
variable {m q e ε o α k:ℝ}{D:GramM N}{T:Plant N}
def heatW (x:Loft F δ c v η): Lv N→Lv N→ℂ:=flank (paymentE x)
variable {y:Pay}
def oracle (x:Loft F δ c v η) (u:Phys N):= normal u (pressK x)
variable {U:Phys N}(s:valid x U)
include s
lemma pulse : Scores (heatW x) (fun L=>oracle x U (rollC (act (Oasis.letter _ (coreSkew x)) (nursery _ (leanA x))) L)):=by
 have he:= finalGauge s (Tape.apartSeat x.val.1.val.2) (show Ride .. from x.property).frame (glass (coreA x) (coreB x)); simp_rw [flankIssue] at he; rw [show act (Oasis.letter _ (coreSkew x)) (nursery _ (leanA x))=fun i=> printT (glass (coreA x) (coreB x) i) from funext (token_x (leanA x) (coreSkew x))]; exact he
lemma sharp: inner ℂ (pressK x) U ≠0:=value_press s (Tape.apartSeat _) (show Ride .. from x.property).frame
variable (M:Marks H y c v η)(q:Cargo D m o)(R:Tube D y m ε o α e)
def gustLog(A:OptionJ N→ℂ)(B:OptionF N→ℂ)(t:ℝ)(E:GramM N)(Z:Pane N) (i:Y (More N)): ℂ:=logF (plaza E.p N) (M.eye x) (hotA E t B Z A) i
include R
lemma extinctD(t:ℝ)(Z:Pane N) (A:OptionJ N→ℂ)(B: OptionF N→ℂ) (h:Known (M.eye x) (hotA D t B Z A) M.award (q.runs ε)): oracle x U ((Oasis.letter _ (coreSkew x)).cook ((ArcJ N).foldS A)*tank (coreA x) (zoom D t B Z))= Complex.exp (PriceR D t Z+ ∑ i, gustLog x M A B t D Z i):=by
 let W:= s; let C:=heatW x; have hg:=censorSkew (I:=Lv N) C; have hf:= pulse x s; rw [trio (coreSkew x) D Z q.fitted (leanA x) (oracle x U) hf hg (censorTruth _ _ _ hf), Complex.exp_add]; exact congrArg (Complex.exp (PriceR D t Z)*·) (Able.pfC (Tube.known M q R) h _ hg (fun i j t=> M.law x t))
omit s
lemma quiet (t:ℝ)(v:‖t‖≤1)(Z:Pane N) : Known (M.eye x) (hotA D t 0 Z 0) M.award (q.runs ε) :=by
 apply cKnown; rintro (i|(i|i)); exact (by change ‖(0:ℂ)‖≤ε*sitePrice; rw [norm_zero]; exact mul_nonneg R.height (zero_le_one.trans sitePrice_p)); exact r_cost q v _ _; change ‖(0:ℂ)‖≤_; rw [norm_zero]; exact q.fend ..
omit R
lemma busy (b:Orbit N)(S:Support N)(X:Fields N){w:ℂ}(f:∀ i, ‖T.leaf i‖ ≤ sitePrice)(g:‖w‖≤ ε) : Known (M.eye x) (hotA D 1 (RateF D X.1 b) b.1 (tokenJ S X.2 w T (coreB x))) M.award (q.runs ε):=by
 apply cKnown; rintro (i|(i|i)); exact j_cost g f S x X.2 i; exact r_cost q (by simp: ‖(1:ℝ)‖≤1) _ _; exact f_cost ..
-- root equality from support reads
lemma niceEye(i:Support (More N))(x':Loft F δ c v η)(d:(Tape.kiln H.1 c v η).st.eval i x x'=0)(p u: Lv N) : M.eye x p u i=M.eye x' p u i:=by
 have he:= (M.expo p u i).variation x x'; change _ ≤ M.award p u i * (Tape.kiln H.1 c v η).st.eval i x x' at he; rw [d,mul_zero] at he; exact sub_eq_zero.mp (norm_le_zero_iff.mp he)
end YM.CF.BProof.Oasis
