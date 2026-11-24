import GaugeFieldConstruction.StencilContour
import GaugeFieldConstruction.StencilWightman
import YM.SU5.Registration.Ink.Potential

/-!
Unpadding applied to the actual Carton in the elected phase.
-/
set_option autoImplicit false
set_option maxHeartbeats 170000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.NSF.Boundary
open MeasureTheory Filter Function Set Complex
open scoped Topology BigOperators NNReal ENNReal ContDiff InnerProductSpace
open YM.SatinWFixed InkPort Carton
open YM.Boundary (Joint)
variable {G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}{B:Small S C}
variable {V : Type*} [AddCommGroup V][Module ℂ V]{K:Hilbert}{D:YM.OS.Semigroup K timeAxis}
variable {A:Carton D V}
variable {n:ℕ}{q:V→ₗ[ℂ]S.Union}{U: K→ₗᵢ[ℂ] C.H}{F:InkWaves V}{W:WView V}
variable (v:InkPort A F W) (h:PreservesSmall D A.bar A.omega q U B)
variable {Φ:Waves S}{R:Surface S} (p:Bid.Direct B Φ)
private lemma trainCart {z:Times n}(x:SpacePoints n)(u:Fin n→ V)(a:ℝ≥0)(t:ℂ)(w: Space3): A.trainZ a n z x u t w=inkTrain D A.bar A.omega a n z x u t w:= by
 induction n generalizing t w with
 | zero=>rfl
 | succ n ih=> rw [Carton.trainZ,inkTrain,ih]; rfl
include v p h
lemma cont_reg (l:Fin n→V) (r:Φ.NonTangentialFree R) : (∀ z:Times n, z∈ strict n→∀ x:SpacePoints n, F.F n z x l= Φ.F n z x (q ∘ l))∧ W.W n l= R.W n (q ∘ l):=by
 obtain ⟨s,t⟩:= h.registration (F:=F) (W:=W) (R:=R) p (v:=l) (by
    intro n z a g k x l; calc
       _= _:= (show F.F n z x l= A.matrixZ g n z x l from v.strict_mat n z a g k x l)
       _= _ := by
          cases n with
          | zero=>rfl
          | succ n=> rw [Carton.matrixZ,inkAt,← trainCart])
 exact ⟨s,t v.level r⟩
-- filled Carton for all Union, including star valuation for Gram.
omit v p h
open SatinRegistration Grading
section
variable {A: Carton D S.Union}{F:InkWaves S.Union}{W:WView S.Union}{Y:Wightman S}{T:S.Rotation}{X:S.RealSpin}
variable (Z:Y.Realizes (W:=R) T X)(t:InkPort A F W)
local notation "ρ"=> A.row
local notation "δ"=> A.activate
variable (e: Remembers A Y.J)(Y0:∀ n (i:Fin n→S.Union), W.W n i = R.W n i)
include t Y0
lemma row_price (L:Sentence S) : inner ℂ (A.row []) (A.row L)= R.expect L:= by
 change inner ℂ A.omega (A.row L).val= _; rw [←t.real_value]; exact DFunLike.congr_fun (Y0 _ _) _ -- probe definition same
include Z e
lemma row_lift : Nonempty (WordLiftSt Y (H:=K) (radial D) A.row A.activate):=by
 refine word_dic Z _ _ _ ?_ (fun f g=>rfl); intro f g; rw [show inner ℂ _ _=_ from (show inner ℂ (A.row (f:MarkWords _)) (A.row (g:MarkWords _))=W.kernel Y.J f g from (t.real_pair Y.J e f g).symm)]
 change W.expect (Sentence.rev _ _ ++ g)= R.expect _; exact DFunLike.congr_fun (Y0 _ _) _
end
#print axioms cont_reg
#print axioms row_lift
end YM.NSF.Boundary
end
