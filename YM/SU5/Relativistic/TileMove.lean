import YM.SU5.Relativistic.MapEase
/-!
# Relabel tiles
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace
variable {H:Hilbert}{I:Type*}{M:Mesh}{j:Axis}
def Slab.byStamp (S:Slab M)(z:Stamp M): Slab M := ⟨S.lower+z,S.upper+z, add_lt_add_left S.thick _⟩
lemma Slab.linesExtent {b: Stamp M}(z:Stamp M)(l:List I)(T:I → Slab M)(p:inRow T b l): inRow (fun i=> (T i).byStamp z) (b+z) l:=by
 induction l generalizing b with
 | nil=>trivial
 | cons i l ih=> exact ⟨add_le_add_left p.1 _,ih p.2⟩
lemma coh_origin (S:OS.Semigroup H j)(u v:Axis→ℝ) : S.U (diameter (u+v))= S.U (diameter u) * S.U (diameter v):=by unfold diameter; rw [show WithLp.toLp 2 (u+v)=WithLp.toLp 2 u+WithLp.toLp 2 v from rfl,map_add,S.space]; rfl
lemma coh_zero (S:OS.Semigroup H j) : S.U (diameter (0:Axis→ℝ))=1:=by unfold diameter; rw [show WithLp.toLp 2 (0:Axis→ℝ)=0 from rfl,map_zero, S.uZero]; rfl
lemma u_shift_cost (S:OS.Semigroup H j) (u:OS.Cross j) (x y:H): inner ℂ (S.U u x) (S.U u y)=inner ℂ x y:= LinearIsometry.inner_map_map ({ (S.U u).toLinearMap with norm_map' v:= S.unitary u v } : H →ₗᵢ[ℂ] H) x y
variable (P:Sunbelt j (marks M) H)(E: OS.Semigroup H j)
variable (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z))
local notation "L"=> P.track.Realm P.list
local notation "Ξ"=> glass P (daylight M) E e
local notation "Υ" u:max=> (Ξ).U (diameter u)
variable (B:H.Op) (S T:Slab M)
local notation "E₀"=> envelope P E e B
lemma margin_conj (z:Stamp M)(u v: Axis→ℝ)(p: (z:ℝ)= v j) :
    envelope P E e B S (T.byStamp z) (u+v)*Υ v = (Υ v)*(E₀ S T u):=by
 have h₂: ahead j S (T.byStamp z) (u+v)=ahead j S T u:=by unfold ahead; change Real.toNNReal (S.lower.val+(u j+v j)-(T.lower.val+(z:ℝ)))=_; rw [p]; congr 1; abel
 have h₃: off j S (T.byStamp z) (u+v)=off j S T u:=by unfold off; change Real.toNNReal ((T.upper.val+(z:ℝ))-(S.upper.val+(u j+v j)))=_; rw [p]; congr 1; abel
 have h(k:ℝ≥0)(v:Axis→ℝ): (Ξ).E k * (Υ v) = (Υ v)*(Ξ).E k:= (Ξ).independent ..
 unfold envelope; rw [h₂,h₃]
 let G₀:=compressed P B
 let g:= ahead j S T u
 let c:=off j S T u
 have hz: Υ (-(u+v)) * Υ v = Υ (-u):=by rw [← coh_origin, show -(u+v)+v = -u by abel]
 -- ac calc
 rw [show (Υ (u+v))=Υ v * (Υ u) from (by rw [add_comm u v, coh_origin])]
 change (Ξ).E g * (((Υ v) * Υ u)* G₀*(Υ (-(u+v))))*(Ξ).E c * Υ v= (Υ v)* _
 -- h
 rw [mul_assoc _ ((Ξ).E c),h c,←mul_assoc, mul_assoc ((Ξ).E g) _ (Υ v),mul_assoc _ (Υ (-(u+v))), hz]
 simp only [mul_assoc]
 rw [←mul_assoc ((Ξ).E g) (Υ v),h,mul_assoc] -- tune
lemma arc_shift (b:Stamp M)(l: List I)(S T:I→ Slab M)(B:I→H.Op)(z:Stamp M)(u:I→Axis→ℝ)(x:P.track.Realm P.list)(v:Axis→ℝ)(p:(z:ℝ)=v j):
    let G:=glass P (daylight M) E e; let U: (P.track.Realm P.list).Op:= G.U (diameter v)
    bracing G.E (fun i=> (T i).byStamp z) (fun i=> envelope P E e (B i) (S i) ((T i).byStamp z) (u i+v)) (b+z) l (U x)= U (bracing G.E T (fun i=> envelope P E e (B i) (S i) (T i) (u i)) b l x):=by
 induction l generalizing b with
 | nil=> exact rfl
 | cons i l ih=>
    have hg:heatGap (b+z) ((fun i=> (T i).byStamp z) i).lower= heatGap b (T i).lower:=by unfold heatGap; change Real.toNNReal ((_+(z:ℝ))-(b.val+(z:ℝ)))=_; simp
    dsimp only; rw [bracing,bracing]
    let A:= (Ξ).E (heatGap b (T i).lower)
    let Y:= envelope P E e (B i) (S i) (T i) (u i)
    rw [hg]; simp only [ContinuousLinearMap.mul_apply]
    specialize ih (T i).upper; rw [show ((T i).byStamp z).upper=(T i).upper+z from rfl, ih]
    let Y₀:= envelope P E e (B i) (S i) ((T i).byStamp z) (u i+v)
    let w:= bracing (glass P (daylight M) E e).E T (fun i=>envelope P E e (B i) (S i) (T i) (u i)) ((T i).upper) l x
    change A ((Y₀*(Υ v)) w)=_
    rw [show (Y₀*Υ v)=(Υ v)*Y from margin_conj P E e (B i) (S i) (T i) z (u i) v p]
    exact congrArg (fun f:(L).Op=> f (Y w)) ((Ξ).independent _ _)
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.arc_shift
