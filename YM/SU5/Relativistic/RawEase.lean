import YM.SU5.Relativistic.CorridorRaw
import YM.SU5.Relativistic.MapEase
/-!
# Geometry registration of local physical polynomials.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5500
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory Metric
open Lattice Wilson RG SU Lat Mir RP Reflect Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Py Py.Rate LocalLimit PhaseChoice Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)(G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis) (J: Arena Y H G.history.circuit j 0 false)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "D₀"=> Dome (tent Y H)
local notation "Τ"=> Cloud (Dome (tent Y H))
local notation "P₀" n:max=> vistaFinish Y H n D
local notation "d★" => vistaDressing Y H D
local notation "B₀" => driveAlgebra Y H D.univ_ G.history G.clipped j false J
local notation "Rg" t:max => Docked Y H D.univ_ t G.history G.clipped j J

local notation "ρ"=> D.univ_
local notation "reach" n:max f:max => reachMark (tent Y H) ((P₀ n) f)
section billing
variable (d:Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(χ : displayAlgebra Y H D.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "Χ"=> SameCharacter.resident Y H D.univ_ G d false (c d) χ
local notation "Ψ"=> onDrawing Y H D.univ_ G D d c Χ
local notation "Θ"=> procession Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "V"=>fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "p★"=>saunters Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "ω"=> vocation Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "A"=>ride Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ξ"=> peninsula Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j)
local notation "P□"=> mainsea Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "e□"=> follows_road Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "B□"=> docket Y H D G j (c j)
local notation "Φ"=> driveAlgebra Y H D.univ_ G.history G.clipped j false (c j)
local notation "dock" n:max => Docked Y H D.univ_ n G.history G.clipped j (c j)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

variable {I':Type*}(f:I'→ Cloud (Dome (tent Y H)))
variable (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ)) (l':List I')(b₁: Stamp (timeMesh Λ))
local notation "EE" i:max z:max => envelope (P□) (A) (e□) (Θ (B□ (t i) (f i) (S i))) (S i) (T i) z
local notation "Q₀" g:max=> packetEnvelope Y H D G j d c χ f t S T g l' b₁
local notation "ϕ" v:max=> integerRead v
local notation "GΛ"=> Axis → Stamp (timeMesh Λ)
local notation "R★" q:max=> rawRoom Y H D G j d c χ f l' b₁ T t S q
variable (u:I'→Axis→ℝ)
local notation "cm" t:max S:max T:max l:max b:max u:max=> Corridor Y H j f t S T l b u
local notation "Hb" l:max b:max x:max => bracing (A).E T (fun i=> E□ (S i) (T i) (B□ (t i) (f i) (S i)) (x i)) b l
section handmoves
variable {W:Type*}{F:Filter W}
lemma passing {x y:W→ I'→ Axis→ Stamp (timeMesh Λ)}(p:cm t S T l' b₁ u)(v:Tendsto (fun w=> integerRead (x w)) F (𝓝 u))(k:Tendsto (fun w=> integerRead (y w)) F (𝓝 u))(h:∀i∈l',∀ᶠ w in F,∀ a:Axis,a≠j→ x w i a=y w i a):
    Tendsto (fun w=> R★ (x w)- R★ (y w)) F (𝓝 0):=by
  let Z: (Ρ).Op →L[ℂ]ℂ:= (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ (Ρ).space Ω)
  let B i:= Θ (B□ (t i) (f i) (S i)); let C (w:W):= Hb l' b₁ (x w); let Y₀(w:W):= Hb l' b₁ (y w)
  have ht : Tendsto (fun w=> C w - Y₀ w) F (𝓝 0):= passage_cost (P□) A S T l' b₁ B u x y p.assured v k h
  have hs:= Z.continuous.tendsto 0 -- tune
  unfold rawRoom; change Tendsto (fun i => Z (C i)- Z (Y₀ i)) _ _; rw [show (fun i=> Z (C i)-Z (Y₀ i))= Z ∘ (fun w=>C w-Y₀ w) from funext fun i=> (map_sub Z _ _).symm, show (0:ℂ)= Z 0 from (map_zero _).symm]; exact hs.comp ht
end handmoves
lemma contour_cont : Continuous (windowPrice Y H D G j d c χ f t S T l' b₁):= continuous_const.inner (𝕜:=ℂ) (braceCont P□ A S T l' b₁ (fun i=> Θ (B□ (t i) (f i) (S i))) e□ ω)
lemma handholds (v:I'→Axis→ Stamp (timeMesh Λ))(p:cm t S T l' b₁ (ϕ v))(g:∀ k:Axis,∃ (w:List I')(b':Stamp (timeMesh Λ))(t':I'→ℕ)(X X': I'→ Slab (timeMesh Λ)), Corridor Y H k f t' X X' w b' (integerRead v) ∧ l'.Perm w): ContinuousAt (rawRoom Y H D G j d c χ f l' b₁ T t S) v:=by
  let G₁ := (ϕ v)
  let r := fun i: I'→Axis→ Stamp (timeMesh Λ)=> R★ i
  let M'(s: Finset Axis)(x:I'→Axis→ Stamp (timeMesh Λ))(i:I')(a:Axis):= if a∈s then x i a else v i a
  have he(s:Finset Axis): Tendsto (fun i=> integerRead (M' s i)) (𝓝 v) (𝓝 G₁):= by
    apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro a; by_cases h:a∈s
    · simp only [integerRead,M',if_pos h]; exact (continuous_subtype_val.comp ((continuous_apply a).comp (continuous_apply i))).continuousAt.tendsto
    simp only [integerRead,M',if_neg h]; exact tendsto_const_nhds
  have hp(s:Finset Axis): Tendsto (fun i=>r (M' s i)) (𝓝 v) (𝓝 (r v)):=by
     induction s using Finset.induction with
     | empty=> simpa [M'] using (show Tendsto (fun _ : I'→Axis→ Stamp M=>r v) (𝓝 v) (𝓝 (r v)) from tendsto_const_nhds)
     | insert a s h ih=>
       obtain ⟨w,b,t',X,X',q,m⟩:=g a
       let z₀:= M' s; let z₁:= M' (insert a s); have h₁:= he s; have h₂:= he (insert a s)
       let R' (v:I'→ Axis→ Stamp M):= rawRoom Y H D G a d c χ f w b X' t' X v
       have e(s:Finset Axis): (fun i=> R' (M' s i))=ᶠ[𝓝 v](fun i=> r (M' s i)):=by
          filter_upwards [(he s).eventually (q.openAt Y H a f t' X X' w b _),(he s).eventually (p.openAt Y H j f t S T l' b₁ _)] with i u v; exact (Corridor.raw_cmp Y H D G j d c χ f t S T l' b₁ (M' s i) v a w b t' X X' u m).symm
       have hh(i:I')(z:I'→Axis→ Stamp (timeMesh Λ)) (d:Axis)(v:d≠a):z₁ z i d=z₀ z i d:=by simp [z₁,z₀,M',v]
       have hv:= (passing Y H D G a d c χ f t' X X' w b G₁ (x:=z₁) (y:=z₀) q h₂ h₁ (fun i _=> Eventually.of_forall (fun j=> hh i j)))
       have hk:= hv.add (ih.congr' (e s).symm)
       change Tendsto (fun i=> R' (z₁ i)- R' (z₀ i)+R' (z₀ i)) (𝓝 v) (𝓝 (0+r v)) at hk
       simp_rw [sub_add_cancel,zero_add] at hk
       exact hk.congr' (e (insert a s))
  have he(x) : M' Finset.univ x=x:=by simp [M']
  apply tendsto_congr' ?_|>.1 (hp Finset.univ); exact Eventually.of_forall fun i=> congrArg r (he i)

end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.handholds
