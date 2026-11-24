import YM.SU5.Reconstruction.AllGrades.Caption
import YM.SU5.Reconstruction.AllGrades.EvenRoute
import YM.SU5.Reconstruction.Trap.Castle
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Fm"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
open WindRose PolarArchives ConePrice SelectionAnalysis Chambers Brazier
variable (C:∀ j, Arena Y H G.history.circuit j 0 false)(j:Axis)
variable (χ: displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "mK"=> marks (timeMesh Λ)
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped a false (C a)
local notation "Ω₀"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped a false (C a)
local notation "F₊"=> Domain Y H G false (flank a 0)
local notation "Sm" m:max=> strip a (-(m:ℝ)) (m:ℝ)
local notation "Qt" m:max=> flank a (m:ℝ)
local notation "bM" d:max=> strip a (-d) d
local notation "A₀"=> atlasAt Y H V G
local notation "Pt" m:max=> Pub Y H a m
local notation "Bk" d:max f:max => (((badge Y H V G D a b d (atlasAt Y H V G)) f))
local notation "Px" u:max f:max=> ticket Y H G u f
local notation "rF"=> studio (tent Y H) a 0 b
local notation "rW"=> studio (tent Y H) a 0 false
local notation "Δ"=> timeMesh Λ
local notation "Wq" n:max=> walkC Y H a b n
local notation "Tr"=> cruise Y H a b

/-! # Unconditional even Spacebody voter equivalence & movement. -/
open Nymph
local notation "SJ"=> displacement Y H V G.history G.clipped j false (C j) χ a (C a)
local notation "KJ"=> indoor Y H V G.history G.clipped a false (C a) SJ
local notation "Τ"=> voterAt Y H V G C j χ
local notation "Q" t:max => badge Y H V G D a false t Τ
local notation "B⚬" t:max x:max=> bud Y H V t G.history G.clipped a false (C a) SJ x
local notation "FA"=>studio (tent Y H) a 0 false
local notation "FW" t:max=> Tower.Field Y H t a 0 false
local notation "ρ" t:max u:max p:max x:max=> homePlane Y H V G D a false t u p x
local notation "Sx"=> Works Y H V G D a false Τ

open Roy ConePrice.Session LightBudget
variable (B:BoostBacking Y H V G C j χ)
local notation "S"=> peninsula Y H V G.history G.clipped a false (C a) SJ
local notation "F"=> fort Y H V G.history G.clipped a false (C a) SJ
local notation "Fc"=> saunters Y H V G.history G.clipped a false (C a) SJ
local notation "Mu"=> voter_credit Y H V G D a false C j χ
local notation "R"=> wheelTimes Y H V G D a false Τ Mu
local notation "cr"=> regime Y H V G D a false Τ
local notation "λy"=> spokesman Y H V G D a C j χ
local notation "u₀"=> echoV Y H V G D a C j χ
local notation "kR"=> ride Y H V G.history G.clipped a false (C a) SJ
local notation "da"=> dainty Λ

lemma echo_clock(t:ℝ≥0)(x:Sx): u₀ ((R).E t x)=(kR).E t (u₀ x):=by
    apply closure_minimal (s:=times (dainty Λ)) (t:={t:ℝ≥0|(λy) ((R).E t x)=(kR).E t (u₀ x)}) ?_ (isClosed_eq ((λy).continuous.comp ((R).continuousE x)) ((kR).continuousE (u₀ x))) (fills (dainty Λ) t)
    rintro t ⟨s,t,rfl⟩; exact DFunLike.congr_fun (echo_heatN Y H V G D a s C j χ t) x
lemma echo_vac : u₀ ((Q s) (evenVac Y H a)) = doorstep Y H V G.history G.clipped a false (C a) SJ :=by
    rw [echo_at,show presentAt Y H a s _ =unity Y H a 0 false s from Subtype.ext rfl]; exact Selected.root ..
noncomputable def compression {H:Hilbert}(P:Submodule ℂ H)(p:P=⊤): H≃ₗᵢ[ℂ] P where
 toFun x:= ⟨x, by rw [p]; exact Submodule.mem_top⟩
 map_add' _ _:=Subtype.ext rfl
 map_smul' _ _:=Subtype.ext rfl
 invFun x:=x.val
 left_inv _:=rfl
 right_inv _:=Subtype.ext rfl
 norm_map' _:=rfl
include B
noncomputable def worthy : Sx≃ₗᵢ[ℂ] F:= (u₀).trans (compression (H:=indoor Y H V G.history G.clipped a false (C a) SJ) (Fc) (B.present a))
local notation "Zr"=> worthy Y H V G D a C j χ B
lemma worth_in(x:Sx):(Zr x:Fc).val=u₀ x:=rfl
lemma caption_even : Captions (R) cr (S) (Zr):=by
 let E' := Zr
 refine ⟨fun t x=>?_,fun i v x=>?_⟩
 · exact Subtype.ext (echo_clock Y H V G D a C j χ t x)
 obtain ⟨s,z,rfl⟩:= notch_exists (dainty Λ) v; apply Subtype.ext
 change echoV Y H V G D a C j χ _= ((S).U (_ • transversal a i.val i.property) (E' x):Fc).val
 rw [Nymph.enjoy Y H V G j C χ a i (B.forward a),regime_value]
 exact DFunLike.congr_fun (echo_spacN Y H V G D a s C j χ i z) x
lemma worth_this : Zr ((Q s) (evenVac Y H a))= vocation Y H V G.history G.clipped a false (C a) SJ:= by
 apply Subtype.ext; rw [worth_in,echo_vac,vocate]

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.caption_even
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.worth_this
