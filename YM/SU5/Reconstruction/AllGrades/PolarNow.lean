import YM.SU5.Reconstruction.AllGrades.GatherPace
import YM.SU5.Reconstruction.AllGrades.LinkRamp
import YM.SU5.Reconstruction.AllGrades.Passage
import YM.SU5.Reconstruction.AllGrades.Dinner
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
open Germ
variable (T:Frostland Y H V G C j χ)(x y:studio (tent Y H) a 0 b)(l':Trans a)
local notation "ℋ" d:max s:max=> homePlane Y H V G D a d s
local notation "V₀"=> Impetus Y H V G D a b Τ
local notation "η"=>voter_credit Y H V G D a b C j χ
local notation "λx" b:max s:max x:max=> badge Y H V G D a b s (voterAt Y H V G C j χ) x
local notation "λo" b:max=>regime Y H V G D a b (voterAt Y H V G C j χ)
local notation "So"=> wheelTimes Y H V G D a b Τ η
local notation "Zμ"=> Lore (So) (λo b)
local notation "We" => turnLane Y H a b l'
local notation "Ml" n:max=> multiplyG Y H a b x (We n x)
local notation "ρL" s:max n:max=> notch (dainty Λ) s (n:ℤ)
open ConePrice.Session Germ SelectionAnalysis ConePrice Picket -- tune namespace
local notation "Tw"=> timeMesh Λ
private noncomputable def pocketHalfHelp(v:marks (timeMesh Λ)): marks (dainty Λ):= by
    refine ⟨(v:ℝ)/2,?_⟩; obtain ⟨s,z,rfl⟩:= notch_exists (timeMesh Λ) v
    refine ⟨s,(2*Λ.block.val*z:ℤ),?_⟩; rw [show (notch Tw s z:ℝ)=_ from as_deep Λ s z]; unfold bell; push_cast; ring
local notation "CH"=> pocketHalfHelp
noncomputable def halfMark (Λ:Preparation): marks (timeMesh Λ) →+ marks (dainty Λ) where
 toFun:= CH
 map_zero':= Subtype.ext (by change (0:ℝ)/2=(0:ℝ); ring)
 map_add' x y:= Subtype.ext (by change ((x+y:marks (timeMesh Λ)):ℝ)/2= (x:ℝ)/2+(y:ℝ)/2; rw [AddSubgroup.coe_add]; ring)
local notation "mP"=> halfMark Λ
lemma halfmark_on (v:marks Tw): mP v + mP v=finerNow Λ v:=by apply Subtype.ext; change (v:ℝ)/2+(v:ℝ)/2=v; ring
lemma cont_halfmark (Λ:Preparation): Continuous (halfMark Λ):= Continuous.subtype_mk (show Continuous (fun x:marks (timeMesh Λ)=>(x:ℝ)/2) by fun_prop) _

noncomputable abbrev realmReg := pull (λo b) (finerNow Λ)
local notation "Rt"=> realmReg Y H V G D a b C j χ
include B T
lemma walks_o (x:Works Y H V G D a b (voterAt Y H V G C j χ)) (i:Trans a): x∈ ((Rt).crew i).lives (Works Y H V G D a b (voterAt Y H V G C j χ)):=by
 let P:= T -- tune shadow notation
 let RP:=(λo b).crew i; have H':= Session.aunt_doubled (So) (λo b) (peninsula Y H V G.history G.clipped a false (C a) SJ) i x (allReplicas Y H V G D a b C j χ B T x) (B.forward a) (commutes_heat Y H V G D a b Τ i (voter_credit ..))
 change ContinuousAt (fun v:marks Tw=> RP.play (finerNow Λ v) x) 0
 have ht: ContinuousAt (fun r:marks Tw=>RP.play (mP r + mP r) x) 0 := ((show ContinuousAt (fun v:marks da=> RP.play (v+v) x) (mP 0) from (by rw [map_zero]; exact H')).comp (cont_halfmark Λ).continuousAt) -- tune syntax
 simpa only [halfmark_on] using ht
lemma ownWarm : (Rt).aviator (look a)=⊤:=by apply le_antisymm le_top; intro x _; exact ((Rt).assembled (look a) x).2 fun i _=> walks_o Y H V G D a b C j χ B T x i
omit B T in
lemma phase_one (i:Trans a)(v:marks (timeMesh Λ))(k:ℝ≥0):(((Rt).crew i).play v).comp ((So).E k)= ((So).E k).comp (((Rt).crew i).play v):= commutes_heat ..
noncomputable def travelingAll : OS.Semigroup (Works Y H V G D a b (voterAt Y H V G C j χ)) a:= Session.launchHouse (So) (Rt) (ownWarm Y H V G D a b C j χ B T) (phase_one Y H V G D a b C j χ) (daylight (timeMesh Λ))
local notation "σ"=> travelingAll Y H V G D a b C j χ B T
lemma latticeCaptions : Captions (So) (Rt) (σ) (LinearIsometryEquiv.refl ℂ (Works Y H V G D a b (voterAt Y H V G C j χ)).space):= caption_real ..
lemma all_light : Forward (σ):=by
 apply covers_forward (S) (σ) (daylight (timeMesh Λ)) (T.granted a) (B.forward a); intro x
 have h : Coupon.tagT (Γ:=marks Tw) (σ) x = Lore (So) (Rt) x := ((invoice (So) (Rt) _ _ (latticeCaptions Y H V G D a b C j χ B T) x)).symm
 let Q1:(∀ v:marks Tw,(finerNow Λ v:ℝ)=(v:ℝ)):= fun _=>rfl
 rw [h,← financed (So) (λo b) (finerNow Λ) Q1 x,show (Lore (So) (λo b) x∘ port (a:=a) _ Q1)^2=( ((Lore (So) (λo b) x)^2)∘ port (a:=a) _ Q1) from rfl]; exact pleasure (S) _ Q1 (allReplicas Y H V G D a b C j χ B T x) -- pow_fun rfl?
-- no extra Ward assumptions

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.all_light
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.latticeCaptions
