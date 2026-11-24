import YM.SU5.Reconstruction.AllGrades.EpochEddy
import YM.SU5.Reconstruction.AllGrades.Offset
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
local notation "Σv"=> peninsula Y H V G.history G.clipped a false (C a) SJ
local notation "ᾼ"=> fort Y H V G.history G.clipped a false (C a) SJ
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
open ConePrice Session
open InnerProductSpace
local notation "Kσ"=> (Works Y H V G D a b Τ)
local notation "σ"=> travelingAll Y H V G D a b C j χ B T
local notation "Hψ"=> (λo b).crew l'
local notation "Ζ"=> (Hψ).play
local notation "pm" t:max x:max=> ((badge Y H V G D a b t Τ) x)
local notation "CK" c:max=> wheelTimes Y H V G D c b Τ (voter_credit Y H V G D c b C j χ)
local notation "Ho" c:max s:max x:max=> badge Y H V G D (c:Axis) b s Τ x
local notation "Sk" c:max=> studio (tent Y H) c 0 b
local notation "vR" t:max=> (travelingAll Y H V G D a b C j χ B T).E t

local notation "nf" t:max=> whenly (dainty Λ) t
-- unconditional credit far b. Includes even/odd all regulators incl space.Time $vol Beacon. No overlays assumption.
lemma coastal_far : ∃ d:ℝ,∃ f:ℝ→ℂ, Continuous f ∧ ∀ t:marks (dainty Λ), d < (t:ℝ) → inner ℂ (pm s x) (Ζ t (pm s y))=f (t:ℝ) :=by
 let k:= l'.val; obtain ⟨d,v⟩:= left_fit Y H k b (axial (tent Y H) a 0 (atSouth Y H a b x).choose_spec.1); obtain ⟨e,w⟩:= right_fit Y H k b (atSouth Y H a b y).choose_spec.1
 let T₁:ℝ:= whenly da s (d+e); let Z':=fun v:ℝ=> Real.toNNReal (v-T₁); let F:=(CK k); let p: Sk k := ⟨_,v⟩; let q: Sk k:= ⟨_,w⟩; let r:= Ho k s p; let f:= Ho k s q
 refine ⟨T₁,fun t=> inner ℂ r (F.E (Z' t) f), continuous_const.inner ((F.continuousE f).comp (by unfold Z'; fun_prop)),fun t u=>?_⟩; exact stroll_identity Y H V G D a b s C j χ x y l' t p q (n:=d) (m:=e) rfl rfl u.le
include B T
local notation "Ψ" v:max=> (σ).U ((v:ℝ) • transversal a l'.val l'.property)
private lemma cruise_old (n:marks (timeMesh Λ)): Ψ (n:ℝ)=Ζ (finerNow Λ n):= (tracks_h (So) (realmReg Y H V G D a b C j χ) _ _ _ l' n)
variable (t:marks (dainty Λ))
local notation "Ep"=> whenly (dainty Λ) 0 1
lemma traceMatch : inner ℂ (pm s x) ((Ψ (t:ℝ)) ((vR Ep) (pm s y)))= inner ℂ (pm s x) (Ζ t ((vR Ep) (pm s y))) :=by
 apply coast_credit (σ) (λo b) (finerNow Λ) (fun _=> rfl) (daylight (timeMesh Λ)) l' (cruise_old Y H V G D a b C j χ B T l') (all_light ..) t (pm s x) (pm s y) Ep (when_pos da 0 1 (by decide))
 let k':= MeshClock.acts da 0 s 1; let z:=walkC Y H a b k' y; rw [show (σ).E Ep (pm s y) = pm s z from ?_]; exact coastal_far Y H V G D a b s C j χ x z l'
 rw [show Ep=whenly da s k' from (MeshClock.matchR da _ s 1 (by omega)).symm]; exact ages_pose ..
lemma coast_real : Ζ t=(σ).U ((t:ℝ) • Picket.cross a l'.val l'.property):=by
 let X:= Works Y H V G D a b Τ; let q:= (Ψ (t:ℝ)); let f:=(travelingAll Y H V G D a b C j χ B T).E Ep; let ht: DenseRange f:= (travelingAll Y H V G D a b C j χ B T).whole Ep
 have hp:(Ζ t).comp f= q.comp f:=by
    apply badges_ext Y H V G D a b 0 Τ; intro i v y; apply ext_inner_left ℂ; intro z; let b₀:= f (pm i y)
    apply closure_minimal (t:={z:X|inner ℂ z (Ζ t b₀)=inner ℂ z (q b₀)}) ?_ (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) (badges_roll Y H V G D a b i Τ z)
    rintro z h; obtain ⟨u,h⟩:= Set.mem_iUnion.mp h; obtain ⟨x,rfl⟩:=h; let v:=show i≤ u+i by omega
    change inner ℂ _ (Ζ t (f (pm i y)))= inner ℂ _ (q (f (pm i y))); rw [badges_join Y H V G D a b Τ v]; exact (traceMatch Y H V G D a b (u+i) C j χ B T x (hP v y) l' t).symm -- badges_join first rewrites lhs (badge u+i x)? if i different.
 exact DFunLike.coe_injective (ht.equalizer (Ζ t).continuous q.continuous (congrArg DFunLike.coe hp))
lemma superCaptions : Captions (So) (λo b) (σ) (LinearIsometryEquiv.refl ℂ (Works Y H V G D a b Τ).space):= ⟨fun _ _=>rfl,fun i t x=> DFunLike.congr_fun (coast_real Y H V G D a b C j χ B T i t) x⟩

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.superCaptions
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.coastal_far
