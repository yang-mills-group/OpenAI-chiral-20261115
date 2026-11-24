import YM.SU5.Reconstruction.AllGrades.EvenInspect
import YM.SU5.Reconstruction.UVPrice.Void
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
local notation "SV"=> peninsula Y H V G.history G.clipped a false (C a) SJ
local notation "F"=> fort Y H V G.history G.clipped a false (C a) SJ
local notation "Fc"=> saunters Y H V G.history G.clipped a false (C a) SJ
local notation "Mu"=> voter_credit Y H V G D a false C j χ
local notation "R"=> wheelTimes Y H V G D a false Τ Mu
local notation "cr"=> regime Y H V G D a false Τ
local notation "λy"=> spokesman Y H V G D a C j χ
local notation "u₀"=> echoV Y H V G D a C j χ
local notation "kR"=> ride Y H V G.history G.clipped a false (C a) SJ
local notation "da"=> dainty Λ
local notation "Qt0" s:max=> ticket Y H G s
variable {S Z:Finset Cover}{x y:Family (tent Y H)}
local notation "Γ"=> FA
local notation "μ" t:max=> badge Y H V G D a false t Τ
local notation "ζ"=> (worthy Y H V G D a C j χ B)
local notation "Yr" t:max f:max=> badge Y H V G D a b t P f
-- positive pose alignment from arbitrary calibration Epoch.T
local notation "Cc"=> chime (tent Y H)
lemma right_fit(p:InTest K true S b x):∃ i:ℕ,(Cc a (2*i) x)∈ studio (tent Y H) a 0 b:=by
    obtain ⟨m,q⟩:= Tower.sizes S; obtain ⟨z,h⟩:= q a; let i:= z.natAbs+(tent Y H).ℓ; refine ⟨i,address a (2*(i:ℤ)) S,flow_port (tent Y H) a (2*i:ℤ) p,?_⟩
    intro k v; obtain ⟨i',r,t⟩:= Finset.mem_image.mp v; rw [←t,SlabMark.moves,if_pos rfl]; specialize h i' r; unfold i; omega
lemma left_fit(p:InTest K true S b x):∃ i:ℕ,Θ a 0 (Cc a (2* (-(i:ℤ))) x)∈ studio K a 0 b:=by
 obtain ⟨i,v⟩:= right_fit Y H a b (axial K a 0 p)
 rw [← show Θ a 0 (Cc a (2*(-(i:ℤ))) x)= Cc a (2*(i:ℤ)) (Θ a 0 x) from by rw [march_flip a b p,mul_neg,neg_neg]] at v
 exact ⟨_,v⟩
private lemma product_budget {a₁ a₂:Finset Cover}(v:InTest K true a₁ b x)(q:InTest K true a₂ b y) : TestFamily K true (x*y):=by
 have h:= InTest.mul (v.mono (Finset.subset_union_left (s₂:=a₂))) (q.mono Finset.subset_union_right); rw [Bool.xor_self] at h; exact aux_test h
lemma reach_eq(p:InTest K true S b x)(q:InTest K true Z b y) {i₁ i₂:ℕ}(u:Θ a 0 (Cc a (2* (-(i₁:ℤ))) x)∈ studio (tent Y H) a 0 b)(v:Cc a (2*(i₂:ℤ)) y ∈ studio (tent Y H) a 0 b)(n:ℕ)(h:i₁+i₂≤ n):
    let f: studio (tent Y H) a 0 b:=⟨_,u⟩; let f':studio (tent Y H) a 0 b:=⟨_,v⟩; let e:ℕ:= n-(i₁+i₂);
    inner ℂ (Yr s f) (Yr s ((Wq e) f'))= Reflect.chord b • (P.pulse s (x* (Cc a (2*n) y))) :=by
 intro f f' e; rw [measures_here]; let Y':= Cc a (2*(-(i₁:ℤ))) x; let W':=(Wq e) f'; have hY:Θ a 0 f.val=Y':= reversal _ a 0 (flow_port _ a (2*(-(i₁:ℤ))) p)
 unfold poleForm; rw [hY, (P.scale s (product_budget Y H b (flow_port K a (2*(-(i₁:ℤ))) p) (atSouth Y H a b W').choose_spec.1))]
 have ht: (Cc a (2*(-(i₁:ℤ))) (Cc a (2*n) y))=( (walkC Y H a b e) f').val:=by
    change _ = Cc a (2*e) (Cc a (2*i₂) y); rw [march_sums a b q,march_sums a b q]; unfold e; rw [Nat.cast_sub h]; congr 1; omega
 change _ • P.pulse s (Cc a (2*(-(i₁:ℤ))) x * W'.val) = _
 rw [show W'.val=(Cc a (2*(-(i₁:ℤ))) (Cc a (2*n) y)) from ht.symm, ← chime_product, P.parity s a _ (product_budget Y H b p (flow_port _ a _ q))]
local notation "Ω₁"=> (Τ).pulse
noncomputable def homeF : Works Y H V G D a false Τ:= (Q s) (evenVac Y H a) -- notation Q need parentheses!
include B
include D
lemma planar_cluster (T:Frostland Y H V G C j χ)(p:InTest K true S false x)(q:InTest K true Z false y) : Tendsto (fun n:ℕ=> Ω₁ s (x* (C₀ a (2*n) y))) atTop (𝓝 (Ω₁ s x*Ω₁ s y)):= by
 obtain ⟨i,h₁⟩:=left_fit Y H a false p; obtain ⟨i₂,h₂⟩:=right_fit Y H a false q
 let e(n:ℕ):= n-(i+i₂); let f:Γ:= ⟨_,h₁⟩; let g:Γ:=⟨_,h₂⟩; let F':= (Q s) (evenVac Y H a); let X:= (μ s) f; let Z₁:= (μ s) g
 have p₀(n)(p':i+i₂ ≤ n): Ω₁ s (x* (C₀ a (2*n) y))=inner ℂ X ((R).E (whenly (dainty Λ) s (e n)) Z₁):=by
    have ht:= reach_eq Y H V G D a false s Τ p q h₁ h₂ n p'; unfold Z₁ X; rw [ages_pose]; exact (show inner ℂ ((μ s) f) ((μ s) (walkC Y H a false (e n) g)) = Ω₁ s _ from ((show _ = Reflect.chord false • _ from ht).trans (one_smul _ _))).symm -- inspector params order tune
 have hX:Ω₁ s x= inner ℂ X F':=by nth_rw 1 [← (Τ).parity s a (-(i:ℤ)) (aux_test p)]; unfold X F'; rw [measures_here]; change _= (Τ).pulse s ((1:ℂ) • (mirror (tent Y H) a 0 (mirror (tent Y H) a 0 (Cc a _ x))*1)); rw [one_smul,mul_one,reversal K a _ (flow_port (tent Y H) a _ p)]
 have hZ:Ω₁ s y= inner ℂ F' Z₁:=by nth_rw 1 [← (Τ).parity s a (i₂:ℤ) (aux_test q)]; unfold F' Z₁; rw [measures_here]; change _= (Τ).pulse s ((1:ℂ) • (mirror K a 0 1* Cc a _ y)); rw [mirror_unit,one_smul,one_mul]
 let z:= vocation Y H V G.history G.clipped a false (C a) SJ
 have Ht:ζ F'=z:= worth_this ..
 have hv:= time_event Y H V G C j χ a B.present (T.unique_normal a) (ζ X) (ζ Z₁); change Tendsto _ _ (𝓝 (inner ℂ (ζ X) z*inner ℂ z (ζ Z₁))) at hv; rw [←Ht,(ζ).inner_map_map,(ζ).inner_map_map,←hX,←hZ] at hv
 let u(n:ℕ):= whenly (dainty Λ) s (e n)
 have du: Tendsto u atTop atTop:=by
    have hi:Tendsto e atTop atTop:= tendsto_atTop_atTop.mpr fun b=> ⟨b+(i+i₂), fun r x=>by unfold e; omega⟩
    unfold u whenly
    apply (tendsto_natCast_atTop_atTop.comp hi).atTop_mul_const (mill_pos (dainty Λ) s)
 apply (hv.comp du).congr'; filter_upwards [eventually_ge_atTop (i+i₂)] with n H'; change inner ℂ (ζ X) ((SV).E _ (ζ Z₁))= _; rw [p₀ n H', ← (caption_even Y H V G D a C j χ B).time]; exact (ζ).inner_map_map ..

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.planar_cluster
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.reach_eq
