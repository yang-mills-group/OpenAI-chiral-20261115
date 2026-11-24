import YM.SU5.Reconstruction.AllGrades.Library
import YM.SU5.Reconstruction.Pitch.Coupling
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
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
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
structure Impetus : Prop where
 backed (x:Sc)(s n:ℕ): ‖(Bp s) ((Wq n) x)‖≤ ‖(Bp s) x‖
 lit (x:Sc)(s n:ℕ):0≤ inner ℂ ((Bp s) x) ((Bp s) ((Wq n) x))
local notation "VP" => voterAt Y H V G C j χ
local notation "rχ"=> displacement Y H V G.history G.clipped j false (C j) χ a (C a)
local notation "vS" t:max=> badge Y H V G D a b t VP
local notation "We" n:max=> notch (Pitch.loomD Λ) s n
variable {S:Finset Cover}{F:Family (tent Y H)}(x:studio (tent Y H) a 0 b)
lemma slides_inspector {h:InTest (tent Y H) true S false F} (z:ℤ) : price Y H V G C j χ s false (chime (tent Y H) a z F) = price Y H V G C j (Pitch.wagerUp Y H V G j C a (notch (Pitch.loomD Λ) s z) χ) s false F:=by
    let T:= We z; let t:= Pitch.wagerUp Y H V G j C a T χ; let d:Dome (tent Y H):= ⟨F,aux_test h⟩; let S':=PhaseChoice.cruise a (tent Y H) z d
    let y':=PhaseChoice.sailsTo a (tent Y H) z d; rw [price_oneAt' Y H V G C j χ s S' (show S'.val=_ from y'),price_oneAt' Y H V G C j t s d (f:=F) rfl] -- F vs d.val
    let Y':Domain Y H G false univ:= ⟨ticket Y H G s S', ticket_loose ..⟩; let d':Domain Y H G false univ:= ⟨ticket Y H G s d,ticket_loose ..⟩
    let L:= osValue Y H V G j (C j) χ
    have Ht:L Y'= osValue Y H V G j (C j) t d' :=by have ht: osValue Y H V G j (C j) t = L.comp (Pitch.plusLaw Y H G a T) := Pitch.neighbor_wager ..; rw [ht, LinearMap.comp_apply]; exact congrArg L (Subtype.ext (Pitch.trek_mark Y H G a T s z rfl d).symm)
    exact (os_ticket Y H V G j (C j) χ s S').symm.trans (Ht.trans (os_ticket Y H V G j (C j) t s d))
lemma pose_even (n:ℕ): let h:(a=a→ 0 ≤ (n:ℤ)):=(fun _=>by positivity); let f:Sc:=cart Y H a b a (n:ℤ) h x
     poleForm (tent Y H) a 0 b x.val ((walkC Y H a b n) x).val= chime (tent Y H) a n (poleForm (tent Y H) a 0 b f.val f.val):=by
 intro h f; unfold poleForm f walkC; simp_rw [chime_scale,chime_product,cart_apply]; let p:=(atSouth Y H a b x).choose_spec.1
 rw [march_flip a b p, march_sums a b (axial (tent Y H) a 0 p), add_neg_cancel, march_zero a b (axial _ a 0 p),march_sums a b p,←two_mul]

lemma voter_credit : Impetus Y H V G D a b VP:=by
    refine ⟨fun x s n=> ?_, fun x s n=>?_⟩ -- prove norm sup using walk_herm and PassOLD
    · let L33:= badge Y H V G D a b s VP; let Z(i:ℕ):=L33 ((Wq i) x); let d:= 4*Λ.block.val; have hd:0 < d:=Nat.mul_pos (by omega) Λ.block.property
      let S0:Set ℝ:= Set.range fun (i:ℕ)=> ‖Z i‖; have hs(i):‖Z i‖∈ S0:=Set.mem_range_self i
      have Ht:BddAbove S0:=by
         let B₁:Set ℝ:= (fun (i:ℕ)=> ‖Z i‖) '' Set.Iic d; obtain ⟨D₁,k⟩:= ((Set.finite_Iic d).image (fun (i:ℕ)=> ‖Z i‖)).bddAbove
         refine ⟨D₁, by rintro y ⟨w,rfl⟩; nth_rw 1 [← Nat.mod_add_div w d,add_comm]; unfold Z; dsimp only; rw [←walk_plus Y H a b]; exact (voter_passOld Y H V G D a b s C j χ (w/d) ((Wq (w%d)) x)).trans (k ⟨w%d,(Nat.mod_lt _ hd).le,rfl⟩)⟩
      let B:=sSup S0; let e(i):‖Z i‖≤B:= le_csSup Ht (hs i)
      let v':=‖L33 x‖; have hv:0≤ v':=norm_nonneg _
      have hB:0≤ B:=(norm_nonneg _).trans (e n)
      have g(i): ‖Z i‖^2≤ v'* B:=by
        have ht:‖Z i‖^2= ‖inner ℂ (Z i) (Z i)‖:=by rw [inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖Z i‖:ℝ):ℂ)‖^2; simp
        rw [ht, show inner ℂ (Z i) (Z i)=inner ℂ (L33 x) (Z (i+i)) from (walk_herm Y H V G D a b s VP x ((Wq i) x) i).trans (congrArg _ (congrArg L33 (walk_plus Y H a b x i i)))]
        exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (e _) hv)
      refine (e n).trans ?_
      have ht:B ≤ Real.sqrt (v'*B):=csSup_le ⟨_,hs n⟩ (by rintro _ ⟨i,rfl⟩; exact Real.le_sqrt_of_sq_le (g i))
      have h':= Real.sq_sqrt (mul_nonneg hv hB); change B ≤ v'; nlinarith [Real.sqrt_nonneg (v'*B)]
    let t:= show a=a→0 ≤ (n:ℤ) from (fun _=>by positivity); let f:=cart Y H a b a (n:ℤ) t x; rw [measures_here]; change 0≤ price Y H V G C j χ _ _ _
    rw [pose_even Y H a b x n, slides_inspector Y H V G a s C j χ (h:=(printedS Y H a b f f).paid.choose_spec)]
    exact (voterAt Y H V G C j _).gram_price s a b f
lemma root_credit : Impetus Y H V G D a b (atlasAt Y H V G):=by
    refine ⟨fun x s n=> root_walk_time Y H V G D a b s n x,fun x s n=> ?_⟩
    let t:= show a=a→0 ≤ (n:ℤ) from (fun _=>by positivity); let f:=cart Y H a b a (n:ℤ) t x; rw [measures_here]; change 0≤ E s _
    rw [pose_even Y H a b x n, PhaseChoice.shift_eFull Y H V a (printedS Y H a b f f)]
    exact (atlasAt Y H V G).gram_price s a b f

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.voter_credit
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.root_credit
