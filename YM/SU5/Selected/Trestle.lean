import YM.SU5.Selected.Landing
/-! # CP5. Exact further tight left margin available for every Porch, after refining.
 Used for open chart equality on ALL weak-separation configurations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "S"=> turnstile Y H V Q Qt j strict C f
local notation "R" => ride Y H V Q Qt j strict C f
local notation "P" k:max => (S).crew k
local notation "T" => look j
open Germ SelectionAnalysis Sunbelt
local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
abbrev windhund (Λ : Preparation):ℕ:= 16*Λ.block.val
noncomputable def risingGrade (Λ:Preparation)(s:ℕ):= s+windhund Λ
local notation "V₀"=> risingGrade Λ s
lemma rising_le (Λ:Preparation)(s:ℕ): s ≤ risingGrade Λ s:= by unfold risingGrade; omega
local notation "v₀"=> rising_le Λ s
local notation "E'" F:max => upGrade Y H s Q strict F V₀
local notation "A'" p:max => addLevel Y H V s Q j strict p V₀ v₀

variable {F : Marks (tent Y H) strict} (P' : Veranda Y H s j strict F)
-- can make ANY porch with a larger budget high into a strictly interior one on left
lemma glissade : ∃ P₀ : Veranda Y H (risingGrade Λ s) j strict (upGrade Y H s Q strict F (risingGrade Λ s)), P₀.rise + 1=(A' P').rise ∧ P₀.span+1=(A' P').span:=by
 let p:=windhund Λ; let V':= A' P'; have hp: (p:ℤ)=ruler (K).B:=by unfold p windhund; unfold ruler; push_cast; rfl
 have h : V'.span= L₀^p * P'.span:= by change L₀^(s+p-s)*_=_; rw [Nat.add_sub_cancel_left]
 have hv : 1< V'.span:= by
    rw [h]; apply lt_of_lt_of_le (b:=L₀) (show 1<L₀ from lt_of_lt_of_le (by decide) (Μ).Llarge)
    apply le_trans _ (Nat.le_mul_of_pos_right _ P'.pos); have he:0<p:=by have h11:=ruler_gene (K).B; omega
    calc
      _ = L₀^1:=by simp
      _ ≤ L₀^p:=pow_le_pow_right₀ Λ.R.L.property he
 let C' := V'.fwd.val; obtain ⟨r,i,t⟩:=P'.fwd.property
 let B:=volumeAround Λ l p r
 have hc:InTest K true B false C'.val:= by
    change InTest K true B false (stream Y H D s (s+p-s) _); rw [Nat.add_sub_cancel_left]; exact (proceeds Y H Q.circuit _ _ i).1
 have he:Tower.region j 0 ((K).ℓ+p) B:= by
    have he:= increase Y H s Q.circuit j 0 r (by rw [area0]; exact fun i m=> (t i m).1) p; rwa [area0] at he
 let a:= V'.span-1; let Z:=ruler (K).B
 let V1:=plow K j (-1) B; let W:= (moveMark Y H j strict (-1)) ((M₁ V₀) C'); have hw: InTest K true V1 false W.val:=flow_port K j _ hc
 have hy:Between K j 0 (ruler Λ.block*a) V1:=by
    intro i w; obtain ⟨k,m,rfl⟩:=plow_stays K j _ B w; rw [moves,if_pos rfl,mul_neg,mul_one]; have h₀:=he k m; have h₁:Between K j 0 (Z*V'.span) B:= by -- may rewrite t h rising block
       rw [h,Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact expands_shape Y H t p -- `t` at K
    specialize h₁ k m; change 0 + _ ≤ k j + -Z ∧ k j + -Z + _ ≤ Z * (a:ℤ); have h2 : (a:ℤ)=(V'.span:ℤ)-1:=by unfold a; omega
    rw [h2,mul_sub,mul_one]; change (p:ℤ)=Z at hp; omega
 let x':Tower.Field Y H V₀ j 0 strict:= ⟨W.val,(purpose_ok ..).mpr ⟨(show _ from ⟨_,hw,by rw [area0]; exact fun i k=> (hy i k).1⟩), (marksSpec strict W).2⟩⟩; let y : Entry Y H V₀ j strict a:= ⟨x',V1,hw,hy⟩
 have hh : x'.val= relocate K j (V'.rise-1) (upGrade Y H s Q strict F V₀).val:=by
    change relocate K j (-1) V'.fwd.val.val=_; rw [V'.yes]; -- need exact cast
    change relocate K j (-1) (relocate K j _ (E' F).val)= _
    rw [relocate_sums K j _ _ (marksSpec strict (E' F)).1, show -1+V'.rise=V'.rise-1 by omega]
 refine ⟨⟨V'.rise-1,a,by unfold a; omega,y,hh⟩, by change V'.rise-1+1=V'.rise; omega,by change V'.span-1+1=V'.span; omega⟩
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.glissade
