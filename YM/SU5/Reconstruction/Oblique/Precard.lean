import YM.SU5.Reconstruction.Oblique.PierTerms
/-! # The tilted Kernel on Mark funding. Hermitian and freeing. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
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
local notation "D" => Domain Y H G
variable (P:Ramp) {J: Calibration}
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "Π" => Domain Y H G false (northD P)
local notation "S" => Domain Y H G false (southD P)
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open _root_.YM.Kernel
variable {f y: Sky (tent Y H)}
local notation "📥" => gust P K
lemma funds_stamp (u:f∈µ): whiff Y H V G C a χ f=osValue Y H V G a (C a) χ ⟨f,u⟩:= by rw [whiff,dif_pos u]
lemma funds_add(u:f∈ µ)(v:y∈µ): Ω (f+y)= Ω f+ Ω y:=by rw [funds_stamp Y H V G C a χ u, funds_stamp Y H V G C a χ v,funds_stamp Y H V G C a χ ((µ).add_mem u v)]; exact map_add (osValue Y H V G a (C a) χ) ⟨f,u⟩ ⟨y,v⟩
lemma funds_scale(u:f∈ µ)(z:ℂ): Ω (z • f)= z*Ω f:=by rw [funds_stamp Y H V G C a χ ((µ).smul_mem z u),funds_stamp Y H V G C a χ u]; exact map_smul (osValue Y H V G a (C a) χ) z ⟨f,u⟩

noncomputable def fanoForm : Π →ₗ⋆[ℂ] Π →ₗ[ℂ] ℂ where
 toFun f:= {
    toFun:= fun g=> Ω ((📥 f.val)*g.val)
    map_add' :=fun x y=>by rw [Submodule.coe_add,mul_add]; exact funds_add Y H V G C a χ (on_Cover Y H V G P f.property x.property) (on_Cover Y H V G P f.property y.property)
    map_smul':=fun z x=>by change Ω ((📥 f.val)* (z • x.val)) = z*_; rw [mul_comm _ (z • _), sky_smul_mul, mul_comm x.val]; exact funds_scale Y H V G C a χ (on_Cover Y H V G P f.property x.property) z } -- needs sky_smul_mul Y H args
 map_add' f g:= LinearMap.ext fun x=>by change Ω _= Ω _+ Ω _; rw [Submodule.coe_add, map_add, add_mul]; exact funds_add Y H V G C a χ (on_Cover Y H V G P f.property x.property) (on_Cover Y H V G P g.property x.property)
 map_smul' z f:= LinearMap.ext fun x=>by change Ω _= star z*Ω _; rw [Submodule.coe_smul,gust_z,sky_smul_mul]; exact funds_scale Y H V G C a χ (on_Cover Y H V G P f.property x.property) _

local notation "K₀"=>fanoForm Y H V G P C a χ
/-- estimate on only angular positive-half.Mark with strict support already. -/
noncomputable def RPos: Prop:= ∀f:Sky (tent Y H), f∈Π → 0≤ whiff Y H V G C a χ (gust P (tent Y H) f*f)
variable (e:RPos Y H V G P C a χ)
include e in
lemma frees (p:f∈ Domain Y H G false Set.univ): Ω (gust P K f) = star (Ω f):= by
 obtain ⟨M,g⟩:= pump_x Y H V G P p; obtain ⟨v,u⟩:= anywhere Λ M; let Z:= stretchD P v 0; have h: move K Z f∈ Π:= g Z (by unfold Z; rw [hourMark,add_zero]; exact u)
 let F:Π:= ⟨move K Z f,h⟩; let B:Π:= ⟨1,domain_one ..⟩; have hf:= halfSpaceSymm (K₀) (fun (f:Π)=> e f.val f.property) F B -- unresolved
 change star (Ω (gust P K 1* _)) = Ω (gust P K (move K Z f)*1) at hf; rw [gust_unit,one_mul,mul_one,zone_gust Y H P] at hf;
 have hx: gust P K f∈ µ:=domain_mono Y H G (subset_univ _) (shelters Y H V G P p); exact ((whiff_move Y H V G C a χ hx _).symm.trans hf.symm).trans (congrArg star (whiff_move Y H V G C a χ p _))

abbrev Chat : Type 1 := _root_.YM.Kernel.Gram fun x y=> fanoForm Y H V G P C a χ x y
include e
lemma available_phase_Kermit: Nonempty (Chat Y H V G P C a χ):= _root_.YM.Kernel.host fun _ _=> halfSpaceKernel (K₀) (fun (f:Π)=> e f.val f.property) _
omit e
section
variable (W: Chat Y H V G P C a χ)
lemma guide (x y:Π): inner ℂ (W.plant x) (W.plant y) = whiff Y H V G C a χ (gust P K x.val*y.val):= W.measure x y -- tune macro
end
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
