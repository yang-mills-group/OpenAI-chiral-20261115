import YM.SU5.Reconstruction.Moat.Pulse
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
namespace Reflector
variable (j:Axis)
local notation "Π₁"=> opCarries Y H V G j (C j) (w j)
variable (Fc: saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
include V G Fc
local notation "Ω" i:max=>doorstep Y H V G.history G.clipped i false (C i) (w i)
lemma buoy (t: marks (timeMesh Λ))(h:0≤(t:ℝ))(x:D' j) : ∃ y:D' j, y.val=m₁ (eject j t) x.val ∧ (Vo j) y=(S₀ j).E (Real.toNNReal (t:ℝ)) ((Vo j) x):= by
 have hx:= later_frame Y H V G j x.val (eject j t) x.property (by rw [eject_at]; exact h); refine ⟨⟨_,hx⟩,rfl,?_⟩; rw [voice_move Y H V G j _ _ Fc _ x (by rw [coordinates_eject,eject_at]; exact h), bridge_time]
lemma down (t:marks (timeMesh Λ))(v:0≤(t:ℝ))(x:D' j)(g:x.val∈Domain Y H G false (flank j (t:ℝ))): ∃ y:D' j, m₁ (eject j t) y.val=x.val ∧ (S₀ j).E (Real.toNNReal (t:ℝ)) ((Vo j) y)=(Vo j) x:=by
 let d:=m₁ (eject j (-t)) x.val; let h: d∈ Domain Y H G false (flank j 0):= domain_mono Y H G (even_flank j _ (by simp)) (FirstWindows.moving Y H V G _ _ g)
 obtain ⟨y,p,e⟩:=buoy Y H V G C a χ j Fc t v ⟨_,h⟩; have ht:x.val=y.val:= p.symm ▸ (by change _= m₁ (eject j t) d; unfold d; rw [move_sum,selectRay,add_neg_cancel,eject_zero,move_by_zero]) -- cast direction
 exact ⟨⟨_,h⟩,p.symm.trans ht.symm,e.symm.trans (congrArg _ (Subtype.ext ht.symm))⟩
-- uniform
variable (X' : ℕ → (indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  {B:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
  (q:ℕ→marks (timeMesh Λ)) (S':Tendsto (fun i=>(q i:ℝ)) atTop (𝓝 0))
  (w0: ℕ→Sky (tent Y H))(h₀:∀ i,Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) (w0 i) (q i) (X' i))
  (p:Limited atTop X' B)
include S' h₀ p
local notation "€"=>Fund Y H V G C a χ
lemma surroundings (x y:D' j)(t:marks (timeMesh Λ))(s:0<(t:ℝ))(g:y.val∈ Domain Y H G false (flank j (t:ℝ))): ∃ F:ℕ→ℂ,(∀ᶠ i in atTop, Fund Y H V G C a χ ((θ j) x.val * w0 i * y.val) (F i)) ∧ Tendsto F atTop (𝓝 (inner ℂ ((X j) x) (B ((X j) y)))):= by
 obtain ⟨d,v,t'⟩:= down Y H V G C a χ j Fc t s.le y g
 let ℓ (i:ℕ): ℝ≥0:= Real.toNNReal (t-(q i):ℝ); let r:= (t:ℝ).toNNReal; let A(i):= (S₀ j).E (ℓ i)
 have ht:Tendsto ℓ atTop (𝓝 r):= (continuous_real_toNNReal.tendsto _).comp (by simpa only [sub_zero] using (tendsto_const_nhds (x:=(t:ℝ))).sub S')
 have hb (x:G₀ j): Tendsto (fun i=> A i x) atTop (𝓝 ((S₀ j).E r x)):= ((S₀ j).continuousE x |>.tendsto r).comp ht
 have vA: Pearl atTop A ((S₀ j).E r):= ⟨⟨1,zero_le_one,Eventually.of_forall fun i=> (S₀ j).shrinks _⟩,hb,fun x=>?_⟩
 swap; · unfold A; simp_rw [(S₀ j).sym]; exact hb x
 let V₁(i):=Π₁ (X' i)* A i; let F(i):=inner ℂ ((Vo j) x) (V₁ i ((Vo j) d)) -- Lean shadow name V replacement in Vo!! fix
 refine ⟨F,?_,?_⟩
 · filter_upwards [S'.eventually (ge_mem_nhds s)] with i hx
   change (q i:ℝ) ≤ t at hx; let I':= t-q i; obtain ⟨y',e,h⟩:= buoy Y H V G C a χ j Fc I' (sub_nonneg.mpr hx) d
   obtain ⟨j',f,g⟩:=voice_follows Y H V G j (C j) (w j) Fc (h₀ i) y'
   have p': (θ j) x.val * w0 i*y.val=(θ j) x.val*j'.val:= by
      rw [f,e,move_sum,selectRay, show q i + I'=t from by unfold I'; abel,v,mul_assoc]; -- reorder
   rw [p']; let he:= pairedFund Y H V G C a χ j Fc x j'
   rw [g,h] at he; exact he
 have he : inner ℂ ((X j) x) (B ((X j) y)) = inner ℂ ((Vo j) x) (((Π₁ B) * (S₀ j).E r) ((Vo j) d)):=by
     rw [mul_apply_eq_comp,t']; rw [Hearthbank.uplink,voice_full Y H V G j _ _ Fc,voice_full Y H V G j _ _ Fc]
 rw [he]; exact ((Hearthbank.projected Y H V G j (C j) (w j) p).toRight vA).confirms _ _
end Reflector
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
