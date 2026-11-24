import YM.SU5.Reconstruction.Sleet.Firn
/-! # Moving the wings (no cost at center supplied). -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5200
set_option synthInstance.maxSize 33000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers LightBudget Storm
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
local notation "W" => placement Λ
local notation "L" j:max=> lowland j 0
local notation "N" j:max=> flank j 0
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
variable (j b:Axis)(p:b≠j)
variable {x y: Sky (tent Y H)}

include V
lemma lowering {q:Bool}{U:Set RSpace} (h:x∈ Domain Y H G q U)(v:placement Λ){t:ℝ}(e:∀ y∈ U,y j+(v j).val≤t): move K v x ∈ Domain Y H G q (lowland j t):= by
 apply domain_mono Y H G ?_ (moving Y H V G v x h)
 rintro _ ⟨y,z,rfl⟩; exact e y z
lemma heightening {q:Bool}{U:Set RSpace} (h:x∈ Domain Y H G q U)(v:placement Λ){t:ℝ}(e:∀ y∈ U,t≤ y j+(v j).val): move K v x ∈ Domain Y H G q (flank j t):= by
 apply domain_mono Y H G ?_ (moving Y H V G v x h)
 rintro _ ⟨y,z,rfl⟩; exact e y z
variable (h:Thermal Y H G j x y)
include p h
local notation "Pad"=>terrainK j b
local notation "X" s:max=> move (tent Y H) (terrainK j b 0 (-s:↥Gt)) x
local notation "Y₀" s:max=> move (tent Y H) (terrainK j b 0 (s:↥Gt)) y
open Metric
lemma observation: ∃ s:Shard Gt, Thermal Y H G j (move (tent Y H) (terrainK j b 0 (-s.val)) x) (move K (terrainK j b 0 s.val) y) ∧ Thermal Y H G b (X s.val) (Y₀ s.val):=by
 obtain ⟨A,Hx,i,h₀⟩:=(compact_domain Y H G).1 h.cloud; obtain ⟨B,Hy,k,h₁⟩:=(compact_domain Y H G).1 h.pupil
 have hw: Continuous fun v:RSpace=> v b:= continuous_apply b
 obtain ⟨t,u⟩:=(Hx.image hw).bddAbove; obtain ⟨r,v⟩:=(Hy.image hw).bddBelow
 obtain ⟨w,g,e⟩:=(daylight (timeMesh Λ)).exists_mem_open isOpen_Ioi (show (Ioi (max (max t 0) (-r))).Nonempty from nonempty_Ioi)
 have hp:max (max t 0) (-r)< w:= e
 let s:↥Gt:=⟨w,g⟩; change _ < (s:ℝ) at hp
 refine ⟨⟨s,lt_of_le_of_lt (le_trans (le_max_right t 0) (le_max_left ..)) hp⟩,⟨lowering Y H V G j h.cloud _ (fun v hv=> ?_), later_frame Y H V G j y _ h.pupil (by rw [terrain_time p]; exact le_refl (0:ℝ))⟩,lowering Y H V G b h₀ _ (fun v hv=>?_), heightening Y H V G b h₁ _ (fun l hl=>?_)⟩ -- structure nesting flatten
 · rw [terrain_time p]; simpa using (show v j ≤ 0 from hv) -- lowland reducible?
 · rw [terrain_space]; linarith [show v b≤t from u (mem_image_of_mem _ hv),le_max_left (max t 0) (-r),le_max_left t 0,show (-s).val = -(s:ℝ) from rfl]
 rw [terrain_space]; linarith [show r≤ l b from v (mem_image_of_mem _ hl),le_max_right (max t 0) (-r)]
lemma clip_observer(v t s:Gt)(e:0≤ v.val) : whiff Y H V G C a χ (ridgeLine Y H j b (X s) (Y₀ s) v t)=
    whiff Y H V G C a χ (ridgeLine Y H j b x y v (t+(s+s))):= by
 let q:= Pad 0 (-s); rw [← whiff_move Y H V G C a χ (Thermal.outgo Y H V G j b p h v (t+(s+s)) e) q]; unfold ridgeLine
 rw [move_prod,move_sum,move_sum]
 rw [show terrainK j b v t + terrainK j b 0 s= q + terrainK j b v (t+(s+s)) from ?_]
 unfold q; rw [terrain_sum p,terrain_sum p,zero_add,add_zero,show t+s= -s+(t+(s+s)) from by abel]

local notation "CMy" v:max s:max => whiff Y H V G C a χ (ridgeLine Y H j b x y v s)
lemma wing_hatch: ∃ (B ℐ:ℝ),0<B ∧ ∀ v:Gt,0≤(v:ℝ)→ ∃ F:ℂ→ℂ,AnalyticOnNhd ℂ F (Snowball.rightWork B) ∧ (∀ z∈ Snowball.rightWork B, ‖F z‖≤ℐ) ∧ ∀ z:Gt,B<(z:ℝ)→ F (↑(z:ℝ))=CMy v z:=by
 obtain ⟨s,e,t⟩:= observation Y H V G j b p h
 let y':= Y₀ s.val; let x':= X s.val; let B':= s.val+s.val
 let ℐ:= maxFare Y H V G C a χ b t
 refine ⟨(B':ℝ),ℐ,by unfold B';rw [AddSubgroup.coe_add]; exact add_pos (thermal_pos s) (thermal_pos s),fun v q=>?_⟩
 obtain ⟨F,k,u⟩:= Voucher.wear _ _ _ (progress_heat Y H V G C a χ b j p.symm t ℐ le_rfl v) thermal_pos
 let g(z:ℂ):= z -(B':ℝ)
 let V':= F ∘ g
 have he(z:ℂ)(v:z∈Snowball.rightWork (B':ℝ)): g z∈optimistic:=by change 0< (g z).re; unfold g; rw [Complex.sub_re,Complex.ofReal_re]; exact sub_pos.mpr v
 refine ⟨V', fun z v=> (k.1 _ (he z v)).comp (by unfold g; fun_prop), fun z v=> k.2 _ (he z v),?_⟩
 intro z Z; let w:Shard Gt:=⟨z-B',by rw [AddSubgroup.coe_sub]; exact sub_pos.mpr Z⟩
 specialize u w; unfold V' Function.comp
 rw [show g (↑(z:ℝ)) = (thermal w:ℂ) from (by unfold g thermal; change _= (↑(↑(z-B'):ℝ):ℂ); push_cast;rfl),u]
 rw [show ridgeLine Y H b j _ _ w.val v=ridgeLine Y H j b x' y' v w.val from ?_,clip_observer Y H V G C a χ j b p h v w.val s.val q] -- tune reduction
 · rw [show w.val+(s.val+s.val)=z from (by change z-B'+ B'=z; abel)]
 unfold ridgeLine; rw [terrain_reverse p.symm]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
