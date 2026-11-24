import YM.SU5.Reconstruction.PolarArchives.Morning
/- Amplify the CP18 kernel proofs (adapt our Dr. ..) from just the fixed-FAR SINGLET stencils. Economical area. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open PolarArchives
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
variable (gap:ℝ≥0)
local notation "Π" => Domain Y H G true (PolarArchives.Acres P gap)
local notation "S" => Domain Y H G true (PolarArchives.SkyAcres P gap)
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
variable {f:Sky (tent Y H)}
open _root_.YM.Kernel
include V
lemma glides_S_remote (v:f∈ S): gust P K f∈ Π := domain_mono Y H G (acre_S_N P gap) (shelters Y H V G P v)
lemma glides_N_remote (v:f∈ Π): gust P K f∈ S:= domain_mono Y H G (acre_N_S P gap) (shelters Y H V G P v)
lemma on_Cover_remote {f g:Sky (tent Y H)}(p:f∈ Π)(v:g∈ Π): gust P K f * g∈ µ:= domain_loose Y H G univ (pay_your Y H V G P gap p v)
omit V
include V
lemma advanceN_remote(p:placement Λ)(v:0≤ (hoursN P p).val) (u:f∈Π): move K p f∈ Π:=by
 apply domain_mono Y H G ?_ (moving Y H V G p f u)
 rintro _ ⟨y,z,rfl⟩; show (gap:ℝ) < landN P _ ; rw [map_add,hour_age]; exact lt_of_lt_of_le z (le_add_of_nonneg_right v)
noncomputable def sails_remote (p:placement Λ)(h:0≤ (hoursN P p).val) : (Π)→ₗ[ℂ] (Π) := ((move K p).comp (Π).subtype).codRestrict Π (fun x=>advanceN_remote Y H V G P gap p h x.property)
lemma issue_add_remote (v t:placement Λ) (x y s)(f:Π) : sails_remote Y H V G P gap v x (sails_remote Y H V G P gap t y f)=sails_remote Y H V G P gap (v+t) s f:=Subtype.ext (move_sum ..)
lemma pump_x_remote(p:f∈ Domain Y H G true Set.univ): ∃ M:ℝ, ∀ t:placement Λ,M<(hoursN P t).val→ move K t f∈ Domain Y H G true (Acres P gap):=by
 obtain ⟨A,B,C,d⟩:=(compact_domain Y H G).1 p
 obtain ⟨c,e⟩:= (B.image (landNp P)).bddBelow; refine ⟨(gap:ℝ)-c,fun t h=> domain_mono Y H G ?_ (moving Y H V G t f d)⟩
 rintro _ ⟨x,y,rfl⟩; show (gap:ℝ)<landN P (x+coordinates Λ t); rw [map_add,hour_age]; linarith [show c≤landN P x from e (Set.mem_image_of_mem _ y)]
lemma dump_x_remote(p:f∈Domain Y H G true Set.univ): ∃ M:ℝ,∀ t:placement Λ,(hoursN P t).val< -M → move K t f ∈ Domain Y H G true (SkyAcres P gap):=by
 obtain ⟨A,B,C,d⟩:=(compact_domain Y H G).1 p
 obtain ⟨c,e⟩:= (B.image (landNp P)).bddAbove; refine ⟨c+(gap:ℝ),fun t h=> domain_mono Y H G ?_ (moving Y H V G t f d)⟩
 rintro _ ⟨x,y,rfl⟩; show landN P (x+coordinates Λ t)< -(gap:ℝ); rw [map_add,hour_age]; linarith [show landN P x≤ c from e (Set.mem_image_of_mem _ y)]
omit V
local notation "📥" => gust P K
include V
noncomputable def fanoForm_remote : Π →ₗ⋆[ℂ] Π →ₗ[ℂ] ℂ where
 toFun f:= {
    toFun:= fun g=> Ω ((📥 f.val)*g.val)
    map_add' :=fun x y=>by rw [Submodule.coe_add,mul_add]; exact funds_add Y H V G C a χ (on_Cover_remote Y H V G P gap f.property x.property) (on_Cover_remote Y H V G P gap f.property y.property)
    map_smul':=fun z x=>by change Ω ((📥 f.val)* (z • x.val)) = z*_; rw [mul_comm _ (z • _), sky_smul_mul, mul_comm x.val]; exact funds_scale Y H V G C a χ (on_Cover_remote Y H V G P gap f.property x.property) z } -- needs sky_smul_mul Y H args
 map_add' f g:= LinearMap.ext fun x=>by change Ω _= Ω _+ Ω _; rw [Submodule.coe_add, map_add, add_mul]; exact funds_add Y H V G C a χ (on_Cover_remote Y H V G P gap f.property x.property) (on_Cover_remote Y H V G P gap g.property x.property)
 map_smul' z f:= LinearMap.ext fun x=>by change Ω _= star z*Ω _; rw [Submodule.coe_smul,gust_z,sky_smul_mul]; exact funds_scale Y H V G C a χ (on_Cover_remote Y H V G P gap f.property x.property) _

local notation "K₀"=>fanoForm_remote Y H V G P C a χ gap
/-- estimate on only angular positive-half.Mark with strict support already. -/
noncomputable def RPos_remote: Prop:= ∀f:Sky (tent Y H), f∈Π → 0≤ whiff Y H V G C a χ (gust P (tent Y H) f*f)
variable (e:RPos_remote Y H V G P C a χ gap)
abbrev Chat_remote : Type 1 := _root_.YM.Kernel.Gram fun x y=> fanoForm_remote Y H V G P C a χ gap x y
include e
lemma available_phase_Kermit_remote: Nonempty (Chat_remote Y H V G P C a χ gap):= _root_.YM.Kernel.host fun _ _=> halfSpaceKernel (K₀) (fun (f:Π)=> e f.val f.property) _
omit e
section
variable (W: Chat_remote Y H V G P C a χ gap)
lemma guide_remote (x y:Π): inner ℂ (W.plant x) (W.plant y) = whiff Y H V G C a χ (gust P K x.val*y.val):= W.measure x y -- tune macro
end
variable (W:Chat_remote Y H V G P C a χ gap)
noncomputable def treks_remote(t:Gt)(h:0≤ (t:ℝ)): Domain Y H G true (PolarArchives.Acres P gap) →ₗ[ℂ] Domain Y H G true (PolarArchives.Acres P gap) := sails_remote Y H V G P gap (billT P t) (billT_pos P t h)
local notation "ξ" => treks_remote Y H V G P gap
local notation "Ωy"=> gust P K
local notation "Wr"=> stretchD P
lemma trek_add_remote(i j:Gt)(x y z)(f:Π): treks_remote Y H V G P gap i x (treks_remote Y H V G P gap j y f) = ξ (i+j) z f:=by apply Subtype.ext; change move K (Wr i i) (move K (Wr j j) f.val)=move K (Wr _ _) f.val; rw [move_sum,stretch_add]
lemma trek_zero_remote(f:Π): ξ (0:Gt) (by simp) f=f:=by apply Subtype.ext; change au (Wr 0 0) _=_; rw [mark_zero,move_by_zero]; rfl

lemma shifts_remote(x y:Π)(s u v p:placement Λ)(hs hu hv hp)
    (e:P.s.act u+v=P.s.act p+s):
    inner ℂ (W.plant (sails_remote Y H V G P gap u hu x)) (W.plant (sails_remote Y H V G P gap s hs y)) = inner ℂ (W.plant (sails_remote Y H V G P gap p hp x)) (W.plant (sails_remote Y H V G P gap v hv y)):= by
 let T:=sails_remote Y H V G P gap p hp x; let D':=sails_remote Y H V G P gap v hv y
 simp only [guide_remote Y H V G P C a χ gap W]
 rw [←whiff_move Y H V G C a χ (on_Cover_remote Y H V G P gap T.property D'.property) (s-v)] -- target exact match? unfolds not?
 change Ω ((Ωy (au u x.val))* (au s y.val))= Ω (au (s-v) ((Ωy (au p x.val)) *(au v y.val)))
 rw [move_prod, zone_gust Y H P, zone_gust Y H P,move_sum,move_sum,sub_add_cancel,show s-v+P.s.act p=P.s.act u by rw [eq_sub_of_add_eq e]; abel]
private lemma sailing_zero_remote(f:Π): sails_remote Y H V G P gap 0 (by rw [map_zero];exact le_rfl) f=f:=Subtype.ext (move_by_zero Λ K f.val)
lemma doubly_take_remote (x y:Π)(s u v:placement Λ)(hs hu hv) (h:u = P.s.act s+v):
    inner ℂ (W.plant (sails_remote Y H V G P gap s hs x)) (W.plant (sails_remote Y H V G P gap u hu y)) = inner ℂ (W.plant x) (W.plant (sails_remote Y H V G P gap v hv y)) := by
 nth_rw 2 [← sailing_zero_remote Y H V G P gap x]; exact shifts_remote Y H V G P C a χ gap W x y u s v 0 hu hs hv (by rw [map_zero];exact le_rfl) (by rw [Signed.act_zero,zero_add,h])
lemma sail_cost_remote (x y:Π)(s v:Gt)(p:0≤ (hoursN P (stretchD P s v)).val)(u)
    (A:Π) (q:A.val=au (Wr (s+v) (s+v)) y.val) (H':0≤((s+v:Gt):ℝ)) : inner ℂ (W.plant (sails_remote Y H V G P gap (Wr s v) p x)) (W.plant (sails_remote Y H V G P gap (Wr s v) u y))=inner ℂ (W.plant x) (W.plant A) := by
 rw [show A=ξ _ H' y from Subtype.ext q]
 refine doubly_take_remote Y H V G P C a χ gap W x y _ _ _ p u (billT_pos P _ H') ?_
 unfold billT; rw [stretch_turn,stretch_add]; congr 1 <;> abel_nf -- tune

lemma doubles_take_remote (x:Π)(v:Gt)(p:0≤(v:ℝ))(q:0≤((v+v:Gt):ℝ)): inner ℂ (W.plant (ξ v p x)) (W.plant (ξ v p x)) = inner ℂ (W.plant x) (W.plant (ξ (v+v) q x)):= sail_cost_remote Y H V G P C a χ gap W x x v v (billT_pos P v p) (billT_pos P v p) (ξ (v+v) q x) rfl q -- args tune
lemma monotone_v_remote(t:Gt)(q:0≤(t:ℝ))(x:Π): 0 ≤ inner ℂ (W.plant x) (W.plant (ξ t q x)):=by
 have hx:0≤(hoursN P (Wr t 0)).val:=by rw [hourMark,add_zero]; exact q
 rw [← sail_cost_remote Y H V G P C a χ gap W x x t 0 hx hx (ξ t q x) (by change au _ _=_; rw [add_zero]; rfl) (by rw [add_zero]; exact q)]
 rw [inner_self_eq_norm_sq_to_K]; positivity
lemma motionScore_remote (x y:Π)(t:Gt)(q:0≤ (t:ℝ)): inner ℂ (W.plant x) (W.plant (ξ t q y))= Ω (gust P K x.val * move K (Wr t t) y.val):= guide_remote Y H V G P C a χ gap W x (ξ t q y)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
