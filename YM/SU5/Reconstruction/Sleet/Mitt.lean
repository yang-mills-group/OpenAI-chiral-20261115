import YM.SU5.Reconstruction.Sleet.Yak
/-! # Charge of the Sail cost for the whole selected representation. Only using selected measurements in criterion. Isolate this estimate from other costs. -/
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
variable {x:Sky (tent Y H)}(p_h:x∈ Domain Y H G true (flank j 0))
local notation "kp" j:max e:max => physicalKet Y H V G j (C j) (wk j) e
local notation "p'" b:max p:max=> (U₀ j).track.crew ⟨b,p⟩

noncomputable def inspect (j b:Axis)(x:Sky (tent Y H))(u: marks (timeMesh Λ)) (s t:Shard (marks (timeMesh Λ))) : Sky (tent Y H) := ridgeLine Y H j b ((θ j) x) x (u+s.val+t.val) (s.val-t.val)
noncomputable def arcing (j b:Axis)(x:Sky (tent Y H))(u:Gt)(v t: Shard Gt) := whiff Y H V G C a χ (inspect Y H j b x u v t)
include p
include V
lemma separation_price {r:ℝ} (p1:0≤r)(e:x∈ Domain Y H G true (flank j r))(u:Gt)(v t:Shard Gt)(q:0≤(u:ℝ)) :
    let V':=u+v.val+t.val
    let y:= move (tent Y H) (terrainK j b V' (v.val-t.val)) x
    let A:= lowland j (-r)
    let B:= flank j (r+(V':ℝ))
    (flipMark j (tent Y H) x ∈ Domain Y H G true A ∧ y ∈ Domain Y H G true B) ∧ Disjoint A B ∧ (∀ a'∈A,∀ b'∈B,(V':ℝ) ≤ b' j-a' j) ∧ 0<(V':ℝ) ∧ inspect Y H j b x u v t ∈ Domain Y H G true (A∪B) := by
 intro V' y A B
 have hy:0 < (V':ℝ):=by unfold V'; rw [AddSubgroup.coe_add,AddSubgroup.coe_add]; exact (add_pos (add_pos_of_nonneg_of_pos q (thermal_pos v)) (thermal_pos t))
 have hx:= frontLow Y H G j r e
 have ht: y∈ Ds B:= by refine heightening Y H V G j e _ (fun a h=>?_); rw [terrain_time p]; gcongr; exact h
 have p(x:RSpace)(q:RSpace)(g:x∈A)(h:q∈B): (V':ℝ) ≤ q j-x j:= by
    have hz:x j ≤ -r:=g; have hr:r+(V':ℝ)≤ q j:=h; linarith
 have hd: Disjoint A B:= Set.disjoint_left.mpr fun z u v=> by linarith [p z z u v]
 exact ⟨⟨hx,ht⟩, hd,fun x hx y hy => p x y hx hy,hy,domain_mult Y H G hx ht hd⟩ -- indent
include p_h in
lemma clue {v s:Gt}(e:0≤ (v:ℝ)): whiff Y H V G C a χ (ridgeLine Y H j b (flipMark j (tent Y H) x) x v s)= radiation (A₀ j) (p' b p) (kp j ⟨x,p_h⟩) v s:=by
 let h:= domain_loose Y H G _ p_h
 let t: (θ j) ((θ j) x)∈D (N j):=by rw [mirror_twice]; exact h
 have hv:= measure_dials Y H V G C a χ j t h p v s e; rw [show (⟨(θ j) ((θ j) x),t⟩ : D (N j))=⟨x,h⟩ from Subtype.ext (mirror_twice ..)] at hv; exact hv -- tune let def shadow
include p_h
lemma available_wings: ∃ B C':ℝ,Blizzard (ride Y H V G.history G.clipped j false (C j) (wk j)) ((mainsea Y H V G.history G.clipped j false (C j) (wk j)).track.crew ⟨b,p⟩) (physicalKet Y H V G j (C j) (wk j) ⟨x,p_h⟩) B C' := by
 let t:=domain_loose Y H G _ p_h
 obtain ⟨B,C',e,h⟩:= wing_hatch Y H V G C a χ j b p ⟨(show flipMark j (tent Y H) x∈D (L j) from by simpa only [neg_zero] using frontLow Y H G j 0 t),t⟩
 refine ⟨B,C',⟨fun s pR=>?_,e⟩⟩; obtain ⟨F,h,v,t'⟩:= h s pR; exact ⟨F,h,v,fun u b'=> (t' u b').trans (clue Y H V G C a χ j b p p_h pR)⟩

-- Per chosen mark `x`. No cost uniform in all such x.
def Desired (x:Sky (tent Y H)): Prop:=∃ u: marks (timeMesh Λ),∃ B:ℝ,0≤ (u:ℝ)∧ ∀ s, Voucher thermal (fun t=>arcing Y H V G C a χ j b x u t s) B
variable (e:Desired Y H V G C a χ j b x)
include p_h p e
lemma shapes_missing:∃ (u:Gt)(B:ℝ),0≤(u:ℝ) ∧ Reflex (A₀ j) (p' b p) (kp j ⟨x,p_h⟩) u B:= by
 obtain ⟨u,B,q,H'⟩:=e; refine ⟨u,B,q,fun s=>Voucher.rename thermal B ?_ (H' s)⟩ -- tune
 funext t; refine clue Y H V G C a χ j b p p_h ?_; change 0≤(↑(u+t.val+s.val):ℝ); rw [AddSubgroup.coe_add,AddSubgroup.coe_add]; exact add_nonneg (add_nonneg q (thermal_pos t).le) (thermal_pos s).le
lemma fleeting : physicalKet Y H V G j (C j) (wk j) ⟨x,p_h⟩ ∈ ((U₀ j).track.crew (show Trans j from ⟨b,p⟩)).lives (J₀ j):= by
 obtain ⟨u,C',r,q⟩:= shapes_missing Y H V G C a χ j b p p_h e
 exact Reflex.lit (daylight (timeMesh Λ)) (A₀ j) (p' b p) (follows_road Y H V G.history G.clipped j false (C j) (wk j) ⟨b,p⟩) _ q
lemma reclaim (v:C₀ j=⊤)(s:Gt)(H':0<(s:ℝ)): let t:= (face (Picket.byStamp j b s) j).toNNReal; let y:= physicalKet Y H V G j (C j) (wk j) ⟨x,p_h⟩; ‖(A₀ j).E t (transverse_play (U₀ j) (Picket.byStamp j b s) y) - (A₀ j).E t y‖≤‖y-(A₀ j).E t y‖:= by
 obtain ⟨u,C',r,q⟩:= shapes_missing Y H V G C a χ j b p p_h e; obtain ⟨B,D',g⟩:= available_wings Y H V G C a χ j b p p_h
 intro t y'; let Y₁:C₀ j:=⟨y',v.symm ▸ (show y'∈ (⊤:Submodule ℂ (J₀ j)) from Submodule.mem_top)⟩
 exact drops (A₀ j) (daylight (timeMesh Λ)) (U₀ j) (follows_road Y H V G.history G.clipped j false (C j) (wk j)) ⟨b,p⟩ Y₁ r q g s H'

omit p_h p e
/-- the Stamp compatibility condition. Sufficient without any further spectral, locality or angle assumptions for CP5 Boost reconstruction. -/
def Consult (r:ℝ):Prop:=∀ j b:Axis, b≠j→ ∀ x:Sky (tent Y H), x∈ Domain Y H G true (flank j r) → Desired Y H V G C a χ j b x
variable {r:ℝ}(pr:0≤r)(hp: Consult Y H V G C a χ r)
include pr hp
lemma fulfil_seats : saunters Y H V G.history G.clipped j false (C j) (wk j) =⊤:= by
 apply eq_top_iff.mpr; intro x _
 apply ((U₀ j).track.assembled (U₀ j).list x).2; intro i v
 let F':= ((U₀ j).track.crew i); refine closure_minimal ?_ F'.lives_closed (TimeMesh.dense_flanks Y H V G j (C j) (wk j) r x)
 rintro _ ⟨y,u,t,rfl⟩; exact fleeting Y H V G C a χ j i.val i.property t (hp j i.val i.property _ u)
lemma realDemand (ε:ℝ)(v:0<ε): StageT Y H V G C a χ ε r:= by
 refine ⟨fun j=>?_⟩
 intro b p z h t z₀ f c s p_h; have ht: face z₀ ∈ CostDomain j ε:= Picket.starch (U₀ j) ⟨b,p⟩ z h t; let u:= domain_mono Y H G (TimeMesh.flank_mono j pr) c
 exact (pressure_test Y H V G j (C j) (wk j) f z₀ (show 0≤ (z₀ j).val from ht.1.le) u s p_h).mpr (reclaim Y H V G C a χ j b p u (hp j b p _ c) (fulfil_seats Y H V G C a χ j pr hp) z h)
theorem Consult.funded: BoostBacking Y H V G C a χ := (real_boost_purchase Y H V G C a χ pr (by norm_num:0<(1:ℝ))).1 (realDemand Y H V G C a χ pr hp _ zero_lt_one)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
