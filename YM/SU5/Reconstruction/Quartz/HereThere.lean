import YM.SU5.Reconstruction.Crease.Launch
import YM.SU5.Reconstruction.Quartz.Tunnel
-- # Graph recipe on this same law through any authentic Quarter
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
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
lemma crest_charge (s n:ℕ) (S:Finset Cover)(h: PhaseChoice.SupportedPhysically Λ l s S (flank j (whenly (timeMesh Λ) s n:ℝ))): Tower.region j (SlabMark.ruler Λ.block*n) (tent Y H).ℓ S:=by
 rw [supported_iff] at h; let δ:ℝ:= (reserve Λ l:ℝ)*gaugeMesh Λ s; have he:0≤δ:=by unfold δ; have k:= gaugeMesh_pos Λ s; positivity
 intro x q; let t:= gaugePosition Λ s x
 have hq:t-eject j δ∈ bufferedHull Λ l s S:=by
   refine Set.mem_iUnion₂.mpr ⟨x,q,?_⟩; rw[shield_region_exact]; intro i _; change t i-δ≤t i-eject j δ i ∧ t i-eject j δ i≤t i+δ; by_cases h:i=j <;> simp[h,he];linarith
 have hz:= h hq; change (whenly (timeMesh Λ) s n:ℝ) ≤ t j-eject j δ j at hz; unfold t δ at hz; rw[eject_at,double_clock_calibration,gaugePosition] at hz; rw[← _root_.sub_mul,mul_le_mul_iff_left₀ (gaugeMesh_pos Λ s),le_sub_iff_add_le] at hz
 change _+ (↑(reserve Λ l):ℤ) ≤ x j; exact_mod_cast hz
-- light-budget aperture touching bills over true field panels
lemma span_front {Yₗ Yr A:Set RSpace}(u:Gt)(k:0<(u:ℝ))(hl:Yₗ⊆ strip j 0 (u:ℝ))(hr:Yr⊆ flank j (u:ℝ))(h1:Yₗ ⊆ A)(h2:Yr⊆ A) (x y: Sky K) (px:x∈ Ds Yₗ) (py:y∈Ds Yr) : x*y ∈ Ds A := by
 obtain ⟨s,⟨⟨x₀,v,rfl⟩,y₀,w₀,rfl⟩,r,-,hr'⟩:= ((((domain_eventually Y H G).1 px).and ((domain_eventually Y H G).1 py)).and (notch_nat_event u k)).exists
 obtain ⟨⟨S,xv,hs⟩,-⟩:= (mem_insideAt x₀ _).1 (insideAt_mono hl v); obtain ⟨⟨T,xt,ht⟩,-⟩:= (mem_insideAt y₀ _).1 (insideAt_mono hr w₀)
 have hb: (whenly (timeMesh Λ) s r:ℝ) = (u:ℝ):= hr' ▸ (natural_time ..).symm
 rw [← hb] at hs ht; have e:= (strip_seats Y H j s r).1 hs; let p:= (crest_charge Y H j s r T ht); have hp:= cover_between (tent Y H) Λ l rfl j (fun i hi=> (e i hi).2) p
 let t:= ticket Y H G s
 have hy: t x₀ * t y₀ = t (x₀*y₀):= Eq.symm (Filter.Germ.coe_eq.mpr (Eventually.of_forall (fun n=> Subtype.ext (woven_product Y H G.history.circuit s (n-s) xv xt hp)))) -- tune
 rw [show ticket Y H G s x₀*_=_ from hy]; exact ticket_mem Y H G ((insideAt Λ l K true A s).mul_mem (insideAt_mono h1 v) (insideAt_mono h2 w₀))
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Tm" i:max=> Picket.trans (S₀ i)
include F b
lemma stageTime (x:Sky K)(t s:Gt)(B:(J₀ j).Op) (h:(Q j) x t B) (N:Set RSpace)(e:N⊆ flank j 0)(y f: Ds N)(q:f.val=x* move K (eject j t+eject z s) y.val) : (((Π j) B)*(Tm j) ((s:ℝ) • basis z)) ((Λ₁ j) N e y)=(Λ₁ j) N e f:=by
 let g: D' j:=Submodule.inclusion (le_trans (domain_loose Y H G _) (domain_mono Y H G e)) y
 let g': D' j:= ⟨_,later_frame Y H V G j g.val (eject z s) g.property (by simp[b])⟩
 have hg:(Λ₁ j) N e y=(Vo j) g:=rfl
 obtain ⟨u,t',v⟩:=voice_follows Y H V G j _ _ (F.present j) h g'
 change u.val=x*move K (eject j t) (move K (eject z s) y.val) at t'; rw[move_sum] at t'; let z':D' j:=Submodule.inclusion (le_trans (domain_loose Y H G _) (domain_mono Y H G e)) f
 change _=(Vo j) z'; rw [show z'=u from Subtype.ext (q.trans t'.symm),v, hg, ← castSpace Y H V G C a χ j b.symm s,mul_apply_eq_comp, ← voice_move Y H V G j (C j) (w j) (F.present j) (eject z s) g (by simp [b]) g'.property]
local notation "W" i:max t:max=> strip i 0 (t:ℝ)
include p
lemma herePass (x:Sky K)(t s:Gt)(B:(J₀ j).Op)(A:(J₀ z).Op) (h:(Q j) x t B)(g:(Q z) x s A)(k:0<(t:ℝ))(v:0≤(s:ℝ))(q:x∈ Ds (W j t ∩ W z s)) : Z.Pass (((Π j) B)*(Tm j) ((s:ℝ) • basis z)) (((Π z) A)*(Tm z) ((t:ℝ) • basis j)) := by
 apply p.port.pass
 intro f; let d:=(eject j t+eject z s); let y:= move K d f.val; let N:= slides (coordinates Λ d) U
 have w₁ : N⊆ U:= by
     rintro _ ⟨i,a,rfl⟩; simp only [flank,Set.mem_inter_iff,Set.mem_setOf_eq,Pi.add_apply,map_add,coordinates_eject,d,eject_at,eject_away _ _ _ b,eject_away _ _ _ b.symm,add_zero,zero_add] -- order
     exact ⟨add_nonneg a.1 k.le,add_nonneg a.2 v⟩
 have w₂ : N⊆ flank j (t:ℝ):= by
    rintro _ ⟨i,a,rfl⟩; simp only [flank,mem_setOf_eq,Pi.add_apply,map_add,d,coordinates_eject,eject_at,eject_away _ _ _ b,add_zero,le_add_iff_nonneg_left]; exact a.1
 have hx : x*y∈Ds U:= span_front Y H G j t k inter_subset_left w₂ (Set.inter_subset_inter (strip_in ..) (strip_in ..)) w₁ x y q (moving Y H V G d f.val f.property)
 let y':Ds U:=⟨_,hx⟩; rw[stageTime Y H V G C a χ F j z b x t s B h U inter_subset_left f y' rfl, stageTime Y H V G C a χ F z j b.symm x s t A g U inter_subset_right f y' ((by change x* move K (eject j t+eject z s) f.val= _; rw [add_comm] ))]; exact p.port.sees y'
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
