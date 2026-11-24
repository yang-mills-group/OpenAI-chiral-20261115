import YM.SU5.Reconstruction.Crease.Screen
import YM.SU5.Reconstruction.Crease.Reservoir
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
local notation "Φ"=> Flare Y H V G C a χ F j z b
local notation "ℶ"=> Flare Y H V G C a χ F z j b.symm
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
include F p
lemma deep_after (x y:D₀): inner ℂ ((Φ).f (Z.l x)) (Z.l y) = inner ℂ ((ℶ).f (Z.r x)) (Z.r y):= by
   apply closure_minimal ?_ (show IsClosed {x:D₀| inner ℂ ((Φ).f (Z.l x)) (Z.l y) = inner ℂ ((ℶ).f (Z.r x)) (Z.r y)} from isClosed_eq (((Φ).f.continuous.comp Z.l.continuous).inner continuous_const) (((ℶ).f.continuous.comp Z.r.continuous).inner continuous_const)) (p.port.full x)
   rintro x ⟨f,e,h⟩; change inner ℂ ((Φ).f (Z.l x)) (Z.l y)=_;rw [e,h]
   let W:=lowland j 0 ∩ lowland z 0; have hp: flipMark j K ((θ z) f.val)∈ Ds W:= by
     apply domain_mono Y H G _ (mirror_support Y H G j _ (mirror_support Y H G z f.val f.property))
     rintro _ ⟨_,⟨m,v,rfl⟩,rfl⟩; constructor
     · change _≤ (0:ℝ); simp [mirrorE,b]; exact v.1
     change _≤ (0:ℝ); simp [mirrorE,b.symm]; exact v.2
   let g:=(⟨_,hp⟩: Ds W); have ht:=p.port.meets g y
   refine Eq.trans ?_ (ht.trans ?_) -- birthday
   · apply congrArg (fun i:G₀ j=> inner ℂ i (Z.l y)); apply flare_cash Y H V G C a χ F j z b (Submodule.inclusion (le_trans (domain_loose Y H G U) (domain_mono Y H G inter_subset_left)) f) (Submodule.inclusion (domain_loose Y H G _) (⟨(θ j) g.val,domain_mono Y H G (top_ready j z b.symm) (mirror_support Y H G j g.val g.property)⟩: Ds (flank j 0))) ?_; exact mirror_twice ..
   apply congrArg (fun i:G₀ z=> inner ℂ i (Z.r y)); apply Eq.symm (flare_cash Y H V G C a χ F z j b.symm (Submodule.inclusion (le_trans (domain_loose Y H G U) (domain_mono Y H G inter_subset_right)) f) (Submodule.inclusion (domain_loose Y H G _) (⟨(θ z) g.val,domain_mono Y H G (low_ready j z b.symm) (mirror_support Y H G z g.val g.property)⟩: Ds (flank z 0))) ?_); change (θ z) ((θ j) ((θ z) f.val))=_; rw [mirror_commuting Y H z,mirror_twice]; rfl
variable (u v: Axis→ marks (timeMesh Λ))(x:Sky (tent Y H))(h:marks (timeMesh Λ))(t:0<(h:ℝ))(B:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
variable (d:Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x h B) (g:x∈ Domain Y H G true (Tarp j (fun i=>(u i:ℝ)) (fun i=> (v i:ℝ)) (h:ℝ))) (e:0<(u z:ℝ))
local notation "Ψ"=>reversion (tent Y H) Λ j
omit F p
include b e g
lemma tarps : x∈ Ds (flank j 0 ∩ flank z 0):= by
 apply domain_mono Y H G _ g; rintro _ ⟨⟨k',_⟩,h⟩; exact ⟨k',le_trans e.le ((h z b.symm).1)⟩
include F p t d
lemma spends : ∃ i:Ds (flank j 0∩flank z 0),i.val=x ∧ ((Λ₁ j) U inter_subset_left i)= (Π j) B (Ω₀ j) ∧ Z.Latch ((Π j) B (Ω₀ j)) ((Λ₁ z) U inter_subset_right i):=by
 let w':=tarps Y H G j z b u v x h g e; let y:Ds U:=⟨x,w'⟩
 have hx : ((Π j) B) (Ω₀ j)=(Λ₁ j) U inter_subset_left y:= (Reflector.carries Y H V G C a χ j x h d (F.present j) t).1
 rw [hx]; exact ⟨y,rfl,rfl,p.port.sees y⟩
-- adjoint & norm cost in same
lemma second_mirror (hv:0<(v z:ℝ))(S:(J₀ z).Op)(b':(Q z) (m₁ (eject z (-u z)) x) (v z) S): ∃ y:(G₀ z),Z.Latch ((Π j) B (Ω₀ j)) y ∧ Z.Latch (star ((Π j) B) (Ω₀ j)) (Picket.trans (S₀ z) ((h:ℝ) • basis j) ((ℶ).f y)) ∧ ‖y‖≤ ‖(Π z) S‖:= by
 obtain ⟨i,e',-,p1⟩:=spends Y H V G C a χ F j z b Z p u v x h t B d g e; obtain ⟨k',g',-,q⟩:= spends Y H V G C a χ F j z b Z p u v (Ψ h x) h t (star B) (fromBack Y H V G C a χ j x h d t) (repo Y H V G j u v x h g) e
 let V₁(f: Ds U) : D' z:= Submodule.inclusion (le_trans (domain_loose Y H G U) (domain_mono Y H G inter_subset_right)) f; let Y' := V₁ k'; let y₀ := V₁ i
 refine ⟨(Vo z) y₀,p1,?_,?_⟩
 · rw [op_star Y H V G C a χ F j] at q
   let yp: D' z:=⟨_,sidestamp Y H G z j b.symm y₀⟩; rw [flare_cash Y H V G C a χ F z j b.symm y₀ yp rfl]
   have hv:(V₁ k').val=m₁ (eject j h) yp.val:= by change k'.val=m₁ _ ((θ j) i.val); rw [e',g']; rfl
   have hx:(Λ₁ z) U inter_subset_right k'= Picket.trans (S₀ z) ((h:ℝ) • basis j) ((Vo z) yp):=by
     change (Vo z) (V₁ k')=_
     rw [← castSpace Y H V G C a χ z b]
     exact Eq.trans (congrArg _ (Subtype.ext hv)) (voice_move Y H V G z _ _ (F.present z) _ yp (by simp [b.symm]) (hv ▸ (V₁ k').property))
   rw [← hx]; exact q
 let y:= outgoing Y H G z _ _ b'.pose; have he:y₀.val=m₁ (eject z (u z)) y.val:= by change i.val=m₁ _ (m₁ _ x); simp only [e',move_sum,selectRay,add_neg_cancel,eject_zero,move_by_zero]
 let s := (u z:ℝ).toNNReal; let T:=(S₀ z).E s
 have hb: (Vo z) y₀=T ((Vo z) y):= by
    rw [← show (Pr z) (eject z (u z))=T from bridge_time ..]; exact Eq.trans (congrArg _ (Subtype.ext he)) (voice_move Y H V G z _ _ (F.present z) _ y (by rw [coordinates_eject,eject_at]; exact e.le) (he ▸ y₀.property))
 rw [hb,← (Reflector.carries Y H V G C a χ z _ _ b' (F.present z) hv).1]; apply le_trans ?_ (show ‖((Π z) S) (Ω₀ z)‖≤ ‖(Π z) S‖ from (by simpa only [vocation_norm,mul_one] using ((Π z) S).le_opNorm (Ω₀ z)))
 exact (T.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) ((S₀ z).shrinks _))
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
