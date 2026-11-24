import YM.SU5.Reconstruction.Oblique.Dynamo
import YM.SU5.Reconstruction.Quartz.Pomona
import YM.SU5.Reconstruction.Quartz.Rake
/-! # Opposite widths pricing.WOT aperture. Used for local regions' rotation -/
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
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (B:BoostBacking Y H V G C a χ){s: Signed}(A:Pave Y H V G C a χ s){j z:Axis}(t:Oriented s j z)
def newwidth(s:Signed)(x:placement Λ):placement Λ := fun i=>x (s.perm.symm i)
def thresholdV (p:Bool)(x y: Gt) :↥(marks (timeMesh Λ)):=if p then -(x+y) else x
noncomputable def newstart(s:Signed) (u v:placement Λ): placement Λ:=fun i=>thresholdV (s.flip (s.perm.symm i)) (u (s.perm.symm i)) (v (s.perm.symm i))
lemma crate(s:Signed)(x:placement Λ)(i:Axis): newwidth s x (s.perm i)=x i:= by unfold newwidth; rw [s.perm.symm_apply_apply]
lemma newAt(s:Signed)(u v:placement Λ)(i:Axis): newstart s u v (s.perm i)=thresholdV (s.flip i) (u i) (v i):=by unfold newstart; rw [s.perm.symm_apply_apply]
lemma twistedHere{w:ℝ}(b r:Gt)(p:Bool): w∈ Set.Icc (b:ℝ) ((b:ℝ)+(r:ℝ)) ↔ hush p w ∈ Set.Icc ((thresholdV p b r):ℝ) ((thresholdV p b r: Gt).val+(r:ℝ)):=by
 cases p; · rfl
 simp only [hush_true,thresholdV,↓reduceIte,Set.mem_Icc, AddSubgroup.coe_neg,AddSubgroup.coe_add]; constructor <;> rintro ⟨_,_⟩ <;> constructor <;> linarith
local notation "▹" u:max=>fun i=>(u i:ℝ)
open BridgeClub
include t
lemma motor_tarp (w:ℝ)(u v:placement Λ): s.act '' Tarp j (▹ u) (▹ v) w = Tarp z (▹(newstart s u v)) (▹ (newwidth s v)) w:=by
 ext y; obtain ⟨y,rfl⟩:= s.actEquiv.surjective y
 -- tune Eq statement s.actEquiv
 change s.act y∈ _ ↔ s.act y∈ _; rw [Set.mem_image_iff_of_inverse (g:=s⁻¹.act) s.inv_act s.act_inv, s.inv_act]; constructor
 · intro ⟨x,c⟩ -- projection maybe as if Tarp membership defin?
   refine ⟨t.height y |>.symm ▸ x,?_⟩; intro i w'; obtain ⟨i,rfl⟩:= s.perm.surjective i; dsimp only; rw [crate,newAt, show s.act y (s.perm i)=hush (s.flip i) (y i) from Signed.act_at s y i]; exact (twistedHere ..).1 (c i (fun g=> w' (g.symm ▸ t.peer))) -- Signed act_at must change to hush
 intro hx; refine ⟨t.height y ▸ hx.1,?_⟩; intro i w'
 have h:= hx.2 (s.perm i) (by rw [←t.peer]; exact s.perm.injective.ne w'); dsimp only at h; rw [crate,newAt] at h; apply (twistedHere _ _ (s.flip i)).2; exact ((show s.act y (s.perm i)=hush (s.flip i) (y i) from Signed.act_at s y i) ▸ h)
lemma motor_data(u v:placement Λ): sailPoint s '' Reel j (▹ u) (▹ v)= Reel z (▹ (newstart s u v)) (▹ (newwidth s v)):=by
 ext y; constructor
 · rintro ⟨x,p,rfl⟩; refine ⟨(t.sees x).trans p.1,?_⟩
   intro i q; obtain ⟨i,rfl⟩:=s.perm.surjective i; dsimp only; rw [crate, newAt,sails_coord]; exact (twistedHere ..).1 (p.2 i (fun g=> q (g.symm ▸ t.peer)))
 intro h; let x:= sailPoint s⁻¹ y; have hv:sailPoint s x=y:= sail_right s y; refine ⟨x,⟨t.return_z.sees y |>.trans h.1, ?_⟩,hv⟩; intro i u'
 have he:= h.2 (s.perm i) (by rw [←t.peer]; exact s.perm.injective.ne u'); rw [←hv] at he; dsimp only at he; rw [crate,newAt,sails_coord] at he; exact (twistedHere _ _ (s.flip i)).2 he
omit t
open Quartz.Ship Crease Reflector
lemma unit_norms {X M:Hilbert}(F:X≃ₗᵢ[ℂ]M)(x:X.Op): ‖F.conjStarAlgEquiv x‖=‖x‖:= le_antisymm (Quartz.lift_budget F x) (by
 let y:= F.conjStarAlgEquiv x; have h:= Quartz.lift_budget F.symm y; unfold y at h; rwa [run_base] at h)
include B A
-- Return costs even for opposite signed directions. Notice Width strictly positive as needed in program.
lemma turned_width (u v:Gt)(e:0<(v:ℝ))(d:Axis)(x: Sky (tent Y H))(T:(J₀ d).Op)(h:(Qv d) (au (eject d (-u)) x) v T):
    let i:= s.perm d; ∃ Tm:(J₀ i).Op, (Qv i) (au (eject i (- thresholdV (s.flip d) u v)) (A.shift x)) v Tm ∧ ‖(π i) Tm‖=‖(π d) T‖:= by
 intro z; cases y:s.flip d
 · let r: Oriented s d z:= ⟨rfl,y⟩
   obtain ⟨D₀,h₀,p⟩:=follows_move Y H V G C a χ B A r v e T h; rw [A.strips,r.axis_eject] at h₀; exact ⟨_,h₀,by rw [p,unit_norms]⟩
 obtain ⟨b,k⟩:= exists_ne z; let Q:=Signed.mirror b * Signed.mirror z; let V₁:=Pave.relay Y H V G C a χ A (Blush.properMem Y H V G C a χ (plain Y H V G C a χ z) (plain Y H V G C a χ b)); have e': Oriented (Q*s) d z:=by refine ⟨rfl,?_⟩; unfold Q; simp only [Signed.mul_flip, Signed.mirror, y]; simp [z,k]
 let f:= V₁.shift (au (eject d (-u)) x)
 obtain ⟨M,hM,vM⟩:= follows_move Y H V G C a χ B V₁ e' v e T h
 obtain ⟨Dx,hN,uN⟩:= Crease.otherFate Y H V G C a χ B z b k.symm f v e M hM
 refine ⟨star Dx,?_,?_⟩
 · convert Reflector.fromBack Y H V G C a χ z (flipMark b K f) v hN e using 1
   unfold reversion; change au _ _= au (eject z v) ((θ z) ((θ b) _))
   rw [show f=(θ b) ((θ z) (A.shift (au (eject d (-u)) x))) from rfl,A.strips,tilt_eject,y,hush_true,neg_neg,mirror_twice,mirror_twice, move_sum, show s.perm d=z from rfl, selectRay, add_comm v u, thresholdV]; simp -- may extra goals
 rw [op_star Y H V G C a χ B z,uN,norm_star,Flash.shade_cost,vM,unit_norms]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
