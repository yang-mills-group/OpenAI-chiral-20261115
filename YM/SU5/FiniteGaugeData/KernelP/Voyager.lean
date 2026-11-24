import YM.SU5.FiniteGaugeData.KernelP.Replica
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (j:Axis)(H:Harbor Y h W' R Φ a)
local notation "G" s:max => H.leaf s
section engine
include H S'
private lemma comptP (x:D)(z:ℤ)(p:Allows a j z): ‖H.leaf s (hoist Y h a j z p x)‖≤ ‖H.leaf s x‖:= by
 apply (moneyB _ _).1; rw [H.measure,H.measure]; by_cases e:j=a
 · subst j; obtain ⟨n,rfl⟩:= Int.eq_ofNat_of_zero_le (p rfl); exact (S'.hardy s a x n).2
 rw [hoist_val,helve, clock_normal Kₜ j a 0 z x.val (Ne.symm e),← clock_mul,S'.color]

private abbrev clocks (s' :ℕ) (p:Allows a j z) : Decko Y h a→ₗ[ℂ] Decko Y h a := hoist Y h a j (Chrono.scaleR Λ s s' z) (positive_scale z Λ.R.L (s'-s) p)
variable (p:Allows a j z)
local notation "c" b:max=> clocks Y h s a z j b p -- argument order
lemma envelop : Codec Y h s W' R a H (fun s' :ℕ=>clocks Y h s a z j s' p) 1:=by
 constructor
 · intro i t x; unfold clocks; rw [hoist_up Y h i W' R a j x _]; apply Subtype.ext; rw [hoist_val,hoist_val,scale_step s i z t]
 intro i t x; rw [one_mul]; exact comptP Y h i W' R A S' a j H x _ _
def conquer:H.space.Op:= criterion Y h s W' R a H (fun t:ℕ=> clocks Y h s a z j t p) 1 (envelop Y h s W' R A S' a z j H p)
lemma conquered {x:Decko Y h a} (v:s ≤ i) : conquer Y h s W' R A S' a z j H p ((G i) x)= (G i) ((c i) x):= criterion_seed Y h s i W' R a H x _ _ _ v
lemma conquered_c : ‖conquer Y h s W' R A S' a z j H p‖≤1:= criterion_norm Y h s W' R a H _ _ _ zero_le_one

local notation "C" i:max=> conquer Y h i W' R A S' a
set_option maxHeartbeats 620000 in
def level_policy : Terrace H.space Λ.R.L a:=by -- `def` later.Proof robust due p dependent.
 refine { stepT:=fun s j z p=> conquer Y h s W' R A S' a z j H p,size_:=fun t i z p=> conquered_c Y h t W' R A S' a z i H p, ident:=?_, via:=?_, cool:=?_, repeats:=?_ }
 · intro s j; apply leaf_ext Y h s W' R a H (H':=H.space); intro i t x; rw [conquered ..]; have hz: clocks Y h s a 0 j i (fun _=>le_rfl) x=x:= Subtype.ext (by unfold clocks; rw [hoist_val,scalaZero,tic_zero]); rw [hz]; rfl; exact t -- multi goals
 · intro s j z t v u p q b; apply leaf_ext Y h s W' R a H (H':=H.space); intro k w x; rw [mul_apply_eq_comp, conquered Y h s k W' R A S' a t j H p w,conquered Y h s k W' R A S' a z j H u w,conquered Y h s k W' R A S' a v j H q w]; apply congrArg; apply hoist_sum; unfold Chrono.scaleR; rw [← mul_add,b] -- equality arg provide
 · intro s i j z n w p u; apply leaf_ext Y h (max s n) W' R a H (H':=H.space); intro k v x; obtain ⟨p',u'⟩:=max_le_iff.mp v; change _= (_*_ : H.space.Op) _; simp_rw [mul_apply_eq_comp]; rw [conquered Y h n k W' R A S' a w j H u u',conquered Y h s k W' R A S' a z i H p p',conquered Y h s k W' R A S' a z i H p p',conquered Y h n k W' R A S' a w j H u u']; apply congrArg; exact hoist_cross ..
 intro s j z t u; apply leaf_ext Y h (s+1) W' R a H (H':=H.space); intro k p' x; rw [conquered Y h s k W' R A S' a z j H t (by omega), conquered Y h (s+1) k W' R A S' a _ j H u p']; apply congrArg; apply Subtype.ext; unfold clocks; rw [hoist_val,hoist_val]; rw [scale_trans s (s+1) k z (by omega) p',scale_step s s z le_rfl, scale_same]
-- relations to plants
lemma stairsK (x:D): (level_policy Y h W' R A S' a H).stepT s j z p (H.leaf s x)=H.leaf s (hoist Y h a j z p x):=by
  change conquer Y h s W' R A S' a z j H p _= _; rw [conquered ..]; apply congrArg; apply Subtype.ext; unfold clocks; rw [hoist_val,hoist_val,scale_same]; exact le_rfl
#print axioms stairsK
end engine

-- TicketI allows discrete reconstruction for any candidate and all scales. A package so that we can use the ACTUAL gram solutions without replacing by an isometric choice. primitive assumption not incl.L.
abbrev Engine:= {A: Terrace H.space Λ.R.L a // ∀ (s:ℕ)(x:Decko Y h a) (j:Axis)(z:ℤ)(p:Allows a j z), A.stepT s j z p (H.leaf s x)= H.leaf s (hoist Y h a j z p x) }
local notation "𝓔"=> Engine Y h W' R a H
def dispatch : Engine Y h W' R a H := ⟨_, fun s x j z p=> stairsK Y h s W' R A S' a z j H p x⟩
variable (Q:Engine Y h W' R a H)
def legacyEngine : Engine Y h W' R a (OriginalH Y h W' R A a):= ⟨StructureH Y h a W' R (A a),fun s x j z p=> clock_own Y h s W' R a j (A a) x z p⟩
local notation "P'"=> Q.val
-- identification arbitrary scale
include Q
lemma Vessel (x:Decko Y h a)(p: Allows a j z)(t:s ≤ i): Q.val.stepT s j z p (H.leaf i x)= H.leaf i (hoist Y h a j (Chrono.scaleR Λ s i z) (positive_scale z Λ.R.L (i-s) p) x):=by
 suffices E: (P').stepT s j z p=(P').stepT i j (Chrono.scaleR Λ s i z) _ from (congrArg (fun T:H.space.Op=>T (H.leaf i x)) E).trans (Q.property i x j _ (positive_scale z Λ.R.L (i-s) p))
 induction i,t using Nat.le_induction with
 | base=> apply matching _ _ (scale_same s z).symm
 | succ k v ih=> apply ih.trans; refine ((P').ascent k j (Chrono.scaleR Λ s k z) _).trans ?_; apply matching; symm; exact scale_step s k z v
where matching s j {z y:ℤ}{e c}(v:z=y):Q.val.stepT s j z e=Q.val.stepT s j y c:= by subst z; rfl

lemma Vessel_total (p: Allows a j z): Q.val.stepT s j z p=conquer Y h s W' R A S' a z j H p:=by apply leaf_ext Y h s W' R a H (H':=H.space); intro i t x; exact (Vessel Y h s i W' R a z j H Q x p t).trans (conquered Y h s i W' R A S' a z j H p t).symm
#print axioms dispatch
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
