import YM.SU5.FiniteGaugeData.Hills.Fragments
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
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
variable (a₀ a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:∀ a:Axis,Repertory Y h W' R a)
variable (p:Actors Y h a₀ W' R (A a₀))(α:p.val.X)
local notation "F"=> Camera Y h a W' R (A a)
local notation "P₀"=>issueH Y h s a₀ W' R (A a₀) p α
local notation "H₁"=>route Y h s a W' R (A a)
local notation "U1"=> (StructureH Y h a W' R (A a)).Unity
local notation "M" i:max d:max f:max p:max=> Wedge Y h i a d W' R (A a) f p
variable {f:W (tent Y h)}(x:Decko Y h a)
include A p α
local notation "z"=> vectorT Y h a x n
lemma step_selected (u:0≤n): 0 ≤ issueH Y h s a₀ W' R (A a₀) p α (helve Kₜ a x.val (vectorT Y h a x n).val) ∧
    issueH Y h s a₀ W' R (A a₀) p α (helve Kₜ a (vectorT Y h a x n).val (vectorT Y h a x n).val) ≤ issueH Y h s a₀ W' R (A a₀) p α (helve Kₜ a x.val x.val):= by
 obtain ⟨S,p₁,V⟩:= x.property; obtain ⟨d,c,t⟩:= resident Y h S a _ p₁ V; have e:0 < n+d:= by omega
 let y:= z; have p₁':Plan Y h a (n+d) y.val:= plan_steps Y h a d _ t (n:ℤ) (by positivity) (show (d:ℤ)+n≤↑(n+d) from by omega)
 let T' := tock Y h s W' R a a (A a) n (fun _=> Nat.cast_nonneg' _)
 have hz : M s (n+d) p₁' e=T'*(M s d t c) := wicket_adv Y h s a d (n+d) x.val W' R (A a) t c n rfl (show Plan Y h a (n+d) (clockW Kₜ a n x.val) from p₁')
 constructor
 · apply phase_property Y h s a₀ W' R A p α _ a isClosed_Ici; intro u hu; change 0 ≤ inner ℂ u ((H₁) (helve Kₜ a x.val y.val) u); rw [plate_score Y h s d (n+d) W' R A x.val a t c _ y.val p₁' e,hz]; exact (tock_positive Y h s W' R a (A a) n (Nat.cast_nonneg' _)).inner_nonneg_right _
 apply sub_nonneg.mp; rw [← map_sub (f:=P₀)]; apply phase_property Y h s a₀ W' R A p α _ a isClosed_Ici; intro w v; change 0 ≤ inner ℂ w ((H₁) (_ - helve Kₜ a y.val y.val) w)
 rw [map_sub (H₁),_root_.sub_apply,inner_sub_right,sub_nonneg,plate_score Y h s d d W' R A x.val a t c _ _ t c,plate_score Y h s (n+d) (n+d) W' R A y.val a p₁' e _ _ p₁' e,hz]; apply (moneyB _ _).mpr; exact (T'.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (toll_bound Y h s W' R a a (A a) _ _))
-- transport op bound.One fixed level only then use price every higher by Wedge-step coherence
lemma lease_selected (t:Plan Y h a d f)(c:0<d):
    let y:=embark Y h a d t x
    let V:ℂ:= (↑‖Wedge Y h s a d W' R (A a) t c‖:ℂ)^2
    issueH Y h s a₀ W' R (A a₀) p α (helve Kₜ a y.val y.val) ≤ V • (issueH Y h s a₀ W' R (A a₀) p α (helve Kₜ a x.val x.val)) := by
 intro y V₁; obtain ⟨S,p₁,v₁⟩:= x.property; obtain ⟨n,t₀,V⟩:= resident Y h S a _ p₁ v₁; let T':=Wedge Y h s a d W' R (A a) t c; let Z:= M s n V t₀
 apply sub_nonneg.mp; rw [← map_smul (P₀) V₁, ← map_sub (f:=P₀)]; apply phase_property Y h s a₀ W' R A p α _ a isClosed_Ici; intro w cw; let D:= couplePlan Y h a d n t V; have hd:Plan Y h a (d+n) y.val:=D; change 0 ≤ inner ℂ w ((H₁) _ w)
 rw [map_sub (H₁),map_smul (H₁),_root_.sub_apply, _root_.smul_apply, inner_sub_right,inner_smul_right,plate_score Y h s n n W' R A x.val a V t₀ _ _ V t₀, plate_score Y h s (d+n) (d+n) W' R A y.val a hd (by omega) _ y.val hd (by omega)] -- needs y.val
 have he: M s (d+n) hd (by omega) = T'*Z:=(wedge_glues Y h s a d n W' R (A a) t c V D t₀).symm; rw [he]; exact moneyA (T' (Z (cpo U1 w))) _ ‖T'‖ (norm_nonneg _) (T'.le_opNorm _)
#print axioms step_selected
#print axioms lease_selected

-- Extend positivity any aligned s∈Z issue.Roll promoting marker finitely.Header. Pop.Move. Later
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
