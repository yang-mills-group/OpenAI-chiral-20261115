import YM.SU5.FiniteGaugeData.Hills.Pal
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
variable (a b:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)(B:Repertory Y h W' R b)(p:a≠b)
local notation "F"=> Camera Y h a W' R A
local notation "G"=> Camera Y h b W' R B
local notation "X" s:max=> route Y h s a W' R A
local notation "V" s:max=> route Y h s b W' R B
local notation "U"=> Sync (Pears Y h a b W' R A B)
local notation "K"=> (Pears Y h a b W' R A B)
local notation "Ω"=> orbitSeed Y h a W' R A
local notation "φ"=> orbitSeed Y h b W' R B
variable {u' x:(Camera Y h a W' R A).Op}{y v':(Camera Y h b W' R B).Op}
include A B p
-- C.expect implies comm in whole vacuum subspace
lemma peer_e (z:Sync (Pears Y h a b W' R A B) x y)(t:Sync (Pears Y h a b W' R A B) u' v'): x*u'=u'*x:=by
 let f:=sync_mul Y h a b W' R A B p z t
 let g:=sync_flip Y h a b W' R A B p t z
 apply phase_ac Y h a W' R A
 intro i k w s; let a':= fire Kₜ a 0 w
 let u₀:= meet_x Y h k a b W' R A B s; let c:=meet_x Y h i a b W' R A B a'
 have he {P₁ : (F).Op}{P₂:(G).Op}(t:U P₁ P₂): inner ℂ ((X i) w Ω) (P₁ ((X k) s Ω))=inner ℂ φ (((V i) a' * (P₂ * (V k) s)) φ) := by
    rw [← _root_.mul_apply_eq_comp]; -- maybe rewrites wrong
    refine Eq.trans ?_ (sync_identity Y h a b W' R A B (sync_mul Y h a b W' R A B p c (sync_mul Y h a b W' R A B p t u₀)))
    unfold a'; simp_rw [route_mirror, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint]; rw [ContinuousLinearMap.adjoint_inner_right]
 exact (he f).trans (he g).symm
-- extension to all generators etc
lemma compass (d i:ℕ)(f g:W (tent Y h)):
 Commute (route Y h i a W' R A f) (route Y h d a W' R A g):= peer_e Y h a b W' R A B p (meet_x Y h i a b W' R A B f) (meet_x Y h d a b W' R A B g)
omit B p in
lemma sibling : ∃ b:Axis,a≠b:= by
 by_cases p:a=3; · subst a; exact ⟨1,by decide⟩
 exact ⟨3,p⟩ -- formatting
omit B p in
lemma commute_pt (d i:ℕ)(x y:W (tent Y h)): Commute ((X i) x) ((X d) y):=by obtain ⟨b,p⟩:=sibling Y h a W' R A; exact compass Y h a b W' R A (Agora Y h W' R b) p d i x y
omit B p in
lemma effectiveV (p:∀ i f,Commute ((X i) f) x)(v:x Ω=0): x=0:=by
 apply phase_ac Y h a W' R A; intro i k u v'; rw [← mul_apply_eq_comp,← (p k _).eq,mul_apply_eq_comp,v]; simp

-- different reflection-stars coincide on routes. Test f with a-star and negative b-star. Any anti-comm discrepancy lives in this zero route.
variable (f: W (tent Y h))
lemma opposed (v:fire Kₜ b 0 f= -(fire Kₜ a 0 f)): route Y h s a W' R A f=0:=by
 let Z:= fire Kₜ a 0 f
 have hz: -(route Y h s b W' R B Z)=star (route Y h s b W' R B f):=by rw [← map_neg,← route_mirror,v]
 have he:= sync_identity Y h a b W' R A B (sync_mul Y h a b W' R A B p (meet_x Y h s a b W' R A B Z) (meet_x Y h s a b W' R A B f))
 rw [show (X s) Z=star ((X s) f) from route_mirror .., show (V s) Z= -star ((V s) f) from by rw [← hz,neg_neg],mul_apply_eq_comp,neg_mul, _root_.neg_apply,mul_apply_eq_comp, inner_neg_right, ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at he
 -- tune order precedence
 let w := (X s) f Ω; let r:= (V s) f φ; change inner ℂ w w= -inner ℂ r r at he
 have hv {S:Hilbert} (x:S) : 0 ≤ inner ℂ x x:= by rw [inner_self_eq_norm_sq_to_K]; change 0≤(↑‖x‖:ℂ)^2; rw [←Complex.ofReal_pow]; exact ⟨sq_nonneg _, rfl⟩
 have hw:inner ℂ w w=0:= le_antisymm (le_trans he.le (neg_nonpos.mpr (hv (S:=G) r))) (hv (S:=F) w)
 exact effectiveV Y h a W' R A (fun i v=>commute_pt Y h a W' R A s i v f) ((inner_self_eq_zero (𝕜:=ℂ)).1 hw)
lemma reflects_x : route Y h s a W' R A (fire Kₜ b 0 f)=star (route Y h s a W' R A f) := by
 let g:=fire Kₜ b 0 f-fire Kₜ a 0 f
 have hg: fire Kₜ b 0 g= -fire Kₜ a 0 g:=by
    have he(i:Axis)(x y:W (tent Y h)): fire Kₜ i 0 (x-y)=fire Kₜ i 0 x-fire Kₜ i 0 y:=map_sub (Playlist.Show.freezing Y h i 0) ..
    unfold g; rw [he,he,burning_ice,burning_ice,← fire_pair a b p]; abel
 have ht:= opposed Y h s a b W' R A B p g hg; unfold g at ht; rw [map_sub, route_mirror Y h s a W' R A] at ht; exact sub_eq_zero.mp ht
lemma star_eye : Sync (Pears Y h a b W' R A B) (star (route Y h s a W' R A f)) (star (route Y h s b W' R B f)):= by rw [←reflects_x Y h s a b W' R A B p f, ←route_mirror]; exact meet_x ..
lemma award_e (g:W (tent Y h))(t:Sync (Pears Y h a b W' R A B) x y): inner ℂ (((X s) f) Ω) (x ((X i) g Ω))=inner ℂ ((V s) f φ) (y ((V i) g φ)):= by
 have he:= sync_identity Y h a b W' R A B (sync_mul Y h a b W' R A B p (star_eye Y h s a b W' R A B p f) (sync_mul Y h a b W' R A B p t (meet_x Y h i a b W' R A B g))); simp_rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at he; exact he
#print axioms commute_pt
#print axioms award_e
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
