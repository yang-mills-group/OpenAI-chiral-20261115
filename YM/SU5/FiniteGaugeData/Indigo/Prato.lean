import YM.SU5.FiniteGaugeData.Jadot.Chor
import YM.SU5.FiniteGaugeData.Indigo.Floral
/-! # Color. Halo and authentic estimation, Revenue.Holding all clocks. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon

open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
variable {N:Side}{V: Calibration}{n m w ℓ d:ℕ}{p C x y r θ ξ v' u' H μ ε δ e ρ:ℝ}{S:Finset Cover}{ζ:ℂ}
set_option maxRecDepth 3500
set_option maxHeartbeats 570000
/-! # Mixed factors: raw-link-only sensors, not necessarily uniformly geometric
 cost. -/
open Tint Eight.Bonbon
namespace Prato
open scoped Classical
section
abbrev RawX (f:Mark N):Prop := ∃ x:Pane N→ℂ,∀ U:Fields N, f U=x U.1 • 1
/-- each phase/chord width charged independently. Pure raw link only (even Borel). -/
abbrev RawG(K':Calibration)(f:W K'):Prop:= ∀ N:Side,RawX (f.val N)
namespace RawG
variable {K':Calibration}{f f':W K'} (h:RawG K' f)
lemma oneG(K':Calibration) : RawG K' 1:= fun _=> ⟨fun _ => 1,fun W=> (one_smul ..).symm⟩
include h
lemma scaleG(z:ℂ): RawG K' (z • f):=by
 intro N; obtain ⟨F,q⟩:= h N; refine ⟨fun U=> z*F U,fun V=>?_⟩; change z•f.val _ _=_; rw [q,mul_smul]
lemma subG(h':RawG K' f'):RawG K' (f-f'):=by intro N; obtain ⟨F,q⟩:= h N; obtain ⟨G,p⟩:=h' N; refine ⟨fun X=> F X-G X,fun V=>?_⟩; change f.val _ _-f'.val _ _=_; rw [p,q,sub_smul]  -- orientation
lemma mulG(h': RawG K' f'):RawG K' (f*f'):=by intro N; obtain ⟨F,q⟩:=h N; obtain ⟨G,p⟩:=h' N; refine ⟨fun X => F X*G X,fun V=>?_⟩; change f.val _ _*f'.val _ _=_; rw [p,q, Algebra.smul_mul_assoc, one_mul, mul_smul] -- ambiguous rewrites
omit h
lemma swath (h:Real.exp 1 ≤ Λ.x)(s:ℕ)(Z:Finset (Face ℤ))(r:ℝ): RawG (tent Y h) (swatch Y h s Z r):=by
 intro N; refine ⟨fun X=> if triggerM Y h s Z r N X then 1 else 0,fun X=> ?_⟩; rw [Bonbon.stroke]; split_ifs <;> simp <;> assumption
lemma inside(h:Real.exp 1 ≤ Λ.x)(s:ℕ)(Z:Finset (Face ℤ))(p:ℕ){F:W (tent Y h)}(t:RawG (tent Y h) F):RawG (tent Y h) (insideM Y h s Z p F):= mulG (subG (oneG _) (swath Y h s Z p)) t
end RawG
-- transport to sold, no need meas.
lemma brandP(h:Real.exp 1≤ Λ.x)(s i:ℕ){f:W (tent Y h)}(v:RawG (tent Y h) f)(t:Width (tent Y h) f p) :
 let N:= side Y i s; let x:= sold Y h s i f.val; ∃ T:Pane N→ℂ,(∀ U:Fields N,x U=T U.1 • 1) ∧ (∀ U:Pane N,‖T U‖ ≤ p) ∧ ∀ U:Pane N,∀ g:Mosquito N, T (gauge g U)=T U:= by
 intro N x; apply castP (terrain Y h (Y.ir i) s) (v (momentm Y i s)) (t _) ((well_for _ f).2 _)
where castP {N M:Side}{x:Mark N}(e:N=M)(v:RawX x)(t:∀ U,‖x U‖≤p)(r:covariant x): ∃ T:Pane M→ℂ,(∀ U:Fields M,ship e x U=T U.1 • 1)∧(∀ U, ‖T U‖≤p)∧ ∀ U,∀ g:Mosquito M,T (gauge g U)=T U := by
          subst M; obtain ⟨F,v⟩:=v; refine ⟨F,by exact v,fun U=>?_, fun U g=>?_⟩
          · have u:= t (U,U); rwa [v,norm_smul,norm_one,mul_one] at u
          have u:=r g (U,U); rw [v,v,twist_scalar,map_one] at u
          exact smul_left_injective ℂ (show (1:FC (Single N))≠0 from one_ne_zero) u -- check
end
section
local notation "V₁"=> Bar C (investK S.card:ℝ)
local notation "Θ"=> tickA N
local notation "Πx"=> modesIn N (region S N)
variable {V:Calibration}{f:W V}{Z:Paint}(hp:Auth V S f Z)
variable {P M D:Op (Single N)}(T:Fable P (tickA N))(G:Currency (tickA N) P 0 p y u' C M D)(h₀:0≤C)
variable (hC:forall U:Pane N,Art (Bar C (investK S.card:ℝ)) (tickA N) (modesIn N (region S N)) false (Z N U) H)
variable (Fu:Pane N→ℂ)(p₁:∀ U,∀ g:Mosquito N, Fu (gauge g U)=Fu U)(k₁:∀ U,‖Fu U‖ ≤ 1)
variable (v₁:0< r)(e₁:‖ζ‖≤ r)(b₀:∀ U:Pane N,fieldR (region S N) ξ U→ Art (Bar C (investK S.card:ℝ)) (tickA N) (modesIn N (region S N)) false (Z N U-Z N 1) r)
include T
lemma volt_one :Volt (tickA N) P 1=1:=by unfold Volt; rw [act_one,div_self (Fock.Relief.vision T.tender (mantleP T.tender.hedge) (mantleP T.tender.carpet) 1).1]
include G h₀ hC
lemma big_chip (U:Pane N): ‖Volt Θ P (Z N U)‖ ≤ H:= chip T.tender (cost_zero (S:=region S N) (s:=(investK S.card:ℝ)) T.tender G (by apply Nat.cast_le.mpr; exact LyraBill.seatCard S N) h₀) (hC U)
local notation "Z₀"=> Volt (tickA N) P (Z N 1)
lemma stencil(U:Pane N): Art V₁ Θ Πx false (Z N U-Z₀ • 1) (H+H):=by
 let W:= big_chip T G h₀ hC 1; let W' : Art V₁ Θ Πx false (-Z₀ • (1:FC (Single N))) (‖-Z₀‖*1):= Art.scale (-Z₀) Art.lone; have h:‖-Z₀‖*1 ≤ H:=by simpa only [norm_neg,mul_one] using W
 rw [_root_.sub_eq_add_neg, ← neg_smul]; exact Art.sum (hC U) (W'.pump h)
include e₁ v₁ k₁ b₀ hp p₁
def flank :Emblem N P S.card (spreadN S) ξ C (r*(H+H)) (r^2) 0 (r*(H+H)) where
 S:=region S N
 existsS:=hp.cell.image (wrap _)
 pays:=card_image_le
 span:=spread_region N S
 X U:= (ζ*Fu U) • (Z N U-Z₀ • 1)
 colored g U:=by rw [twist_scalar,map_sub,hp.story, twist_scalar,map_one,p₁]
 stocked U:= (Art.scale _ (stencil T G h₀ hC U)).pump (by have hu:0 ≤ H:=(norm_nonneg _).trans (big_chip T G h₀ hC U); apply mul_le_mul_of_nonneg_right ?_ (by positivity); exact (norm_mul ..).trans_le ((mul_le_of_le_one_right (norm_nonneg _) (k₁ U)).trans e₁))
 rough U:= by
    rw [zero_add]; apply (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans ?_); rw [volt_scale]; exact (norm_mul ..).trans_le (mul_le_mul ((norm_mul ..).trans_le ((mul_le_of_le_one_right (norm_nonneg _) (k₁ U)).trans e₁)) (chip T.tender (cost_zero (S:=region S N) (s:=(investK S.card:ℝ)) T.tender G (by apply Nat.cast_le.mpr; exact LyraBill.seatCard S N) h₀) (stencil T G h₀ hC U)) (norm_nonneg _) v₁.le)
 soaks U E:=by
    rw [zero_add]; apply (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans ?_); rw [sq r,volt_scale,volt_subx,volt_scale,volt_one T, mul_one,← volt_subx]; exact (norm_mul ..).trans_le (mul_le_mul ((norm_mul ..).trans_le ((mul_le_of_le_one_right (norm_nonneg _) (k₁ U)).trans e₁)) (chip T.tender (cost_zero (S:=region S N) (s:=(investK S.card:ℝ)) T.tender G (by apply Nat.cast_le.mpr; exact LyraBill.seatCard S N) h₀) (b₀ U E)) (norm_nonneg _) v₁.le) -- tune
end
#print axioms flank
#print axioms brandP
end Prato
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
