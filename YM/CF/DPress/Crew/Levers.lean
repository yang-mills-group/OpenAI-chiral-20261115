import YM.CF.DPress.Crew.Tutor
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay Glyph Nacre Docket Tutor
variable {N:Side}{P:BudgetPoint}{h W a b c t M L u e:ℝ}{T S:BeatL N}{D:Docket P}{q:ℕ}{F:Scree.Loom N}(A:BondL T S (body_Q 1) b c a e)(v:Room F P e u h q)
namespace Tutor
lemma loosen {x y h:ℝ}{p:BudgetPoint}{F:RegBudget N}(t:IncX Ione.Utrue F p h x)(v:x≤y):IncX Ione.Utrue F p h y:=by obtain ⟨u,q,w⟩:=t.weight; exact ⟨⟨u,q,fun i=>(w i).trans v⟩,t.face⟩
variable (H:Tutor P h W a b c)(uA:pureB A 1)
variable (i:ΘS t)(w:0≤t)
include uA w H
lemma starLP: IncX Utrue (v.L_Q A i.val) P h (Lc P h t):=by
 letI:Nonempty (ΘS t):= ⟨i⟩; rw [← LP v w i A]; exact (Room.rho A w).starH v.proof v.pos h v.heil i v.Hope v.hue v.tone v.r1 v.r2 v.r3' (Qzeta.faithful t A w uA) H.posA H.ny
omit uA
lemma play_w: IncX Utrue (v.W_Q A i.val) P h (Wc P h a b c t):=by
 letI:Nonempty (ΘS t):= ⟨i⟩; rw [← WF v w i A]; let Z:=Room.rho A w; exact Ione.addT _ (Z.pay_r v.proof v.pos h v.heil i v.Hope v.hue v.tone v.r1 v.r2 v.r3' H.posA H.ny H.year) (Z.pay_z v.proof v.pos h v.heil i v.Hope v.hue v.tone v.r1 v.r2 v.r3' H.posA H.ny H.year)
omit w
lemma pt_W {V:Θ}: IncX Utrue (v.W_Q A V) P h (str W P h ‖V‖):=by have hv:= H.κpc ‖V‖ (norm_nonneg _); exact loosen (play_w A v H (t:=‖V‖) ⟨V,le_refl _⟩ (norm_nonneg _)) hv
include uA
lemma pt_L {V:Θ}: IncX Utrue (v.L_Q A V) P h (Tutor.spot P h ‖V‖):=loosen (starLP A v H uA (t:=‖V‖) ⟨V,le_refl _⟩ (norm_nonneg _)) (seize _ (norm_nonneg _))
-- Bead fund estimate. scaled profiles
omit uA
abbrev φFee (P:BudgetPoint)(h a b c r:ℝ) := feeΨ P a (Cad.rent*r*b) (Cad.rent*r*c) h
abbrev ζFee (P:BudgetPoint)(h a b c r:ℝ):=|φFee P h a b c 1| * r
abbrev μρ (P:BudgetPoint)(h:ℝ)(A:BondL T S (body_Q 1) b c a e)(u:0 ≤ t):= (Room.rho A u).bead h P
abbrev Ride (P:BudgetPoint)(h a b c r:ℝ)(D:Docket P): Prop := 20 * ζFee P h a b c r ≤ D.d
lemma μρp(o:Seat N)(w:0≤ t): tallB (μρ P h A w) P.B (wu P+2) o ≤ ζFee P h a b c t:=by
 haveI:= Cad.nonzero w; have hp:= (Room.rho A w).duty h P (wu P+2) H.posA (add_nonneg Wu (by norm_num)) H.nf o; rw [←parse, mul_zero, sub_zero] at hp; refine (hp.trans_eq ?_).trans (mul_le_mul_of_nonneg_right (le_abs_self (φFee P h a b c 1)) w); unfold φFee priceN feeΨ; ring
include v w
lemma allowance (r:t≤M)(p: Ride P h a b c M D) : D.Chip (μρ P h A w):=by
 let X:ΘS t:=⟨0,by rw [norm_zero]; exact w⟩
 refine ⟨(Kernel.realPitch A v w X).dice,fun o=>?_⟩; unfold Ride at p; have hk:0≤ ζFee P h a b c M:=mul_nonneg (abs_nonneg _) (w.trans r); refine ((μρp A H o w).trans (mul_le_mul_of_nonneg_left (r) (abs_nonneg _))).trans ?_; change ζFee P h a b c M≤_; linarith
omit w
lemma generous(w:0<t)(r:t ≤ M)(p: Ride P h a b c M D) : D.Chip (Probe.μχ A h P w):=by
 let W1:= μρ P h A w.le; refine ⟨smul_nonneg (show 0≤(10:ℝ) by norm_num) (H.allowance A v w.le r p).1,fun o=>?_⟩; change tallB ((10:ℝ) • W1) P.B _ _ ≤_; rw [tall_s]; have h1:tallB W1 P.B (wu P+2) o≤ ζFee P h a b c M:= ((μρp A H o w.le).trans (mul_le_mul_of_nonneg_left (r) (abs_nonneg _))); have ht:0≤ζFee P h a b c M:=mul_nonneg (abs_nonneg _) (w.le.trans r); unfold Ride at p; linarith
end Tutor
end YM.CF.Sour.Heath
