import GaugeFieldConstruction.LayerQ4
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Oath Roots Riant
open Oath Roots Riant TableF Lenten Layout Fren
open SectorNext.Remainder.Scales Stockpile
open CoeffArc
open Scree.Ing Scree.Ing.Iona Scree.Ing.Grotto Lattice.Corona.Hive Scree.Ing.Rio
variable (R:Patch) (V:ℝ)(k:ℕ)
local notation "C0"=>sizeK R.L 0
local notation "C1"=>sizeK R.L 1
local notation "Dq"=>sizeK R.L
private lemma cubeCt_R : sizeK R.L 0 fun i=>cubeCt (radiusB i) :=by
 have ht:=sizeK.Bcash R.L; change C0 _; unfold cubeCt; simp_rw[Nat.cast_add,Nat.cast_one]; exact ((ht.accrue ht|>.accrue (sizeK.mild R.L 1)).powC 4) -- tune
lemma age_η : let w(x):=Flow4 k (radiusB x); let p(x):=Eta4 k (radiusB x); sizeK R.L 0 w ∧ sizeK R.L 0 (fun x=>(p x)⁻¹)∧ sizeK R.L 0 fun x=> Cube_M (radiusB x):=by
 intro w p; have hz:= cubeCt_R R; have he: sizeK R.L 0 w:=by
    unfold w Flow4 Lattice.Corona.Hive.yardZ yard_M; push_cast; exact (((((((sizeK.Bcash R.L).accrue (sizeK.mild R.L 1)).scale _ |>.scale _).accrue (sizeK.mild R.L 9)).scale _).powC 4).tint (sizeK.mild R.L _))
 refine ⟨he,?_,?_⟩
 · unfold p Eta4; simp_rw [inv_div,div_eq_mul_inv]; exact (((he.tint hz).accrue (sizeK.mild R.L _)).tint (sizeK.mild R.L _)) -- ambiguity. 
 simp_rw[Cube_M, div_eq_mul_inv]; exact hz.tint (sizeK.mild R.L _)
-- General press clock ℓ(X) small: coefs O(q times ConstPoly) and need control gray.Price. choose ΩScale = Z+ΛF +2Z+2ℓ...solve Ψ includes ℓ Ω. set S:=4*(Z+ℓ Φ) constant. boot eventually.P.R.Pl.Pl.
abbrev Speedy (Z ℓ:ℝ→ℝ)(k:ℕ)(x:ℝ):ℝ:= 4*(Z x+ℓ x*Flow4 k (radiusB x)) -- use Journey
variable {Z ℓ:ℝ→ℝ}
lemma BootChrono (d:sizeK R.L 1 Z)(v:sizeK R.L 1 ℓ) (g:∀ᶠ x in atTop,0≤Z x∧0≤ℓ x): sizeK R.L 1 (Speedy Z ℓ k)∧∀ᶠ x in atTop, Boot4 (radiusB x) (Speedy Z ℓ k x) (Eta4 k (radiusB x)) (ℓ x) (Z x) (Flow4 k (radiusB x)):=by
 obtain ⟨f,e,K⟩:= age_η R k
 have hp: C1 (Speedy Z ℓ k):=(d.accrue (v.tint f)).scale _; have hx:= (K.tint hp).spine.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1)); have ht:= (((v.tint (sizeK.mild R.L 4)).tint e)).spine.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1))
 refine ⟨hp,?_⟩; filter_upwards [hx,ht,g] with i h t g
 let R':= Speedy Z ℓ k i; let Y:=Z i; let F:= Flow4 k (radiusB i); let L:=ℓ i; let p:=Cube_M (radiusB i)*R'; let A:=advanceC (ℓ i) (Eta4 k (radiusB i)); have H:0≤F:=by unfold F Flow4 Lattice.Corona.Hive.yardZ; positivity
 have J:0≤ R':=mul_nonneg (by norm_num) (add_nonneg g.1 (mul_nonneg g.2 H))
 change p ≤ 1 at h; change A≤ 1 at t
 refine ⟨g.2, h,J,t,?_⟩
 have U': stolon (radiusB i) R' (Eta4 k (radiusB i)) (ℓ i) ≤ L*3:=by
    apply mul_le_mul_of_nonneg_left _ g.2; change 2*p +A≤3; linarith
 apply (le_trans (add_le_add_right (add_le_add (mul_le_of_le_one_left g.1 t) (mul_le_mul_of_nonneg_right U' H)) (Y+L*F)))
 change Y + L*F +(Y+L*3*F)≤4*(Y+L*F); nlinarith only[g.1,show Y=Z i from rfl]
abbrev booty4 (p k:ℕ)(d:ℝ):= reserveT p 6 k ζd * d
abbrev WhiteC (P:ℝ→ℝ)(k:ℕ)(x:ℝ):= P x*Flow4 k (radiusB x)
abbrev GrayC (Z ℓ:ℝ→ℝ)(k:ℕ)(x:ℝ):= advanceC (ℓ x) (Eta4 k (radiusB x)) *Z x + stolon (radiusB x) (Speedy Z ℓ k x) (Eta4 k (radiusB x)) (ℓ x) * Flow4 k (radiusB x)
lemma ΨAge (a:sizeK R.L 1 Z)(e:sizeK R.L 1 ℓ) (g:∀ᶠ x in atTop,0≤Z x∧0≤ℓ x) {l j:ℕ}(p:sizeK R.L l Z)(q:sizeK R.L j ℓ) (w:l≤ j) : sizeK R.L (l+j) (GrayC Z ℓ k) :=by
 have b:= (BootChrono R k a e g).1; obtain ⟨f,u,H⟩:=age_η R k
 have d:Dq j (fun i=> advanceC (ℓ i) (Eta4 k (radiusB i))):= ((q.tint (sizeK.mild R.L 4)).tint u);
 have e: Dq l (Speedy Z ℓ k):= (p.accrue ((q.low w).tint f)).scale _
 have K:= (q.tint (((H.tint e)|>.scale 2)|>.accrue (d.low (by exact Nat.zero_add _ |>.symm ▸ w)))).tint f
 rw [add_comm]; apply (d.tint p).accrue; simpa only [Nat.zero_add,Nat.add_zero,stolon] using K -- tune add lemma width
lemma βearn (l p:ℕ) {A:ℝ→ℝ}(h:sizeK R.L l A) : sizeK R.L l fun i=>booty4 p (radiusB i) (A i):= by
 simpa only [Nat.zero_add] using ((Nor.vale_u p 6 ζd).creditK R.L).tint h
abbrev olderM (R:Patch)(x:ℝ)(V:ℝ):= 2 * (chi_f 6 * (V*QLife R x))
lemma Age4γ (w:0<V)(A P:ℝ)(a:0<A)(b:0<P):let Z:=fun x=>olderM R x V; let ℓ:= ounce4 ∘ radiusB; let β:= fun i=> WhiteC ℓ k i + GrayC Z ℓ k i; ∀ᶠ x in atTop, Boot4 (radiusB x) (Speedy Z ℓ k x) (Eta4 k (radiusB x)) (ℓ x) (Z x) (Flow4 k (radiusB x)) ∧ booty4 3 (radiusB x) (β x) ≤ A*QLife R x ∧ booty4 2 (radiusB x) (GrayC Z ℓ k x) ≤ P*QLife R x:=by
 intro Z ℓ β; have hV:Dq 2 (QLife R):= (sizeK.main R.L).square 2
 have pZ:Dq 2 Z:=(((hV.scale V).scale _).scale _); have pℓ:Dq 3 ℓ:= (wing_x0 (L:=R.L) (a:=1) zero_lt_one 3).scale _
 have v:∀ᶠ x in atTop,0≤Z x∧0≤ℓ x:=by
    filter_upwards with x; have u:0≤QLife R x:=sq_nonneg _; exact ⟨mul_nonneg zero_le_two (mul_nonneg (spicy_f _) (mul_nonneg w.le u)),mul_nonneg (by norm_num) (Real.exp_pos _).le⟩
 have m:= BootChrono R k (pZ.low (k:=1) (by norm_num)) (pℓ.low (k:=1) (by norm_num)) v
 have he:Dq 3 (GrayC Z ℓ k):= (ΨAge R k (pZ.low (by norm_num)) (pℓ.low (by norm_num)) v pZ pℓ (by norm_num)).low (by norm_num)
 have hp:Dq 3 β:= (pℓ.tint (age_η R k).1 |>.accrue he)
 exact m.2.and ((age_w R A _ (βearn R _ _ hp) a).and (age_w R P _ (βearn R _ _ he) b))
#print axioms Age4γ
end Focus
end Pitching
end YM.CF.Py.Rate
end
