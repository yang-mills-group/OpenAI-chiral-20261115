import YM.SU5.Fineness.Stitch
import Refrain.Bouquet
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
/-!
# Exact headroom asymptotic, all periods on the signed law.
 Not absolute values on the integrands. Comes from transporting the weights/norms of ZERO
 insertions; this still only pays downstream with further *matching upper* bounds.
-/
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
local notation "ℒ"=> Λ.R.L
local notation "v'" i:max s:max=> sites (Λ.Ctor (Y.ir i) s)
local notation "X₀" i:max k:max=> (Y.voyage i).X (Y.uv k)
private lemma bankStart (s:ℕ): ∃ x≥ (0:ℝ),∀ i k:ℕ, (Y.voyage i).kick ≤ k → s≤ Y.uv k → VLine Y s i k x:=by
 obtain ⟨w,h,T⟩:= entry_distant (by norm_num:(0:ℝ)<1/2) Λ.chart (by rw [Λ.kJ]; decide) Λ.W; let W:= expense Λ.C Λ.R Λ.x Y.τ s
 refine ⟨W+w, add_nonneg (posExpense Y.τ Y.revenue _) h.le,fun i k p e=>?_⟩
 let Z:= X₀ i k; let F:= Z.gram s; let V0:= v' i s; let hx:= Z.pull.sift s e; --- inspect
 have hl:1/2≤ F.beta:=le_trans (div_le_div_of_nonneg_right (Y.oneP.trans (Vale.crown ..)) (by norm_num)) hx.1
 let hu:=Λ.J.gran.trans ((Y.voyage i).ownership s).size
 have hf:sod Y k s i≤w*V0:= T _ hu F.J _ hl _
 exact le_trans (Real.exp_monotone (show sod Y k s i- (W+w)*V0≤ - W*V0 by linarith only [hf])) (level_secured _ Z Y.τ Y.revenue ((Y.voyage i).lower k p) s e)
private lemma line_cheap (s i k:ℕ){x y:ℝ}(p:x≤y)(h:VLine Y s i k x) : VLine Y s i k y:= h.trans' (Real.exp_monotone (sub_le_sub_left (mul_le_mul_of_nonneg_right p (zero_le_one.trans (sites_pos _))) _))
local notation "R" => ( (Λ.R.L.val:ℝ)^4)
open CF.Refrain BProof
abbrev GeometrySharp (P:Preparation):Prop:= CorridorSharp P.J Chi.canonical P.h P.P P.N0
local notation "X" n:max=> hat Λ.R.L Λ.x n
include Λ
lemma chain_sharp (q:GeometrySharp Λ):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → |(((X₀ i k).gram s).v.re-(( (X₀ i k).gram (s+1)).v).re)-(sod Y k (s+1) i-sod Y k s i)| ≤ 7*shrift ℒ (Vale.hat ℒ Λ.x s)*sites (Λ.Ctor (Y.ir i) s):=by
 filter_upwards [Branch.brakeSharp (α:=0) (x:=Λ.x) q Λ.H Λ.chart] with s hx i k hs; let T:=Y.voyage i; let Z:= X₀ i k
 obtain ⟨qT,b,v,h,H⟩:= T.paths (Y.uv k); unfold sod; dsimp only; change Z.gram=_ at h; change |((Z.gram s).v.re-(Z.gram (s+1)).v.re)-(entryFin _ _ _ (Z.gram (s+1)).J (Z.gram (s+1)).beta-entryFin _ _ _ (Z.gram s).J (Z.gram s).beta)|≤ _
 rw [h]; exact hx _ _ _ b qT v (Λ.W.pose _ _) hs
private lemma chainR_sharp (q:GeometrySharp Λ):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → ∀ r,VLine Y s i k r → VLine Y (s+1) i k ((r+7*shrift ℒ (Vale.hat ℒ Λ.x s))/R):=by
 have he:R>0:=pow_pos (by positivity) _
 filter_upwards [chain_sharp Y q] with s v i k u r hr; let ε:=7*shrift ℒ (X s); let Z:= X₀ i k; let Xw:=Z.gram; let d:= ‖partitionZ (Xw s) Λ.U ((Y.voyage i).CapeT s)‖; let V:= v' i s; let a:=sod Y k s i; let b:=sod Y k (s+1) i; let A:= (Xw s).v.re; let B:= (Xw (s+1)).v.re
 have hx:b-a - ε*V ≤ A-B:=by
    have he:|A-B-(b-a)|≤ ε*V:= v i k u; linarith only [(abs_le.mp he).1]
 simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hr ⊢
 change Real.exp (a-r*V) ≤ Real.exp (-A)*d at hr
 rw [(Z.balance (s+1) u).trans (Z.balance s u.le).symm, expansionStep]
 let X' := b-a- ε*V
 change Real.exp (b-(r+ε)/R*(R*V)) ≤ Real.exp (-B)*d
 calc _= Real.exp X'*Real.exp (a-r*V) := by rw [← Real.exp_add]; congr 1; unfold X'; field
      _ ≤ _:= (mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le).trans (by rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; unfold X'; linarith only [hx])

omit Λ
lemma speed_coupon (Q:Preparation):∀ᶠ s:ℕ in atTop, shrift Q.R.L (Vale.hat Q.R.L Q.x s) ≤ 2*shrift Q.R.L (Vale.hat Q.R.L Q.x (s+1)):=by
 let v:= Q.R.L; let c:=Vale.billX v; let p (i:ℕ):=y G5 v (Vale.hat v Q.x i)
 have he:Tendsto p atTop atTop:= (year G5 v).comp (stage_slope Q.V Q.x)
 have hm:0<c:=mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1 < Q.R.L.val by have ht:= Q.V.tallX; omega)))
 filter_upwards [he.eventually_gt_atTop c] with s hs
 let a:=p s; let b:=p (s+1); have ha:0<a:=hm.trans hs
 have h0:b=a+c:=by unfold a b p y betaF c Vale.hat; push_cast; ring
 have hb:0<b:=by rw [h0]; positivity
 have hz:1≤ b/a:= (one_le_div ha).mpr (by linarith only [h0,hm]); have ht:b/a≤2:=(div_le_iff₀ ha).mpr (by linarith only [h0,hs])
 change BProof.coin a (-1/4) 0 0≤ 2*BProof.coin b (-1/4) 0 0
 unfold BProof.coin; simp only [mul_zero,add_zero]; rw [← div_le_iff₀ (Real.exp_pos _), ←Real.exp_sub, show Real.log a*(-1/4)-Real.log b*(-1/4)=(Real.log b-Real.log a)*(1/4) from by ring,←Real.log_div hb.ne' ha.ne']
 exact (Real.exp_monotone (show Real.log (b/a)*(1/4) ≤ Real.log (b/a) by linarith only [Real.log_nonneg hz])).trans ((Real.exp_log (div_pos hb ha)).le.trans ht)
lemma rising_height (P:Preparation) : 4 ≤ (P.R.L.val:ℝ)^4:=by
 have hp : 2 ≤ (P.R.L.val:ℝ):= by exact_mod_cast (show 2≤ P.R.L.val from le_trans (by decide) P.V.tallX)
 nlinarith only [pow_le_pow_left₀ (by norm_num) hp 4]

include Λ
lemma benchmarksSharp (q:GeometrySharp Λ):∃ C> (0:ℝ),∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k→ s≤Y.uv k→VLine Y s i k (C*shrift ℒ (X s)):=by
 obtain ⟨v,w⟩:= eventually_atTop.mp ((chainR_sharp Y q).and (speed_coupon Λ))
 let f(n:ℕ):= shrift ℒ (X n)
 have hf(i:ℕ):0<f i:=BProof.coin_pos ..
 obtain ⟨D,hD,pD⟩:=bankStart Y v
 let C:=7+D/(f v); have hC:7≤C:= le_add_of_nonneg_right (div_nonneg hD (hf v).le); have hc:0<C:=by linarith only [hC]
 refine ⟨C,hc,(eventually_ge_atTop v).mono (fun s hs i k hi hk=> ?_)⟩
 change VLine Y s i k (C*f s)
 induction s,hs using Nat.le_induction with
 | base=> apply line_cheap Y _ _ _ _ (pD _ _ hi hk); unfold C; have h0:=hf v; field_simp; nlinarith only [hD,h0] -- division simpl
 | succ s hs IH=>
    apply line_cheap Y _ _ _ _ ((w s hs).1 i k hk (C*f s) (IH (le_of_lt hk)))
    rw [div_le_iff₀ (pow_pos (by positivity) _)]; have he:f s≤2*f (s+1):=(w s hs).2
    change C*f s+7*f s≤C*f _*R; nlinarith only [mul_le_mul_of_nonneg_left he hc.le, mul_le_mul_of_nonneg_left (rising_height Λ) (show 0≤C*f (s+1) from mul_nonneg hc.le (hf _).le), he, mul_le_mul_of_nonneg_right hC (hf s).le]
end LocalLimit
end Rate
end YM.CF.Py

