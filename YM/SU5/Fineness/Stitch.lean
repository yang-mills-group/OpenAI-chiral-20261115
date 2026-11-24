import YM.SU5.Fineness.Driving
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
def sod (k:ℕ)(s:ℕ)(i:ℕ):= let F:= ((Y.voyage i).X (Y.uv k)).gram s;
                            entryFin Λ.V (Y.uv k-s) (Λ.Ctor (Y.ir i) s) F.J F.beta
local notation "ℒ"=> Λ.R.L
local notation "v'" i:max s:max=> sites (Λ.Ctor (Y.ir i) s)
local notation "X₀" i:max k:max=> (Y.voyage i).X (Y.uv k)
def VLine (Y:Course Λ (VolumeCape.Dream.Nimbus l))(s i k:ℕ)(x:ℝ):Prop:= Real.exp (sod Y k s i - x*sites (Λ.Ctor (Y.ir i) s)) ≤ ‖compensated Λ.U (((Y.voyage i).X (Y.uv k)).gram s) ((Y.voyage i).CapeT s)‖
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
abbrev Geometry (P:Preparation):Prop:= Corridor P.J Chi.canonical P.h P.P P.N0
include Λ
lemma chain_abs (ε:ℝ)(p:ε>0)(q:Geometry Λ):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → |(((X₀ i k).gram s).v.re-(( (X₀ i k).gram (s+1)).v).re)-(sod Y k (s+1) i-sod Y k s i)| ≤ ε*sites (Λ.Ctor (Y.ir i) s):=by
 filter_upwards [Branch.brakeYears (α:=0) (x:=Λ.x) q Λ.H Λ.chart ε p] with s hx i k hs; let T:=Y.voyage i; let Z:= X₀ i k
 obtain ⟨qT,b,v,h,H⟩:= T.paths (Y.uv k); unfold sod; dsimp only; change Z.gram=_ at h; change |((Z.gram s).v.re-(Z.gram (s+1)).v.re)-(entryFin _ _ _ (Z.gram (s+1)).J (Z.gram (s+1)).beta-entryFin _ _ _ (Z.gram s).J (Z.gram s).beta)|≤ _
 rw [h]; exact hx _ _ _ b qT v (Λ.W.pose _ _) hs
private lemma chainR (ε:ℝ)(p:ε>0)(q:Geometry Λ):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → ∀ r,VLine Y s i k r → VLine Y (s+1) i k ((r+ε)/R):=by
 have he:R>0:=pow_pos (by positivity) _
 filter_upwards [chain_abs Y ε p q] with s v i k u r hr; let Z:= X₀ i k; let X:=Z.gram; let d:= ‖partitionZ (X s) Λ.U ((Y.voyage i).CapeT s)‖; let V:= v' i s; let a:=sod Y k s i; let b:=sod Y k (s+1) i; let A:= (X s).v.re; let B:= (X (s+1)).v.re
 have hx:b-a - ε*V ≤ A-B:=by
    have he:|A-B-(b-a)|≤ ε*V:= v i k u; linarith only [(abs_le.mp he).1]
 simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hr ⊢
 change Real.exp (a-r*V) ≤ Real.exp (-A)*d at hr
 rw [(Z.balance (s+1) u).trans (Z.balance s u.le).symm, expansionStep]
 let X' := b-a- ε*V
 change Real.exp (b-(r+ε)/R*(R*V)) ≤ Real.exp (-B)*d
 calc _= Real.exp X'*Real.exp (a-r*V) := by rw [← Real.exp_add]; congr 1; unfold X'; field
      _ ≤ _:= (mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le).trans (by rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; unfold X'; linarith only [hx])
private lemma grow_height : 2 ≤ R:= by
    have hp : 2 ≤ (Λ.R.L.val:ℝ):= by exact_mod_cast (show 2≤ Λ.R.L.val from le_trans (by decide) Λ.V.tallX)
    exact hp.trans (le_self_pow₀ (one_le_two.trans hp) (by decide))
theorem benchmarks (ε:ℝ)(p:0<ε)(q:Geometry Λ): ∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k → s≤Y.uv k → VLine Y s i k ε:=by
 let t:=ε/2; have ht:0<t:= half_pos p
 obtain ⟨b,hb⟩:= eventually_atTop.mp (chainR Y t ht q); obtain ⟨C,pC,H⟩:= bankStart Y b
 have hu:=grow_height (Λ:=Λ); have h:R>1:=one_lt_two.trans_le hu
 let r(n:ℕ):= t+ C/R^n; have he(n i k:ℕ)(v:(Y.voyage i).kick≤k)(p:b+n≤Y.uv k): VLine Y (b+n) i k (r n):=by
    induction n with
    | zero=> simp only [Nat.add_zero] at p ⊢; unfold r; rw [pow_zero,div_one]; exact line_cheap Y _ _ _ (le_add_of_nonneg_left ht.le) (H _ _ v p)
    | succ n ih=>
       rw [← Nat.add_assoc] at p ⊢; refine line_cheap Y _ _ _ ?_ (hb _ (Nat.le_add_right ..) i k p (r n) (ih (le_of_lt p)))
       unfold r; rw [div_le_iff₀ (zero_lt_one.trans h),add_mul, pow_succ (R) n, show C/(R^n*R)*R=C/R^n from ?_]; nlinarith only [hu,ht]; field
 have hx:Tendsto (fun n:ℕ=> C/R^n) atTop (𝓝 0):=tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt h)
 obtain ⟨i,u⟩:= eventually_atTop.mp (hx.eventually (ge_mem_nhds ht))
 filter_upwards [eventually_ge_atTop (b+i)] with n p i w v s; -- overlap i shadow
 let k:=n-b; have t':n=b+k:=by unfold k; omega; -- won't close 
 have ht': VLine Y n i w (r k):=t' ▸ he k i w v (by omega)
 apply line_cheap Y n i w ?_ ht'; unfold r; exact le_trans (add_le_add le_rfl (u k (by unfold k; omega))) (by unfold t; linarith)
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.benchmarks
