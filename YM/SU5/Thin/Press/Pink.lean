import YM.SU5.Thin.Press.Brumal
set_option autoImplicit false
set_option maxHeartbeats 800000
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
private lemma bankFrost (s:ℕ): ∃ x≥ (0:ℝ),∀ i k:ℕ, (Y.voyage i).kick ≤ k → s≤ Y.uv k → VLine Y s i k x:=by
 obtain ⟨w,h,T⟩:= entry_distant (by norm_num:(0:ℝ)<1/2) Λ.chart (by rw [Λ.kJ]; decide) Λ.W; let W:= expense Λ.C Λ.R Λ.x Y.τ s
 refine ⟨W+w, add_nonneg (posExpense Y.τ Y.revenue _) h.le,fun i k p e=>?_⟩
 let Z:= X₀ i k; let F:= Z.gram s; let V0:= v' i s; let hx:= Z.pull.sift s e; --- inspect
 have hl:1/2≤ F.beta:=le_trans (div_le_div_of_nonneg_right (Y.oneP.trans (Vale.crown ..)) (by norm_num)) hx.1
 let hu:=Λ.J.gran.trans ((Y.voyage i).ownership s).size
 have hf:sod Y k s i≤w*V0:= T _ hu F.J _ hl _
 exact le_trans (Real.exp_monotone (show sod Y k s i- (W+w)*V0≤ - W*V0 by linarith only [hf])) (level_secured _ Z Y.τ Y.revenue ((Y.voyage i).lower k p) s e)
private lemma line_frugal (s i k:ℕ){x y:ℝ}(p:x≤y)(h:VLine Y s i k x) : VLine Y s i k y:= h.trans' (Real.exp_monotone (sub_le_sub_left (mul_le_mul_of_nonneg_right p (zero_le_one.trans (sites_pos _))) _))
local notation "R" => ( (Λ.R.L.val:ℝ)^4)
abbrev pinkRay (Λ:Preparation)(s:ℕ):ℝ:= (hat Λ.R.L Λ.x s)^(-(1/4:ℝ))
include Λ
lemma chain_power (ε:ℝ)(p:ε>0)(q:Cistern Λ.J Chi.canonical Λ.h Λ.P Λ.N0):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → |(((X₀ i k).gram s).v.re-(( (X₀ i k).gram (s+1)).v).re)-(sod Y k (s+1) i-sod Y k s i)| ≤ (ε*pinkRay Λ s)*sites (Λ.Ctor (Y.ir i) s):=by
 filter_upwards [Branch.brake_power (α:=0) (x:=Λ.x) q Λ.H Λ.chart ε p] with s hx i k hs; let T:=Y.voyage i; let Z:= X₀ i k
 obtain ⟨qT,b,v,h,H⟩:= T.paths (Y.uv k); unfold sod; dsimp only; change Z.gram=_ at h; change |((Z.gram s).v.re-(Z.gram (s+1)).v.re)-(entryFin _ _ _ (Z.gram (s+1)).J (Z.gram (s+1)).beta-entryFin _ _ _ (Z.gram s).J (Z.gram s).beta)|≤ _
 rw [h]; exact hx _ _ _ b qT v (Λ.W.pose _ _) hs
private lemma chainV (ε:ℝ)(p:ε>0)(q:Cistern Λ.J Chi.canonical Λ.h Λ.P Λ.N0):∀ᶠ s in atTop,∀ i k:ℕ,s<Y.uv k → ∀ r,VLine Y s i k r → VLine Y (s+1) i k ((r+ε*pinkRay Λ s)/R):=by
 have he:R>0:=pow_pos (by positivity) _
 filter_upwards [chain_power Y ε p q] with s v i k u r hr; let Z:= X₀ i k; let X:=Z.gram; let d:= ‖partitionZ (X s) Λ.U ((Y.voyage i).CapeT s)‖; let V:= v' i s; let a:=sod Y k s i; let b:=sod Y k (s+1) i; let A:= (X s).v.re; let B:= (X (s+1)).v.re
 have hx:b-a - (ε*pinkRay Λ s)*V ≤ A-B:=by
    have he:|A-B-(b-a)|≤ (ε*pinkRay Λ s)*V:= v i k u; linarith only [(abs_le.mp he).1]
 simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hr ⊢
 change Real.exp (a-r*V) ≤ Real.exp (-A)*d at hr
 rw [(Z.balance (s+1) u).trans (Z.balance s u.le).symm, expansionStep]
 let X' := b-a- (ε*pinkRay Λ s)*V
 change Real.exp (b-(r+ε*pinkRay Λ s)/R*(R*V)) ≤ Real.exp (-B)*d
 calc _= Real.exp X'*Real.exp (a-r*V) := by rw [← Real.exp_add]; congr 1; unfold X'; field
      _ ≤ _:= (mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le).trans (by rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; unfold X'; linarith only [hx])

include Y
private lemma pink_a (s:ℕ): 1≤hat ℒ Λ.x s:= Y.oneP.trans (Vale.crown ..)
lemma pink_hub (s:ℕ):0<pinkRay Λ s:= Real.rpow_pos_of_pos (zero_lt_one.trans_le (pink_a Y s)) _
omit Y in
private lemma grow_leap : 4 ≤ R:= by
    have hp : 2 ≤ (Λ.R.L.val:ℝ):= by exact_mod_cast (show 2≤ Λ.R.L.val from le_trans (by decide) Λ.V.tallX)
    exact (pow_le_pow_left₀ zero_le_two hp 4).trans' (by norm_num)
lemma pinkSlope : ∀ᶠ s in atTop,pinkRay Λ s≤ 2*pinkRay Λ (s+1):=by
 let r:=ℒ; filter_upwards [(stage_slope Λ.V Λ.x).eventually (Sleigh.fitYear r SU.group)] with s hs
 let X:=hat ℒ Λ.x s; let Y':=hat ℒ Λ.x (s+1); have hx: Y'≤2*X:= (hat_succ ℒ Λ.x s).le.trans (show Scales.y SU.group ℒ X≤2*X from hs.2); have hp:0<X:=zero_lt_one.trans_le (pink_a Y s); have hy:0<Y':= zero_lt_one.trans_le (pink_a Y (s+1))
 unfold pinkRay; rw [Real.rpow_neg hp.le,Real.rpow_neg hy.le]; let t:ℝ:=1/4; have ht:0<t:= by unfold t; norm_num; -- indent
 change (X^t)⁻¹ ≤ 2*(Y'^t)⁻¹ -- inspect or field_simp
 -- tune
 have he:Y'^t ≤ 2*X^t:= (Real.rpow_le_rpow hy.le hx ht.le).trans (by rw [Real.mul_rpow (by norm_num: (0:ℝ) ≤ 2) hp.le]; apply mul_le_mul_of_nonneg_right _ (by positivity); exact (Real.rpow_le_rpow_of_exponent_le one_le_two (by unfold t; norm_num : t≤1)).trans (by rw [Real.rpow_one]))
 field_simp; linarith only [he]
theorem benchmarks_power (ε:ℝ)(p:0<ε)(q:Cistern Λ.J Chi.canonical Λ.h Λ.P Λ.N0):∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k → s≤Y.uv k → VLine Y s i k (ε*pinkRay Λ s):=by
 let t:=ε/2; have ht:0<t:= half_pos p
 obtain ⟨b,hb⟩:= eventually_atTop.mp ((chainV Y t ht q).and (pinkSlope Y)); obtain ⟨C,pC,H⟩:= bankFrost Y b
 have hu:=grow_leap (Λ:=Λ); have h:R>1:=by linarith only [hu]
 let w:=pinkRay Λ
 let r(n:ℕ):= t*w (b+n)+ C/R^n
 have he(n i k:ℕ)(v:(Y.voyage i).kick≤k)(p:b+n≤Y.uv k): VLine Y (b+n) i k (r n):=by
    induction n with
    | zero => simp only [Nat.add_zero] at p ⊢; unfold r; rw [pow_zero,div_one]; exact line_frugal Y _ _ _ (le_add_of_nonneg_left (mul_nonneg ht.le (pink_hub Y _).le)) (H _ _ v p)
    | succ n ih=>
       rw [← Nat.add_assoc] at p ⊢; have hz:=hb _ (Nat.le_add_right b n); refine line_frugal Y _ _ _ ?_ (hz.1 i k p (r n) (ih (le_of_lt p)))
       let v₀:= w (b+n); let v₁:= w (b+n+1)
       have hv₁: v₀ ≤ 2*v₁:=hz.2; change ( (t*v₀+C/R^n)+t*v₀)/R ≤ _; have hy:r (n+1)=t*v₁+C/(R^n*R):=by unfold r v₁; rw [pow_succ]; rfl
       rw [hy,div_le_iff₀ (zero_lt_one.trans h),add_mul, show C/(R^n*R)*R=C/R^n from ?_]; nlinarith only [mul_le_mul_of_nonneg_left hv₁ ht.le,mul_le_mul_of_nonneg_left hu (mul_pos ht (pink_hub Y (b+n+1))).le]; field -- include bounding R
 let g(i:ℕ):=hat ℒ Λ.x (b+i)
 have hx:Tendsto (fun n:ℕ=> C*(g n/R^n)) atTop (𝓝 0):=by simpa only [mul_zero] using (head_geo h ℒ Λ.x b).const_mul C
 have hv:∀ᶠ i in atTop,C/R^i ≤ t*w (b+i):=by
    filter_upwards [hx.eventually (ge_mem_nhds ht)] with i h₀; have hp:= pink_a Y (b+i); have hg:0<g i:= zero_lt_one.trans_le hp
    apply le_trans _ (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp (by norm_num : -(1:ℝ)≤-(1/4:ℝ))) ht.le); change C/R^i ≤ t * (g i)^(-(1:ℝ)); rw [Real.rpow_neg_one]; change C*(g i/R^i) ≤_ at h₀; field_simp at h₀ ⊢; linarith only [h₀]
 obtain ⟨i,u⟩:= eventually_atTop.mp hv
 filter_upwards [eventually_ge_atTop (b+i)] with n p' l k v s
 let j:=n-b; have t':n=b+j:=by unfold j; omega
 let B: VLine Y (b+j) l k (r j):= he j l k v (by omega)
 rw [t']; apply line_frugal Y _ _ _ _ B; unfold r; exact le_trans (add_le_add le_rfl (u j (by unfold j; omega))) (by unfold t w; linarith)
end LocalLimit
end Rate
end YM.CF.Py
