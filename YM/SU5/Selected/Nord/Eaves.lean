import YM.SU5.Selected.Nord.Regime
set_option autoImplicit false
set_option maxHeartbeats 1200000
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x z : ℝ} {D C R0 : ℝ → ℝ} (h' : ℝ) {delay : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {N0 B1 : ℕ} {q : Chi}
variable {n T' : ℕ → ℕ} {P : Prescription R B}
namespace LocalLimit
open Preparation Chene Pitching Focus
variable {Λ:Preparation}{Z:(s:Side)→ Scree.Loom s → Prop} (Y: Course Λ Z)(Q:Scooped Λ)
local notation "Ξ" i:max s:max => age Y i s
local notation "M" i:max k:max =>RootBook Y i k
local notation "Z'" i:max => Y.voyage i

def milli (i k s:ℕ):= compensated Λ.U (RootBook Y i k s) ((Y.voyage i).CapeT s)
lemma measurableFee (i k s:ℕ)(p:(Y.voyage i).kick≤k)(u:s≤Y.uv k): Real.exp (-Y.charge s*sites (age Y i s))≤‖milli Y i k s‖:= (Y.each_level i k s p u).lower
lemma log_milli(i k s:ℕ)(p:(Y.voyage i).kick≤k)(t:s≤ Y.uv k): Real.log ‖milli Y i k s‖= Real.log ‖partitionZ ((M i k) (Y.uv k)) Λ.U ((Y.voyage i).CapeT (Y.uv k))‖- (RootBook Y i k s).v.re:=by
 let x:= RootBook Y i k s; let X:=partitionZ x Λ.U ((Y.voyage i).CapeT s); let J:= (Z' i).X (Y.uv k); have he:X≠0:=(Y.each_level i k s p t).valid
 change Real.log ‖Complex.exp _* X‖=_
 rw [norm_mul,Real.log_mul (by exact norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)) (norm_ne_zero_iff.mpr he),Complex.norm_exp, Complex.neg_re, Real.log_exp]; unfold X x; rw [show partitionZ _ _ _= _ from (J.balance s t)]; abel
lemma twoVolume (i s:ℕ): 2*sites (age Y i s) ≤ sites (age Y i (s+1)):=by
 let V:= (Λ.R.L.val:ℝ); let G:= sites (age Y i s); have hp:2 ≤V:= by unfold V; exact_mod_cast (by have hc:=Λ.V.tallX; omega : 2 ≤ Λ.R.L.val)
 have hx: V^4*G=sites (age Y i (s+1)):=by unfold V G sites age Ctor cell CSide More; rw [mesh_succ]; push_cast; ring
 exact hx ▸ mul_le_mul_of_nonneg_right (hp.trans (le_self_pow₀ (by linarith: 1 ≤ V) (by decide: (4:ℕ)≠0))) (zero_le_one.trans (sites_pos _)) -- tune
include Q
/-- Uniform *high-scale* (native) denominator bound on THIS pressure election. Need still settle upper absolute and applications. -/
theorem signsF (ε:ℝ)(e:0<ε) : ∀ᶠ s:ℕ in atTop,∀ i k,(Y.voyage i).kick≤k→ s≤Y.uv k → Real.exp (marks Y i k s- ε*sites (age Y i s)) ≤ ‖milli Y i k s‖:=by
 let r:= ε/4; have h:0<r:= by unfold r; positivity; -- indentation
 obtain ⟨C,t⟩:= marks_rent Y; obtain ⟨s,S⟩:= eventually_atTop.mp ((futureCost Y Q r h).and t); let F_ (i s':ℕ) := sites (age Y i s'); let a:=max 0 (C+Y.charge s); let u(i k s):= Real.log ‖milli Y i k s‖
 let d(j:ℕ):= a*((1/2:ℝ)^j); have ha(j:ℕ):0≤ d j:= mul_nonneg (le_max_left ..) (by positivity)
 have H(i k j)(p:(Y.voyage i).kick≤k)(v:s+j≤Y.uv k): marks Y i k (s+j)-(d j+2*r)*F_ i (s+j)≤ u i k (s+j):=by
    induction j with
    | zero=> let U:= Y.charge s; have hx:=Real.log_le_log (Real.exp_pos _) (measurableFee Y i k s p v); rw [Real.log_exp] at hx; let V:=F_ i s; have hh:0≤V:= zero_le_one.trans (sites_pos _); have hg:marks Y i k s ≤ C*V:= (S s le_rfl).2 i k v
             have he: -U* V≤ u i k s:=hx; have hk:C+U≤ a:= le_max_right ..; change marks Y i k s- (d 0+2*r)*V≤ u i k s; rw [show d 0=a from by simp [d]]; nlinarith [mul_le_mul_of_nonneg_right hk hh]
    | succ j ih=>
       have hb:s+j+1 = s+(j+1) := rfl; let j':=s+j; let v0:= F_ i j'; let v':=F_ i (j'+1); have hx: s+j<Y.uv k:= v; have hu:= ih hx.le
       have hr:= (S (s+j) (Nat.le_add_right ..)).1 i k hx
       let t:= (RootBook Y i k j').v.re-(RootBook Y i k (j'+1)).v.re; have he: u i k (s+(j+1))=u i k (s+j)+t:=by unfold u; rw [log_milli Y i k (s+(j+1)) p v,log_milli _ _ _ _ p hx.le]; unfold t j'; rw [← hb]; abel
       let b:=marks Y i k j'; let B:=marks Y i k (j'+1); have hv: - (r*v') ≤ t - (B-b) := (abs_le.mp hr).1
       have hw: v0≤ v'/2:=by have ht: 2*v0≤v':=twoVolume Y i j'; linarith
       rw [he]; change b-(d j +2*r)*v0 ≤ _ at hu; change B-(d (j+1)+2*r)*v' ≤ _; rw [show d (j+1)=d j/2 from ?_]; swap; · unfold d; rw [pow_succ]; ring
       linarith only [hv,hu,mul_le_mul_of_nonneg_left hw (show 0≤d j+2*r by linarith [ha j])]
 have hp : Tendsto d atTop (𝓝 0):=by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)).const_mul a
 obtain ⟨n,x⟩:= eventually_atTop.mp (hp.eventually (ge_mem_nhds h))
 filter_upwards [eventually_ge_atTop (s+n)] with j e i k p t'
 let t:= j - s; have hf:j=s+t:=by unfold t; omega
 have hz:=x t (by unfold t; omega); have hl:= two_mul r
 have ht:d t+2*r ≤ ε:=by dsimp only [r] at *; linarith -- optimize 
 rw [hf]; have g:s+t ≤ _:= hf ▸ t'; let V:=F_ i (s+t)
 obtain he: 0 < ‖milli Y i k (s+t)‖:= lt_of_lt_of_le (Real.exp_pos _) (measurableFee Y i k _ p g); rw [←Real.exp_log he,Real.exp_le_exp]; exact le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_right ht (by change 0 ≤ V; exact zero_le_one.trans (sites_pos _))) _) (H i k t p g)
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.signsF
