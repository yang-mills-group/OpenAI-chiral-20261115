import YM.CF.Vp929.Phase.Teller
import YM.CF.Vp929.Stage.Forecast
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
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
namespace Pitching.Focus
open Set Stockpile Tap
variable {z w:ℂ}{h' :ℝ} {K' : Teller SU.group}
local notation "η"=> Scales.y SU.group R.L x
include R
lemma thin_convex (x:ℝ): Convex ℝ {v:ℂ|Stockpile.thinR R x v}:=by
 let y:= Scales.y SU.group R.L x; let A:= (51/100:ℝ)*y; let B:=(19/10:ℝ)*y; let r:=dwidth R x/(100*(1+Real.log y)^2)
 rw [show {v|Stockpile.thinR R x v}= Complex.reLm ⁻¹' Set.Ioo A B ∩ Complex.imLm ⁻¹' Metric.ball (0:ℝ) r from Set.ext fun v=>by simp only [mem_setOf_eq,Set.mem_preimage,mem_inter_iff, Set.mem_Ioo, mem_ball_zero_iff,Real.norm_eq_abs]; rw [and_assoc]; rfl]
 exact ((convex_Ioo A B).linear_preimage Complex.reLm).inter ((convex_ball (0:ℝ) r).linear_preimage Complex.imLm)
variable {x:ℝ}
omit R
abbrev Client {n:Side}(K:Teller SU.group)(R:Patch)(x:ℝ)(I:Interest n)(p:BudgetPoint)(h:ℝ)(b:ℂ)(F:Pair (Corr n)) :Prop:= thinR R x b ∧ ∃ t< Stockpile.εLeaf R.L x /3,Both (fun F=>Charged p I K.j R.L.val h t F) F
private lemma momentum0 (u v t:ℝ)(p:0≤ u)(q:0≤v)(s:u<t)(h:v<t):∃ S:Set ℂ, Convex ℝ S∧ IsOpen S∧ (0:ℂ)∈ S ∧ Complex.I∈ S∧ ∀ x∈ S,u+|x.re| *v<t ∧ |x.im| *v<t:=by
 by_cases b:v=0
 · subst v; exact ⟨Set.univ,convex_univ,isOpen_univ,Set.mem_univ _,Set.mem_univ _,fun i _=>by simp_all [h]⟩
 let A:=(t-u)/v; let B:=t/v; have hv:0<v:=q.lt_of_ne (Ne.symm b); have ha:0<A:=div_pos (sub_pos.mpr s) hv; have hb:1 < B:=(lt_div_iff₀ hv).mpr ((one_mul _).trans_lt h)
 refine ⟨Complex.reLm ⁻¹' ball (0:ℝ) A ∩ Complex.imLm ⁻¹' ball 0 B, ((convex_ball (0:ℝ) A).linear_preimage _).inter ((convex_ball (0:ℝ) B).linear_preimage _),(isOpen_ball.preimage Complex.continuous_re).inter (isOpen_ball.preimage Complex.continuous_im),⟨mem_ball_self ha,mem_ball_self (zero_lt_one.trans hb)⟩,⟨mem_ball_self ha,by change (1:ℝ)∈ ball (0:ℝ) B; simpa using hb⟩,?_⟩
 intro i t; have hp:= (lt_div_iff₀ hv).mp ((mem_ball_zero_iff.mp t.1) : ‖i.re‖<A); have hg:= (lt_div_iff₀ hv).mp (mem_ball_zero_iff.mp t.2 : ‖i.im‖<B); rw [Real.norm_eq_abs] at hp hg; exact ⟨by linarith,hg⟩
open Sour.MatchW.Technique
abbrev bearer {r:ℝ}(q:Pair (Haro.ΘS r)) :Pair ((Haro.SpaceM : Submodule ℝ (Op SU.Slot)):Type):=(q.1.val,q.2.val)
abbrev sunny {r:ℝ}(q:Pair (Haro.ΘS r)) := ‖q.1.val‖ < r ∧ ‖q.2.val‖< r
variable {r:ℝ}[Nonempty (ΘS r)]
local notation "Δ"=> Pair (Haro.ΘS r)
abbrev emptyV (A:ΘS r): Prop:= A=buzero r
local notation "Ω"=> ↥Haro.SpaceM
abbrev inward(arg:↥Haro.SpaceM)(p:ℝ)[Nonempty (ΘS p)]:ΘS p:= if h:‖arg‖ ≤ p then ⟨arg,h⟩ else buzero p
variable {s':Side}{p:BudgetPoint}{M:Interest s'}(h:ℝ)
local notation "ε"=> εLeaf R.L x /3
include R
lemma travel (i:Δ)(s:sunny i)(b:ℂ)(F:Pair (Corr s'))(X:Client K R x M p h b F)(v:1≤h):∃ S:Set ℂ,∃ f:ℂ→ℂ,∃ G:ℂ→ Pair (Corr s'),∃ j:ℂ→Pair (Haro.ΘS r),Resident S G f ∧ DifferentiableOn ℂ f S∧ HoloCorr S G∧ Sour.MatchW.Technique.Scen S j∧ (∀ x:ℝ,(x:ℂ)∈ S→emptyV (j x).2)∧ (∀ y∈ S,sunny (j y)∧ Client K R x M p h (f y) (G y))∧ f Complex.I=b∧G Complex.I=F∧ j Complex.I=i:=by
 obtain ⟨bL,t,u,q⟩:= X; let H:=fluid b; let A: Set ℂ:= {z| H z∈{z|thinR R x z}}
 have ht:0≤t:=q.1.toCost.nonneg v; let X:= ‖i.1.val‖; let Y:=‖i.2.val‖; obtain ⟨W,pW,eW,w0,w₁,hW⟩:= momentum0 t t (εLeaf R.L x/3) ht ht u u; obtain ⟨p',u',ht',p₀,p₁,t'⟩:=momentum0 X Y r (norm_nonneg _) (norm_nonneg _) s.1 s.2
 let S:= W∩(p'∩A); have hx:Convex ℝ A:=by
    intro i q j w a b' te he Hx; apply (?_ : H (a • i + b' • j)=a • H i+b' • H j) |>.symm ▸ (thin_convex (R:=R) x q w te he Hx); apply Complex.ext<;>simp [H,fluid,Complex.mul_re,Complex.mul_im]<;>nlinarith [show b.re*(a+b')=b.re from (by rw [Hx,mul_one])]
 have h0:H Complex.I=b:=by unfold H fluid; rw [Complex.re_add_im]
 have ℓ:Thorough S:=by refine ⟨eW.inter (ht'.inter (window_open (R:=R) x |>.preimage (f:=H) (by unfold H fluid; fun_prop))), (pW.inter (u'.inter hx)).isPreconnected,⟨w0,p₀,?_⟩,⟨w₁,p₁,(?_ :thinR R x (H Complex.I))⟩⟩; change thinR R x (H 0); simp only [H,fluid,mul_zero,add_zero,thinR,Complex.ofReal_re,Complex.ofReal_im,abs_zero] at *; refine ⟨bL.1,bL.2.1,(abs_nonneg _).trans_lt bL.2.2⟩; rwa [h0]
 let U(z:ℂ):= i.1.val+z.re • i.2.val; let V(z:ℂ):= z.im • i.2.val; let Q(z:ℂ): Δ:= (inward (U z) r, inward (V z) r)
 have hr(z:ℂ)(v:z∈ S): ‖U z‖<r ∧ ‖V z‖<r:=by obtain ⟨a,b⟩:= t' z v.2.1; unfold U V; refine ⟨(norm_add_le _ _).trans_lt ?_,?_⟩<;> rw [norm_smul,Real.norm_eq_abs]; exact a; exact b
 have H₁(z)(q:z∈S) : (Q z).1.val =U z := by change (inward _ _).val=_; rw [inward,dif_pos (hr _ q).1.le]
 have H₂(z)(q:z∈S) : (Q z).2.val =V z := by change (inward _ _).val=_; rw [inward,dif_pos (hr _ q).2.le]
 refine ⟨S,H,orbital F,Q,⟨ℓ,fun x h=>?_⟩, (by unfold H fluid; fun_prop),foot F ℓ.cover, (orbits Ω S (i.1.val,i.2.val)).congr (fun x q=>Prod.ext (H₁ _ q) (H₂ _ q)), fun x p=>?_, ?_, h0, by simp [orbital], Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
 · simp [orbital,H,fluid,Complex.mul_im]
 · apply Subtype.ext; exact (H₂ _ p).trans (zero_smul ..)
 · intro y qy; obtain ⟨a,b⟩:= hW y qy.1; let w:=zero_le_one.trans v; refine ⟨⟨(H₁ _ qy)|>.symm ▸ (hr _ qy).1,(H₂ _ qy)|>.symm ▸ (hr _ qy).2⟩,qy.2.2,max (t+|y.re| *t) (|y.im| *t), (max_lt_iff).mpr ⟨a,b⟩,?_ ,?_⟩; · exact ((Charged.add q.1 (Charged.smul q.2 y.re w) w)).mono (le_max_left ..)
   exact ((Charged.smul q.2 y.im w).mono (le_max_right ..))
 · rw [H₁ _ ℓ.comet]; simp [U]
 rw [H₂ _ ℓ.comet]; simp [V]
end Pitching.Focus
end YM.CF.Py.Rate
