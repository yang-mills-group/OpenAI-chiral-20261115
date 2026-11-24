import YM.SU5.WakeInvestment.Funnel
import YM.SU5.WakeInvestment.Foil
import YM.SU5.WakeInvestment.Asymptotic
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

open Lamour.Bridge Celeste Clock Hookah
open Cliplet
variable {m p:ℕ} {E u κ C:ℝ} (H:Real.exp 1≤ P.x)
section
abbrev strips (Z:List (Hookah (side Y i s)))(j:Fin Z.length) : Mark (side Y i s) := (Z.get j).x-1
lemma strip_eq (Z:List (Hookah (side Y i s))) : fullRead Y s i (strips Y s i Z)=Hookah.buffet Z := by
 have hx:(fun j => 1+strips Y s i Z j)=Hookah.x ∘ Z.get := funext fun j=>by simp [strips]
 unfold fullRead; rw [hx, ←List.map_ofFn, List.ofFn_get]; rfl
lemma strip_comm {F0:Hookah (side Y i s)} {Z:List (Hookah (side Y i s))} (t:Shellac F0 p Z) (j q:Fin Z.length) (x:Fields (side Y i s)) : Commute (strips Y s i Z j x) (strips Y s i Z q x):=by
 let S(e:Fin Z.length):= ((t.core (Z.get e) (List.get_mem _ e)).owner.mono (subset_univ _)).allV x
 let a:= (Z.get j).x x; let b:= (Z.get q).x x
 have h: Commute a b := by unfold Commute SemiconjBy a b; rw [(S j).sign_com (S q)]; simp [Sector.grainB]
 exact Commute.sub_right (Commute.sub_left h (Commute.one_left _)) (Commute.one_right _)
end

structure StripProof (p B m : ℕ) (A:Hookah (side Y i s)) (κ:ℝ) : Prop where
 owner: AtSupport false A.S A.x
 span: ∀ j,cows j (Lattice.halo p A.S) B
 -- price only on adequate replication; allow $κ$ negative.
 report (Z:List (Hookah (side Y i s)))(q:Shellac A p Z)
        (g:(More (side Y i s)).val ^4 ≤ Z.length*(4*(B+addgap (tent Y H)))^4) :
   ∃ e:Orbit (side Y i s)→ℝ,
    (∀ᵐ x : Orbit (side Y i s) ∂city (side Y i s), Fitting Y s i k (chip (hat P.R.L P.x s) (-199)) (chip (hat P.R.L P.x s) (-198)) (e x) m (strips Y s i Z) x)
    ∧ Integrable (fun x=> Real.exp (e x)*shadeY Y s i k 0 (ηP s) x) (city _)
    ∧ (∫ x: Orbit _, Real.exp (e x)*shadeY Y s i k 0 (ηP s) x∂city (side Y i s)) ≤ Real.exp (Z.length*κ+Papal.gBaseR Y s i k+7*(ℰ s)*sites (N s i))

variable {H s i k} {A:Hookah (side Y i s)} {B : ℕ}
local notation "𝐃" NN:max => (More NN).val^4
local notation "ω*" a:max => chip (hat P.R.L P.x s) a
include H
lemma StripProof.sign (P':CorridorFee Y s i k E m) (Z:StripProof Y s i k H p B m A κ)
    (v: 12* Worth.meterC (hat P.R.L P.x s)*(4*((↑B:ℝ)+↑(addgap (tent Y H))))^4 ≤ u)
    (L':List (Hookah (side Y i s)))(t:Shellac A p L')(a:𝐃(N s i) ≤ L'.length*(4*(B+addgap (tent Y H)))^4) :
    ‖Journey.compass Y i k s (Hookah.buffet L')‖≤ Real.exp (L'.length*(κ+ ω* (-205)+ u)):=by
 obtain ⟨e,p,q,r⟩:= Z.report L' t a; have hx:= P'.ready _ e (L'.length * κ) p (show Envelope _ from (strip_eq Y s i L').symm ▸ t.occupy.env) q r
 rw [strip_eq] at hx; let w:= Worth.meterC (hat P.R.L P.x s); let G:=addgap (tent Y H)
 apply hx.trans (Real.exp_monotone _)
 have ht:=mul_le_mul_of_nonneg_left v (Nat.cast_nonneg (α:=ℝ) L'.length)
 have hy: sites (side Y i s) ≤ L'.length*(4*((B:ℝ)+(G:ℝ)))^4:=by unfold sites; exact_mod_cast a
 have hG:12*w*sites (side Y i s)≤ L'.length*u :=by
    apply le_trans (mul_le_mul_of_nonneg_left hy (mul_nonneg (by norm_num) (BProof.coin_pos _ _ _ _|>.le))); apply le_trans (le_of_eq ?_) ht; ring
 linarith only [hG]

omit H
lemma pose_switch {pX:ℕ} {a b u:ℝ}(p:0≤a)(v:0<b) (f:Ferry Y s i k)
    (h:∀ F, Envelope F → (∀ x, ‖F x‖≤ Real.exp (a*sites (N s i))) → ‖Journey.compass Y i k s F-solder Y i k f.depth s F‖ ≤ (Real.exp b-1)/Real.exp (|u| *sites (N s i)))
    {t:ℝ} (q:u ≤ t) (g:AtSupport false A.S A.x) (d:∀ x, ‖A.x x‖ ≤ Real.exp a)
    {W:List (Hookah (side Y i s))}(e:Shellac A pX W) -- implicit p'
    (y:1 ≤ W.length)(w:W.length≤ 𝐃 (N s i))
    (Bv:‖solder Y i k f.depth s A.x‖^W.length≤ ‖solder Y i k f.depth s (Hookah.buffet W)‖)
    (x:‖Journey.compass Y i k s (Hookah.buffet W)‖ ≤ Real.exp (W.length*t)) :
    ‖Journey.compass Y i k s A.x‖ ≤ Real.exp (t+2*b)∧‖solder Y i k f.depth s A.x‖ ≤ Real.exp (t+b):=by
 let F:= Journey.compass Y i k s; let Q:=solder Y i k f.depth s
 let n:=W.length; let T:=sites (side Y i s); let z:=Real.exp b; let a':=Real.exp t; let c:=z-1; let X:=Hookah.buffet W
 have hz:1≤z:=Real.one_le_exp v.le; have hc:0≤c:=sub_nonneg.mpr hz; have ha':0≤a':=(Real.exp_pos _).le
 have hG {m:ℕ}(G:Mark (side Y i s))(h0:m≤𝐃 (N s i))(s0:Envelope G)(H':∀ x, ‖G x‖ ≤ Real.exp a ^ m) :
    ‖F G - Q G‖ ≤ c * a'^m := by
     have hm:(m:ℝ)≤T:=by unfold T sites; exact_mod_cast h0
     apply (h G s0 (fun x=> (H' x).trans (by rw [←Real.exp_nat_mul]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_right hm p]))).trans; change c / Real.exp _ ≤ _
     rw [div_eq_mul_inv,←Real.exp_neg]; apply mul_le_mul_of_nonneg_left _ hc; unfold a'; rw [←Real.exp_nat_mul]; apply Real.exp_monotone
     have hx := (neg_abs_le u).trans q; linarith only [mul_le_mul_of_nonneg_right hm (abs_nonneg u), mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (α:=ℝ) m)]
 have h':‖Q A.x‖ ≤ z*a':=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hz) ha') (by omega:W.length≠0)).1; apply Bv.trans; apply (norm_le_norm_sub_add (Q X) (F X)).trans; rw [norm_sub_rev,mul_pow]
    rw [Real.exp_nat_mul] at x
    apply (add_le_add (hG X w e.occupy.env (fun x=> e.presup d (Real.exp_pos _|>.le) x)) x).trans; change c*a'^n+a'^n ≤ z^n*a'^n; have ht: z ≤ z^n:=by exact le_trans (by rw [pow_one] : z≤z^1) (pow_le_pow_right₀ hz y)
    exact le_trans (le_of_eq (by unfold c; ring)) (mul_le_mul_of_nonneg_right ht (pow_nonneg ha' _))
 refine ⟨?_, h'.trans_eq (by unfold a' z; rw [Real.exp_add,mul_comm]) ⟩
 apply (norm_le_norm_sub_add (F A.x) (Q A.x)).trans; have hT:=hG A.x (y.trans w) g.env (fun x=> (d x).trans_eq (pow_one _).symm); rw [pow_one] at hT; apply (add_le_add hT h').trans; rw [show t+2*b=b+b+t by ring,Real.exp_add (b+b),Real.exp_add b]; change c*a'+z*a'≤ z*z*a'; unfold c; nlinarith only [mul_nonneg (sq_nonneg (z-1)) ha']


include H
lemma pose_budget {a b ε:ℝ}(t:0≤a) (u_:0<b)(B:ℕ)(s:ℕ) (v: 12* Worth.meterC (hat P.R.L P.x s)*(4*((↑B:ℝ)+↑(addgap (tent Y H))))^4 ≤ u) : ∀ᶠ r:ℕ in atTop, ∀ i k, B+addgap (tent Y H) ≤ (side Y i s).val → r≤k → ∀ f:Ferry Y s i k, ∀ {p m:ℕ}{E:ℝ}, CorridorFee Y s i k E m → ∀ (A:Hookah (side Y i s))(κ:ℝ), ε ≤ κ → StripProof Y s i k H p B m A κ → (∀ x, ‖A.x x‖ ≤ Real.exp a) →
     ‖Journey.compass Y i k s A.x‖ ≤ Real.exp (κ+ chip (hat P.R.L P.x s) (-205)+u+2*b) ∧
     ‖solder Y i k f.depth s A.x‖ ≤ Real.exp (κ+chip (hat P.R.L P.x s) (-205)+u+b) := by
 let d:=chip (hat P.R.L P.x s) (-205); let v':=ε+d+u; obtain ⟨t',p'⟩ := eventually_atTop.mp (Papal.pose_change Y (Real.exp b-1) a |v'| (sub_pos.mpr (Real.one_lt_exp_iff.mpr u_)) s)
 filter_upwards [eventually_ge_atTop t'] with r z i k c l f p m E e A κ h D0 w
 obtain ⟨Z,h₀,h₁,h₃,h₄,h₅⟩:= Hookah.cavalcade (Papal.revive Y H s i k f) (terrain Y H (Y.ir i) s).symm c A ⟨Foil.base, D0.owner⟩ D0.span -- A0
 exact pose_switch Y t u_ f (p' k (z.trans l) _ f.depth) (by linarith : v'≤κ+d+u) D0.owner w (show Shellac A p Z from h₀) h₁ h₃ h₅ (D0.sign Y e v Z h₀ h₄)
#print axioms StripProof.sign
#print axioms pose_switch
#print axioms pose_budget
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
