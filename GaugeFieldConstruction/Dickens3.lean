import GaugeFieldConstruction.Dole3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner Ladder3 Branch Tenant XGarden.MastTin
variable (F:RegLime I α n)(Q:LeaseQ γ n)(k:I)(M:Mica I β n){J:Type}[Fintype J](C:J→Factor3 n)
section
variable (P:BudgetPoint)(L K:ℕ)(S:Ids n)(σ:I→ Seat n)
local notation "G"=> Actors Q C
local notation "B"=> P.B
local notation "Φ" i:max=> C (i:Actors Q C).1
local notation "V0" i:max=> spark3 Q C P L i
local notation "Zπ" i:max=> core3 Q (Φ i) i.2.1
local notation "H" i:max=> (V0 i).val.2
variable {c ℓ r h p δ δ' η:ℝ}{U:γ→ℝ}{A V:J→ℝ}
open Py Py.Riant Push.AbsoluteSums Nor
variable (X:KPower Q δ c U)(Yt:∀ i, BasePower (C i) (A i)) (v:∀ i,Act3 (C i) P K h (A i))(W:Leased Q P K h U)
variable (t:1≤ h)(d:0 <r)(w:0<δ)(wc:Frosty Q P U h η)(uη:0≤ η)(Uη: η≤1)
variable (j₀:ℕ)
local notation "P'"=> KeyUp P
local notation "Δ"=> ThermalH L
local notation "Θ"=> Win3 Q C r U A
variable (Tκ:∀ i,Sugar (C i) P h (V i) S)
local notation "αΞ"=> Antique Q C P L j₀ r h η U A V
section
variable (a:ℝ)(z₁:0≤ a)
-- LT factor optical
local notation "K0"=> reserveT (KeyUp P).power P.order
local notation "z0"=> reserveT (KeyUp P).power P.order P.B ζd
abbrev belt3(m:ℕ)(a:ℝ):= a+ m*ζd
abbrev moment3 (Q:LeaseQ γ n)(C:J→Factor3 n)(P:BudgetPoint)(L:ℕ) (a h r:ℝ)(U:γ→ℝ)(A:J→ℝ)(i:Actors Q C):ℝ:= Win3 Q C r U A i*March P.B (belt3 2 a) (spark3 Q C P L i).val.2 *rent (h/2) (nucleQ Q C i).val.2
local notation "αμ"=> moment3 Q C P L a δ r U A
local notation "D"=> windPulse P.B
local notation "ζθ"=> March P.B
lemma rub3 (A:Support (More n))(b:ℝ): fareX P.B P' A * March P.B b A ≤ reserveT (KeyUp P).power P.order P.B ζd * March P.B (b+ζd) A:=by
 apply (mul_le_mul_of_nonneg_right (coinPay P' A ζd ζdp (k:=P.B)) (Real.exp_pos _).le).trans_eq
 change _*_= _; unfold March; rw[add_mul,Real.exp_add]; unfold heft; ring
lemma starQ(k:ℕ):0≤reserveT (KeyUp P).power P.order k ζd:=by unfold reserveT coin_n stilK ζd; positivity
variable (o y:Seat n) (hz:∀ i,(C i).H.val.1=o)
include X Yt W d w
abbrev curve_p(b:ℝ)(Bx:ℕ):= Real.exp (-(b/2)*Bx)
lemma concave_L (i:Actors Q C):0≤ moment3 Q C P L a δ r U A i:=mul_nonneg (mul_nonneg (πpot Q C X Yt w d.le i) (Real.exp_pos _).le) (Real.exp_pos _).le
omit W
lemma concave_cost (i:Actors Q C) (p:y∈ (H i))(hz:∀ i,(C i).H.val.1=o) : fareX P.B (KeyUp P) (H i)*Θ i * March P.B a (H i) ≤ z0* (D o y)*(Win3 Q C r U A i*March P.B (belt3 2 a) (H i)):=by
 let X':=H i; let Z:=Θ i; let b:=z0; let A:=March (n:=More n) B (a+ζd); let P2:= March (n:=More n) B (belt3 2 a); let Λ:= D o y
 have he:= pulse_core B o X' (show _ from (hz i.1) ▸ (V0 i).property) p
 have hv:0≤Z:=πpot Q C X Yt w d.le i; have ht:0≤b:=starQ ..; have hb:0≤A X':=(Real.exp_pos _).le
 have hy : A X'*ridg B X'= P2 X':=by unfold A P2 belt3 March; rw [show a+ ↑(2:ℕ)*ζd= a+ζd+ζd from (by norm_num; ring)]; unfold ridg; rw [show (a+ζd+ζd)*_= _ from add_mul ..,Real.exp_add]
 change _≤ b*Λ*(Z*P2 X'); rw[mul_right_comm (fareX P.B P' _),←hy]
 apply (mul_le_mul_of_nonneg_right (rub3 ..) hv).trans; change b*A X'*Z≤ _
 nlinarith only [mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg ht hb) hv)]
include W
lemma curvy3 (m:Actors Q C)(b:B< (Zπ m).val.2.card)(p:y∈H m)(hz:∀ i,(C i).H.val.1=o) : Antique Q C P L j₀ r h η U A V m *March P.B a (H m) ≤ z0 *curve_p δ P.B *(D o y)*(αμ m) :=by
 let Vx:=H m; let KrH:=Zπ m; let M':= A; let Tt:=Θ m; let U':=z0; let Λ:=D o y
 have ht:= concave_cost Q C P L X Yt d w a o y m p hz; have hu:=pulse_pos P.B o y; have hx:= starQ P P.B
 have hΛ:0≤curve_p δ P.B:=(Real.exp_pos _).le
 unfold Antique; dsimp only; split; next b=> rw [zero_mul]; exact mul_nonneg (mul_nonneg (mul_nonneg hx hΛ) hu.le) (concave_L Q C P L K X Yt W d w a m) -- tune extra K' param
 next t'=>
    apply ht.trans
    let Z:=Tt*March P.B (belt3 2 a) (H m)
    have hZ:0≤ Z:=mul_nonneg (πpot Q C X Yt w d.le m) (Real.exp_pos _).le; let F:= curve_p δ P.B; let R:= rent (δ/2) KrH.val.2
    have hf:1≤ F*R:=by
       unfold F R Branch.rent curve_p; rw [←Real.exp_add]; apply Real.one_le_exp; nlinarith only [mul_le_mul_of_nonneg_right (show (B:ℝ)≤KrH.val.2.card from Nat.cast_le.mpr b.le) w.le]
    change U'*Λ*Z≤U'*F*Λ*(Z*R)
    nlinarith only [mul_le_mul_of_nonneg_left hf (show 0≤U'*Λ*Z from mul_nonneg (mul_nonneg hx hu.le) hZ)]
local notation "Zg"=> (fun a:ℝ=>Real.exp (a*(Yaw.χ Δ:ℝ)))
def sumZ (k:ℕ)(a:ℝ):ℝ:= Real.exp (a*Yaw.χ k)
variable (ht:(belt3 2 a)*2*↑(Yaw.χ (ThermalH L)) ≤ (P.B:ℝ)*(δ/2))(h0:ζd*2*(Yaw.χ 0:ℝ)≤j₀*(δ/2))(hk: 0 < j₀)
-- Near envelope inject 'single kernel inv' requires Λ μ.struct.ρ H. Keep billing previous.V V slots cust.J unit
abbrev coltV (F:Factor3 n)(Q:LeaseQ γ n)(i:AV3 Q F) : Prop:= i.1.val=(0,0) -- equivalence short d.V
abbrev crotL(k i:ℕ):=reserveT 3 i k ζd * Real.exp (ζd*Yaw.χ 0)
variable (i:Actors Q C)(g:i∈IIW Q C)
local notation "ΩΠ"=> Φ i
abbrev tune3 (δ:ℝ)(a:ℝ)(k L p:ℕ) := crotL k p * sumZ (ThermalH L) a -- tune
include z₁ ht w
private lemma relief (g:Grove (terr _) (Zπ i).val.2): March P.B a (H i)≤Real.exp (a*Yaw.χ (ThermalH L))* rent (δ/2) (Zπ i).val.2 :=by
 have p' := ht; have y:a≤belt3 2 a:=le_add_of_nonneg_right (mul_nonneg (by positivity) ζdp.le)
 apply crust _ _ P.B_pos a _ z₁ (le_trans _ p') (by positivity) _ _ g (pad_cover ..)
 gcongr
include hk h0 t v g Tκ
abbrev Ponly (a:Actors Q C):= a.2.1.1.val=(0,0)
-- i belongs to Short set p=0.
lemma rib_q (p:i.2.1.1.val.1=0)(k:(Zπ i).val.2.card≤P.B)(dC:A i.1 ≠0): (if (C i.1).pure then r*V i.1 else fareX j₀ P' (C i.1).H.val.2*(Θ i)) *March P.B a (H i) ≤ if (C i.1).pure then r* V i.1* Real.exp a else tune3 δ a j₀ L P.order*r*(A i.1*rent (3*δ) (C i.1).H.val.2):=by
 obtain ⟨e,Q₁,Kx,T⟩:= hue_B Q C P K S X Yt v W t d i g p
 let z:= C i.1; let E:= z.H; let c:=E.val.2; have u:= (Yt i.1).pos
 let H0:= (H i)
 split
 next v=>
    rw[show H i=c from congrArg (fun x: Hub n=>x.val.2) (pure_pad Q _ _ _ _ v)]
    obtain ⟨h,p⟩:= (Tκ _).light v; have h2:0 ≤ V i.1:= (SecX P' (zero_le_one.trans t) _).posG _ _ _ h
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg d.le h2); apply Real.exp_monotone
    exact (mul_le_mul_of_nonneg_left (show heft P.B c≤1 from (by unfold heft; exact_mod_cast p)) z₁).trans_eq (mul_one _)
 next s=>
   rw[Kx]; let Z:= P'; let T:= rent (δ/2) c
   have g:Grove (terr _) c:=(Yt i.1).grow dC
   have he: rent (δ/2) (Zπ i).val.2=T:=congrArg (fun x:Hub n=> rent _ x.val.2) e
   let R:= reserveT 3 P.order j₀ ζd; have hR:0≤R:=starQ P j₀
   have hz: fareX j₀ P' c ≤ crotL j₀ P.order * T:=by
      apply (coinPay P' c ζd ζdp).trans
      apply le_trans (mul_le_mul_of_nonneg_left (crust 0 j₀ hk ζd (δ/2) ζdp.le h0 (by positivity) _ _ g (halo_subset _ _)) hR)
      exact le_of_eq (by unfold T R crotL; ring) -- tune Hx?
   let W':=Real.exp (a * Yaw.χ Δ)
   have hp : March P.B a H0 ≤ W'*T:=by rw[←he]; exact relief Q C P L K X Yt W d w a z₁ ht i (e.symm ▸ g) -- include.B メ
   have he: T*T≤rent (3*δ) c:=by unfold T Branch.rent; rw[← Real.exp_add]; exact Real.exp_monotone (by nlinarith [Nat.cast_nonneg (α:=ℝ) c.card])
   have hu:0≤ crotL j₀ P.order:=mul_nonneg hR (Real.exp_pos _).le
   let β:=crotL j₀ P.order; let η:= A i.1 * r; have hη:0≤η:= mul_nonneg u d.le
   change fareX j₀ P' c* η * March P.B a H0≤_
   refine (mul_le_mul (mul_le_mul_of_nonneg_right hz hη) hp (Real.exp_pos _).le (mul_nonneg (mul_nonneg hu (Real.exp_pos _).le) hη)).trans ?_
   change β*T* η *(W'*T)≤ β*W'*r*(A i.1*Branch.rent (3*δ) c); nlinarith only [mul_le_mul_of_nonneg_left he (mul_nonneg hη (mul_nonneg hu (show 0≤ W' from (by unfold W'; positivity))))]
end
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
