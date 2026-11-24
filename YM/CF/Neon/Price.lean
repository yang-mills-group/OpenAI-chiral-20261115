import YM.CF.Neon.Ortho
import YM.CF.Neon.Glass
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
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
variable{N P B:Side}{S_O:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S_O}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
open Moto Hove Tap Tune Taxi Nor Oath Larch
-- LIFT Budget arithmetic before L constant functions. Need after L pose grants.Width.State contracts analyticity log jets. Explicit says where heating. b_e=pre.L UNIT price.Can.Op not warming.
abbrev gyro_S(Xp Yp:BudgetPoint)(l:ℕ)(kC A:ℝ):= Real.exp (Xp.supportExponent*(KX l:ℝ))*(kC*trotΦ Yp 1 A)
abbrev ψC(Xp:BudgetPoint)(k p l:ℕ):= Real.exp (Xp.supportExponent*(PKard l:ℝ))*(deck_K k p (10*(l+300))* Oath.stakeH k)
abbrev mC0(Xp:BudgetPoint):= 2*peka_H Xp.power
abbrev ume (C:ℝ):= (C+‖baseF false‖+‖baseF true‖+1)^2
variable (Xp Yp:BudgetPoint)(L':Side)(k p l j:ℕ)(Ωs:Hove.Grant j p)(aX A Zq:ℝ)
local notation "Lr"=> ((L'.val:ℝ)⁻¹)
local notation "Ωv"=> (Ωs.F)
local notation "Ωw"=> (ume Ωs.C)
local notation "Ωa"=> (Ωs.A+2)
local notation "H0"=> (mC0 Xp)
local notation "S_"=> (Sauce Yp A)
abbrev mNv(Xp Yp:BudgetPoint)(l:ℕ)(v u:ℝ)(L':Side) := Tune.l_fee (Fintype.card (PlaqAxes×PlaqAxes)) Yp Xp v 1+ u*(KX l:ℝ)*‖(↑(qCorset Xp.threshold Yp.threshold (L'.val:ℝ)):ℂ)‖
abbrev pUθ (HfC s:ℝ):= HfC*s
abbrev ΩZad(s a:ℝ):= (a+2)*(2*s)
local notation "Zφ"=> (ΩZad S_ Ωs.A)
variable (Fχ:ℝ)(kC:ℝ)(hL:0 ≤ Fχ)(hk:0≤ kC)(hA:0≤ A)
variable (n0:ℕ)(hv0: (1+(n0:ℝ))⁻¹ ≤ ((L'.val:ℝ)⁻¹)^2)
local notation "qG"=> gyro_S Xp Yp l kC A
local notation "κA"=> (Fχ * S_)
local notation "νψ"=> ψC Xp k p l
local notation "Kμ"=> Haro.κP p -- tune
local notation "ζl"=> (lace 0 L')
local notation "ζp"=> (lace 1 L')
local notation "Z'"=> (1+(n0:ℝ))
lemma peach (L:Side): lace 0 L^2= (L.val:ℝ)⁻¹^3 ∧ lace 0 L*lace 1 L=(L.val:ℝ)⁻¹^4:=by
 let v:ℝ:= L.val; have hv:0<v:=by unfold v; positivity
 have h:Real.sqrt v^2=v:= Real.sq_sqrt hv.le; unfold lace; norm_num only [Nat.reduceAdd]; change (Real.sqrt v/v^2)^2= _ ∧ Real.sqrt v/v^2*(Real.sqrt v/v^3)=_
 constructor
 · rw [div_pow,h]; change v/(v^2)^2=v⁻¹^3; field_simp -- expensive
 change Real.sqrt v/v^2*(Real.sqrt v/v^3)=v⁻¹^4; rw [div_mul_div_comm,←pow_two, h]; field_simp
lemma mint_p(P:BudgetPoint)(hA:0 ≤ A):0 ≤ Moto.trotΦ P 1 A:=by unfold Moto.trotΦ tollV; have h:= AnalyticBridge.VerifiedReset.pair_nonneg SU.group P; positivity
lemma hale_L(c:ℝ):0≤ume c:=sq_nonneg _
section
variable (Q a b c R S₂ h dP d0 G' E μ kK W μ0 :ℝ)(Hf Fd:ℝ)(zv vY vB:ℝ) -- tape post rent aggregate.Retry arbitrary big
-- A.C omega PH parameters Zhu etc. A≥0 for base. Kx.Frame Sparse.
variable (ha:a≥0)(hb:b≥0)(hc:c≥0)(hq:0 ≤ Q)(hW:0 ≤W)(pz:Moto.Skate) -- pz remove
local notation "γw"=> (b *h^2)
local notation "αw"=> (c*h^2)
local notation "Ωk"=> (ζl^2*b)
local notation "Θy"=> (c+δK0*b) -- full part projection charge.
local notation "Ωℓ"=> (ζl*ζp)
local notation "Φp"=> (Ωs.F*(ζl^2*b+8*(ζl*ζp)*Θy))
local notation "γℓ"=> (G') -- growth U0 paid output
local notation "γS"=> kK -- input TkΨ
local notation "Tu"=> (1+(n0:ℝ))
local notation "K₁"=> (Ωw*(ζl^2*b))
local notation "P₁"=> (Ωw*(ζl*ζp*Θy)/(1+(n0:ℝ)))
local notation "X0"=> (κP p*d0*kK)
local notation "Z₁"=> (reserveT Xp.power Xp.order Xp.B 2*dP) -- Wk residual
local notation "τx"=> d0 -- delta per era readiness ≤ Ωa*L^-5. doesn't assume δ≥0; feasible from frame.
variable (hF:Hf ≤ Fχ*(L'.val:ℝ)⁻¹^5)(pF:0 ≤Hf)(htD:d0≤ (Ωs.A+2)*((L'.val:ℝ)⁻¹)^5)(hv':vB ≤W)(hp:Fd≤W)(hpρ:reserveT Xp.power Xp.order Xp.B 2*dP ≤ W)(hΨ:mNv Xp Yp l zv vY L'≤2*((L'.val:ℝ)⁻¹)^5)
-- Θ costs from faith_P.Real.P. Use R=T multiplier to actual thermo. G'=output paid_M. field
variable (hG':G' ≤ Ωs.F*((lace 0 L')^2*b+8*(lace 0 L'*lace 1 L')*(c+δK0*b))+d0*kK)(pKcost:R ≤ Sauce Yp A * Q) (hkc:kK*h^2 ≤ 2*(Sauce Yp A *Q))(hk0:0 ≤ kK)
local notation "AL"=> (Real.exp (Xp.supportExponent*(PKard l:ℝ))*(deck_K k p (10*(l+300))*(Oath.stakeH k*h^2* G')))
local notation "Df"=> (Hf*R+Fd)
local notation "ZΦ"=> (Real.exp (Xp.supportExponent*(KX l:ℝ))*(kC*(((L'.val:ℝ)⁻¹)^4)* Moto.trotΦ Yp a A)+vB)
local notation "Εκ"=> (ZΦ+(Df+AL)+Z₁)
local notation "JΦ"=> (l_fee (Fintype.card (PlaqAxes×PlaqAxes)) Yp Xp zv a+ vY*KX l*(‖(↑(qCorset Xp.threshold Yp.threshold (L'.val:ℝ)):ℂ)‖*a))
local notation "Tζ"=> (mC0 Xp*(vB+(Df)+Z₁))
local notation "BL"=> mintR Lr a γw αw Q W
local notation "BH"=> naxR Lr a γw αw Q W
local notation "BΩ"=> nagR Lr a γw αw Q W
lemma math_E (x a b c Q W y h d k D u v g η ζ_ r q t Y C M U BΞ S Lf Ω' Hf Fd :ℝ)
 (xa:0≤x)(hu:x≤1)(hA:0≤ a)(hb:0 ≤ b)(hc:0 ≤ c)(hQ:0 ≤ Q)(hW:0 ≤ W)(hy:0≤y)(hk:0≤k)(hD:0≤D)(hs:0≤u)(hv:0≤v)(hg:0≤g)(huY:0≤ Y)(hz:0≤ ζ_)(hBξ:0 ≤ BΞ)(hr:0≤ r) -- map r=kC_rank, ζ=Pu, q=pruneQ, η=uΩ.cap, BΞ=δK0. y=ume, v=Φκ. Y=ψC, k=κP, t=n0, D=δpump.Kcost, S paid Ekin, U=Aura Pμ, M=vB, C=PSI thanh.P Λ, Lf= Ωz,
 (hΛ:Hf ≤u*x^5)(hF:0 ≤ Hf)(hHt:t⁻¹ ≤ x^2)(hd:d ≤ η*x^5)(hη:0 ≤ η)(huK:0 ≤ q)
 (hC:S≤ v*(x^3*b+8*(x^4)*(c+BΞ*b))+d*D)(hkQ:D*h^2 ≤ 2*(ζ_*Q))(hZ:Lf≤2*x^5*a)(wU: Ω'≤ ζ_*Q)(hM:M≤W)(hp:U≤W)(hw:Fd≤W):
 let Z1:= η*(2*ζ_); let G:= g*(x^4*a)+M; let XTa:=k*d*D; let ε:= r*(M+(Hf*Ω'+Fd)+U); let Bm:= b*h^2; let Bz:= c*h^2; let K:= y*(x^3*b); let Zκ:= y*(x^4*(c+BΞ*b))/t; let Kt:=d*C; let R0:= Q -- unused.
 G+(Hf*Ω'+Fd+Y*(S*h^2))+U ≤ lush g Y (u*ζ_) v Z1 BΞ* mintR x a Bm Bz Q W ∧ Lf+2*M+(Hf*Ω'+Fd)+U≤ loon (u*ζ_)*naxR x a Bm Bz Q W∧ ε+(XTa+(2*K/t+8*Zκ))*h^2≤coil_T (u*ζ_) Z1 BΞ y k r*naxR x a Bm Bz Q W∧ ε+ (q*(XTa+(K+12*Zκ)))*h^2 ≤ coin_T (u*ζ_) Z1 BΞ y k q r*nagR x a Bm Bz Q W:=by
 intro Z1 G XTa ε Bm Bz K Zκ Kt R0
 have hh: d*D*h^2 ≤ Z1*(x^5*Q):= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hD) (sq_nonneg h)).trans ((mul_assoc ..).le.trans ((mul_le_mul_of_nonneg_left hkQ (mul_nonneg hη (pow_nonneg xa _))).trans_eq (by unfold Z1; ring)))
 have h2:y*(x^3*b)*h^2/t ≤ y*(x^5*Bm):=by rw [div_eq_mul_inv]; exact (mul_le_mul_of_nonneg_left hHt (by positivity)).trans_eq (by unfold Bm; ring)
 have h3:y*(x^4*(c+BΞ*b))/t*h^2 ≤ y*(x^5*(Bz+BΞ*Bm)):=by
    rw [div_eq_mul_inv,mul_right_comm _ _ (h^2)]; have h:t⁻¹≤ x:= hHt.trans (pow_le_pow_of_le_one xa hu (by decide:1≤ 2) |>.trans (pow_one _).le); exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by unfold Bz Bm; ring)
 have hk0:k*d*D*h^2≤ k*Z1*(x^5*Q):=by refine le_trans (Eq.le (show k*d*D*h^2=k*(d*D*h^2) from (by ring))) ((mul_le_mul_of_nonneg_left hh hk).trans_eq ?_); ring
 refine dower_s x a Bm Bz Q W xa hu hA (show 0 ≤ b*h^2 from by positivity) (show 0 ≤ c*h^2 from by positivity) hQ hW _ _ (u*ζ_) v Z1 BΞ y k q r hg huY (by positivity) hv (mul_nonneg hη (mul_nonneg (by norm_num) hz)) hBξ hy hk huK hr G ((XTa+(2*K/t+8*Zκ))*h^2) (Hf*Ω'+Fd) (Y*(S*h^2)) U M Lf ((q*(XTa+(K+12*Zκ)))*h^2) (add_le_add le_rfl hM) ?_ ?_ hZ hM hp ?_ ?_
 · exact add_le_add ((mul_le_mul_of_nonneg_left wU hF).trans ((mul_le_mul_of_nonneg_right hΛ (mul_nonneg hz hQ)).trans_eq (by ring))) hw
 · refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hC (sq_nonneg h)).trans ?_) huY; rw [add_mul]; exact add_le_add (le_of_eq (by unfold Bm Bz; ring)) hh
 · rw [add_mul, add_mul]; refine add_le_add hk0 (add_le_add ?_ ?_)
   · unfold K; refine le_trans (Eq.le (show 2*_ / t*h^2= 2*(y*(x^3*b)*h^2/t) from (by ring))) ((mul_le_mul_of_nonneg_left h2 (by norm_num:0≤(2:ℝ))).trans_eq (by ring))
   exact (mul_assoc ..).le.trans ((mul_le_mul_of_nonneg_left h3 (by norm_num:0≤(8:ℝ))).trans_eq (by ring))
 rw [mul_assoc q,add_mul,add_mul,←add_assoc]; exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hk0 (Eq.le (by unfold Bm K; ring))) ((mul_assoc ..).le.trans ((mul_le_mul_of_nonneg_left h3 (by norm_num:0≤(12:ℝ))).trans_eq (by ring)))) huK
include hv0 hA hk hL ha hb hc hq hW hF pF htD hv' hp hpρ hΨ hG' pKcost hkc hk0
set_option maxHeartbeats 1400000 in
lemma peak_T : Εκ ≤ lush qG νψ κA Ωv Zφ δK0 *BL ∧ JΦ+2*vB+Df+Z₁ ≤ loon κA*BH∧ Tζ+(X0+(2*K₁/Tu+8*P₁))*h^2 ≤ coil_T κA Zφ δK0 Ωw (κP p) H0*BH ∧ Tζ+(pruneQ*(X0+(K₁+12*P₁)))*h^2 ≤ coin_T κA Zφ δK0 Ωw (κP p) pruneQ H0*BΩ:=by
 let x:= Lr; have hV:0≤ x:=(by unfold x; positivity); have he:x≤ 1:= inv_le_one_of_one_le₀ (by exact_mod_cast L'.property)
 let C:= ume Ωs.C; have ht:0≤ C:= hale_L _
 have hy:0≤ gyro_S Xp Yp l kC A:=mul_nonneg (Real.exp_pos _).le (mul_nonneg hk (mint_p _ _ hA)); have hZ:0≤νψ:=by unfold ψC deck_K Oath.stakeH Jet.composeCost γD Haro.flavor; have h:=Haro.p0; have hv:=Haro.wheels_p (n:=k); positivity
 have hv:0≤ S_:= honor_B _ hA _; have he':= Ωs.hp; have hz:0≤Ωa:= add_nonneg Ωs.hp (by norm_num)
 have hp':0≤Zφ:= mul_nonneg hz (mul_nonneg (by norm_num) hv)
 have hkP:0≤κP p:=by unfold κP Haro.ξP; have hx:=mpe true; have hy:=mpe false; positivity
 have htP:0≤pruneQ:=(by unfold pruneQ; positivity); have hu:0≤ mC0 Xp:=by unfold mC0 peka_H κP Haro.ξP pruneQ; have hx:=mpe true; have hy:=mpe false; positivity
 have hd:=δtop true
 obtain ⟨hp2,hp3⟩:=peach L'; have hv': vB ≤ W:=hv' -- tune
 let G:=G'; let y:=Ωw; have ht1 :ζl*ζp=x^4:=hp3; have ht2: ζl^2=x^3:=hp2
 have ha':JΦ ≤2*x^5*a:=by refine le_trans (Eq.le (show JΦ = mNv Xp Yp l zv vY L'*a from by unfold mNv Tune.l_fee; ring)) (mul_le_mul_of_nonneg_right hΨ ha)
 have hg: G' ≤ Ωs.F*(x^3*b+8*x^4*(c+δK0*b))+d0*kK:= by rw [←ht1,←ht2]; exact hG'
 let V':=math_E x a b c Q W y h d0 (κP p) kK Fχ Ωs.F qG Ωa S_ (mC0 Xp) pruneQ Tu νψ G vB Z₁ δK0 G JΦ R Hf Fd hV he ha hb hc hq hW ht hkP hk0 hL Ωs.hx hy hZ hv hd hu hF pF hv0 htD hz htP hg hkc ha' pKcost hv' hpρ hp -- tune order cast
 have heq: ZΦ=qG*(x^4*a)+vB:=by unfold x trotΦ gyro_S trotΦ tollV; ring
 have hpq:AL=νψ*(G*h^2):=by unfold ψC; unfold G; ring
 rw [heq,hpq,ht1,ht2]; exact V' 
end
end YM.CF.Neon
