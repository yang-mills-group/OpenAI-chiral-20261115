import YM.CF.Tar.Tanks
import YM.CF.Tar.Yell
import YM.CF.Tar.Lime
import YM.CF.Tar.Duty
import YM.CF.Ridge.Kalk
import YM.CF.Reed.Trio
import YM.CF.Ridge.Trio
import YM.CF.Ridge.Ply
import YM.CF.Paxos.Heron
import YM.CF.Tar.Run
import YM.CF.Paxos.Luz
import YM.CF.Bloom.Kale
set_option autoImplicit false
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
open Oise
variable {Mκ:ℝ}
local notation "χ"=> (grant_B R.L)
local notation "Vμ"=> (Duty V a p i N0 J q h)
variable(hp0:1≤h)
open Salt
abbrev zone_F(j c:ℕ):RankX:= if c < j then some (j-(c+1)) else none
abbrev area_K(F G:ℝ→ℝ)(t:ℕ)(j:ℕ)(L:Side)(x:ℝ):ℝ:=max (dleaf L (hat L x j)) ((1/2:ℝ)^(post_H t-j)* F (hat L x (post_H t))) -- G unused keep
abbrev table_B(L:Side)(F G:ℝ→ℝ)(t:ℕ)(x:ℝ)(Q:ℕ→ℝ→ℝ)(j:ℕ):ℝ:=if post_H t<j then Q (j-(post_H t+1)) (hat L x j) else area_K F G t j L x -- want area_K for j≤cut too, equals leaf by post pay
abbrev tide_W(t j:ℕ)(F:ℕ→ℝ):= if j < buoy t then F j else 0
abbrev wage_B(t n j:ℕ)(R:Side)(x:ℝ):= if j<buoy t then nu_B R else grant_B R (hat R x (trunkY t n))
abbrev mode_D(t j:ℕ)(R:Side)(x:ℝ)(D:ℝ→ℝ):=if j<buoy t then D (hat R x j) else grant_B R (hat R x j)
-- ready.Service one of chain relative α. one-step antitone ranking. national bound ξθ not explicitly needed early. positivity T. all M skill step. Lit.D spill
variable (D R0 E C:ℝ→ℝ)(z:ℝ)(Z':Heron V a p i N0 k₀ J q h Mκ R0 E C D z)(hy:z ≤ x)
local notation "W₀"=> ζ-- remove
open Haro
structure Sculp (Fp:ℝ→ℝ)(t c:ℕ)(J0:ℕ→ℝ)(A0:ℕ→ℝ) :Prop where
 rateB(i:ℕ):0 < J0 i
 maxim(j:ℕ): 0 < wage_B t c j R.L x
 dose(j:ℕ): j< trunkY t c → mode_D t j R.L x D ≤ wage_B t c j R.L x
 step(j:ℕ): j< trunkY t c → Duty V a p i N0 J q h (V.L.op (trunkY t c-1-j) (kint M B R.L j)) (apt M B R.L j) (hat R.L x j) (J0 j) (mode_D t j R.L x D) (A0 j) (A0 (j+1)) (tide_W t j (Hertz V a p i N0 M k₀ J q h R0 E C D z Z' hy)) (zone_F j (post_H t)) (zone_F (j+1) (post_H t))
 fill(j:ℕ):j<trunkY t c→ (zone_F j (post_H t)).isSome=false→ 0 < A0 j
 fund(j:ℕ): j < buoy t → J0 j= R0 (hat R.L x j)
 vane(j:ℕ): j ≤ buoy t→ A0 j=dleaf R.L (hat R.L x j)
 cost: Fp (hat R.L x (trunkY t c)) ≤ A0 (trunkY t c)
 yoke: (↑(trunkY t c-buoy t):ℝ)*grant_B R.L (hat R.L x (trunkY t c)) ≤ (buoy t:ℝ)* nu_B R.L
-- remember offset B0 label B. top j=post+t+1 offset t. Fp from lives.
variable (κ σ:ℝ)(P0:MoveX (p:=p) (k:=i) V U W q a J.d J.n k J.k J.roomX h)(vv0:k≤N0)(P1:VaultXU (p:=p) (k:=i) V U W q a J.d J.n σ N0 J.k J.roomX h)(P2:HoldU (p:=p) (k:=i) V U W q a J.d J.n κ N0 J.k J.roomX h)(hκ:κ/R.L.val≤1/4)
local notation "Ων"=> ν_PS R.L
include hp0 P0 vv0 P1 P2 hκ
lemma calendar (t:ℕ)(d':ℝ→ℝ)(pd:sizeK R.L 2 d')(pZ: Chill_v D): ∀ᶠ x in atTop,∀ hy:z ≤ x,∀ M:Side,∀ᶠ b:ℕ in atTop,∃ Jx Vt,Sculp V a p i N0 M k₀ J q h D R0 E C z Z' hy d' b t Jx Vt:=by
 obtain ⟨Fp,hF,pX⟩:= CoolX.roomZ R.L _ pd
 obtain ⟨QW,τW⟩:= start_K V a p i N0 J q h P0 vv0 Fp t hF
 obtain ⟨Yt,Dp,cost,wV⟩:=vault_U V a p i N0 J q h P1 _ (τW.grow 0).small ((τW.grow 0).costs.mono fun i p=>p.1)
 obtain ⟨Eψ,hE,Yq⟩:=fcap_v R.L _ _ cost (dev_R R).1
 have hwS:= hold_y V a p i N0 J q h hp0 P2 hκ Eψ hE (Yq.mono fun i p=>p.2.2.1)
 have hU:∀ᶠ x:ℝ in atTop,∀ u:ℕ,u<t→∀ {N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B))(j:ℕ),Duty V a p i N0 J q h S G x 1 (χ x) (QW u x) (QW (u+1) x) 0 (some j) (some (j+1)):=by
    have h':∀ iv:Fin t,∀ᶠ x:ℝ in atTop,∀ {N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B))(j:ℕ),Duty V a p i N0 J q h S G x 1 (χ x) (QW iv.val x) (QW (iv.val+1) x) 0 (some j) (some (j+1)) :=?_ -- `_` remove shadow
    swap; · exact fun i=>τW.warp _ i.isLt
    filter_upwards [eventually_all.mpr h'] with x h i u N P; exact h (⟨i,u⟩:Fin t)
 have hΩ:= eventually_all.mpr (fun i:Fin (t+1)=> (τW.grow i).costs); have hZ:=pardon V a p i N0 k₀ J q h hp0 _ R0 E C D z Z' pZ -- order hP?
 obtain ⟨x,Wz⟩:=eventually_atTop.mp (wV.and (Yq.and (hwS.and (hU.and (pX.and (hΩ.and (hZ.and ((year SU.group R.L).eventually_gt_atTop 0))))))))
 filter_upwards [eventually_ge_atTop x] with X hX hy M
 let T:=hat R.L X; filter_upwards [glow_y V (x:=X) t Yt cost] with j tK; let k:= buoy j; let l:=post_H j; let L:= trunkY j t; let xk:=T k; let yl:=T l
 let S(i):=V.L.op (L-1-i) (kint M B R.L i); let G(i):= apt M B R.L i; let uℝ(t:ℕ):= Hertz V a p _ N0 M k₀ J q h R0 E C D z Z' hy t
 have hT(i): X ≤ T i:=crown ..
 let F_(i):=wage_B j t i R.L X; let P_(i):= mode_D j i R.L X D; let Z(i):=tide_W j i uℝ
 let Dk:= table_B R.L Yt Yt j X QW; let sp(i):=zone_F i l
 let E'(x):=dleaf R.L x
 let Q(j:ℕ):= Wz _ (hX.trans (hT j))
 have hf(o):z ≤ T o:= hy.trans (hT o); have hk(o):0 < E' (T o):=(Z'.me _ (hf o)).1
 have hg(i u:ℕ)(w:i≤u): T i ≤ T u:= fast_β _ _ _ _ w
 have hx(i u:ℕ)(w:i≤u):E' (T u) ≤ E' (T i):=((Z'.me _ (hf i)).2 _ (hg _ _ w)).1
 have hQa(u:ℕ)(p:u≤t)(i v:ℕ)(w:i≤v): QW u (T v) ≤ QW u (T i):=((Q i).2.2.2.2.2.1 (⟨u,by omega⟩:Fin (t+1))).2 _ (hg i v w)
 have hp':0 ≤ Yt yl:= (Q l).1.2.1; have hJ:k≤l:=Nat.le_add_right ..; have hl:l<L:=by unfold L trunkY; unfold l; omega
 let Jℝ(u):=(1/2:ℝ)^(l-u)*Yt yl;
 have he(u:ℕ)(s:u≤l):Dk u=max (E' (T u)) (Jℝ u):=if_neg (not_lt_of_ge s)
 have hc(u:ℕ)(s:u ≤l):Dk u ≤ Eψ (T u):=by
    rw [he u s]; apply max_le ((Q u).2.1.2.1); exact (mul_le_of_le_one_left hp' (pow_le_one₀ (by norm_num) (by norm_num))).trans (((Q u).1.2.2.1 _ (hg _ _ s)).trans (Q u).2.1.1)
 have ht'(u:ℕ)(p:u≤l):0 < Dk u:=by rw [he u p]; exact (hk _).trans_le (le_max_left ..)
 have hx_d(u:ℕ)(p:u ≤k): Dk u= E' (T u):=by
    rw [he u (le_trans p hJ)]; have h': Jℝ u ≤ Jℝ k:=mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le_sub_left p _)) hp'
    have hu:= tK.2; change (1/2:ℝ)^j * Yt yl≤_ at hu; have hv: Jℝ k ≤ E' (T k):=by unfold Jℝ l k post_H; rw [Nat.add_sub_cancel_left]; exact hu
    exact max_eq_left (h'.trans (hv.trans (hx u k p)))
 let R_(u:ℕ)(r:ℝ):Prop:= Duty V a p i N0 J q h (S u) (G u) (T u) r (P_ u) (Dk u) (Dk (u+1)) (Z u) (sp u) (sp (u+1))
 have hcκ(u:ℕ):∃ θ:ℝ,0<θ∧ (u<k→ θ=R0 (T u))∧ (u<L→ R_ u θ):=by
    by_cases g:u<k
    · obtain ⟨p,t,w,s⟩:=(Q u).2.2.2.2.2.2.1; refine ⟨_,p,fun _=>rfl,fun z=>?_⟩
      unfold R_ P_ mode_D Z sp tide_W zone_F; rw [if_pos g,if_pos g,if_neg (by omega:¬l<u),if_neg (by omega:¬l<u+1),hx_d u g.le,hx_d _ g]; -- DHz swap
      apply Duty.weakX _ _ _ _ _ _ _ _ (s (hf u) (S u) (G u)) le_rfl (hx u (u+1) (by omega)) le_rfl (le_of_eq ?_) -- wrong field notation names / congr orientation
      exact swap_hrt ..
    by_cases z':u<L; swap; · exact ⟨1,zero_lt_one,fun m=>False.elim (g m),fun q=>False.elim (z' q)⟩
    
    by_cases p':u< l
    · obtain ⟨tX,uℓ,νℝ⟩:= (Q u).2.2.1 (Dk (u+1)) ⟨(ht' _ p').le,(hc (u+1) p').trans ((Q u).2.1.2.2.2 _ (hg u (u+1) (by omega)))⟩
      refine ⟨_,uℓ,fun p=>False.elim (g p),fun q=>?_⟩; unfold R_ P_ sp Z zone_F tide_W mode_D; rw [if_neg g,if_neg g,if_neg (by omega:¬ l<u),if_neg (by omega : ¬ l<u+1)]; apply Duty.weakX _ _ _ _ _ _ _ _ (νℝ (S u) (G u)) le_rfl le_rfl _ le_rfl -- fix
      rw [he _ p'.le, he _ p']; have hh: Jℝ u = 1/2 * Jℝ (u+1):=by unfold Jℝ; rw [show l-u=l-(u+1)+1 from by omega, pow_succ]; ring
      have hφ:= hx u (u+1) (by omega); change 1/4* _+1/4* E' (T u) ≤_; rw [hh]
      by_cases h: 1/2*Jℝ (u+1)≤ E' (T u)
      · rw [max_eq_left h]; by_cases hx: Jℝ (u+1) ≤ E' (T (u+1))
        · rw [max_eq_left hx]; linarith [hk u]
        rw [max_eq_right (le_of_not_ge hx)]; linarith [hk u]
      rw [max_eq_right (le_of_not_ge h)]; by_cases ht: Jℝ (u+1) ≤ E' (T (u+1));
      · rw [max_eq_left ht]; linarith [hk u]
      rw [max_eq_right (le_of_not_ge ht)]; linarith [hk u]

    by_cases s:l=u
    · subst u; refine ⟨_,(Q l).1.1,fun p=>False.elim (g p),fun q'=>?_⟩; have hi:Dk (l+1)= QW 0 (T (l+1)):=by unfold Dk table_B; rw [if_pos (by omega:post_H j<l+1),Nat.sub_self]
      -- have hv:= (Q l).1.2.2.2 -- (?? wV includes `(0≤F∧... ) ∧ step`, inspect.)
      unfold R_ P_ sp Z zone_F tide_W mode_D; rw [if_neg g,if_neg g,if_neg (by omega:¬l<l),if_pos (by omega:l<l+1), hi,Nat.sub_self]; have hl':Yt yl ≤ Dk l:=by rw [he l le_rfl]; unfold Jℝ; rw [Nat.sub_self,pow_zero,one_mul]; exact le_max_right ..
      exact Duty.weakX _ _ _ _ _ _ _ _ ((Q l).1.2.2.2 (S _) (G _)) le_rfl (hQa 0 (by omega) _ _ (by omega)) hl' le_rfl
    have hz:l<u:=by omega
    refine ⟨1,zero_lt_one,fun p=>False.elim (g p),fun m=>?_⟩
    let a':=u-(post_H j+1); have hvB: a'<t:=by unfold a'; change u<post_H j+1+t at m; change post_H j<u at hz; omega
    have h:= (Q u).2.2.2.1 _ hvB (S u) (G u) a'; unfold R_ P_ Z sp zone_F tide_W mode_D; -- unfold order
    rw [if_neg g,if_neg g,if_pos hz,if_pos (by omega:l<u+1)]
    unfold Dk table_B; rw [if_pos hz,if_pos (by omega : l < u+1),show u+1-(post_H j+1)= a'+1 from (by unfold a'; change post_H j < u at hz; omega)]
    exact Duty.weakX _ _ _ _ _ _ _ _ h le_rfl (hQa (a'+1) hvB _ _ (by omega)) le_rfl le_rfl
 choose Jx hJt hyU mℝ using hcκ; have hβ:Vale.billX R.L≥0:= pitch R.L; have hzJ:= (Q L).2.2.2.2.2.2.2; refine ⟨Jx,Dk,⟨hJt,?_ ,?_ ,mℝ,?_ ,hyU,hx_d,?_ ,tK.1⟩⟩
 · intro u; unfold wage_B; split; exact half_pos (billx_T V); exact Real.sqrt_pos.mpr hzJ
 · intro u t'; unfold wage_B mode_D; split; next p=> exact (Q u).2.2.2.2.2.2.1.2.2.1
   next p=> exact Real.sqrt_le_sqrt (add_le_add_left (hg _ _ t'.le) _)
 · intro i t m; unfold zone_F at m; split at m; simp at m; exact ht' i (by omega)
 have hd:L-(post_H j+1)= t:=by unfold L trunkY; omega
 have he:Dk L = Fp (T L):=by unfold Dk table_B; rw [if_pos (show post_H j<L from hl),hd,τW.atK] -- tune
 rw [show trunkY j t=L from rfl,he]; exact (Q L).2.2.2.2.1
end YM.CF.Py
