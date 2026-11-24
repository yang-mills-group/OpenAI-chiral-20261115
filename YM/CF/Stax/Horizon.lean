import YM.CF.Stax.Hare
import YM.CF.Sour.Stow
import YM.CF.Stax.Bust
import YM.CF.Pith.Pole
import YM.CF.Stax.Cast
import YM.CF.Sour.Park
import YM.CF.Sour.Tile
import YM.CF.Ione.Tape
import YM.CF.Cadre.Point
import YM.CF.Cadre.Gear
import YM.CF.Vow.Grow
import YM.CF.Bake.Pep
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
open Salt Ione Levier Sour
variable (s:Sweep n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "Pu"=> Palot.robe
local notation "SD"=> Support (More n)
local notation "Πt"=> (boxA s).symm.toEmbedding
local notation "σX'"=> σX (n:=n) P
variable {H:Bag n}(V:Orbit n)(c:Bias δ H P h z)(p:Injective (priorP V.2)) -- tune shadow
variable (hb:∀ i:Orbit n,Injective (priorP i.2)→∀ X:Aura n,H (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (Sour.γS s) (H X i))
local notation "M"=> Cadre.chip (Bias.payX c) F
local notation "M'"=> nutL (Bias.payX c) F
local notation "Λ"=> Ione.suit_Y s
local notation "W'"=> yellA s V
variable (e:∀ X:Aura n,∀ D⊆X.val,F (moldA s X) (actY s D) (yellA s V)= Ione.suit_Y s (F X D V))
variable {m:ℕ}
lemma sail_l(X:Aura n)(D:SD): visible P X.val D V.1↔visible P (Tu X).val (Ta D) (W').1:=by
 have hv(s:Sweep n)(V:Orbit n)(X Z:Support (More n))(p:visible P X Z V.1):visible P (actY s X) (actY s Z) (yellA s V).1:=by
    obtain ⟨i,l,t⟩:= p; have hl:= (Salt.glowA P.threshold (X\Z) s i).mpr l -- orientation
    exact ⟨flashA s i,(show actY s (X\Z)=_ from Finset.map_sdiff ..) ▸ hl,(yellow s V (i,V.2) X t (fun _ _=>rfl)).1⟩
 constructor; exact hv s V _ _; intro p; have he:= hv s⁻¹ W' _ _ p -- tune
 change visible P (actY s⁻¹ (actY s X.val)) _ (flashA s⁻¹ (flashA s V.1)) at he; rw [revB, tape_C,tape_C] at he; exact he
variable (l:3 ≤ P.B)(w_:1 ≤ h)
include hb c p e l hF w_
lemma cloudT (X:Aura n)(D:SD)(u:D⊆ X.val)(hz:Aqua (Nd X D)): rem_X (P:=P) F c.payX (Tu X) (Ta D) W'=Λ (rem_X (P:=P) F c.payX X D V):=by
 have hp:= hz.of_norm; let Tk(i:ℕ):= coeff i (M' X D) V; have H':= c.buys l (zero_le_one.trans w_)
 unfold rem_X Vow.lasting Vow.zenS; rw [← sail_l]; split_ifs with v; swap; exact (map_zero _).symm
 have hv:Summable Tk:=lend (fun i=> (deck F r hF c.payX z H' (zero_le_one.trans w_) X D u i).merit) hp w_ V v
 let L:=(suit_Y s).toLinearMap.toContinuousLinearMap; change _=L (∑' i,Tk i); rw [L.map_tsum hv]; exact tsum_congr fun i=> nut_k F z s V c p hb e X D i u
lemma lightC(X:Aura n)(D:SD)(u:D⊆ X.val)(hz:Aqua (Nd X D)): lamp (P:=P) F c.payX (Tu X) (Ta D) W'=Λ (lamp (P:=P) F c.payX X D V):=by
 unfold lamp; simp only [Pi.add_apply,map_add]; rw [bark F z s V c p hb e _ D u, cloudT F r hF z s V c p hb e l w_ X D u hz,e X D u] -- tune
omit hb c p e l hF w_
-- clean.SII.Tire. pointwise x even if orientation requires inj
variable (hs:∀ X Y:Aura n,X.val⊆Y.val→∀ V:Orbit n,V.1∈ σX P Y ∅→∀ i:Ids n,H X (V.1,i)=H X V)
include c hs
variable (U:Ids n)
lemma opva(X Y:Aura n)(F G:Copy n)(t:F (V.1,U)=G V): c.payX X ∅ Y F (V.1,U)= c.payX X ∅ Y G V:=by
 by_cases u:Bias.αt Y X ∅ δ; swap; · unfold Bias.payX; rw [dif_neg u,dif_neg u]; rfl
 apply Subtype.ext; rw [c.truth _ _ _ _ u _, c.truth _ _ _ _ u _,t]; congr 2; unfold coll_T; split_ifs with k; swap; · rfl
 let W:=gloss P X ∅ V; have hp:= (pillar X.val (open_l P.threshold X.val (∅:Support (More n)))).choose_spec.2 V.1|>.2 k
 exact hs Y X u.1 W hp U -- tune gloss def
variable (h0:∀ X: Aura n,F X ∅ V=F X ∅ (V.1,U))
include h0
lemma clean_p(X: VX)(i:ℕ):coeff i (M X ∅) V=coeff i (M X ∅) (V.1,U):=by
 induction i using Nat.strong_induction_on generalizing X with |h i ih=>
    cases i with
    |zero=> rw [Cadre.peg]; exact h0 X
    |succ i=>
       have hv(X:Aura n):coeff (i+1) (M X ∅)=((i:ℝ)+1)⁻¹ • coeff i (Cadre.stepL c.payX M X ∅):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       rw [hv]; rw [Pi.smul_apply, Pi.smul_apply, Cadre.ore, Finset.sum_apply,Finset.sum_apply]; apply congrArg; apply sum_congr rfl; intro j _; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro G v; symm; apply opva z V c hs U; rw [coeff_prod,Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro y w; rw [Finset.prod_apply, Finset.prod_apply]; apply prod_congr rfl; intro m q; rw [empty_inter]; exact (ih (y m) (Nat.lt_succ_of_le (le_trans (single_le_sum (fun i _=>Nat.zero_le (y i)) q) ((mem_finsuppAntidiag.mp w).1.le))) m).symm
lemma clean_l(X:Aura n):lamp (P:=P) F c.payX X ∅ V=lamp (P:=P) F c.payX X ∅ (V.1,U):=by
 have he:(birthL c.payX X ∅ V)=birthL c.payX X ∅ (V.1,U):=by simp only [birthL,ite_true]; exact (opva z V c hs U X X 1 1 rfl).symm
 have hv:(∀ Y T X,c.payX Y T X 0=0):=by -- don't assume.L binds Ward. always
    intro Y T X; unfold Bias.payX; split; next v=> exact funext fun i=>(c.scope _ _ _ v.1 v.2.1 v.2.2).toCrate.lit0 _ _ rfl
    rfl
 have hx(i:ℕ): coeff i (M' X ∅) V= coeff i (M' X ∅) (V.1,U):=by
    have hp:=clean_p F z V c hs U h0 X i; rw [Cadre.park _ _ _ _ hv] at hp; rw [map_add,map_add,coeff_C,coeff_mk] at hp; simp only [Pi.add_apply] at hp
    unfold birthL at he; rw [if_pos rfl] at he; split_ifs at hp <;> first|simpa only [Pi.zero_apply,h0,he,add_right_inj] using hp
 unfold lamp; simp only [Pi.add_apply]; rw [h0,he]; congr 1; unfold rem_X Vow.lasting zenS; split; exact tsum_congr hx; rfl -- tune
end YM.CF.Stax
