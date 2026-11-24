import YM.CF.BProof.Start.Core
import YM.CF.BProof.Start.Aura

set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark Branch
open scoped Topology BigOperators Classical
open Gates Gates.Stage Gates.Stage.Setup Mapping House
open Stint Tape Hearth Prime Estate Cliff
open Jet Paige Drapes Vault Oasis Bias Weights Cabinet Mint Contour
variable {N:Side}{d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)
variable {m m' L B:Side}{j:ℕ}{a b l r:ℝ}{D:Spin.Ready j a b l r}{u:ℝ}(E:Essence D u)
variable {rₜ a':ℕ}(Δ: Rhythm.Note E (gap L a') rₜ)
variable {p:Odd L.val} {Y:Pricing j L p (Vault.Thread j)} {δ:ℝ}{F:Grasp Y B δ}
variable {E Δ S}{U H:ℝ} (J:Mote S E Δ F U H)
namespace Mote
abbrev μ := Seam.silhouette Δ.clock.extentT E.H.body.val E.H.whole.val -- fails use J not included. tune include explicit
abbrev sizeC (y:ℝ) := cutξ J.z y
abbrev payZ := Estate.wealth J.arc J.A J.C
-- expense move gases. $o'= dleaf$, forecast fixed NEC not from pole. Γ profile validity throughout.
variable (B':ℝ→ℕ)(Fp:ℝ→ℝ)(y:ℝ)(W:ℕ)
abbrev stampFee(y:ℝ) (W:ℕ) := Scene.PHfee 0 (gap L a') J.k (J.sizeC y) W (payZ J) (Real.log (BProof.g y))
abbrev mode := costRoom (d:=gap L a') S J.fuel (J.stampFee y W) W y
abbrev ζg(y:ℝ):= gas_α B' J.oak y
abbrev ζy(y:ℝ):= feeVal B' J.oak Fp y
abbrev ε(y:ℝ):= (BProof.g y:ℂ)
abbrev houseE(y:ℝ) := money_θ D S y (J.sizeC y)+ Rhythm.Lease.wearC S y -- tune
local notation "κζ"=> gap L a'
def demand := wallet y W S.P S.M c R w v S.height κζ (S.focus κζ y) 4+(Scene.qο κζ (B' y) W J.k (Fp y) (ζy J B' Fp y) (J.ζg B' y) + Scene.ζϝ κζ (B' y) J.k (J.sizeC y) W (houseE J y) J.z (Fp y) (ζy J B' Fp y) J.payZ)
abbrev priceA (y:ℝ) := J.payZ+(Cargo.roomAge (B' y) (Fp y+Fp y)+4*(J.ζy B' Fp y))
variable {T:ℝ→ℕ}
include J
lemma budgetClock : NAT (sizeC J):=(tailP J.hp).1
lemma priceShort(p:NAT T): PL (fun y=> Primer.price_short κζ J.k (J.sizeC y) (T y) J.payZ):= PL.mul (rootsBill (U:=fun y=> J.k+J.sizeC y) (V:=T) (PL.const _) (NAT.add (PL.const _) J.budgetClock) p) (PL.const _)
lemma stampPrice(p:NAT T): PL (fun y=>J.stampFee y (T y)):=by
 unfold stampFee Scene.PHfee; apply PL.add ((PL.const _).mul ((PL.const _).mul (J.priceShort p))); unfold Risk.σF; apply (PL.const _).mul; exact PL.mul (rootsBill (U:=fun _=>J.k) (V:=T) (PL.const _) (PL.const _) p) (Gates.log_pl (-1/2) 0 0).abs -- tune ambiguity Risk
lemma housePrice : NPL (fun y=>houseE J y):= (smallMoney (D:=D) S _ J.budgetClock).add (Rhythm.Lease.wearPL S)
variable (pB: NAT B')(pF:NPL Fp)
include pB pF
lemma age_p : NPL (fun y=>Cargo.roomAge (B' y) (Fp y+Fp y)+4*(J.ζy B' Fp y)):= (Oasis.ageN B' _ pB (pF.add pF)).add ((PL.const _).muln (Oasis.fees J.oak pB pF))
lemma demandΩ (pW:NAT T) : NPL (fun y=> demand J B' Fp y (T y)):=by
 let D:=gap L a'; have he:= island (p:=gap L a') (r:=J.k) (t:=0) 0 0 T T (κ:=J.ζg B') pW (αPL J.oak pB) (fun y=>(gas_p B' J.oak y).1) (fun y=>(gas_p B' J.oak y).2.1); unfold demand Scene.qο Scene.ζϝ Primer.WgR; refine ((S.wallet_p T (gap L a') (Gates.GP ..) pW).add ((NPL.add ((age_p J B' Fp pB pF).mulp he) (((PL.const 2).muln ((PL.const 4).muln (Oasis.fees J.oak pB pF))).mulp he)).add (((PL.const _).muln (housePrice J|>.mulp (priceShort J pW))).add ?_))) -- tune Arc h arguments
 exact ((tailP J.hp).2.mulp (PL.const _)).mulp (island (p:=gap L a') (t:=0) 0 0 T T (κ:=fun _=>J.z) pW (PL.const _) (fun _=>J.hp) (fun _=> J.zu))
omit pB pF
lemma weightCore(V:ℝ→ℕ): ∀ᶠ y in atTop,
 (J.mode y (V y)).bias + House.root_port κζ (J.k+J.sizeC y) (V y)*(2*(Primer.expL J.z (J.sizeC y)*J.payZ)) ≤ J.fuel/64*(V y:ℝ)^3:=by
 let f(y:ℝ):=(((κζ+2*(J.k+J.sizeC y)+1:ℕ):ℝ)) * (2*(Primer.expL J.z (J.sizeC y)*J.payZ)); have ht:NPL f :=by
    unfold f; push_cast; apply PL.muln; exact ((PL.const _).add ((PL.const _).mul ((PL.const _).add J.budgetClock))).add (PL.const 1); exact (PL.const _).muln ((tailP J.hp).2.mulp (PL.const _))
 filter_upwards [ht.limit.eventually (ge_mem_nhds (div_pos J.fuel_p (by norm_num): 0<J.fuel/128))] with y hy
 dsimp only [mode,costRoom,biasW]; unfold f at hy; unfold House.root_port; push_cast at *; nlinarith only [mul_le_mul_of_nonneg_right hy (show 0 ≤ (V y:ℝ)^3 from by positivity)] -- potential shadow notation
end Mote
end YM.CF.BProof.Start
