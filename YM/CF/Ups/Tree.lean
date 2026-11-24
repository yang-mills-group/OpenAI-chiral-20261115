import YM.CF.Song.Lune
import YM.CF.Sere.Teen
import YM.CF.Beau.Merc
import YM.CF.Hype.Whorl
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
variable {r:ℕ}
variable (w':Hive.Vista U Y.J.M Y.J.P P_ (k+2) M.q ((Fintype.card Play:ℝ)*t) M.lot M.tone)
variable (V_:ℝ)
local notation "Φ"=> F.hat R x
variable(Y1: Monk SU.group S)
-- Rflare independent of Y except Bravo, discounted pref before.All
variable {a A' ε b α γ:ℝ}{q q':Chi}{u u0 s:ℝ}(ε':Fend V H M Z F q Y.p X.p γ α j l r)
variable{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}(D_: Girt.BaseL U G Y G₀ G₁ q' u)(L0: StageP V H Y X U)
variable (k₀ k₁:ℕ)(s0:ℝ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x)(pV:1<I.fine)(k_W:5*Y.p.B +4≤10*radiusB x)(η':l≤18)(ss:s ≤ s0)(tK:s0 < d)(hT:0 < s) (pT:0<u)(hU:u< firstRadius SU.group)
variable (Uq:(j+110)*radiusB x+14 ≤ r) (pQ:2*((j+5)*radiusB x) ≤ r)(ht:0 ≤ V_)(hY:Y.p.order=k)(pX:X.p.order=k)(hK:radiusB x ≤ X.p.B)
variable (P_B:Stake.PondP V F x s u j l (k+2)) (K0: Troupe S r (Words S))(P0: Eire.Ride S)
open Plume
open Nor
variable {c vL:ℝ}(Pz: Folk S r (Words S)→ Track (Eire.Ride S) ℝ)
open scoped Classical
variable {γ':ℝ}
variable (h0:vL=(tolQ X.p).supportExponent+γ')(uQ:X.p.B=radiusB x)(p0:0<γ')
local notation "Ue"=> Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B)))
local notation "Ωe"=> Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B)
-- Ribbon vector measured local Aux Proto.SP.Anchor.Norin. Does not assume vacuum.
open Vow Bake
variable (KcV:Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Raid (LeanV (Single (mid N B))))(F':Troupe S r (Words S) → Palot.leaf (Site (Domain N B)) → Orbit (mid N B) → Cipher (mid N B))(Pinc: GroV V F Z M P_ w' ε' D_ KcV F' V_ c γ')
local notation "Zκ"=> pence_v X.p KcV V_
local notation "Zp"=> cone_f F'
 
variable {vS wS:ℝ}(vs:vS<s)(wp:0<wS)(vw:wS<u)(hB:∀ (Q: Monk SU.group S), ‖Q.z‖≤ F.hat R x→ Chir Q x→ Bell S Q x T H.trot H.room H.post H.beta vS wS)(u_B:3 ≤ X.p.B)
local notation "Fe"=> nixV (cone_f F')
local notation "fE"=> nixV (pence_v X.p KcV V_)
local notation "rK"=> budgetR (roomV X.p (nixV (cone_f F')) (cone_f F') 0)
variable (xv yv:ℝ)(dV:DriveT X.p.B X.p.order X.p.power γ' c xv yv)(tP:1≤V_)
local notation "yp"=> (degreePrice X.p.B xv 1)
local notation "zp"=> (degreePrice X.p.B yv 1)
open Girt Tap Next.Fluctuations.Sector
variable (PR:LocalRatio L)(hb:0<Y.beta)(Hk:X.J.M=upMale R.L R.odd_side Y.J.M)(pL:∀ i:Orbit (mid N B), IsStarProjection (spar K.j X.J.M (G₀ i))) -- material
variable (XvE: RegBudget (mid N B))(Zr:ForceBudget (mid N B))
local notation "Kρ"=> (pulseZ (T:=T) (x:=x) (U:=U) (H₀:=Y) (G:=G) (H₁:=X) Y1)
local notation "Pv"=> (↑(prefactor S G5 Y.beta):ℂ) * (↑((shotM L (F.hat R x) Y.beta)^Fintype.card Y1.park.Free):ℂ) * pulseZ (T:=T) (x:=x) (U:=U) (H₀:=Y) (G:=G) (H₁:=X) Y1
local notation "Γv"=> Pv* Complex.exp Y.v
variable (Lρ:ℝ)(eV:ℂ)(p_e:Complex.exp eV=((prefactor S SU.group Y.beta:ℝ):ℂ)*(((shotM L (F.hat R x) Y.beta)^Fintype.card Y1.park.Free:ℝ):ℂ)*pulseZ (T:=T) (x:=x) (U:=U) (H₀:=Y) (G:=G) (H₁:=X) Y1* Complex.exp Y.v*(Real.exp Lρ:ℝ)) -- unused later
local notation "E'"=> slew_e X XvE Zr eV
variable (Aε:Orbit (mid N B))(dF: Rue.FleetS X.p.threshold Aε.1)
variable (Δ:ℝ)
open Sour Py Haro Vow
variable (kq':QuotaH V.f V.g V.F1 V.F2)(Yk:Op SU.Slot)(Kv:Cusp (mid N B))(hq:EdgeC X.p A_ (hT.trans_le ss) (Py.tatE V kq' (mid N B)) (tagE V kq' (mid N B)) (cone_f F') Kv Yk)(hkq:kq'.2=X.J.M)(pK:(kq'.1 (mid N B)).val=X.J.P) -- no quote
variable (e_K:∀ v:Orbit (mid N B),Rue.FleetS X.p.threshold v.1 → Palot.hGas (flags X.p.threshold v.1) (keyL X.p Kv (fun X=>Kv X ∅) v)=Real.exp (Lρ+enerS_K X Δ v) • (exp (exponentL X.p XvE v.1)*fueled X.p Zr v))
include hq hkq pK A_ A₁ heV ss tK L0 e_K dF Hk pL P_B hT p_e Pinc
set_option maxHeartbeats 600000 in
private lemma treeT : Scree.stove U G₀ Y G₁ G S q' u Yk Aε = Scree.denZ (spark_B X XvE Zr Δ eV) U G₀ Aε:=by
 let k:=spar K.j X.J.M (G₀ Aε); have hv: IsStarProjection k := pL Aε
 let f:=(spark_B X XvE Zr Δ eV); let Zs:= f.board Aε; have he: hGas (flags X.p.threshold Aε.1) (keyL X.p Kv (fun X=>Kv X ∅) Aε)=Real.exp (Lρ+enerS_K X Δ Aε) • Zs:=by
    unfold Zs GramM.board; rw [e_K Aε dF,show f.slip=0 from rfl,Vale.still_Footprint, add_zero] -- tune
 have H0(Is:IsStarProjection (spar K.j (upMale R.L R.odd_side Y.J.M) (G₀ Aε))):= mentor V F Z M P_ w' Y1 ε' D_ L0 k₀ k₁ s0 A_ A₁ heV ss tK hT P_B F' KcV Pinc.quiet Yk Aε Is dF -- order
 have hf':IsStarProjection (spar K.j (upMale R.L R.odd_side Y.J.M) (G₀ Aε)):=by rw [←Hk]; exact hv
 let W:=Real.exp (Lρ+enerS_K X Δ Aε)
 have hy: (nursery k hv).eval (W • Zs).val=(W:ℂ) • tank k Zs:=by change (nursery _ _).eval (W • (Zs).val)=_; rw [←Complex.coe_smul,map_smul , show (nursery _ _).eval Zs.val=tank _ Zs from (tank_eq k Zs hv).symm]
 let Θ:= X.p; let D:=flags X.p.threshold Aε.1; let G00:= (G₀ Aε); let E0:=hGas D (Jade.cargoL X.p F' Aε); let j:= Hive.nest U X.J.P X.J.M G00; let YY:=Kennel.capT k (X.J.P.den G00)
 have hz(C:Cusp (mid N B)): Vow.hailV D C Aε =keyL X.p C (fun i=> C i ∅) Aε:=by
    funext i; unfold keyL; split; next h=> unfold hailV D; rw [Finset.disjoint_iff_inter_eq_empty.mp h]
    rfl
 have h0:Scree.scaleZ Yk (acts (tank k E0) j)=acts (nursery k hv|>.eval (W • Zs).val) j:=by
    rw [tank_eq k E0 hv]; let he':= (A_.paid Aε).shrink tK.le
    have hu:=hq.body Aε dF k YY (changeM U G00 X.J.M) hv (Thera.tag_g _ hv) (Spire.sea_g D_.size G00 he' _) (by unfold k Py.tatE; rw [hkq]; rfl) (by unfold tagE Py.tatE arcB; change Kennel.capT (funde _ kq'.2 _ _) (Moire.bloom _ (Tulip.profile G00))= _; rw [hkq,pK,Moire.bloom_P]; rfl)
    dsimp only at hu; rw [hz Kv,hz (cone_f F'), he] at hu; unfold E0; rw [key_c]; exact hu.symm
 have hf:=H0 hf'; clear H0; rw [show (nursery _ hf').eval _= _ from ((tank_eq _ E0 hf').symm),←Hk] at hf
 have hg(c:ℂ)(x:Scree.Phys (mid N B)):scaleW _ Yk (c • x) = c • scaleW _ Yk x:=by
    rw [ans,ans]; unfold scaleZ; dsimp only; rw [map_smul, smul_comm c]
 rw [map_smul (scaleW _ _),map_smul (scaleW _ _),hg,hg,ans, h0,hy] at hf -- tune h0.T error
 rw [hf]; let J:=Hive.nest U X.J.P X.J.M (G₀ Aε)
 let l:= acts (tank k Zs) J
 change _ = Complex.exp (f.betaL G₀ Aε) • acts (tank k Zs) J
 rw [act_smul, ← Complex.coe_smul,← Complex.coe_smul, smul_smul, smul_smul, smul_smul,smul_smul]; refine congrArg (· • l) ?_
 let w:=X.betaL G₀ Aε-X.v; have hV:f.betaL G₀ Aε=w+eV+ (enerS_K X Δ Aε:ℝ):=by unfold w GramM.betaL GramM.H0; unfold f spark_B slew_e; dsimp only; unfold enerS_K; push_cast; ring
 rw [hV]; unfold W; rw [Real.exp_add,Complex.ofReal_mul]; simp only [Complex.exp_add,p_e,Complex.ofReal_exp]; unfold w; ring
include PR hb Y1
omit eV p_e Aε dF
lemma toTv :∃ eV, Complex.exp eV=Pv * Complex.exp Y.v * (Real.exp Lρ:ℝ)∧∀ Aε:Orbit (mid N B),Rue.FleetS X.p.threshold Aε.1 → Scree.stove U G₀ Y G₁ G S q' u Yk Aε=Scree.denZ (spark_B X XvE Zr Δ eV) U G₀ Aε:=by
 let W:= (Pv)* Complex.exp Y.v; have hW:W ≠ 0:=by
    have ha:0 < shotM L (F.hat R x) Y.beta:=mul_pos (spare_pos _ PR hb) (point_p (enough_r ε'))
    unfold W; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (prefactor_pos _).ne') (Complex.ofReal_ne_zero.mpr (pow_pos ha _).ne')) (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
 let L':=W * (Real.exp Lρ:ℝ)
 exact ⟨Complex.log L',Complex.exp_log (mul_ne_zero hW (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')),fun Aε dF=> treeT V F Z M P_ w' V_ Y1 ε' D_ L0 k₀ k₁ s0 A_ A₁ heV ss tK hT P_B KcV F' Pinc Hk pL XvE Zr Lρ _ (Complex.exp_log (mul_ne_zero hW (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'))) Aε dF Δ kq' Yk Kv hq hkq pK e_K⟩ -- tune Y1 is omitted. include
end YM.CF.Jade
