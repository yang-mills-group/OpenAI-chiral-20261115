import YM.SU5.SatinWard.Resolution.Stage
import Anomaly.Hop.Pages
import Anomaly.Hop.Paver
import SatinThinScale
-- extends SatinThinSkyline.computed_rc to full Ward aperture arities


set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
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
open Mew Waxy Roots Rive Oise


/- The HOT lens estimate is affordable even *at* all these final hills. -/
open Fief
variable (C:ℝ)(R:Patch)(v:1≤ C)
local notation "q"=>allotΨ R.L
local notation "b"=>radiusB
local notation "ϑ"=>(1/256:ℝ)
private lemma size_exp_full (n:ℕ) : sizeK R.L (2*(n+1)) (fun x:ℝ=> Real.exp (-(1/256:ℝ)*(radiusB x:ℝ))):=by
 let k:= (1/256:ℝ)/((n:ℝ)+1); have he:0<k:=by unfold k; positivity
 apply ((sizeK.tip R.L k he).square (n+1)).cost_d; filter_upwards with x; rw [abs_of_pos (Real.exp_pos _)]
 refine le_trans ?_ (le_abs_self _); unfold tipPay; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; push_cast; have ht:(↑(radiusB x/60):ℝ) ≤ (radiusB x:ℝ):=by exact_mod_cast (Nat.div_le_self (radiusB x) 60)
 rw [show (↑n+1:ℝ)* (-(k)*(↑(radiusB x/60:ℕ):ℝ))= -(1/256:ℝ)*(↑(radiusB x/60:ℕ):ℝ) from (by unfold k; field_simp)]; linarith
include v
lemma energyRoom (f:ℕ):∀ᶠ x:ℝ in atTop,Nice_B (radiusB x) f (C*(allotΨ R.L x)⁻¹) (1/8):=by
 let G(x:ℝ):= Real.exp (-ϑ*b x)
 have h:sizeK R.L (2*f+1) (fun x:ℝ=> (2*C)^f*G x):=((size_exp_full R f).scale ((2*C)^f)).low (by omega)
 have hx:0<C:=zero_lt_one.trans_le v
 obtain ⟨u,w⟩:= eventually_atTop.mp (tear_r (15^4:ℝ) ϑ 8 (by norm_num))
 let p':= Work.E01.radiusB_tendsto
 have hg:= (pill_R _ (k:=2*f) (d:=1) (by norm_num) h) -- tune order
 filter_upwards [hg,p'.eventually (tear_r (3^4:ℝ) ϑ 12 (by norm_num)),p'.eventually_ge_atTop u,p'.eventually_ge_atTop 1,(pal_U R.L 0 le_rfl)] with x g vK e hz hi m pm
 let B:= b x; have hs:0<q x:=by simpa using hi.1
 let P:= C*(q x)⁻¹; let K:= (2*P)^f; have hK:0 ≤ K:= by unfold K P; positivity
 have hk:K ≤ Real.exp (ϑ*B):=by
    have hl:G x=(Real.exp (ϑ*B))⁻¹:=by unfold G; rw [neg_mul,Real.exp_neg]
    change _<1*Scales.g SU.group R.L x^(2*f) at g
    have H: (2*C)^f/ Real.exp (ϑ*B) ≤ (q x)^f:=by
       rw [div_eq_mul_inv,←hl]; refine g.le.trans_eq ?_; unfold allotΨ; rw [pow_mul,one_mul]
    unfold K P; rw [←div_eq_mul_inv,←mul_div_assoc, div_pow, div_le_iff₀ (pow_pos hs f)] -- tune mul_div_assoc orientation
    exact (div_le_iff₀ (Real.exp_pos _)).mp H |>.trans_eq (mul_comm ..)
 let k:=chip_B B m / cape_B B; let T:=pearl (chip_B B m+B); let W:= pearl (cape_B B); have hh:rentP P B m f=T*K*((W:ℝ)*K)^k:=by
    change (T:ℝ)*(W:ℝ)^k*(2*P)^((k+1)*f)=_; rw [Nat.mul_comm (k+1) f,pow_mul]; change (T:ℝ)*(W:ℝ)^k*K^(k+1)=_; rw [pow_succ,mul_pow]; ring
 have hp:0<B:=hz
 have ha: (T:ℝ)*K ≤ Real.exp (2*ϑ*m):=by
    have hv':(T:ℝ)≤ (15:ℝ)^4*(m:ℝ)^8:=by exact_mod_cast pearl_m B m hp pm
    rw [show 2*ϑ*(m:ℝ)=ϑ*m+ϑ*m by ring,Real.exp_add]; exact mul_le_mul (hv'.trans (w m (le_trans e pm))) (hk.trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr pm) (by norm_num)))) hK (Real.exp_pos _).le
 have hv: (W:ℝ)*K≤Real.exp (2*ϑ*B):=by
    have h:(W:ℝ) ≤ (3:ℝ)^4*(B:ℝ)^12:=by exact_mod_cast pearl_y B hp
    rw [show 2*ϑ*(B:ℝ)=ϑ*B+ϑ*B by ring,Real.exp_add]; exact mul_le_mul (h.trans vK) hk hK (Real.exp_pos _).le
 have H:= mul_le_mul ha (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hK) hv k) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) _) (Real.exp_pos _).le
 refine hh.trans_le (H.trans ?_); have p: (k:ℝ)* (B:ℝ)≤ 6*(m:ℝ):=by exact_mod_cast sev_B B m hp
 rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_monotone; linarith only [p,Nat.cast_nonneg (α:=ℝ) m]
omit v
end YM.CF.QuadClock

namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable (uZ:BladeQ P.R Z W V K)(proofW:∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s<Y.uv k → stockedTap Y Pay kc Γ Tξ nmc m Z V K W s i k)(flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A u:ℝ)

abbrev assets (D:ArmorK) :ℝ:=1+(|duty_Q 6 2* D.delta|+(|D.g0|+(|D.g1|+|D.g2|)))
lemma assets_own (D:ArmorK):1≤assets D ∧ |duty_Q 6 2*D.delta|≤assets D ∧ |D.g0|≤assets D∧|D.g1|≤assets D∧|D.g2|≤assets D:=by unfold assets; split_ands<;> linarith [abs_nonneg (duty_Q 6 2* D.delta), abs_nonneg D.g0,abs_nonneg D.g1,abs_nonneg D.g2]

abbrev Asteroid (k:Teller SU.group) (T:Hove.Grant k.j 2)(Pay kc Γ:ℝ) : ArmorK := works_X (K:=k) T 0 6 5 HI Pay kc Γ
local notation "Dψ" => Asteroid P.K Tξ Pay kc Γ
abbrev FundsUp (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(Γ:ℝ)(D:ArmorK)(m:ℕ)(F:ResolutionFrame ι)(η:Type)[Fintype η](C H A u:ℝ)(Z V K W :ℝ→ℝ)(s i k:ℕ):Prop:= let x:=hat P.R.L P.x s; let G:=colorsPhi P.R.L Γ x; Whitened (η:=η) P.V P.U (apt (Y.ir i) P.block P.R.L s) (Stem Y i k s) ((Y.voyage i).CapeT s) ((Y.voyage i).CapeT (s+1)) (RootBook Y i k s) (RootBook Y i k (s+1)) (((Y.voyage i).X (Y.uv k)).wave s).val Chi.canonical P.J.d P.h (V x) (K x) (W x) D.delta D.f0 D.g0 D.g1 D.g2 (3*dleaf P.R.L x+G) G (Z x) m (cipherK P.J.n) F C H (lapQ Y (s+1)) (lapQ Y s) u A
local notation "L'" => P.R.L
include uZ proofW flag
lemma fundsUp (HU:assets Dψ≤ H)(hp:F.Stretch C)(hv:RepositoryRent F C H A L')(hA:1≤A)(he:2*A*(m:ℝ)+1≤ u) (η:Type)[Fintype η] : ∀ᶠ s:ℕ in atTop,∀ᶠ i in atTop,∀ k,s+1<Y.uv k→(Y.voyage i).kick ≤ k → FundsUp Y Γ (Asteroid P.K Tξ Pay kc Γ) m F η C H A u Z V K W s i k:=by
 let L:=L'; let Q:=Dψ; let f:=foyerCap (ResolutionFrame.Primary ι η) L; have hF:1≤f:=le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg (Fintype.card (ResolutionFrame.Primary ι η))) (mul_nonneg (sprint_pos L).le (by norm_num)))
 let e:=min 1 (ResolutionFrame.nullLoss L/2); have p: 0<e:= lt_min zero_lt_one (half_pos (ResolutionFrame.null_pos ..))
 let q:= allotΨ L; have hm:Tendsto q atTop (𝓝 0):=((size_ψ L).low (k:=1) (by omega)).spine
 let t₀:= turnover P; filter_upwards [proofW, (tendsto_add_atTop_nat 1).eventually proofW, frameCredit Y flag, layQ Y Γ 0, layQ Y Γ u, layQ Y Γ A, layQ Y Γ (Real.exp 1*A),layQ Y Γ (Real.exp 1*(2*Moto.peka_H 2)*A),t₀.eventually (nut_V e f hF p m _ _ _ _ uZ), t₀.eventually (energyRoom f P.R hF m), t₀.eventually (hm.eventually (ge_mem_nhds zero_lt_one)), t₀.eventually (uZ.mint.spine_a.eventually (ge_mem_nhds (show 0 < f⁻¹ from inv_pos.mpr (zero_lt_one.trans_le hF))))] with s pO T' a b c d B j v K_ q' h
 obtain ⟨Hc,l⟩:=a; filter_upwards [pO,T',l] with i w t ht k u1 t1
 let R:= RootBook Y i k s; let U:=RootBook Y i k (s+1); let D:= (Y.voyage i).CapeT s; let G:=apt (Y.ir i) P.block P.R.L s; let x:= hat P.R.L P.x s; let r:= lapQ Y s; let s':= lapQ Y (s+1); let g:= colorsPhi P.R.L Γ x
 have z':= w k (by omega); let cϵ:=cipherK P.J.n; -- ABI z'. implicit unfolds
 have Z' : JuiceMeter P.V P.U G (Stem Y i k s) D ((Y.voyage i).CapeT (s+1)) R U (((Y.voyage i).X (Y.uv k)).wave s).val Chi.canonical P.J.d P.h (V x) (K x) (W x) Q.delta Q.f0 Q.g0 Q.g1 Q.g2 (3*dleaf L' x+g) g (Z x) (cipherK P.J.n) m := z'
 obtain ⟨gp,hH⟩:=ht k (by omega); obtain ⟨u2,u3,u4,u5,u6⟩:=p_meters Y i k s (by omega)
 have hs:=quarters Y s i k (by omega) t1
 have hu:s'=allotΨ P.R.L (x+billX L'):=by unfold s' lapQ pinpr; rw [hat_succ]; rfl
 have hq:=hu.symm ▸ v.day.1 -- cast careful x
 refine ⟨Z', ?_, ?_, hs.1, hs.2.1, hs.2.2,P.R.odd_side⟩ -- conditional agenda
 · have θ:(r:ℝ)≤1:=q'; have hκ: s'≤r:=hu.symm ▸ v.day.2.1; have hg: r≤ 2*s':=hu.symm ▸ v.day.2.2; have hr: 0<r:=hq.trans_le hκ; have pA:=assets_own Q
   have z:R.p.B=radiusB x:= u2; have ho:R.p.order=6:=u4; have pR:R.p.power=2:=u5; let bR:=R.p.B
   have ht: χCut bR m f (K x)≤r:= (le_abs_self _).trans (((z.symm ▸ v.warp):|χCut R.p.B m f (K x)|≤ e*r).trans (mul_le_of_le_one_left hr.le (min_le_left ..)))
   have hx:Roots.wish_E bR (K x) ≤ r:=by
      have S:0 ≤ Real.exp ((-(1/4:ℝ))*bR)*Roots.KZ:=mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))))
      by_cases h:0 ≤ K x
      · apply ht.trans'; unfold χCut; linarith only [mul_nonneg S h, mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (zero_le_one.trans hF)) h]
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos S (le_of_lt (lt_of_not_ge h))) hr.le
   have hL:0<f:=zero_lt_one.trans_le hF
   have hy:SpindleFinance ι η F C H L R.p U.p A s' r u P.h (K x) (W x) (duty_Q R.p.order R.p.power*Q.delta) Q.g0 Q.g1 Q.g2 (Z x) m:=by
      refine ⟨hq,hκ,hg,θ,P.height,hA,z.symm ▸ v.pitch,?_, ?_,hp,pA.1.trans HU,hv,pA.2.2.1.trans HU,pA.2.2.2.1.trans HU,pA.2.2.2.2.trans HU,Z'.shore.rate.2,Z'.shore.rate.1,he, ?_, ht, hx, ?_, z.symm ▸ v.term, z.symm ▸ K_⟩ -- Tune order of shore.rate
      · apply (show |W x| ≤ e*r from v.pays).trans; have hz:=mul_le_mul (min_le_right 1 (ResolutionFrame.nullLoss L/2)) hg hr.le (half_pos (ResolutionFrame.null_pos ..)).le; exact hz.trans_eq (by ring)
      · rw [ho,pR]; exact pA.2.1.trans HU
      · apply (le_abs_self _).trans; rw [z]; exact v.spool.trans (mul_le_of_le_one_left hr.le (min_le_left ..))
      change f*r⁻¹*K x≤_; rw [mul_right_comm, ←div_eq_mul_inv, mul_div_assoc]; have hv:(K x)/r ≤ f⁻¹:= h; calc
        f*(K x/r) ≤ f*f⁻¹ :=mul_le_mul_of_nonneg_left hv hL.le
        _ = 1:=mul_inv_cancel₀ hL.ne'
        _ ≤ _:= by linarith
   exact hy
 intro J _ _ σ Z φ E K' a T'; obtain ⟨u2,u3,u4,u5,u6⟩:=p_meters Y i k (s+1) u1; rw [zero_mul] at b
 apply passCotton R U _ E K' (F.enterBasis P.h s' ∘ Z) σ T'.notice (fun z g=>T'.cover z g) L (t k u1).chamber P.height gp hH Hc (le_add_of_nonneg_right b) (add_le_add_right c _) (add_le_add_right c _) T'.axis (mul_nonneg (zero_le_one.trans hA) hq.le) d (by rwa [←mul_assoc]) ?_ a
 · rw [show U.p.power=2 from u5]; linarith only [j]
end YM.CF.Py.Rate.LocalLimit.Preparation
