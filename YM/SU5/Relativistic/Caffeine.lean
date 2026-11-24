import YM.CF.Vp929.Stage.Clothes
import YM.CF.Cascade.Sow
/-! # the ART relatives at authorized Hull. exact `retail` includes THIS signed sea flat price. no topology hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
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
open Py.Rate
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L)
open Eire Girt
-- use OrbT value as baseline (rank nonzero and Gram facts later, but always). sign.
def seaPrec (j:ℕ)(n:Side)(M:Tulip.Male) := -OrbT (tickA n) (spar j M (1:Bkg (More n))) 0
private lemma emptyFlag (n:Side)(p:Pride n): Pec.pigment p 1=0:=by
 unfold Pec.pigment lexn zinger Pec.tag; have he(s:Signed):Yg (incX s) (1:Bkg (More n))=1:= by funext i; simp [Yg,stir,Lattice.pull,Step.read] -- tuner
 simp_rw [he,silt_0,inner_zero_right,zero_smul,sum_const_zero,map_zero,sum_const_zero,smul_zero]
variable {d:ℝ}{b m n N M:Side}{U:Grasp V.U b d}{W:GivenX V U}{J:Robes N V W}{q: Chi}
local notation "F0"=> Scree.mid n b
local notation "C0"=> Scree.mid m b
include V
lemma arc_pay : ∀ᶠ x:ℝ in atTop,∀ {m n:Side}{Q:Location (R:=R) b m n}{N0:ℕ}{p p':BudgetPoint},Location.Request V U W J q Q N0 x p p' →∀ {β:ℝ}(hz:β∈Stake.Year R x),
    -(Cour.shipA Q.G U Q.input.M Q.input.P.den Q.input.I Q.output.I 1).re= seaPrec K.j (Scree.mid n b) Q.input.M -seaPrec K.j (Scree.mid m b) Q.output.M:=by
 have he: 1≤K.j:=by have h:=R.order_cut; rw [V.L.lobby] at h; omega
 obtain ⟨j,H⟩:= hol_proj K.j he
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (j+V.W.n+U.roundZ+V.r)] with x hp m n w N0 p p' z β hh
 let G:=w.G; let Vx:= w.input; let Vy:= w.output; let y:=w.lag; let S:= V.L.op y w.sizes; let D:= V.L.path y; let M':=Vx.M
 let hS:=z.statv β 0 0 0 hh; let U':=hS.hunt.cert
 have hn: 100*(1+radiusB x) ≤ (Domain m b).val:=U'.size; have hy:(Domain m b).val≤ (Domain n b).val:= (Nat.le_mul_of_pos_right _ R.L.property).trans_eq w.sizes.symm
 change _ ≤ (mid m b).val*2 at hn; change (mid m b).val*2 ≤ (mid n b).val *2 at hy
 let o:=S.ratio; let f:=Classical.choice (Tree.select o S.patch.odd_side); have h1:S.ratio=ratio G:=hS.hunt.scaleP; let a:=V.L.sold y; have h2:=V.L.sized y w.sizes; have hw: V.W.n ≤ (Domain m b).val:=by change _ ≤ (mid m b).val*2; omega -- tune
 obtain ⟨g,X,P'⟩:= a.existP _ _ h2 hw f
 have hK:Hull K.j R.L R.odd_side V.a V.b V.d d V.r m n b G S f g V.U U:=by
    refine ⟨V.note,w.count,h1,(by change _ ≤ (mid m b).val; omega),(by change _ ≤ (mid m b).val; omega),V.gate,he,V.sp,⟨_,_,_,_,_,_,Classical.arbitrary S.Choices,X,U'.pace.1,V.L.mood _,(a.all _ _ h2 hw _).1,V.W.tame⟩,W.health,V.d_o⟩
 have hs :Ample Vx.P.den:= den_r hS.sound.leanJ.1; have ht:ContDiffAt ℝ ω ((spar K.j M' (N:=mid n b)) ∘ represent) 0:= H _ (by omega) M'
 have hb: ears f g 0= (1:nomA m n b):= Prod.ext hK.native.flat link_one -- remove PecNom
 have hχ:= (shear Vx.P.den hK hs M' ht).self_of_nhds
 rw [hb,hK.native.flat,hK.val M' hs.self,link_one] at hχ; unfold gala Crops at hχ
 rw [hs.self.1] at hχ; unfold capT at hχ; rw [mul_zero,zero_mul] at hχ
 unfold Cour.shipA; simp only [Prod.fst_one,Prod.snd_one,emptyFlag,zero_add,sub_zero,seaPrec] -- tune
 rw [show w.output.M=upMale R.L R.odd_side w.input.M from hS.dose.grown]; change -(Pec.lush G U M' Vx.P.den 1).re = -OrbT (tickA (CSide n b)) (spar K.j M' 1) 0 - -OrbT (tickA (CSide m b)) (spar K.j (upMale R.L R.odd_side M') 1) 0; linarith only [hχ]
end YM.CF.Papyrus.GaugeFlux
