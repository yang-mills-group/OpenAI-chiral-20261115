import YM.SU5.SatinWard.Resolution.Domic
import YM.SU5.SatinWard.Resolution.Chalice
import YM.SU5.SatinWard.Resolution.Costaria
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Tapestry
open SlabMark Papal Papal.Moon Papal.Moon.Moonlit SwitchC Garland Terrace Juniper
namespace CasaF
-- Move algebra availability Cover.Publish literal movement all fixed scale. No covariance assertion after precise cost? Tapestry launch supplies.
open QuadClock Preparation.Tabletop Fock -- remove unsupported
open Vacancy
open SignSlot ShapeLab StressFlux Tap Vacancy
variable {J:Calibration}(t:Axis)(A:Op SU.Slot)(x:Cover)
-- winding cancellation under charge-free shifts and mirrors. non-selfadj under reflection? keep sign.Still analytic.
namespace Signboard
variable (g:ChiralX 0 A)
local notation "Q_" x:max=> SignSlot.gardenFlower J x t A
include g
local notation "S✲" i:max=>SignSlot.onsiteSensor i (Tap.petal t ⊗ₖ A)
lemma mirrorE (i:Axis)(d:ℤ) : mirror J i d (gardenFlower J x t A)=StressFlux.sign (Signed.mirror i) t • gardenFlower J ((plane i d).flee x) t A:=by
 funext n; let N:= J.c n; let T':= fun (v:Axis) (x:Site N)=> SignSlot.onsiteSensor x (Tap.petal v⊗ₖ A); have ht:Dirfield N T':= ⟨fun s p a b w i=>spin_shift s i A g.herm _ _ w p⟩; change reflMark i d (T' t (wrap N x))=StressFlux.sign (Signed.mirror i) t • T' t _; rw [← Shape.mill]; exact ht.tagged _ _ _ _ ((gardenShot J t A x).support n |>.mono (subset_univ _))
lemma horizonEntry :Domicile 0 (fun x=> SignSlot.gardenFlower J x t A):=by
 refine ⟨fun i=> ((gardenShot J t A i).widen).mono (Finset.singleton_subset_iff.mpr (?_)),fun u n=>gardenPrice t A g.color _,fun i j d=> ?_⟩
 · apply (pav_v ..).mpr; simp
 let p:=StressFlux.sign (Signed.mirror j) t; let q:=plane j d; let z:=(plane j 0).flee i
 have ht: q.flee z=i+d • step j:=by
    funext a; by_cases h:a=j; · subst a; simp [flee_pos, z,q]; omega
    simp [z,q,flee_pos,h, Ne.symm h]
 unfold Tower.chime; rw [mirrorE t A i g j 0, show mirror _ j d _=p • mirror _ j d (Q_ z) from ?_,mirrorE]; change p • (StressFlux.sign (Signed.mirror j) t • Q_ (q.flee z))= Q_ (i+d • step j); rw [ht,smul_smul, show p*StressFlux.sign (Signed.mirror j) t=1 from by unfold p StressFlux.sign; split_ifs <;> norm_num,one_smul]
 · exact g
 unfold z p; simp_rw [← Complex.coe_smul]; exact funext fun i=>funext fun v=>by unfold mirror reflMark; simp only [Pi.smul_apply,theta_smul,Complex.star_def,Complex.conj_ofReal]
-- projected first-generation test later. literal fields.
omit g
abbrev rungLeaf (K:Calibration)(x:ℝ) (t:Axis)(θ:Wage3): Cover→ Family K:= (x:ℝ) • (fun o=>gardenFlower K o t (dynamicSpin (ShapeLab.leg θ)))
variable (s i:ℕ) (X:ℝ)
lemma rungD (θ:Wage3):Domicile 0 (rungLeaf J X t θ):=by apply Domicile.tinted _ (horizonEntry ..); exact (Θc.equivFun.symm (ShapeLab.leg θ)).property
lemma billRun (θ:Wage3): InTest J false {nodeC x} false (rungLeaf J X t θ x):=by simp_rw [rungLeaf,← Complex.coe_smul]; exact (gardenShot ..).smul _
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
lemma relic (θ:Wage3): exhibit Y H s i (rungLeaf (tent Y H) (vigorΩ Λ s) t θ x)= spinClass Y s i t θ (wrap (side Y i s) x):=by
 let v:=vigorΩ Λ s; let N:=side Y i s; let U(n:Side):=SignSlot.onsiteSensor (wrap n x) (petal t⊗ₖ dynamicSpin (ShapeLab.leg θ)); have he{n m:Side}(h:n=m):arrange n m h (v • U n)=v • U m:=by subst n; rfl
 exact he (terrain Y H (Y.ir i) s)
noncomputable def spineField (Λ:Preparation)(J:Calibration)(s:ℕ)(t:Axis): Coords Wage3 →ₗ[ℝ] (Cover→Family J):= ShapeLab.columns (rungLeaf J (vigorΩ Λ s) t)
local notation "v!"=>spineField Λ J s t
lemma letterShape(c: Coords Wage3): Domicile 0 (v! c):=by unfold spineField; rw [ShapeLab.cols_apply]; apply Domicile.count; exact fun i _=> Domicile.tinted _ (rungD ..)
lemma run_bill(c: Coords Wage3)(x:Cover): InTest J false {nodeC x} false (spineField Λ J s t c x):=by unfold spineField; rw [ShapeLab.cols_apply,Finset.sum_apply]; apply InTest.sum; intro i _; simp_rw [← Complex.coe_smul]; exact (billRun ..).smul _
lemma spinogram (c:Coords Wage3): exhibit Y H s i (spineField Λ (tent Y H) s t c x)= ShapeLab.columns (spinClass Y s i t) c (wrap (side Y i s) x):=by
 unfold spineField; rw [ShapeLab.cols_apply, Finset.sum_apply,ShapeLab.cols_apply, Finset.sum_apply,map_sum]; apply sum_congr rfl; intro j _; simp only [Pi.smul_apply]; calc
    _=(c j:ℂ) • exhibit Y H s i (rungLeaf (tent Y H) (vigorΩ Λ s) t j x):=by rw [←map_smul,Complex.coe_smul]; rfl
    _=_:=by rw [relic,Complex.coe_smul]
#print axioms spinogram
end Signboard
end CasaF
end YM.CF.Buffered.Afterglow.Tower
