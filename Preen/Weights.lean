import Preen.Spurt
import Risa.SeedBox
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad
variable (P:Spine) (s:ℕ) (o:Cover)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=>Vale.hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
noncomputable abbrev fellerT:P.Test:= (((θ)^2/P.payday s:ℝ):ℂ) • wp P s o
private lemma overPing{G:Gauge}{s:Side}(r:Signed)(b o:Site s)(Vx:Config G s)(t:ℝ) : Scree.pingS t (Lattice.halo 10 {o}) (Lattice.pull r b Vx) ↔ Scree.pingS t (Lattice.halo 10 {affine r b o}) Vx:=by
 let f:=Face.send r b -- args inspect
 have e:Surjective f:= Finite.injective_iff_surjective.mp (Face.injective_send r b)
 unfold Scree.pingS; simp_rw [Face.send_price Vx _ r b G.chord G.chord_inv (fun i u=>G.chord_conj u _)]
 have hl (i:Face (Per s)): ¬Disjoint (Lattice.halo 10 {o}) (RG.touched i) ↔ ¬ Disjoint (Lattice.halo 10 {affine r b o}) (RG.touched (f i)):=by
    unfold f; rw [Work.H03.touched_send]; constructor
    · intro h; obtain ⟨i,g,hp⟩:=not_disjoint_iff.mp h; obtain ⟨u,he,hu⟩:=halo_spec.mp g; rw [mem_singleton.mp he] at hu; apply Finset.not_disjoint_iff.mpr; exact ⟨affine r b i,halo_spec.mpr ⟨_, mem_singleton_self _,by simpa [affine] using hu⟩, mem_image_of_mem _ hp⟩
    intro h; obtain ⟨i,g,hp⟩:=not_disjoint_iff.mp h; obtain ⟨x,hx,rfl⟩:=mem_image.mp hp; obtain ⟨u,he,hu⟩:=halo_spec.mp g; rw [mem_singleton.mp he] at hu; simp [affine] at hu; apply Finset.not_disjoint_iff.mpr; exact ⟨x,halo_spec.mpr ⟨_,mem_singleton_self _,hu⟩,hx⟩
 constructor
 · intro h i; obtain ⟨v,rfl⟩:=e i; exact fun i=>h v ((hl v).2 i)
 exact fun h i p=>h (f i) ((hl i).1 p)
lemma channel_v (N:Side)(F:Pane N) : guardian SU.group (P.run.meter.a s) (1:Signed) (wrap (More N) (nodeC o)) F ↔ Scree.pingS (V).threshold (lease_H (wrap N o)) F:=by
 rw [← node_of]
 unfold guardian lease_H; rw [overPing,affine,Signed.act_zero,zero_add]
lemma feller_mark (m:Side)(h:0<P.payday s)(U:Fields ((K).c m)) : (fellerT P s o).val m U = ((solicit SU.group (V) (Real.sqrt (Yx)) (1:Signed) (wrap (More ((K).c m)) (nodeC o)) U.1:ℝ):ℂ) • 1:=by
 change ((((θ)^2/P.payday s:ℝ):ℂ)) • (watch P s o m U)=_
 rw [show watch P s o m= cameo (wrap ((K).c m) o) (V) (P.payday s) from lining_at ..]
 unfold cameo tariffB solicit; split
 next e=>
    have hp:= (channel_v P s o ((K).c m) U.1).2 e; rw [if_pos hp,smul_smul]
    let η:=Real.sqrt (Yx); let u:=Cube.node (wrap ((K).c m) o); have hu(i:PlaqAxes):‖_root_.YM.Gleam.Luster.Risa.party SU.group η (1:Signed) (wrap (More ((K).c m)) (nodeC o)) U.1 i‖^2=(Yx)*‖petals U.1 u i‖^2:=by
       have hv:P.par.x ≥1:= (Real.one_le_exp (by norm_num)).trans P.large
       have hx:1 ≤ Yx:= hv.trans (crown ..)
       have he:wrap (More ((K).c m)) (nodeC o)=u:= (node_of ..).symm
       unfold _root_.YM.Gleam.Luster.Risa.party; rw [he,petals_moves,affine,Signed.act_zero,zero_add,show ∀ u:Flux SU.group, reframe u (1:Signed)=u from (fun u=> by funext k; simp [reframe,orderedDir,(show k.val.1<k.val.2 from k.property),not_lt.mpr (show k.val.1 ≤ k.val.2 from k.property.le),StressFlux.sign]),norm_smul,mul_pow,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (zero_le_one.trans hx)]
    unfold naked Inkprice; unfold η at hu; simp_rw [hu]; have hg:0<(Yx):=(by have hp:P.par.x≥1:= (Real.one_le_exp (by norm_num)).trans P.large; exact zero_lt_one.trans_le (hp.trans (crown ..)))
    have he:(V).threshold=Pressure.temp (Yx):=(P.run.meter.boot s).1
    have ht: (Yx)*(V).threshold^2=θ^2:=he.symm ▸ (Gleam.Luster.Almanac.scale_shock hg)
    rw [←Complex.ofReal_mul]; apply congrArg (fun x:ℝ=> (x:ℂ) • (1:FC _))
    let v:=P.payday s
    rw [←ht,Finset.sum_div,Finset.sum_div,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; exact beamA (Yx) (P.payday s) (V).threshold _ _ h.ne' (V).threshold_pos.ne'
 next e=> rw [if_neg (mt (channel_v P s o ((K).c m) U.1).1 e), Complex.ofReal_zero,zero_smul,smul_zero]
where beamA (x p t a b:ℝ)(h:p≠0)(f:t≠0): x*t^2/p * ((p*a/t^2*b^2)/2)= a*(x*b^2)/2:=by field_simp
#print axioms feller_mark
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
