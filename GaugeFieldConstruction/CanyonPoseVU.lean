import GaugeFieldConstruction.GlacierVU
import GaugeFieldConstruction.CaneVistaN
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
open SignetS Patrons ChSigFe
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
variable (P:Spine)(R:Set (Points 2))(r:ℝ)(U:IsOpen R)(v: ZodiacVU r∈R)
noncomputable abbrev PortsVU (x y:Vantage):= PinsVU (WithLp.toLp 2 x) (WithLp.toLp 2 y)
lemma PortCΓvU: Continuous (fun p: Vantage×Vantage=>PortsVU p.1 p.2):=by
 apply (PiLp.continuous_toLp 2 _).comp
 apply continuous_pi; intro i; fin_cases i; exact (PiLp.continuous_toLp 2 _).comp continuous_fst; exact (PiLp.continuous_toLp 2 _).comp continuous_snd
abbrev NegativeBankVU:Set Vantage:= {x|x 3<0}
abbrev PositiveBankVU:Set Vantage:= {x|0<x 3}
-- points strictly negative positive at axis & positive separations; remain inside Pane.
include U v
lemma TenderPortVU (d:0<r): ∃ x y:Vantage,x∈NegativeBankVU∧ y∈PositiveBankVU∧PortsVU x y∈R∧∀ i:Axis,x i<y i:=by
 let L:Vantage:=(RhoExtVU r).ofLp; let Y(t:ℝ):Vantage:=fun i=> L i+t; let X(t:ℝ):Vantage:= -Y t
 have he:∀ᶠ s in 𝓝[>] (0:ℝ),PortsVU (X s) (Y s)∈R:=by
    have hY:Continuous Y:= continuous_pi fun i=> continuous_const.add continuous_id
    have hP:Continuous (fun t=> PortsVU (X t) (Y t)):= PortCΓvU.comp (hY.neg.prodMk hY)
    have ht:Y 0=L:=funext fun i=> add_zero ..
    have hz:PortsVU (X 0) (Y 0)=ZodiacVU r:=by change PortsVU (-(Y 0)) (Y 0)=_; rw [ht]; rfl
    exact (hP.continuousWithinAt (s:=Set.Ioi (0:ℝ))) (U.mem_nhds (show PortsVU (X 0) (Y 0)∈R from hz.symm ▸ v))
 obtain ⟨s,a,b⟩:= (he.and self_mem_nhdsWithin).exists
 have ht(i:Axis):0<Y s i:=by
    apply add_pos_of_nonneg_of_pos _ b
    unfold L RhoExtVU; by_cases p:i=0 <;> simp [p] <;> linarith only [d] -- tune Ne.symm wrong
 exact ⟨X s,Y s, neg_lt_zero.mpr (ht 3),ht 3,a, fun i=> lt_trans (neg_lt_zero.mpr (ht i)) (ht i)⟩
lemma ProvinceVU (p:0<r) : ∃ (A B:Set Vantage)(x y: Vantage)(ε:ℝ)(σ:Fin 2→ PermWallJ P),0<ε∧x∈A∧ y∈ B ∧ IsOpen A∧IsOpen B∧ IsCompact (closure A)∧IsCompact (closure B)∧ A⊆NegativeBankVU ∧ B⊆PositiveBankVU ∧ BundlesΝ A B ε∧ ScopeL2N A B σ∧ ∀ x'∈A,∀ y'∈ B, PortsVU x' y' ∈ R :=by
 obtain ⟨X,Y,x',y',e,d⟩:= TenderPortVU R r U v p
 have ht:Pointers2N X Y∈MasksR _:=by
    intro j i l h; fin_cases i<;>fin_cases l<;>first| exact rfl| exfalso
    exact (d j).ne h; exact (d j).ne h.symm
 have hf:jNDuo.Pairwise (fun i i' => Pointers2N X Y i 3 < Pointers2N X Y i' 3):=by change ([0,1]:List (Fin 2)).Pairwise _; simp; exact d _
 obtain ⟨s,h⟩:= (OpenPatR _ _ P 3 hf).exists
 obtain ⟨A',B',Δ,bW,z₀,z₁,k₀,k₁,tA,tB,u,a⟩:= RangeScopeΝ d _ ⟨ht,h⟩
 let K:Set (Vantage×Vantage):= (fun p: Vantage × Vantage=> PortsVU p.1 p.2)⁻¹' R
 obtain ⟨C,t,N,f,j⟩:= mem_nhds_prod_iff.mp ((show IsOpen K from U.preimage PortCΓvU).mem_nhds (show (X,Y)∈K from e))
 obtain ⟨A,uA,iA,hA⟩:= _root_.mem_nhds_iff.mp (inter_mem (inter_mem (z₀.mem_nhds tA) t) ((isOpen_lt (f:=fun p:Vantage=> p (3:Axis)) (continuous_apply _) continuous_const).mem_nhds (show X 3<0 from x')))
 obtain ⟨B,uB,iB,hB⟩:= _root_.mem_nhds_iff.mp (inter_mem (inter_mem (z₁.mem_nhds tB) f) ((isOpen_lt (g:=fun p:Vantage=> p (3:Axis)) continuous_const (continuous_apply _)).mem_nhds (show 0<Y 3 from y')))
 have l0:A⊆A':=fun k h=>(uA h).1.1; have l1:B⊆ B':=fun k h=>(uB h).1.1
 refine ⟨A,B,X,Y,Δ,_,bW,hA,hB,iA,iB,k₀.of_isClosed_subset isClosed_closure (closure_mono l0),k₁.of_isClosed_subset isClosed_closure (closure_mono l1),fun k hx=>(uA hx).2,fun k hx=>(uB hx).2,fun i h j v=>u i (l0 h) j (l1 v), fun i h j v=>a i (l0 h) j (l1 v), fun i m g h=>?_⟩
 exact j (show (i,g)∈C ×ˢ N from ⟨(uA m).1.2,(uB h).1.2⟩)
#print axioms ProvinceVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
