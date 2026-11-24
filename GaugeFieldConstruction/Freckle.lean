import GaugeFieldConstruction.Flyby
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
def spinRead (u v:Spin): δN →ₗ[ℂ] Op SU.Slot where
 toFun X:=Matrix.submatrix X (Prod.mk u) (Prod.mk v)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma offer_N(g:SU.E)(p:δN)(u v:Spin): spinRead u v (keyR g*p)=Matter.ma g*spinRead u v p:=by
 ext i j; change (keyR g*p) (u,i) (v,j)=_; rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single u]
 · simp only [keyR, Matrix.kronecker_apply, Matrix.one_apply_eq,one_mul]; rfl
 · intro i x w; simp [keyR,Matrix.one_apply,Ne.symm w]
 simp -- tune sum collapse sum_eq_single `u` elaborates wrong name
lemma offer_S(g:SU.E)(p:δN)(u v:Spin): spinRead u v (p*keyR g)=spinRead u v p * Matter.ma g:=by
 ext i j; change (p* keyR g) (u,i) (v,j)=_; rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single v]; · simp only [keyR,Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul]; rfl
 · intro i x w; simp [keyR,Matrix.one_apply,w]
 simp
-- Clifford Hilbert generation. algebra factors.
def chord (x:M2):Axis→ℂ:=![Complex.I*(x 0 1+x 1 0)/2,(x 1 0-x 0 1)/2,Complex.I*(x 0 0-x 1 1)/2,(x 0 0+x 1 1)/2]
lemma chord_v(x:M2): x=∑ i:Axis,chord x i • cliff i:=by
 ext i j; simp only [Matrix.sum_apply]; fin_cases i <;> fin_cases j <;> rw [Fin.sum_univ_four] <;> norm_num [chord,Hij,cliff] <;> ring_nf <;> simp <;> ring_nf <;> rw [Complex.I_sq] <;> ring
abbrev motif (i:Spin×Spin):M2:= Matrix.single i.1 i.2 1
abbrev spectral (k:Matter.FlavorIndex):Op SU.Slot:= Matter.jordan (Pi.single k 1)
def plugC (m:M2)(k:Matter.FlavorIndex): P03:=by
 let X:=m ⊗ₖ spectral k; let p:=sendV (b:=false) (c:=true) X; refine ⟨send_L false true X,(show SheetQ _ from ?_)⟩ -- tune
 exact ⟨p,fun g => (sym_R p p g).2 (by rw [blank_A]; exact (neutralX _ _ _ _ (Matter.coeff_ok _ g).symm).2)⟩
abbrev alloy (i:Axis)(k:Matter.FlavorIndex): P03:= plugC (cliff i) k
lemma plug_v (m:M2)(k): skim_L false true (plugC m k).val=m⊗ₖ spectral k:=blank_A ..
lemma paintU (V W:P03)(h:skim_L false true V.val=skim_L false true W.val) : V=W:=Subtype.ext (swan (show SheetQ V.val from V.property).bin (show SheetQ W.val from W.property).bin h)
lemma crest_P(P:P03):∃ X:Spin×Spin→Matter.FlavorIndex→ℂ, P=∑ i,∑ j,X i j • plugC (motif i) j:=by
 let V:= skim_L false true P.val; have hx(i j:Spin): Matter.neutral (spinRead i j V):=by
    intro x; rw [← offer_N, ← offer_S, show keyR x* V=V*keyR x from ( (sym_R (show SheetQ P.val from P.property).bin (show SheetQ P.val from P.property).bin x).1 (((show SheetQ P.val from P.property).tax x).eq)).symm]
 choose a T using (fun i:Spin×Spin=> (Matter.species _|>.mp (hx i.1 i.2)).exists)
 refine ⟨a,?_⟩; apply paintU
 have hp(i:Spin×Spin) :spinRead i.1 i.2 V=∑ k:Matter.FlavorIndex,a i k • spectral k:=by
    rw [T i,show Matter.coeffs (a i)=Matter.jordan (a i) from rfl,show Matter.jordan (a i)= Matter.jordan (∑ k:Matter.FlavorIndex,a i k • Pi.single k 1) from congrArg _ (Phys.diagonals _).symm]; simp only [map_sum,map_smul]; try rfl
 simp_rw [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,plug_v]; ext ⟨i,c⟩ ⟨j,d⟩; rw [Matrix.sum_apply,sum_eq_single (i,j)]
 · simp_rw [Matrix.sum_apply,Matrix.smul_apply,Matrix.kronecker_apply,show motif (i,j) i j=1 from (by simp [motif]),one_mul]; have he:=Matrix.ext_iff.mpr (hp (i,j)) c d; simp_rw [Matrix.sum_apply,Matrix.smul_apply] at he; exact he
 · intro k _ e; rw [Matrix.sum_apply]; apply sum_eq_zero; intro l _; rw [Matrix.smul_apply,Matrix.kronecker_apply,show motif k i j=0 from (by unfold motif; rw [Matrix.single_apply]; exact if_neg fun u=> e (Prod.ext u.1 u.2)),zero_mul,smul_zero]
 simp -- tune
lemma barκ (m:M2)(k:Matter.FlavorIndex):plugC m k= ∑ i:Axis,chord m i • alloy i k:=by
 apply paintU; simp_rw [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,alloy,plug_v]; conv_lhs=> rw [chord_v m]
 ext ⟨a,p⟩ ⟨b,d⟩; rw [Matrix.sum_apply]; rw [Matrix.kronecker_apply,Matrix.sum_apply,sum_mul]; exact sum_congr rfl fun i _=>by rw [Matrix.smul_apply,Matrix.smul_apply,Matrix.kronecker_apply,smul_mul_assoc]
lemma crests(P:P03): P∈ Submodule.span ℂ (Set.range (Function.uncurry alloy)):=by
 obtain ⟨A,h⟩:=crest_P P; rw [h]; apply Submodule.sum_mem _; intro i _; apply Submodule.sum_mem _; intro j _; apply Submodule.smul_mem; rw [barκ]; apply Submodule.sum_mem _; intro x _; apply Submodule.smul_mem; exact Submodule.subset_span ⟨(x,j),rfl⟩
open Phys
lemma starφ (p:Axis)(k:Matter.FlavorIndex):goldΦ (alloy p k).val=tiap k (Row.B p):=by
 let V:=alloy p k; let A(i j:Tagφ):= (skim_L false true V.val) i j; change ∑ i:Tagφ,∑ j:Tagφ,A i j • wedgeCR i j= tiap k _
 rw [Fintype.sum_prod_type (α₁:=Spin) (α₂:=SU.Slot)]; unfold Row.B; rw [map_sum]; apply sum_congr rfl; intro i _; simp_rw [Fintype.sum_prod_type (α₁:=Spin) (α₂:=SU.Slot)] -- tune
 rw [map_sum,sum_comm]; apply sum_congr rfl; intro j _; rw [map_smul, tiap,LinearMap.sum_apply, smul_sum]; apply sum_congr rfl; intro x _; rw [LinearMap.sum_apply, smul_sum]; apply sum_congr rfl; intro y _
 let f:=Hij p i j; have ht:A (i,x) (j,y)=f*alpha k x y:=by unfold A V alloy; rw [plug_v]; rfl
 rw [ht]; simp_rw [mul_smul]; congr 1; rw [LinearMap.smul_apply]; apply congrArg; unfold sD; rw [straps]; rfl -- tune
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
