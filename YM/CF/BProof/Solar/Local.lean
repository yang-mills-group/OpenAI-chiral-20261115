import Mathlib.MeasureTheory.Function.ContinuousMapDense
import YM.CF.BProof.Transit.Note
import YM.CF.Fixed.MirrorFunctional
import YM.CF.Tye.Spin
import YM.CF.BProof.Physical
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 28000
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
local instance mLocal (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance bLocal (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
variable {N:Side} (s t:Sweep N)
section
variable {α : Type*}[NormedAddCommGroup α][NormedSpace ℝ α]
def twineS(C:ℝ)(x:α):α:= (C/max C ‖x‖) • x
lemma twine_p{C:ℝ}(p:0<C):Continuous (twineS (α:=α) C):= (continuous_const.div (continuous_const.max continuous_norm) fun x=>(p.trans_le (le_max_left ..)).ne').smul continuous_id
lemma twine_b{C:ℝ}(p:0<C)(x:α): ‖twineS C x‖ ≤ C:=by
 unfold twineS; set d:=max C ‖x‖; rw [norm_smul,Real.norm_of_nonneg (div_nonneg p.le (p.le.trans (le_max_left ..))), div_mul_eq_mul_div,(div_le_iff₀ (p.trans_le (le_max_left ..)))]; exact mul_le_mul_of_nonneg_left (le_max_right ..) p.le
lemma twine_q{C:ℝ}(p:0<C)(x y:α)(h:‖y‖ ≤ C): ‖y-twineS C x‖ ≤ 2* ‖y-x‖:=by
 by_cases g:‖x‖ ≤ C; rw [twineS, max_eq_left g,div_self p.ne', one_smul]; exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
 have he:=le_of_not_ge g; have hx:= p.trans_le he
 calc
    _ ≤ ‖y-x‖+ ‖x-twineS C x‖:=norm_sub_le_norm_sub_add_norm_sub ..
    _ = ‖y-x‖ + (‖x‖ - C):=by
        congr 1; unfold twineS; nth_rw 1 [←one_smul ℝ x]; rw [max_eq_right he, ←sub_smul,norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr ((div_le_one hx).mpr he)),sub_mul,one_mul,div_mul_cancel₀ _ hx.ne'] -- tune
    _ ≤ _:=by rw [norm_sub_rev y]; linarith only [norm_sub_norm_le x y,h]
end
open RG
variable (S:Support (More N))
def pore(S:Support (More N))(f:Pane N):Pane N:=fun i=> if ends i ⊆ S then f i else 1
lemma poreD(f): Agrees S f (pore S f):=fun i q v=>Eq.symm (if_pos (Finset.insert_subset_iff.mpr ⟨q,Finset.singleton_subset_iff.mpr v⟩))
lemma poreL : LocalOn S (pore S):=by
 intro f g h; funext i; unfold pore; split; next y=> exact h i (y (by simp)) (y (by simp))
 next _=> rfl
lemma pore_C : Continuous (pore S):=by apply continuous_pi; intro i; unfold pore; split; exact continuous_apply i; exact continuous_const
section
variable {n : Type}[Fintype n][LinearOrder n]
def profileB(S:Finset n)(b:Bool):Submodule ℂ (FC n) where
 carrier:=Sector S b
 zero_mem':=Sector.zero _
 add_mem':= Sector.add
 smul_mem' c _ p:= Sector.scale p c
end
open BoundedContinuousFunction
local notation "Ytw"=> prior SU.group (More N)
variable {S}
theorem probe{F: Obs N}(g:Allowed S F){ε C:ℝ}(hε:0<ε)(hx:0<C)(p:Paid F C) : ∃ G:Obs N, Continuous G ∧ Allowed S G∧ Paid G C∧(∫ x:Pane N, ‖F x-G x‖∂prior SU.group (More N)) ≤ ε:=by
 let W:Submodule ℝ (FC (Single N)):= (profileB (modes S) false).restrictScalars ℝ
 let f(x:Pane N):W:=⟨F x,g.modes_use x⟩; let U:=pore S; let μ:=Measure.map U Ytw; haveI:IsFiniteMeasure μ:=Measure.isFiniteMeasure_map ..
 have hf:Measurable f:=g.bounded.meas.subtype_mk
 have hW(x):‖f x‖ ≤ C:= p x
 have hx': Integrable f μ:= Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hW)
 obtain ⟨v,u,hv⟩:= hx'.exists_boundedContinuous_integral_sub_le (half_pos hε)
 let T (x:Pane N):= twineS C (v x); have hT:Continuous T:=(twine_p hx).comp v.continuous; have he:Continuous U:=pore_C S
 let G(x:Pane N): FC (Single N):=(T (U x)).val
 have hG:Continuous G:= continuous_subtype_val.comp (hT.comp he); have hg(x):‖G x‖ ≤ C:= twine_b hx (v (U x))
 refine ⟨G,hG,⟨⟨hG.measurable,C,hg⟩, fun i j u=> by unfold G; rw [show U i= U j from poreL _ i j u], fun x=> (T (U x)).property⟩,hg,?_⟩
 let a (x:Pane N):= ‖f x-T x‖; have ha:Measurable a:= (hf.sub hT.measurable).norm
 calc
    _ = ∫ i,a i∂μ:=by
       unfold μ; rw [integral_map he.measurable.aemeasurable ha.aestronglyMeasurable]; apply integral_congr_ae; apply ae_of_all; intro i; change ‖F i-G i‖= ‖F (U i)-G i‖; rw [show F i= _ from g.reads _ (U i) (poreD S i)]
    _ ≤ 2*(∫ i, ‖f i-v i‖∂μ):=by
       rw [← integral_const_mul]; apply integral_mono; exact (hx'.sub (Integrable.of_bound hT.aestronglyMeasurable C (ae_of_all μ fun x=>twine_b hx (v x)))).norm; exact (hx'.sub hv).norm.const_mul _; exact fun i=>twine_q hx _ _ (hW _)
    _ ≤ _:= by linarith
end YM.CF.BProof.Bide
