import GaugeFieldConstruction.PrearcM
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Connectors
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I θ E:Type}[Fintype I][LinearOrder I]{n:Side}
open Rio Grotto Isle Lattice.Corona
section
open Nor
variable (p:BudgetPoint)(σ:I→ Seat n)(w z a:ℝ)(T:PI I n→ℝ)(F:KI I n→ℝ)(k₀ B:ℕ)
-- choose η and canopy, Ω= Z + … ; choose exogenous Ω for array available. reuse at A3 with ℓ free.Len.
abbrev Flow4(k B:ℕ):ℝ:=yardZ B*k
abbrev Eta4(k B:ℕ):ℝ:= ζd /(Flow4 k B*cubeCt B+1)
abbrev Boot4(B:ℕ)(Ω η ℓ Z Φ:ℝ): Prop:= ℓ≥0 ∧ Cube_M B*Ω≤1∧ 0≤Ω∧ advanceC ℓ η≤1∧ Z+ℓ*Φ+(advanceC ℓ η*Z+stolon B Ω η ℓ*Φ)≤ Ω
local notation "η1"=> Eta4 k₀ B
local notation "ηF"=> Flow4 k₀ B
local notation "κ"=> (Lattice.Corona.Hive.Scales)
def supplyL (k:ℕ)(σ:I→Seat n)(P:List I):Prop:=P.Nodup∧∀ i,(P.toFinset.filter fun j=>σ j=i).card≤ k
private lemma Flow0:0≤ηF:=by unfold Flow4 yardZ; positivity
lemma etaP4:0<η1:=div_pos ζdp (add_pos_of_nonneg_of_pos (mul_nonneg (Flow0 k₀ B) (by unfold cubeCt; positivity)) zero_lt_one)
lemma Frank (L:List I)(p:supplyL k₀ σ L)(ha:0≤ a): crewFlow B (L.map σ) (Flow4 k₀ B) ∧ Lattice.Corona.Hive.Scales B a (Eta4 k₀ B) (L.map σ):=by
 have h:=crew_at B σ L p.1 (show ∀ i, _ ≤ k₀ from fun i=>?_ )
 swap
 · convert! p.2 i using 1; congr! 3
 have he:ηF=(k₀:ℝ)*yardZ B:=mul_comm ..; rw [←he] at h
 refine ⟨h, ⟨ha, etaP4 .., fun i=>asset B η1 _ i _ h (etaP4 ..|>.le) (Flow0 ..) ?_⟩⟩
 let W:= Flow4 k₀ B*cubeCt B; have hz: Eta4 k₀ B *(W+1)=ζd:= (div_mul_cancel₀ _ (ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg (Flow0 ..) (show 0≤cubeCt B from (by unfold cubeCt; positivity))) zero_lt_one))) -- tune
 exact (mul_le_mul_of_nonneg_left (show W≤W+1 by linarith) (etaP4 ..|>.le)).trans hz.le
lemma tonsY(L:List I)(p:supplyL k₀ σ L)(ha:0≤ a)(q:a+7*ζd ≤ w)(H:∀ i,0≤T i)(V:∀ i,0≤F i)(K:∀ i:Seat n,pointX cloudP T (March B w) i + pointX cloudK F (March B w) i ≤ z)(Ω ℓ:ℝ)(U:Boot4 B Ω (Eta4 k₀ B) ℓ z (Flow4 k₀ B)): Rider4 ℓ Ω (Eta4 k₀ B) a B (rental B a (Eta4 k₀ B) T F) (L.map σ) z (Flow4 k₀ B):=by
 obtain ⟨W,t⟩:=Frank σ a k₀ B L p ha; obtain ⟨g,p,Vc,s,m⟩:=U
 refine ⟨etaP4 k₀ B,g,W,m,Vc,s,fun i=>?_,t⟩
 have e(b:ℝ)(T:b≤6)(X:Support (More n)): tempI B (a+b*ζd) η1 (L.map σ) X ≤ March B w X :=by
    unfold tempI March; rw[←Real.exp_add]; apply Real.exp_monotone; have h :a+b*ζd + ζd ≤ w:=by nlinarith only[q,mul_le_mul_of_nonneg_right T ζdp.le]
    have hg:= mul_le_mul_of_nonneg_right h (show 0≤heft B X from Nat.cast_nonneg _); rw [add_mul] at hg; exact (add_le_add_right (t.toll _) _).trans hg -- tune add lemma
 exact le_trans (add_le_add (pointX_up cloudP T H (RedB B a η1 _) _ (e 6 (by norm_num)) i) (pointX_up cloudK F V (ColdB B a η1 _) _ (e 2 (by norm_num)) i)) (K i)
end
section
open Primitives.GCC Connector
variable (p:BudgetPoint)(σ:I→ Seat n)(μ:ℝ)(k B D:ℕ)(x y:Seat n)
-- exact support anchor at two seats. can till if c≥. 
abbrev Grap (x y:Seat n):Hub n:=⟨⟨x,{x,y}⟩,mem_insert_self ..⟩
-- Toll
lemma hewT : heft B (Grap x y).val.2 ≤ (separation x y:ℝ)/((B:ℝ)+1)+4:=by
 have X:=added (mem_singleton_self x) (mem_singleton_self y) B
 have p: (Grap x y).val.2={x}∪({y}:Finset _):=by change insert x {y}=_; rw [Finset.singleton_union]
 rw[p]; have H: coverNumber B {x}≤1:=?_; have h:coverNumber B {y}≤1:=?_
 swap
 · exact (cover_mono (halo_subset B _) _).trans (AnalyticBridge.CouplingShape.ballPaid ..) -- tune
 swap
 · exact (cover_mono (halo_subset B _) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)
 have r: toll B (separation x y) ≤ toll B (separation x y):= le_rfl; have v: heft B ({x}∪{y}) ≤ (2:ℝ)+toll B (separation x y):=by unfold heft; exact_mod_cast (show coverNumber B ({x}∪{y}) ≤ 2+toll B _ from by omega)
 apply v.trans; have t:= Connector.ratio B (separation x y); split at t<;> linarith only [t]
-- A4 locator.Comp.C._space. choose ℓ≥ℓ_a=5*e^{-B}. Needs lower cutoff (B≥ etc).
local notation "Bq"=> (B:ℝ)
abbrev ounce4 (B:ℕ):ℝ:= 5*Real.exp (-(1:ℝ)*B)
lemma opening (V:ℝ)(μ:ℝ)(a:ℝ)(hb:16≤B)(p:Bq^3≤V)(h:(separation x y:ℝ)≤V)(u:μ ≤ Real.exp (-V))(q:0≤a)(s:a+16*ζd≤2) : 5*(μ*Summit B a (Grap x y).val.2)≤ ounce4 B:=by
 apply mul_le_mul_of_nonneg_left _ (by norm_num); refine le_trans (mul_le_mul_of_nonneg_right u (Real.exp_pos _|>.le)) ?_; unfold Summit March; rw[←Real.exp_add]; apply Real.exp_monotone
 have hz:16≤(B:ℝ):= by exact_mod_cast hb
 have H:=hewT (n:=n) B x y
 let t:=(separation x y:ℕ); have hx:(t:ℝ)/(Bq+1)≤ V/(17:ℝ):=by
    calc _ ≤ t/(17:ℝ):= div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith)
         _ ≤ _:= by gcongr
 have I: (a+16*ζd)* _ ≤ 2* ((t:ℝ)/(Bq+1)+4):=(mul_le_mul_of_nonneg_right s (show 0≤heft B (Grap x y).val.2 from Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_left H zero_le_two)
 have hw: (256:ℝ)* (B:ℝ)≤ V:=by
    apply le_trans _ p
    rw [pow_succ]; exact mul_le_mul_of_nonneg_right (by nlinarith only[hz,pow_le_pow_left₀ (show (0:ℝ)≤16 by norm_num) hz 2]) (Nat.cast_nonneg _)
 have hi:(a+16*ζd)* heft B (Grap x y).val.2 ≤ 2*(V/17+4):= by apply I.trans; gcongr
 refine le_trans (add_le_add_right hi (-V)) ?_ ; linarith only [hz,hw]

end
end Iona
end YM.CF.Scree.Ing
end
