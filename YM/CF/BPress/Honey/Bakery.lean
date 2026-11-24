import YM.CF.BPress.Sugar.Stan
import YM.CF.BPress.Port.Ribbon
import YM.CF.BPress.Port.Residence
/- Uniform Loom gauge stipend (prices per-column, pre-mapping). At actual sector on Role. We assemble & pack exact gauge contributions before paying flag estimates. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Honey
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
variable (H:Crew A)(V:GramM N)
-- genuine parameters at one baker torus on A.Fin. Work independent of H.
structure Recipe where
 M:ℕ
 σ: ℝ
 C:ℝ
 Λ:ℝ
 work : V.path.Bounds V.funds σ C Λ
 l: Seal A.Hcols→ Tender A
 bill: Tender A
-- `H` not included in Recipe signature.Use opt.Named.
namespace Recipe
variable {V}
variable (F: Recipe (A:=A) V)
def fromSea : Fare A:= wave A F.M V.path V.funds V.beta H.y F.work
structure Budgeting (τ k D ζ a C' :ℝ) :Prop where
 err : Poise B H.T V.funds D H.κ F.C ζ H.y F.M
 chef: Checks F.M V.p V.funds
 rung: V.p.threshold=temp H.y
 cost: V.beta∈Set.Icc (H.y/2) (2*H.y)
 toll: Thinner (s:=More N) (totalWeak V.funds V.path V.p V.beta F.M) (fullWeak V.path V.p V.beta F.M) τ k
 rate : 0≤τ
 pay : ∀ U:Micro (More N), V.path.inChannels V.funds V.p V.beta U=(∑ x:Face (Per (More N)), hide V.funds V.p V.beta U x)+ (∑ t:Signed, ∑ x, kept V.funds V.p V.path V.beta F.M t U x)+ ∑ i,totalWeak V.funds V.path V.p V.beta F.M i U
 afford : Afford H.J H.T H.P B.D H.κ H.y
 jRoot : LocalRatio H.J
 poly (S): Poly A S (fromSea H F S) (H.F S) (H.P.low H.y) H.P.upper (H.y⁻¹^2)
 summer : Summer A H.F H.P.upper (H.P.low H.y) (H.P.reach H.y) (H.P.chunks H.y)
 jac : JacData A H.F F.l F.bill (H.P.jrate H.y) (H.P.jcostB H.y B.D)
 hope : LieTicket H.J a C'
 stride : strideCost B.D H.P (truncv H.y) H.y<a
 reward : H.P.jcostB H.y B.D + |Real.log (job_m B.D H.J H.y)| ≤ Port.reward B.D H.κ H.y V.funds

-- $before-Weigh$. w evaluated with exact clipping.
abbrev perturbY (x:mState N A):= perturb H.T A H.κ H.y (H.skyio x)
abbrev directW (x:mState N A):= weighM (y:=H.y) A F.M V.path V.funds V.p V.beta x.1.1 (perturbY H x) (H.port x)
abbrev mellow (x:mState N A)(i:Root (More N)) := error F.M V.path V.funds V.p V.beta H.y (perturbY H x) (H.port x) i
def tinW (x:mState N A)(i:Root (More N)):= if i∈ Θ A F.M x.1.1 then mellow H F x i else 0
def leftY (x:mState N A)(i:A.Hcols):= Port.lTerm A H.J H.F H.y x.2.1.1 x.1.1 i+ rTerm A H.F (fromSea H F) x.2.1.1 x.1.1 i
abbrev force (x:mState N A)(i:A.Hcols):= (Wealth.pays A F.M V.path V.funds V.p V.beta H.y x.1.1 (perturbY H x) (H.port x) i+ burden A (H.P.heightClose H.y) F.l i x.1.1) - Real.log (job_m B.D H.J H.y)
def cold (x:mState N A)(i:A.Hcols) := if i∈ x.1.1 then force H F x i else 0
abbrev tailY (x:mState N A)(S:Seal A.Hcols):= tailJ A (H.P.heightClose H.y) F.l S x.1.1
abbrev weak (x:mState N A)(S:Support (More N)):= weakRest A V.path V.funds V.p V.beta F.M S (H.port x)
def wage (x:mState N A):=(∑ i,cold H F x i)+∑ i, leftY H F x i -- bracket tune ∑
def Wage (x:mState N A):= wage H F x+(∑ i,tailY H F x i)-(∑ i,tinW H F x i)-∑ i,weak H F x i
abbrev Credit :=Port.gvol A H.J H.y H.F F.M V.funds V.path V.p V.beta
variable {H F}
namespace Budgeting
variable {τ k D ζ a C':ℝ}(Q:Budgeting H F τ k D ζ a C')
include Q
lemma high : High B F.M:= Q.err.high
lemma y_pos : 0<H.y:= Q.err.dividend.young
lemma ageP : 0≤ V.beta:= ((half_pos (Q.y_pos)).le).trans Q.cost.1
lemma money : charged (q:=τ) (k:=k) (N:=N) F.M V.path V.funds V.p V.beta:= ⟨Q.chef,⟨Q.toll,Q.high.large⟩,Q.rate,Q.ageP⟩
lemma income_pos : 0< Credit H F:= (pref_content A H.J H.P H.y H.F F.M V.funds V.path V.p V.beta Q.y_pos Q.jRoot Q.summer F.work Q.chef Q.cost).1 -- tune
lemma vault (x: H.castP): jstamp (y:=H.y) A H.J H.F x.val.1 x.val.2.1 * Real.exp (directW H F x.val)= Credit H F * Real.exp (Wage H F x.val):=by
 let v:mState N A:= x.val; let t:=v.1.1; let P:=v.2.1; let H₀:=P.1; let w:= perturbY H v; have he:=Q.jac.calculate (H.P.heightClose H.y) t; have hk:V.p.threshold=temp H.y:= Q.rung; have hp(v:Quarters A)(p:aware A H.κ H.y H.F t v)(b:Barrel A H.y v.1): detM A (H.F t)*taxG A H.J H.y H.F t v.1*Real.exp (-(∑ i∈Θ A F.M t, second V.path V.funds F.M V.beta i (perturb H.T A H.κ H.y (Aback A (bodyBase A H.y H.F t v)))))= diceV A H.J H.y H.F*(job_m B.D H.J H.y)⁻¹^t.card * Real.exp (jacdiff A H.F t + softLog A H.J H.y H.F t v.1+ Rcoord A (fromSea H F t) H.F t v.1):=by
   obtain ⟨v,W⟩:=v; obtain ⟨v,rfl⟩:= (offer A).surjective v; exact stamp_point t Q.afford Q.jRoot Q.summer (Q.poly t).lid F.work Q.high v W p b -- tune
 let c:= -(∑ i∈Θ A F.M t, second V.path V.funds F.M V.beta i w); let d:= -debtH A F.M V.path V.funds V.p V.beta H.y; let u:= softLog A H.J H.y H.F t H₀; let b:= Rcoord A (fromSea H F t) H.F t H₀; let w0:= (∑ i∈t, Wealth.pays A F.M V.path V.funds V.p V.beta H.y t w (H.port v) i); let s:= ∑ i∈Θ A F.M t, mellow H F v i; let T:= ∑ i, weak H F v i; let K':= job_m B.D H.J H.y
 have hx:0<K':=mul_pos (Port.v_pos B.D H.y) (gH_pos B.D H.J H.y Q.jRoot Q.y_pos); have hw(K:ℝ)(g:0<K) : K⁻¹^t.card = Real.exp ( -((t.card:ℝ)*Real.log K)):=by rw [←mul_neg, Real.exp_nat_mul, ← Real.log_inv, Real.exp_log (inv_pos.mpr g)] -- tune
 let L₀:= ∑ i∈t, burden A (H.P.heightClose H.y) F.l i t; let J:=∑ i,tailY H F v i; have hV : Wage H F v = w0 + L₀-(t.card*Real.log K')+ u+b+J-s-T:=by
    have hk : ∀ {I:Type}(r: Finset I)[DecidableEq I][Fintype I] (f:I→ℝ), (∑ i,if i∈r then f i else 0)=∑ i∈r,f i:=by intro I S Q t f; rw [←sum_filter]; simp [filter_mem_eq_inter]
    have h₁ : (∑ i,cold H F v i)= w0+L₀-(t.card*Real.log K'):=by unfold cold; rw [hk]; unfold force; rw [sum_sub_distrib, sum_add_distrib,sum_const,nsmul_eq_mul]
    rw [Wage, wage,h₁, show (∑ i,leftY H F v i)= u+b from (by unfold leftY; rw [sum_add_distrib]; congr 1; exact (lterms A H.J H.F t H₀ H.y).symm; exact (Rterms A H.F (fromSea H F) t H₀).symm), show (∑ i,tinW H F v i)=s from hk _ _]; unfold u b; abel -- tune
 have hr : directW H F v=c+(d+w0-s-T):=by unfold directW weighM c w0 d s T mellow weak; rw [sum_add_distrib]; unfold w t; abel -- tune syntactic
 have he':jstamp (y:=H.y) A H.J H.F v.1 P* Real.exp c=diceV A H.J H.y H.F * K'⁻¹^t.card* Real.exp (jacdiff A H.F t+u+b):=hp P x.property.2.1 x.property.1.2 -- tune implicit rate
 change jstamp (y:=H.y) A H.J H.F v.1 P * Real.exp (directW H F v) = Real.exp d * diceV A H.J H.y H.F * Real.exp (Wage H F v); rw [hr,Real.exp_add c,←mul_assoc,he',hw K' hx, mul_assoc (Real.exp d)]; rw [show jacdiff A H.F t= L₀ + J from he,hV]; -- rearr exp without inv constants
 let e:= diceV A H.J H.y H.F; rw [← mul_assoc (Real.exp d),mul_comm (Real.exp d) (diceV _ _ _ _)]
 repeat rw [mul_assoc (diceV A H.J H.y H.F)]
 repeat rw [← Real.exp_add]
 refine congrArg (e * ·) (congrArg Real.exp (?_)); abel -- tune
end Budgeting
end Recipe
end YM.CF.BPress.Honey
