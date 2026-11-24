import YM.CF.Mint.Hit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace Roe
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
open MeasureTheory Fock Dial
variable (F:∀ i,Loom (mid (N i) B)) (W:∀ᶠ i in atTop,SkinT (I i) (F i) e) {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (U:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
variable {α:Type*} (R:ℕ→ℝ)
include W U g
abbrev optV (i:ℕ)(s:Side)(o:Site s)(Q: Emu.Plot α R)(J:List α):Opt (α:=α) s:=⟨o,R i,J,Q.pal i⟩
def getF{m:Side}(O: Opt (α:=α) (mid m B))(V:GramM (mid m B))(P:Grasp Y B e)(G:Loom (mid m B))(i:Orbit (mid m B)):ℂ:=feel O i.1 (denZ V P G i)
lemma echo (u:Onyx.Yard NP R)(p:∀ i,Site (NP i))(T:Emu.Plot α R)(J:List α): let Y(i):= optV R i _ (p i) T J
  (∀ᶠ i in atTop,Integrable (getF (Y i) (I i) P (F i)) (city _))∧ Tendsto (fun i=>(∫ z,getF (Y i) (I i) P (F i) z∂city _)/partitionZ (I i) P (F i)) atTop (𝓝 (Emu.runes T.rho J)) :=by
 intro t; let M(i):=Graph.start (I i) P (F i); let S:= NP; let C:=eur S; let cityP i:=city (NP i); let G:=denQ (P:=P) (I:=I) F; let X(i):= ∫ z,baseW (t i) P (I i) (F i) z∂cityP i; let Y(i):=∫ z,recW (t i) P (I i) (F i) z∂cityP i; let L(i):=drip (I i) P
 have ht: ∀ᶠ i in atTop, Integrable (recW (t i) P (I i) (F i)) (city _) ∧ Integrable (baseW (t i) P (I i) (F i)) (city _) ∧ Integrable (getF (t i) (I i) P (F i)) (city _):=by
    filter_upwards [Z.support,W,Z.tend.eventually_ge_atTop k] with i ⟨_,a,w,p⟩ t' v; have hv:k≤(S i).val:=Nat.cast_le.mp v; have hp:= bonB a w; obtain ⟨u,b⟩:=integrable_s _ _ D t' hp (t i) hv; obtain ⟨s,k',m⟩:=t'.wave; have hx:=earned (t i) _ (sailW _ hp hP D.stmt D.eP D.p _ _ m (D.plan _ hv).1); exact ⟨u,b,Integrable.of_bound hx.meas.aestronglyMeasurable _ (Eventually.of_forall hx.cost.choose_spec)⟩
 refine ⟨ht.mono fun i p=>p.2.2,?_⟩
 obtain ⟨δ,hδ,v⟩:= caesar D Z; let D':= b'/(2*Nova.poseX); have hD:0<D'/2:= by unfold D'; have he:= D.pos; have hp:=pose_p; positivity
 have hv: BeamG D N δ 0 (3*J.length):= skybed D (W:=fun i=> (I i).p.threshold) v _ (hδ _)
 obtain ⟨hX,hY⟩:= elfin (a:=1) D (I:=fun i=>Orbit (S i)) (fun i=>dim (I i)) T J u hv p (fun i=> (I i).J.M) (fun _=>Prod.fst) (fun i=> cab (I i) P (F i)) cityP (by norm_num) (by
     filter_upwards [Z.support,W,v] with i ⟨_,a,w,t⟩ l b; exact handout D (I i) (F i) (bonB a w) l b) ((touch D Z).mono fun i e=> e.1) (ht.mono fun i p=>p.2.1)
 have he:∀ᶠ i in atTop, 0<L i∧ M i≠0∧ L i*(D'/2)≤ ‖G i‖:=by filter_upwards [(touch D Z),hX,(costR D Z F W U g).1] with i f p g; exact ⟨f.2,p,g.2.2.2.2.2.2.1⟩
 have hh:Charge α S t:=⟨⟨_,Eventually.of_forall fun i=> (show (t i).dial=J.length from rfl)⟩,(growG u).mono fun i p=> by exact lungG _ _ p.2 p.1⟩ -- tune pair
 have hx : ∀ᶠ i in atTop, ‖(M i-G i)/(L i:ℂ)‖= ‖G i-M i‖/L i := he.mono fun i h=>by rw [norm_div,Complex.norm_real,Real.norm_of_nonneg h.1.le,norm_sub_rev]
 have hK : Tendsto (fun i=>(Y i-X i)/(L i:ℂ)) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (shot D Z U g t F W hh).shrinks; filter_upwards [ht,he] with i ⟨p,b,h⟩ v; rw [norm_div, Complex.norm_real,Real.norm_of_nonneg v.1.le]; unfold Y X cityP; rw [←integral_sub p b]; exact div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) v.1.le
 have hp:= power_v (Z:=Y) (X:=X) he hK (tendsto_zero_iff_norm_tendsto_zero.mpr ((wageK D Z F W U g).shrinks.congr' ((show _=ᶠ[atTop] _ from (show (fun i=> ‖(M i-G i)/(L i:ℂ)‖)=ᶠ[atTop] (fun i=> ‖G i-M i‖/L i) from hx)).symm))) hD _ hY; refine hp.congr' (Eventually.of_forall fun i=>?_); unfold Y; let f(i'):ℂ:=getF (t i) (I i) P (F i) i'; let c:= Complex.exp (-(I i).v); have he: c ≠0:=Complex.exp_ne_zero _; simp_rw [show ∀ j,recW (t i) P (I i) (F i) j=c*f j from fun j=>(by unfold recW feel valA recX; rw [map_smul,inner_smul_right]; rfl),MeasureTheory.integral_const_mul]; change (c*_)/(c*_)=(∫ z,f z ∂cityP i)/_; rw [mul_div_mul_left _ _ he]
end Roe
end YM.CF.Mint
