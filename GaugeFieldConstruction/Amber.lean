import GaugeFieldConstruction.Mullet
import GaugeFieldConstruction.Fangs
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
open BellPrice PinRack
open BellPrice PinRack
open Py.Rate.Pitching.Focus Py.Rate.Pitching
variable {I:Type}[Fintype I]{N P B:Side}{X:GramM (mid N B)}{Y:GramM (mid P B)}{h t s a b v μ g τ:ℝ}{L:Side}{H:Scree.Hub (mid N B)}{o:Seat (mid P B)}{i j l k D:ℕ}
variable (p:Chords t s a g μ h τ X.p Y.p L)
abbrev Walt (L:Side)(γ:I→ℕ)(x:FrameK I): FrameK I:= fun i=>(↑((Rateκ L (γ i))⁻¹):ℂ)*x i
-- pricing $Z → P(CZ)$. linear identities before.C basis. no existence with inverse not functional.D level shape enough.
lemma α_money (x:ℝ)(t:0 ≤ x) : ‖(x:ℂ)‖=x:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg t]
lemma ticket_pay (γ:I→ℕ) (V:FrameK I)(i:I): ‖Walt L γ V i‖= (Rateκ L (γ i))⁻¹* ‖V i‖:= by unfold Walt; rw [norm_mul,α_money _ (inv_nonneg.mpr (Rate_pr ..).le)]
lemma Walt_tip (γ:I→ℕ)(V:FrameK I)(C t:ℝ): ∑ i, ‖Walt L γ V i‖*(C*(Rateκ L (γ i)*t))= LoomK V*(C*t):=by
 unfold LoomK; rw [sum_mul]; apply sum_congr rfl; intro i _; rw [ticket_pay]; let R:=Rateκ L (γ i); have Hp: R≠0:= (Rate_pr ..).ne'; change R⁻¹*‖_‖*(C*(R*t))= _; field_simp
lemma Walt_mon (γ:I→ℕ) (V:FrameK I)(p:∀ i, γ i≤D): LoomK (Walt L γ V) ≤ (Rateκ L D)⁻¹*LoomK V:=by
 unfold LoomK; rw [mul_sum]; exact sum_le_sum fun i _=> (ticket_pay ..).trans_le (mul_le_mul_of_nonneg_right (inv_anti₀ (Rate_pr ..) (rate_lt (p _))) (norm_nonneg _))
variable {G:Type}
-- shape Provisional.Program.K.Φ control.
abbrev Plug (P:BudgetPoint)(o:Seat N)(M: Male)(h:ℝ)(D:ℕ)(V:I→Zone N)(L:Side)(γ:I→ℕ)(t:ℝ):I→Waves := fun i=> T_w L (γ i) t P o M h D (V i)
-- combine without issue NormedSpace (Slot is at opacity)
abbrev W_s {E:Type}[AddCommMonoid E][Module ℂ E](F:I→ E)(V:FrameK I):=∑ i:I, V i • F i
lemma Plinth {P:BudgetPoint}{o:Seat N}{M:Male}{K:I→Zone N}{f:ℝ}{A:I→ℝ}(hF:∀ i,Basalt P o L.val (L.val+1) (K i) (A i) f b h D M)(ht:0≤h)(T:FrameK I) : Basalt P o L.val (L.val+1) (W_s K T) (∑ i, ‖T i‖ * A i) f (LoomK T*b) h D M ∧∀ k:ℕ, CardT (W_s K T) (KeyUp P) M h o k=Woof T (fun i=>CardT (K i) (KeyUp P) M h o k):=by
 have hx(i):= (hF i).smul (T i) ht -- field order? .smul z h
 have hu:= Basalt.sumA (I:=I) univ _ _ _ (fun i _=>hx i) ht
 refine ⟨?_,fun i=>?_⟩
 · unfold LoomK; rw [sum_mul]; exact hu
 calc
   _=∑ j,CardT (T j • K j) _ _ _ o i:= CardT_sum univ _ _ _ (fun i _=>hx i) ht i
   _=_:= sum_congr rfl fun j _ => CardT_scalar (T j) (hF j) ht _
lemma waveSums {I T:Type}[Fintype I](P:TPack T)(s:ℂ):letI:=P.G; letI:=P.S;∀ (f:I→T), s • (∑ i,f i) = (∑ i,s • f i):=by letI:=P.G; letI:=P.S; intro i; exact Finset.smul_sum ..
lemma wave_v {T:Type}(P:TPack T)(a b c d:ℂ)(e:a*(b*c)=d):letI:=P.G; letI:=P.S;∀ x:T,d • x=a • b • c • x:=by letI:=P.G; letI:=P.S; intro x; simp only [smul_smul,e]
lemma wave_spend {P:BudgetPoint}{N:Side}{o:Seat N}{M:Male}(H:I→Zone N)(V:FrameK I)(c:I→ℕ)(m:ℕ)(h:ℝ)(L:Side)(hx:0<t) : Woof (Walt L c V) (fun i=> CardT (H i) (KeyUp P) M h o m)=(t:ℂ) • Woof V (Plug P o M h m H L c t):=by
 unfold Woof; rw [waveSums (I:=I) Packs_U] -- Waves instance time
 apply sum_congr rfl; intro i _; let x:= V i; let y:= Rateκ L (c i); have he :y ≠0:= (Rate_pr ..).ne'; change _ = (t:ℂ) • x • ((((t*y)⁻¹:ℝ):ℂ)) • _; have hz:(t:ℂ) *(x* ((((t*y)⁻¹:ℝ):ℂ)))=Walt L c V i:=by
    change _= ↑(y⁻¹)*x; push_cast; have ht : (t:ℂ)≠0:=by exact_mod_cast hx.ne'
    have he :(y:ℂ)≠0:=by exact_mod_cast he
    field_simp -- tune complex lifts
 exact wave_v Packs_U _ _ _ _ hz _
abbrev Bbt (τ X:ℝ)(D:ℕ):= 2* Frugal.TowerX τ X (D+1)
abbrev Chest (τ μ:ℝ)(D:ℕ):= Bbt τ (BxMir μ τ) D
variable {γ:I→ℕ}{V:I→Waves}(hp:Planaris γ ΓProj D V τ)
variable {δ:I→ RegBudget (mid P B)}{W:I→Vow.Pax (mid N B)}{U:Aura (mid N B)}
variable (Y_ :∀ i:I,FuelKey X Y H o h a b g μ (RamoK L*s) U (δ i) (W i) L) (hq:D ≤2) (T:∀ i:I, TollsK Y.p o Y.J.M (δ i) L s h (RamoK L) D (V i))(hx: Cresc L.val Y.p (Zhub o))
abbrev TipsK (H:Scree.Hub (mid N B))(X:GramM (mid N B))(L:Side)(h:ℝ)(W:I→Vow.Pax (mid N B))(D:ℕ): I→ Zone (mid N B):=fun i=> Brow H X.J.M h X.p (W i) L D
structure Freight {P:BudgetPoint}(o:Seat N)(M:Male)(q σ τ h k:ℝ)(D:ℕ)(V:I→Zone N)(G:I→ℕ)(L:Side): Prop where
    charm(i:I):Basalt P o L.val (L.val+1) (V i) (Winner σ τ*(Rateκ L (G i)*q)) 2 k h D M
    plank (W:FrameK I): ‖Woof W (Plug P o M h D V L G q)‖≤LoomK W*BxMir σ τ
    lever(Q:Waves)(hU:ΓProj D Q=Q):∃ w:FrameK I, Q=scalB (Plug P o M h D V L G q) w
    purse(w:FrameK I):LoomK w ≤ Chest τ σ D*‖Woof w (Plug P o M h D V L G q)‖
    hardy : Function.Injective (scalB (Plug P o M h D V L G q))
include p hp hx Y_ hq T
set_option maxHeartbeats 80000 in
lemma barter_R (c:TowerX τ (BxMir μ τ) (D+1)* Slipρ L μ ≤1/2) : Freight (P:=X.p) H.val.1 X.J.M t μ τ h b D (TipsK H X L h W D) γ L:=by
 let V₀:=TipsK H X L h W D; let H0:=Plug X.p H.val.1 X.J.M h D V₀ L γ t; let E:= PrintQ (s/t) (X.p.threshold/Y.p.threshold)
 have tT:=Price_eclipse (s/t) _ p.ratioT p.ratioY p.calm; have t(i):= Zenith_κ p (Y_ i) hq (V i) (T i) (hp.ray i) hx (hp.saturated i) (hp.bounded i) -- tune order
 have hF: Facies γ ΓProj E D V H0 (BxMir μ τ) (Slipρ L μ):=⟨fun i=>(t i).2.1,fun i=>(t i).2.2.1,fun i=>(t i).2.2.2⟩; have H':0≤τ:=by have he:=p.calm; linarith
 have HX:0≤BxMir μ τ:= mul_nonneg InterestC (PosW p.full H'); have HC:0≤Slipρ L μ:=mul_nonneg (PosR p.full) (α_pos ..).le
 have HG:= onward γ ΓProj E D hp tT hF H' HX HC c -- typeclass FiniteDim? implicit
 refine ⟨fun i=>(t i).1,fun i=>woof_cost i hF.sane,fun Q g=>?_,fun i=>downward γ ΓProj E D hp tT hF H' HX HC i c,HG.1⟩
 obtain ⟨w,V⟩:= HG.2 Q g; exact ⟨w,V.symm⟩
end
end YM.CF.Oath
end
