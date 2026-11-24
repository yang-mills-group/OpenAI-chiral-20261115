import YM.SU5.SatinWard.Resolution.Aspen
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 80000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax Rill Ione Clock Salt Mew PowerSeries Sour Turning
attribute [local instance] opCStarAlgebra
open scoped Mew
variable {n N B:Side}
local notation "Ω"=> mid N B
open QuadClock Neon Bake Larch Roots Py Swell Analysis Pressure Oath Moto Porticus
variable {p:BudgetPoint}{q l m n₀:ℕ}{h w μ c d x a b v s' τ Q:ℝ} {F: ForceBudget (mid N B)}
variable {s:Sweep (mid N B)} {E: Bag (mid N B)}{o:Site (mid N B)}


open ShapeLab ShapeLab.ResolutionFrame Waxy SweepSign
open Vow.TreasuryFog Buffered Swell.Porticus Hive Roots
namespace Lampshade
variable {χ:SweepSign (mid N B)}
open Buffered
variable {j:ℕ}{φ:ArcΦ}{Ψ:Cusp (mid N B)}{ζ:ℂ}{L':RegBudget (mid N B)} {S:Support (More (mid N B))} {e z β:ℝ}
variable {k:ℕ}{L:Side}{p':Odd L.val}{X : Pricing k L p' (Thread k)}{Y:Grasp X B d}{W:Scree.Loom (mid N B)}{R:GramM (mid N B)}
variable {F:Mark (mid N B)}{V:phy (mid N B)}{y:ℝ}
-- symmetric sheet but track two tariffs for Furnaces. analogous to Aspen
abbrev CoaBill (Y:Grasp X B d)(W:Scree.Loom Ω)(R:GramM (mid N B))(χ:SweepSign Ω)(j m q l:ℕ)(M:Site Ω→Mark Ω)(Φ:ArcΦ)(h x a a₀ D e w β:ℝ):Prop:=∃ K V A F, Tabular K M V A F Φ Y W R j m q l χ h x a a₀ D e w β
lemma Gust {a₀:ℝ} (H:Totem Y R W q l m j o E F V φ h x a b w β) (A0:Barrage R.p q (grooveB m R.p (node o)) h E x a a₀) (D:CartRoom Y W R l μ h) (t:χ.Eigenspace φ)(k:χ.KillsScalar):∃ Φ, Nearby Φ φ h w ∧ CoaBill Y W R χ j m q l (orbitAverage BodyPull o χ F) Φ h x a a₀ (emGain R.p μ*b) (Θgain R.p μ l*b) b β:=by
 obtain ⟨G,F',Y',w'⟩:=H.bill.yard.price; let v:= Classical.arbitrary (Ids Ω); let Φ:=pilasters l R.p o (singlePole v E Y' (node o)); let X':=alleyS o χ turnD Φ o
 obtain ⟨bH,p,z⟩:= D.monotony; obtain ⟨s,Vh,τ,ut,r,pτ⟩:= D.tape
 obtain ⟨A,K,t',Ht⟩:=drillSlope (drill_ray H.bill v Y') D.higher Vh s ut bH r pτ p z; refine ⟨X', reshape_near o (H.bill.stamp G F' v Y').estimate t,orbitAverage StockPull o χ E,orbitAverage CartPull o χ V,orbitAverage Eρ o χ A,orbitAverage Kρ o χ K,?_⟩; unfold emGain Θgain; rw [mul_assoc (duty_Q ..),mul_assoc (strive_E ..)]
 apply tabular (ζ:=t') χ _ (zero_le_one.trans D.higher) D.voter k (fun i=> D.transits _ E V H.step); exact ⟨H.tag,H.true',H.step,{Ht with step:=A0}⟩
variable {ι:Type}[Fintype ι][DecidableEq ι] {F₁:ResolutionFrame ι} {M M': Site (mid N B)→Mark (mid N B)}{Θ:ℝ}{C:ℝ}
local notation "Ξr"=> F₁.colors (mid N B)
local notation "atomic"=> F₁.atScale h Θ
abbrev Awareness (J:ResolutionFrame ι)(Y:Grasp X B d)(W:Scree.Loom Ω)(R:GramM (mid N B))(j m q l:ℕ)(M:Site Ω→Mark Ω)(s: Coords ι)(h Θ x a a₀ D e w β:ℝ):Prop:= CoaBill Y W R (J.colors Ω) j m q l M (J.atScale h Θ s) h x a a₀ D e w β
variable {D a₀:ℝ}
lemma sales_B (p:CoaBill Y W R (F₁.colors Ω) j m q l M φ h x a a₀ D e w β)(i: Coords ι)(q':Nearby φ (atomic i) h (Θ * τ))(hc:F₁.Stretch C)(z:0 < Θ)(u:1≤ h): ∃ c,‖c-i‖ ≤ C*τ ∧ Awareness F₁ Y W R j m q l M c h Θ x a a₀ D e w β:=by
 obtain ⟨B',H,K,Q,pB⟩:= p; obtain ⟨u₀,u₁,u₂,u₃,u₄,x',v⟩:= pB.books
 obtain ⟨g,hg⟩:=(F₁.representation _ h Θ Ω z u).1 ⟨v,x'⟩
 have hz:atomic g = φ :=hg; refine ⟨g,?_ ,B',H,K,Q,hz.symm ▸ pB⟩; let c:= F₁.code (g-i)
 rw [←hz] at q'; have h₁:‖(atomic (g-i)).1‖ ≤ Θ*τ:= by rw [map_sub]; exact q'.1
 have h₂:‖(atomic (g-i)).2‖* h^2 ≤ Θ*τ:=by rw [map_sub]; exact q'.2
 change ‖Θ • c.1‖≤_ at h₁; rw [norm_smul,Real.norm_of_nonneg z.le] at h₁
 have hm:0<h^2:=by positivity
 change ‖(Θ/h^2) • c.2‖ * h^2 ≤ _ at h₂; rw [norm_smul,Real.norm_of_nonneg (div_nonneg z.le hm.le), mul_right_comm,div_mul_cancel₀ _ hm.ne'] at h₂
 have h₃:‖c‖ ≤ τ:=by rw [Prod.norm_def]; exact max_le ((mul_le_mul_iff_right₀ z).mp h₁) ((mul_le_mul_iff_right₀ z).mp h₂)
 exact ((hc.pay _).2).trans (mul_le_mul_of_nonneg_left h₃ (zero_le_one.trans hc.large))
namespace Awareness
variable {c v':Coords ι}{r a' b' c' w' d' f:ℝ} {A0:ℝ} (H₀:Awareness F₁ Y W R j m q l M c h Θ x a a₀ r e w β)
include H₀
lemma increase {nQ:ℕ}{wΘ:ℝ}(hk:wΘ ≤ x)(p:j≤n₀)(v:nQ ≤ m)(u:a≤a')(h0:a₀≤A0)(f:r≤b')(g:e≤c')(t:w≤w')(l':β≤d'):Awareness F₁ Y W R n₀ nQ q l M c h Θ wΘ a' A0 b' c' w' d':= by obtain ⟨B,Q,T,V,J⟩:= H₀; exact ⟨B,Q,T,V,fun i=> Tab_upgrade (Tab_down (J.deeds i) p v hk) u h0 f g t l',J.books⟩ -- replace f.fst->u
lemma reform (D:0 < Θ)(p:1≤h)(H₁:Awareness F₁ Y W R j m q l M' v' h Θ x a' A0 b' c' w' d'): Awareness F₁ Y W R j m q l (M+M') (c+v') h Θ x (a+a') (a₀+A0) (r+b') (e+c') (w+w') (β+d'):=by
 obtain ⟨B,Q,T,V,J⟩:= H₀; obtain ⟨G,B',Z,Y',K⟩:= H₁; refine ⟨B+G,Q+B',T+Z,V+Y',?_, bend_add _ J.books.1 K.books.1,bend_add _ J.books.2.1 K.books.2.1,bend_add _ J.books.2.2.1 K.books.2.2.1,bend_add _ J.books.2.2.2.1 K.books.2.2.2.1,bend_add _ J.books.2.2.2.2.1 K.books.2.2.2.2.1,?_⟩
 · intro i; have he:= Tab_add (J.deeds i) (K.deeds i) (zero_le_one.trans p); rw [zero_add,←map_add] at he; exact he
 have he: InΦ (atomic (c+v'))∧ (F₁.colors Ω).Eigenspace (atomic (c+v')):= (F₁.representation _ h Θ _ D p).2 (LinearMap.mem_range_self _ _); exact he.symm
lemma remint (D:0<Θ)(p:1≤h)(s:ℝ): Awareness F₁ Y W R j m q l (s • M) (s • c) h Θ x (|s| *a) (|s| *a₀) (|s| *r) (|s| *e) (|s| *w) (|s| *β):=by
 obtain ⟨B,Q,T,V,J⟩:= H₀; refine ⟨s • B,s • Q,s • T,s • V,?_,bend_scale _ _ J.books.1,bend_scale _ _ J.books.2.1,bend_scale _ _ J.books.2.2.1,bend_scale _ _ J.books.2.2.2.1,bend_scale _ _ J.books.2.2.2.2.1, ((F₁.representation _ h Θ _ D p).2 (LinearMap.mem_range_self _ _)).symm⟩
 intro i; have he:= Tab_coin (J.deeds i) s (zero_le_one.trans p); rw [smul_zero,←map_smul] at he; exact he
omit H₀
lemma nullJ (D:0<Θ)(p:1≤h) : Awareness F₁ Y W R j m q l 0 0 h Θ x 0 0 0 0 0 0:= by refine ⟨0,0,0,0,fun _=> ?_,bend_zero _,bend_zero _,bend_zero _,bend_zero _,bend_zero _,((F₁.representation _ h Θ _ D p).2 (LinearMap.mem_range_self _ _)).symm⟩; rw [map_zero]; exact Tab_zero
lemma finiteT {ε:Type*}(S:Finset ε)(M:ε→ Site Ω→Mark Ω)(c:ε→ Coords ι)(a a0 r e w z:ε→ℝ)(u:∀ i∈ S,Awareness F₁ Y W R j m q l (M i) (c i) h Θ x (a i) (a0 i) (r i) (e i) (w i) (z i))(D:0<Θ)(p:1≤h): Awareness F₁ Y W R j m q l (∑ i∈S,M i) (∑ i∈S,c i) h Θ x (∑ i∈ S,a i) (∑ i∈ S,a0 i) (∑ i∈S,r i) (∑ i∈S,e i) (∑ i∈S,w i) (∑ i∈S,z i):= by
 induction S using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact nullJ D p
 | insert i S t ih => simp only [sum_insert t]; exact (u i (mem_insert_self ..)).reform D p (ih fun j v=>u j (mem_insert_of_mem v))
end Awareness
end Lampshade
end YM.CF.QuadClock
