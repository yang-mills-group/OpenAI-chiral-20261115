import SatinThinPoles

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- estimates on TWO-HILL for all tableaux, and on full final key widths for absolute expenses.
   Adapted `Roots/Poke, Cost, Halo` -/
variable {J I: Type} [Fintype J][Fintype I][LinearOrder J][LinearOrder I]
variable {N P B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{d u q h Vp Va M D Yp BQ Rt Zt κp W VZ VX VY A Γφ Lν Rν:ℝ}
local notation "Ω"=>mid N B
local notation "Ξ"=>mid P B
attribute [-instance] instDecidableEqLex

variable {n:Side}{P0:BudgetPoint}
structure FixedE (P0:BudgetPoint)(h v:ℝ)(X:RegBudget n): Prop where
 pay: ∃ g:Scree.Hub n→ℝ, (∀ i, PressB P0 i (X i) h (g i))∧ ∑ i,g i≤ v
structure FixedF (P0:BudgetPoint)(h v:ℝ)(K:ForceBudget n): Prop where
 pay: ∃ g:Force n→ℝ, (∀ i, ForceB P0 i (K i) h (g i))∧ ∑ i,g i≤ v
lemma FixedE.more {X:RegBudget n}(p:FixedE P0 h u X)(t:u≤q): FixedE P0 h q X:=by obtain ⟨g,r,s⟩:=p.pay; exact ⟨g,r,s.trans t⟩ -- structure tune
lemma FixedF.more {X:ForceBudget n}(p:FixedF P0 h u X)(t:u≤q): FixedF P0 h q X:=by obtain ⟨g,r,s⟩:=p.pay; exact ⟨g,r,s.trans t⟩
lemma sum_FixedE (s:J→RegBudget n)(b:J→ℝ)(z:Key J)(q:∀ i,FixedE P0 h (b i) (s i)): FixedE P0 h (∑ i:J,‖z i‖*b i) (∑ i:J,z i • s i):=by
 choose g r p using fun i=>(q i).pay
 let α (x:Scree.Hub n):=∑ i:J,‖z i‖ * g i x; refine ⟨α,fun i=>?_,?_⟩
 · rw [Finset.sum_apply]; exact Larch.prop_sum univ _ _ _ _ i fun j _=> súe _ _ (r j i) (z j)
 unfold α; rw [sum_comm]; exact sum_le_sum fun i _=>by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (p _) (norm_nonneg _)
lemma sum_FixedF (s:J→ForceBudget n)(b:J→ℝ)(z:Key J)(q:∀ i,FixedF P0 h (b i) (s i)): FixedF P0 h (∑ i:J,‖z i‖*b i) (∑ i:J,z i • s i):=by
 choose g r p using fun i=>(q i).pay
 let α (x:Force n):=∑ i:J,‖z i‖ * g i x; refine ⟨α,fun i=>?_,?_⟩
 · rw [Finset.sum_apply]; exact dom_K_fin i univ _ _ fun j _=> dúe _ _ (r j i) (z j)
 unfold α; rw [sum_comm]; exact sum_le_sum fun i _=>by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (p _) (norm_nonneg _)
lemma Axon_fixedE {L:ℕ}{x:Site (mid N B)}{X: ArcΦ}{E:RegBudget (mid N B)}(p:Axon L x P0 E h q X)(e:0≤h): FixedE P0 h q E:=by
 obtain ⟨G,k,v⟩:= p.vest.weight; let g(i:Scree.Hub (mid N B)):=if i.val.1=Cube.node x then G i else 0; refine ⟨g,fun i=>?_, le_trans ?_ (v (Cube.node x))⟩
 · unfold g; split; exact k i; next f=> rw [p.site i f]; exact Vale.rinse ..
 apply sum_le_sum; intro i _; by_cases t:i.val.1=Cube.node x; simp only [if_pos t.symm]; unfold g; rw [if_pos t]; exact tonne_ge _ _ _ (gradeE _ _ (k _) e) -- syntax
 unfold g; rw [if_neg t,if_neg (Ne.symm t)]

-- two-part bill: at end, low linear estimates on whole arena plus high order-one per-seat bound.
structure Pavilion (P:BudgetPoint)(h v b:ℝ)(E:RegBudget n)(K:ForceBudget n):Prop where
 pay: ∃ F G Y Z, E=F+G ∧ K=Y+Z ∧ FixedE P h b F ∧ FixedF P h b Y ∧ IncX primeU G P h v ∧ Dark primeU Z P h v

def PanoramaBill (P:BudgetPoint)(h W v b:ℝ)(E:Key J→RegBudget n)(K:Key J→ForceBudget n) : Prop:=∀ k:Key J, (∀ i, ‖k i‖≤ W)→ Pavilion P h v (b*Fintype.card J) (E k) (K k)
-- linear bill at a scale. 
variable (X:GramM (mid N B))(σ:J→Site (mid N B)) (tT:ℕ) (hX:1 ≤ h)
local notation "Η"=> Scree.Hub (mid N B)
local notation "Ψc"=>Cube.node ∘ σ
variable (L0:Side)(E:J→ RegBudget (mid N B))(Ys:J→ArcΦ)(pc:Force_M X.p.B (Cube.node ∘ σ) tT)(q_ν:∀ j, Axon L0.val (σ j) X.p (E j) h Γφ (Ys j))
include q_ν pc hX
lemma lean_C (z:Key J)(u:∀ i, ‖z i‖ ≤ 2)(hB:0≤ Γφ): IncX primeU (∑ i:J,z i • E i) X.p h (2*Γφ*tT):=by
 choose G p w using fun i=>(q_ν i).vest.weight; let L(j:J)(x:Η):= if x.val.1=node (σ j) then G j x else 0
 have hv:=zero_le_one.trans hX; have hz(i:J)(x:Η):PressB X.p x (E i x) h (L i x):=by unfold L; split; exact p ..; next t=> rw [show E i x=0 from (q_ν i).site _ t]; exact Vale.rinse ..
 let v(x:Η):=∑ i:J,‖z i‖ * L i x; refine ⟨⟨v,fun x=>?_,fun r=>?_ ⟩,fun _ p=>p.elim⟩
 · rw [Finset.sum_apply]; exact Larch.prop_sum univ _ _ _ _ x (fun j _=>súe _ _ (hz ..) (z j)) -- tune
 let I:=univ.filter fun i : J=> node (σ i)=r; have he:I.card ≤tT:=(card_le_card (show I⊆ _ from ?_)).trans (pc.2 r)
 swap; · intro k t; refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [Function.comp_apply,(mem_filter.mp t).2,separation_self]; omega
 rw [←sum_filter]; let U:= univ.filter fun x:Η=>r=x.val.1
 have hp(x:Η)(b:x∈ U): v x= ∑ i∈ I,‖z i‖* L i x:= Eq.symm (Finset.sum_subset (filter_subset ..) fun i _ q=> by unfold L; rw [if_neg (fun e=> q (mem_filter.mpr ⟨mem_univ _, e.symm.trans (mem_filter.mp b).2.symm⟩)),mul_zero])
 refine (le_trans ?_ (show (I.card:ℝ)*(2*Γφ)≤_ from (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (mul_nonneg (by norm_num) hB)).trans_eq (mul_comm ..))); rw [← nsmul_eq_mul, ←sum_const]; calc
    (∑ i∈ U,X.p.mass i.val.2 (v i)) = ∑ i∈U,∑ j∈I,‖z j‖* X.p.mass i.val.2 (L j i):=by
       refine sum_congr rfl fun i p=>?_ ; unfold BudgetPoint.mass; rw [hp i p,Finset.mul_sum]; exact sum_congr rfl fun j _=>mul_left_comm ..
    _ ≤ _:=by
       rw [Finset.sum_comm]; refine sum_le_sum fun i x=>?_ ; rw [←Finset.mul_sum]; have ht:∑ j∈ U,X.p.mass j.val.2 (L i j) ≤ Γφ:=by
          apply le_trans ?_ (w i r); rw [←sum_filter]; apply sum_le_sum; intro j p; rw [show L i j= G i j from if_pos ((mem_filter.mp p).2.symm.trans (mem_filter.mp x).2.symm)]
       exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (u i) hB)
omit q_ν
variable (V:Grace K R L)
variable {U:Grasp V.U B d} {G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} {Y:GramM (mid P B)}{Xp:Op SU.Slot}{q':Chi}
variable (Xo Yo:Key J→RegBudget (mid P B))(Zo:Key J→ForceBudget (mid P B))(Q:J→ℝ)(F:J→ArcΦ)(E_:Key J→ RegBudget (mid N B))(Yf:Key J→ForceBudget (mid N B))(C:J→ArcΦ)(s:J→ℂ)
variable (Fz: Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xp q' u h Vp Va σ Q F E_ Yf C s M D Yp BQ Rt Zt κp)
include Fz
variable (H:J→J→ℂ)
local notation "Dκ"=> νTip (FlameX σ E_ H)
variable (Tκ:∀ j:J, Axon R.L.val (σ j) X.p (νTip (FlameX σ E_ H) j) h Γφ (Ys j))
include Tκ
variable(hB:0≤Γφ)(g:8 ≤ X.p.B)(v:1≤ Lν)(t:Nice_B X.p.B tT Lν (1/8))
include g v t hB
lemma double_C (z:Key J)(u:∀ i, ‖z i‖ ≤ 2)(r:∀ i,‖ toV_C Ψc H z i‖ ≤ Lν) : IncX primeU (FlameX σ E_ H z) X.p h (2*Γφ*tT+wish_E X.p.B κp) ∧ Dark primeU (FlameK σ Yf H z) X.p h (χCut X.p.B tT Lν Va):=by
 obtain ⟨Φ,Qv⟩:= κFire V σ E_ Yf Xo Yo Zo Xp Q F C s Fz tT Lν v g pc.1 pc.2 t (zero_lt_one.trans_le hX) (toV_C Ψc H z) r
 rw [melt_H V σ E_ Yf Xo Yo Zo Xp Q F C s Fz H z]; exact ⟨Larch.add_v _ _ _ (lean_C X σ tT hX R.L Dκ Ys pc Tκ z u hB) Φ,Qv⟩
omit v t hB pc g Tκ
lemma force_pay (i:J) : FixedF X.p h Va (νΦK Yf {i}):=by
 let S:= MixT σ; have hu:= zero_lt_one.trans_le hX; let P:= X.p; let Q':Finset J:= {i}; let F_:= νΦK Yf Q'; let Y'(y: Force (mid N B)):= F_ y
 obtain ⟨k,w,v⟩:= (πόS V σ E_ Yf Xo Yo Zo Xp Q F C s Fz hu ({i}: Finset J)).bit
 let a(y:Force (mid N B)):= if (Ψc i)∈ y.val.1.val.2 then k y else 0
 refine ⟨a,fun x=>?_,le_trans ?_ (v (Ψc i))⟩
 · unfold a; split; exact w _; next g=>
     have hx:Y' x=0:=by contrapose! g; exact (tiltP_S V σ E_ Yf Xo Yo Zo Xp Q F C s Fz Q').1 _ g i (by simp [Q'])
     change ForceB _ _ (Y' x) _ _; rw [hx]; exact Vale.rinsed ..
 apply sum_le_sum; intro x _; unfold a giftK; split
 next e =>
    refine le_mul_of_one_le_left (gradeQ _ _ (w _) hu.le) (Real.one_le_exp ?_); have hp:= X.p.exponent_pos; positivity
 next e => rw [zero_mul]
include g v t hB pc Tκ
lemma elevated_C (z:Key J)(u:∀ i, ‖z i‖ ≤ Rν) (r:∀ i, ‖ toV_C Ψc H z i‖ ≤ Lν) (a b:ℝ)(k:wish_E X.p.B κp ≤ a)(w:wish_E X.p.B Va ≤ a)(p:Rν*Γφ≤ b)(q:Lν*Va ≤ b): Pavilion X.p h a (b*Fintype.card J) (FlameX σ E_ H z) (FlameK σ Yf H z):=by
 let Y_:= MixT σ; have hi(i)(g:i∈Y_):=(mem_filter.mp g).2; let G:=toV_C Ψc H z; let Q':= Gem_Q σ E_ G
 let W:=fun i:J=>G i; let O: ForceBudget (mid N B):=∑ i∈Y_, Mew.pine i G • νΦK Yf i
 have hf:= zero_lt_one.trans_le hX; have ht:=σηo V σ E_ Yf Xo Yo Zo Xp Q F C s Fz hf
 refine ⟨∑ i:J,z i • Dκ i,Q',∑ i:J,G i • νΦK Yf {i},O,melt_H V σ E_ Yf Xo Yo Zo Xp Q F C s Fz H z,rfl,?_,?_,?_,?_⟩
 · refine (sum_FixedE Dκ (fun _=>Γφ) z (fun i=>Axon_fixedE (Tκ i) hf.le)).more ?_; refine le_trans (Finset.sum_le_sum (g:=fun _=>b) (fun i _=> ((mul_le_mul_of_nonneg_right (u i) hB).trans p))) (le_of_eq ?_); rw [sum_const,nsmul_eq_mul,card_univ,mul_comm]
 · refine (sum_FixedF (fun i:J=>νΦK Yf {i}) (fun _=>Va) G (fun i=>force_pay X σ hX V Xo Yo Zo Q F E_ Yf C s Fz i)).more ?_; refine le_trans (Finset.sum_le_sum (g:=fun _=>b) (fun i _=> ((mul_le_mul_of_nonneg_right (r i) ht.2).trans q))) (le_of_eq ?_); rw [sum_const,nsmul_eq_mul,card_univ,mul_comm]
 · exact Provides.liftE h X _ _ (κFire V σ E_ Yf Xo Yo Zo Xp Q F C s Fz tT Lν v g pc.1 pc.2 t hf G r).1 k
 exact Provides.liftQ h X _ _ (sprint_K Y_ _ _ hf Lν Va (fun i _=> (tiltP_S V σ E_ Yf Xo Yo Zo Xp Q F C s Fz i).1) (fun i _=> πόS V σ E_ Yf Xo Yo Zo Xp Q F C s Fz hf i) (fun i=>Mew.pine i G) (fun i _=> by unfold Mew.pine; rw [norm_prod]; exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> r i)).trans_eq (Finset.prod_const ..)) v g ht.2 pc.1 pc.2 t (fun i x=> (hi i x).1) (fun i x=> (hi i x).2)) w
end YM.CF.QuadClock
