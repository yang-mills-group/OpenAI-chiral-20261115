import YM.CF.Ridge.Worth
import YM.CF.Pso.Fume
import YM.CF.Ione.Lean
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
local notation "B'"=> P.B
local notation "P'"=> (P.supportExponent+1+1)
structure Trim_X(Q:Sweep n→Prop)(P:BudgetPoint)(F:Pax n)(K:Cusp n)(h Lc dK dt γ:ℝ)(a:ℝ)(R':RegBudget n)(Z:Cusp n):Prop where
 render: ∃ (A v:Aura n→ℝ)(C:blazeK n), Ready Palot.stern P.B A (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1) ∧ (∀ X, Medal P X.val ∅ (F X) h (A X)) ∧ Anuk Z v P h ∧ (∀ i:Seat n,tallB v P.B (P.supportExponent+1+1) i ≤ Lc) ∧ (∀ s, Q s →∀ v:Orbit n, Injective (priorP v.2)→Zeal s v (suit_Y s) Z) ∧ Pant_k Q F ∧ (∀ s, Q s→∀ v:Orbit n, Injective (priorP v.2)→Zeal s v (suit_Y s) K) ∧ ArmsK P K C h ∧ (∀ i:Seat n,tallB (Vow.hymn C) P.B (P.supportExponent+1+1) i ≤ dK) ∧ IncX Q R' P h dt ∧ ∀ V:Orbit n,FleetS P.threshold V.1→ coldE P (FeeD P F) V= owed_E n a+exponentL P R' V.1+fuelV P Z V
variable {γ e q α γ' KU:ℝ}{wisp0 c':ℝ}{K':Cusp n}{L:blazeK n} (Q:Sweep n→Prop) (Wp:Wisp P F 0 h γ c d) (T:ArmsK P K L h)(η0:1≤h)(hp:Pant_k Q F)(ht:∀ s,Q s →∀ v:Orbit n, Injective (priorP v.2) → Zeal s v (suit_Y s) K)(KK:∀ i:Seat n,tallB (Vow.hymn L) P.B (P.supportExponent+1+1+1) i ≤ KU)
include Wp T η0 hp ht KK
lemma zeal_b (τ:Ids n): Trim_X Q P F K h (c+d) KU (reserveT P.power P.order P.B 1*(d+d)) γ (∑ i:Aura n,rim_r P F (1,τ) i) (cast_E (rim_t P F (1,τ)) τ) (nextE (rim_r P F (1,τ))):=by
 let PF:=rim_r P F (1,τ); let W:=rim_t P F (1,τ); obtain ⟨A,C,LL,q,uF,uG,hW,hL,hC,hv,wU,hh,he⟩:= pay_Wr P F Q Wp η0 hp (1,τ) rfl
 let Zr:= ∑ i:Aura n,PF i; let hν:=zero_le_one.trans η0; let S:= nextE PF; let R' := cast_E W τ
 refine ⟨⟨A,LL,L,q,uF,⟨fun i=> (uG i).wage hν,fun i D _ _=>nom_F η0 P i _ (uG i) D⟩,hL,?_,hp,ht,T,?_,worth_SK P W τ wU hν hW Q hh hC,?_⟩⟩ -- C used twice
 · intro s q V p i D t v; rw [nextE,he s q]; change _=suit_Y s (-(PF i•1)); rw [map_neg,map_smul,map_one]
 · intro i; apply (tall_m (b:=P.supportExponent+1+1+1) (Vow.hymn L) _ (le_add_of_nonneg_right zero_le_one) i).trans (KK i); exact fun i=>sum_nonneg (fun j v=> (T.price _ _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2).wage hν)
 intro V t; have he:coldE P (FeeD P F) V=coldE P (cashV PF+W) V:=sum_congr rfl fun i q=>hv _ _ (hates (by rw [sdiff_empty]; exact (mem_filter.mp q).2)); have ht':∑ i:Aura n,owed_E n (PF i)= owed_E n Zr:= (Finset.sum_smul ..).symm; have hP: owed_E n Zr+fuelV P (nextE PF) V=coldE P (cashV PF) V:=by rw [←ht']; exact tall_K P PF V t
 change coldE P (FeeD P F) V= owed_E n Zr+exponentL P R' V.1+fuelV P S V; rw [he,crep, ←ocean P W τ wU V, ←hP]; change _=_+exponentL P (cast_E W τ) V.1+fuelV P (nextE PF) V; abel
lemma taut_W (τ:Ids n)(γc ρ:ℝ)(hv:1 ≤ ρ)(hp':0< γc)(hh:degreePrice P.B γc 1<1)(et:c+d+(γ*(degreePrice P.B γ 1)^0*(1-degreePrice P.B γ 1)⁻¹) ≤1)(hpS:ρ*KU+Real.exp 1*((γ*(degreePrice P.B γ 1)^0*(1-degreePrice P.B γ 1)⁻¹)+(c+d))≤ γc) :let f:=cast_E (rim_t P F (1,τ)) τ; let S:= budgetR (roomV P F K (nextE (rim_r P F (1,τ)))); let v:=∑ i:Aura n,rim_r P F (1,τ) i; IncX Q f P h (reserveT P.power P.order P.B 1*(d+d)) ∧ Dark Q S P h (Cog_P P γc ρ) ∧∀ V:Orbit n,FleetS P.threshold V.1 → Palot.hGas (flags P.threshold V.1) (keyL P K F V)= Real.exp v • (exp (exponentL P f V.1)*fueled P S V):=by
 intro f S v; obtain ⟨A,V',C,hR,p,w,l,t,u,i,vT,c₀,hq,xT⟩:=(zeal_b P F K Q Wp T η0 hp ht KK τ).render
 have he: 0 ≤ P.supportExponent+1:=(add_pos P.exponent_pos zero_lt_one).le
 refine ⟨hq,dark_F (γ':=γc) (Qm:=Q) vT w.2 w.1 hR he zero_lt_one p zero_lt_one η0 hv ?_ l c₀ le_rfl hh hp' hpS ?_,fun V t'=>?_⟩
 · intro x; refine (add_le_add_left ?_ _).trans et; obtain ⟨j,k⟩:= x.property; apply le_trans _ (l j); exact (le_mul_of_one_le_right (w.1 x) (Real.one_le_exp (mul_nonneg (add_nonneg he zero_le_one) (by exact Nat.cast_nonneg (coverNumber P.B x.val))))).trans (single_le_sum (s:=Finset.univ.filter (fun i:Aura n=>j∈i.val)) (f:=fun i=>V' i * Trees.currency P.B (P.supportExponent+1+1) i.val) (fun i _=>mul_nonneg (w.1 i) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,k⟩))
 · intro s V W' y m j; refine ⟨fun x D p l=>?_,fun x D p l=>?_,fun x=>?_⟩; rw [tama s _ j]; exact i s y V m x D p l; rw [tama s _ j]; exact t s y V m x D p l; rw [tama s _ j]; exact u s y _ _
 have hx := xT V t'; change _= owed_E n v+ exponentL P f V.1+ fuelV P (nextE (rim_r P F (1,τ))) V at hx
 rw [asterT hR he p zero_lt_one η0 V t' _ hx.symm]; letI :NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ (Cipher n); rw [exp_add]; change exp (owed_E n v)* exp _* _= Real.exp v • _; rw [owed_E, ←thim_v, ←Iva.yeaH, ←Complex.ofReal_exp, thim_v]; unfold Lilt.thim; rw [smul_mul_assoc,one_mul,smul_mul_assoc]
end YM.CF.Ione
