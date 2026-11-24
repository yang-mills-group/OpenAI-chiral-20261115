import YM.CF.BProof.Counter.Duel
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi.Denn
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
variable {X D' Y Z:Support (More n)}{U:Pane n}
open AnalyticBridge.VerifiedReset Next.Foundations Push.Local PhysicalNext.JointLoad Heir
open Vow Rue Ione Larch Beau Floral
open Trees
namespace Cart
variable (C:Cart n m)
abbrev chi(P:BudgetPoint)(m:ℕ)(Γ a:ℝ):= chi_f P.order*chargeP P m Γ a
private lemma medals(P:BudgetPoint)(a:ℝ){Γ:ℝ}(p:DayT P.order Γ)(hp:0 ≤ h)(i:CubeP n)(D:Support (More n)): Medal P (stem i).val.2 D (Vow.flick (pur (block i.2)) (oV (W i.2 (C.kWh i a))) D- Vow.flick (pur (block i.1)) (oV (W i.1 (C.kWh i a))) D) h (chi P m Γ (C.kWh i a)):=by
 have he(x:Skye.Seat n):= rimR (W_paid (m:=m) (C.kWh i a) x (block x) le_rfl (by change separation x x ≤ m; simp) p) hp
 unfold chi chargeP; rw [sub_eq_add_neg,mul_add]; exact (Vow.flick_M (pur (block i.2)) (pur (stem i)) Finset.subset_union_right hp (he i.2) D).plus (Vow.flick_M _ (pur (stem i)) Finset.subset_union_left hp (he i.1) D).negT
private lemma cost_j (P:BudgetPoint)(a Γ:ℝ)(i:CubeP n): chi P m Γ (C.kWh i a)= C.w i.1 i.2*chi P m Γ a:=by unfold chi; rw [pair_main,mul_left_comm]
def places(m:ℕ):ℕ:=(2*m+5)^4
def Z_cost(P:BudgetPoint)(m:ℕ)(Γ a z:ℝ):=(places m:ℝ)*(Real.exp z*chi P m Γ a)
lemma Z_paid(P:BudgetPoint)(hk:m+2≤ P.B)(a z:ℝ){Γ:ℝ}(p:DayT P.order Γ)(hΓ:0 ≤ Γ)(hp:0≤ h)(hz:0≤z) : Heats P h z (C.Zr a) (Z_cost P m Γ a z):=by
 let v(j:CubeP n):= chi P m Γ (C.kWh j a); let K:= chi P m Γ a; let T:= Real.exp z*K; let S(j:CubeP n):=pur (stem j); let A(i:Aura n):=∑ j:CubeP n,if S j=i then v j else 0
 have ht(a):0≤chi P m Γ a:=mul_nonneg (spicy_f _) (add_nonneg (jet_nn _ _ hΓ _) (jet_nn _ _ hΓ _)); have hT:0≤T:=mul_nonneg (Real.exp_pos _).le (ht a)
 refine Heats.iff_anuk.mpr ⟨A,⟨fun i=>sum_nonneg fun j _=> ite_nonneg (ht _) le_rfl,fun i D u w=>migrate S _ univ v u (fun i _ D _ _=> medals C P a p hp i D) i w⟩,fun i=>?_⟩
 unfold tallB A; simp_rw [sum_mul]; rw [sum_comm,Fintype.sum_prod_type]
 let F(j u:Skye.Seat n):=C.w j u*T; let X(x:Skye.Seat n):Prop:= separation x i ≤ m+2; have hx(x:Skye.Seat n)(u:CubeP n)(p:x=u.1): (∑ y:Aura n with i∈ y.val,(if S u=y then v u else 0)* Trees.currency P.B z y.val)≤ if X x then F x u.2 else 0:=by
    rw [sum_filter,sum_eq_single (S u)]; swap
    · intro i _ t; split; rw [if_neg t.symm,zero_mul]; rfl
    swap; · simp
    rw [if_pos rfl]; subst x; unfold v; rw [cost_j]; by_cases p:C.w u.1 u.2=0; · unfold F; rw [p,zero_mul,zero_mul,zero_mul]; split_ifs<;>rfl
    split; rename_i v;
    · obtain ⟨j,h,w⟩:= halo_spec.mp (joined_in _ _ (C.far _ _ p) i v); rw [mem_singleton.mp h] at w; rw [if_pos w]; rw [show F _ _= C.w u.1 u.2 * K * Real.exp z from by unfold F T; ring]; refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (C.nn ..) (ht a))
      apply Real.exp_monotone; apply mul_le_of_le_one_right hz; exact_mod_cast cover_j P _ _ (C.far _ _ p) hk
    refine ite_nonneg (mul_nonneg (C.nn ..) hT) le_rfl
 refine le_trans (sum_le_sum fun i _=> sum_le_sum fun j _=> hx i (i,j) rfl) ?_
 simp_rw [← Finset.ite_sum_zero]; -- tune
 unfold F; simp_rw [← Finset.sum_mul,C.day,one_mul]; rw [←sum_filter,sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hT
 let L:=univ.filter X; have hp:L= Lattice.halo (m+2) {i}:=by ext x; simp only [L,X,mem_filter,mem_univ,true_and,halo_spec,mem_singleton,exists_eq_left]; rw [separation_comm i]
 exact_mod_cast (show L.card ≤ places m from hp ▸ ((Lattice.Corona.halo_size {i} (m+2)).trans_eq (by unfold places; rw [card_singleton,one_mul]; ring))) -- maybe hp ▸ reversed
end Cart
lemma tmax(p:Face (Per n))(x y: Site n)(h:x∈ touched p)(he:y∈ touched p): separation x y≤2:=by
 let a:=p.1; let i:=p.2.val.1; let j:=p.2.val.2; let b:=a+step i; let c:=a+step j; let d:=b+step j
 have ht(p q : Site n) : separation p q=separation q p:=separation_comm ..
 have w(x:Site n)(h:x∈ touched p):x=a∨x=b∨x=c∨x=d:=by rw [touched,square_corners] at h; simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h; change x=a∨x=b∨x=d∨x=c∨x=a at h; tauto -- tune
 have hb:separation a b≤1:= Work.E01.sep_step_le ..; have hc:separation a c≤1:= Work.E01.sep_step_le ..; have hh:separation b d≤1:= Work.E01.sep_step_le ..; have hd:separation c d≤1:=by rw [show d=c+step i from add_right_comm ..]; exact Work.E01.sep_step_le ..
 have hg:= separation_triangle a b d; have hG:= separation_triangle b a c; have := ht b a; have := ht c a; have := ht d a; have := ht d c; have := ht d b; have := ht b c
 rcases w x h with rfl|rfl|rfl|rfl <;> rcases w y he with rfl|rfl|rfl|rfl <;> first | omega | simp
lemma tping (X:Support (More n))(V: Pane n)(h: Agrees (Lattice.halo 2 X) U V): pingS a X U ↔ pingS a X V:=by
 have hp(i:Face (Per (More n)))(q:¬Disjoint X (touched i)): faceValue U i=faceValue V i:=by
    obtain ⟨j,p,v⟩:= Finset.not_disjoint_iff.mp q; exact travel_local _ _ _ _ (agrees_mono h (fun x hx=>show x∈Lattice.halo 2 X from halo_spec.mpr ⟨j,p,tmax i j x v (List.mem_toFinset.mpr hx)⟩))
 exact ⟨fun t i q=>hp i q ▸ t i q,fun t i q=>(hp i q).symm ▸ t i q⟩
-- masked scalar cost: for every V, not just FleetS.
def freeze(P:BudgetPoint)(x:Skye.Seat n)(V:Pane n):ℝ:=if pingS P.threshold (block x).val.2 V then wish x V else 0
lemma frost(x:Skye.Seat n)(s:Sweep n): freeze P ((boxA s).symm x) (flashA s U)= freeze P x U:=by
 have hp : (block ((boxA s).symm x)).val.2=Salt.actY s (block x).val.2:=by rw [block_map]; rfl
 unfold freeze; rw [hp]; simp only [Salt.glowA,W_flash,Equiv.apply_symm_apply]
lemma frost_pay(x:Skye.Seat n): |freeze P x U| ≤ Compass.compassCost SU.group P*P.threshold^2:=by
 unfold freeze; split; rename_i t; · exact W_le (grow_b (singleton_subset_iff.mpr (block x).property) t)
 rw [abs_zero]; exact mul_nonneg (Compass.compass_cost_nn ..) (sq_nonneg _)
@[fun_prop] lemma freeze_M(x:Skye.Seat n): Measurable (freeze P x):=Measurable.ite ping_o.measurableSet (Compass.W_cont x).measurable measurable_const
lemma freeze_g(x:Skye.Seat n) : GaugeInvariant (freeze P x):=by intro k u; unfold freeze; simp only [pingB,wish,Compass.W_gauge]
lemma freeze_local(x:Skye.Seat n): LocalOn (Lattice.halo 4 {x}) (freeze P x):=by
 intro u v t; have hp:Lattice.halo 2 (block x).val.2⊆Lattice.halo 4 {x}:= Eire.icing (by omega: (2:ℕ)+2≤4) -- tune
 unfold freeze; simp only [tping _ v (agrees_mono t (Finset.coe_subset.mpr hp))]; split; exact Compass.W_local x u v (agrees_mono t (Finset.coe_subset.mpr ((Lattice.halo_subset ..).trans hp))); rfl
end YM.CF.Taxi.Denn
