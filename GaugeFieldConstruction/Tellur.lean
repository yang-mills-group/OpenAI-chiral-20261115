import GaugeFieldConstruction.HarvestW
import GaugeFieldConstruction.Matin
/- Loom extension X2-3. Gated arguments. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes Tenant Phase.Sample
variable {K b c d r v e a u:ℝ}{N m B:Side}{n j:ℕ}
local notation "Λ"=> CSide m B
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
namespace Ledger
open Shield
local notation "GS"=> SU.group
variable (j:ℕ)(u:ℝ)(R:Scree.Loom N)(S:Support (More N)) (F:Pane N→X)
abbrev Sect(S:Support (More N))(j:ℕ): Support (More N):=halo (j+8) S
lemma crown_H {V:Support N} (h:Grove (terr _) V)(j:ℕ) : Grove (terr _) (halo j V):=by
 have h'(i:Site N): i∈ bay (terr N) i j:=by rw [Tenant.tract]; exact halo_subset _ _ (mem_singleton_self _)
 rw [← show V ∪ (V.biUnion fun i=>bay (terr N) i j)=halo j V from ?_]; apply (show ∀ Q⊆V, Grove (terr N) (V ∪ (Q.biUnion fun i=>bay (terr N) i j)) from ?_) V (subset_refl V)
    -- order hz swap? 
 · intro Q; induction Q using Finset.induction_on with
   | empty=> intro; simpa using h
   | @insert i t u ih=>
     intro q; have hp:= (ih (subset_trans (subset_insert ..) q)).unite (Tenant.glen i j) (mem_union_left _ (q (mem_insert_self ..))) (h' i); rw [biUnion_insert]; rw [union_comm (bay (terr N) i j),← union_assoc]; exact hp
 rw [show (V.biUnion fun i=> _) = _ from (show (V.biUnion fun i=>bay (terr N) i j)=halo j V from by ext i; simp only [mem_biUnion,halo_spec, bay_mem]; rfl)]; exact Finset.union_eq_right.mpr (halo_subset _ _)
-- equality threshold allowed
abbrev flag_H(S:Support (More N))(j:ℕ)(u:ℝ)(A:Pane N) := Disjoint (flags u A) (halo j S)
def kiosk(S:Support (More N))(j:ℕ)(u:ℝ)(R:Loom N)(T:Ids N)(F:Pane N→ X)(A:Pane N):= if flag_H S j u A then F (R (A,T)) else 0
lemma flag_off (A:Pane N)(t:flags b A=∅)(p:b≤u): flag_H S j u A:=by
 have hx:flags u A=∅:=Subset.antisymm (by rw [← t]; intro i e; obtain ⟨f,h,H⟩:= (flags_spec ..).mp e; exact (flags_spec ..).mpr ⟨f,h,p.trans_lt H⟩) (empty_subset _); unfold flag_H; rw [hx]; simp
lemma flag_pay (A:Pane N)(h:pingS b (Sect S j) A)(p:b≤u):flag_H S j u A:=by
 apply disjoint_left.mpr; intro i e v; obtain ⟨f,w,W⟩:= (flags_spec ..).mp e; exact ((h f (not_disjoint_iff.mpr ⟨_,Corona.halo_mono (Nat.le_add_right ..) (subset_refl _) v,w⟩)).not_gt (p.trans_lt W)) -- tune not_gt
lemma flag_live : LocalOn (Sect S j) (flag_H S j u):=by
 have he (A A': Pane N)(f:Lattice.Agrees (Sect S j) A A')(h:flag_H S j u A): flag_H S j u A':=by
    apply disjoint_left.mpr; intro i v w; obtain ⟨t,z,g⟩:= (flags_spec ..).mp v; apply disjoint_left.mp h _ w; apply (flags_spec ..).mpr; refine ⟨t,z,?_⟩; rw [show faceValue A t=faceValue A' t from WilsonStartup.face_local t A A' (agrees_mono f ?_)]; exact g
    intro x p; obtain ⟨e,k,h⟩:=halo_spec.mp w; apply halo_spec.mpr; refine ⟨_,k,(separation_triangle _ i _).trans (Nat.add_le_add h ?_)⟩; have h:= WilsonStartup.visit_near t p; exact (separation_triangle _ t.1 _).trans ((Nat.add_le_add (WilsonStartup.visit_near t z) ((Eq.le (separation_comm _ x)).trans h)).trans (by decide:2+2≤8))
 exact fun U V h=> propext ⟨he U V h,he V U (fun j u k=>(h j u k).symm)⟩ -- name
variable {j u R} (h:Roof N u e j R)(t:Ids N)(d':e<d)
include h
lemma roof_sub {A:Pane N} (p:flag_H S j u A): Agrees S (R (A,t)) A:= fun i v w=> h.lamp _ _ _ (disjoint_of_subset_right (Corona.halo_mono le_rfl (insert_subset_iff.mpr ⟨v,singleton_subset_iff.mpr w⟩)) p)
lemma roof_elem (A:Pane N)(p:flags b A=∅)(s:b≤u): R (A,t)=A:=funext fun i=>roof_sub univ h t (flag_off j u univ A p s) i (mem_univ _) (mem_univ _)
include d'
lemma top_strict{A:Pane N}(p:flags b A=∅)(s:b≤u):A∈ Clode N d:=by
 let g:Ids N:=Classical.arbitrary _; rw [← roof_elem h g A p s]; exact grow_I (h.paid _) d'
lemma arm_eq (g:Baro K d 6 S F c)(A:Pane N)(p:flags b A=∅)(s:b≤u):kiosk S j u R t F A= F A:=by
 unfold kiosk; rw [if_pos (flag_off j _ _ _ p s),roof_elem h t A p s] -- tune arg
lemma arm_inv(g: Baro K d 6 S F c)(A:Pane N)(t':Ids N): kiosk S j u R t' F A=kiosk S j u R t F A:=by
 unfold kiosk; split_ifs with p; swap; · rfl
 let H(A:Pane N):= {y : Ids N | F (R (A,y))=F A}
 exact g.2.2.1 _ (grow_I (h.paid _) d') _ (grow_I (h.paid _) d') (fun i v w=> (roof_sub S h t' p _ v w).trans (roof_sub S h t p _ v w).symm)
lemma arm_loc (g: Baro K d 6 S F c): LocalOn (Sect S j) (kiosk S j u R t F):=by
 intro A A' p; unfold kiosk; have hp:= iff_of_eq (flag_live j u S _ _ p); by_cases w: flag_H S j u A'; swap; · rw [if_neg w,if_neg (hp.not.mpr w)]
 rw [if_pos w,if_pos (hp.mpr w)]
 apply g.2.2.1 _ (grow_I (h.paid _) d') _ (grow_I (h.paid _) d'); intro i v c; rw [roof_sub S h t w i v c,roof_sub S h t (A:=A) (hp.mpr w) i v c]; exact p i (halo_subset _ _ v) (halo_subset _ _ c)
lemma arm_milk (g:Baro K d 6 S F c)(P:BudgetPoint)(U:Pane N)(p:pingS P.threshold (Sect S j) U)(v:P.threshold ≤u)(k:hud_T 7 K) (w:P.order≤6): Allows P.order (kiosk S j u R t F ∘ Shield.solo P.threshold U) 0 c:=by
 let Y:=Sect S j; let V:=R (U,t); let τ:=P.threshold; let Fq:=Shield.solo τ U; let L:= FlightFlux.Keeper GS S; let H:= τ • L; let B:= increment V ∘ H; have he: flag_H S j u U:=flag_pay j u S U p v
 have hb:B 0∈Clode N d:=by
  change increment V (H 0) ∈_; rw [map_zero]; have he:increment V 0=V:=by simp
  rw [he]; exact grow_I (h.paid _) d'
 have hK: ‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>by rw [one_mul]; apply FlightFlux.keeper_buy (norm_nonneg _) _; exact fun i _=>norm_le_pi_norm ..
 have hh:TransK 7 B 0 K:=by
    intro i; apply comps H (x:=0) (f:=fun x:tangD N=> SU.fund (increment V x i)); rw [map_zero]; apply k; simp
    unfold H; rw [norm_smul,Real.norm_of_nonneg P.threshold_pos.le]; exact (mul_le_mul P.threshold_le hK (norm_nonneg _) zero_le_one).trans (one_mul _).le
 have hf:B=(fun v:tangD N=> increment V (H v)):=rfl
 refine ((g.2.2.2 (tangD N) B 0 hb hh).order w).germ ?_; have hg:Continuous Fq:= Shield.con_t ..; have hQ:ContinuousAt B 0:= cliff_n hh
 filter_upwards [hg.continuousAt.eventually (ping_o.mem_nhds (show Fq 0∈{U | pingS P.threshold Y U} from (show Fq 0=U by unfold Fq τ Shield.solo; simp).symm ▸ p)), hQ.eventually (isOpen_interior.mem_nhds hb)] with x q a'
 have hp:= flag_pay j u S _ q v; change F _=kiosk _ _ _ _ _ F _; rw [kiosk,if_pos hp]; apply g.2.2.1 _ a' _ (grow_I (h.paid _) d'); intro i k z; rw [roof_sub S h t hp i k z]; change SU.group.lieExp (τ • (L x i))*V i= SU.group.lieExp (τ • x i)*_
 rw [show L x i=x i from ?_,show V i=U i from roof_sub S h t he _ k z]; unfold L FlightFlux.Keeper; simp only [ContinuousLinearMap.pi_apply]; rw [if_pos (show FlightFlux.fitsSpan S i from ⟨k,z⟩)]; rfl
lemma arm_Env [MeasurableSpace X][BorelSpace X] (g:Baro K d 6 S F c)(s:1≤K):Envelope (kiosk S j u R t F):=by
 let P:=F ∘ fun i:Pane N=>R (i,t); let W:=fun i:Pane N=> (⟨R (i,t),grow_I (h.paid _) d'⟩ : Clode N d); have he: P=(Clode N d).restrict F ∘ W:=rfl
 have hh:Measurable P:= he.symm ▸ ((continuousOn_iff_continuous_restrict.mp g.2.1).measurable.comp (Measurable.subtype_mk (h.bill.comp (measurable_id.prodMk measurable_const)))) -- tune
 have ht:Measurable (kiosk S j u R t F):=by
    refine mealM (F:=fun i:Pane N=>flags u i) (flags_measurable_eq u) (G:=fun s (i:Pane N)=> if Disjoint s (halo j S) then P i else 0) fun v=> ?_; by_cases p: Disjoint v (halo j S); simp_rw [if_pos p]; exact hh; simp_rw [if_neg p]; exact measurable_const
 refine ⟨ht,c,fun i=>?_⟩; unfold kiosk; split; swap; · rw [norm_zero]; exact g.1
 let F':=R (i,t); exact (g.2.2.2 ℝ (fun _=> F') 0 (grow_I (h.paid _) d') fun e=> allows_const _ ((CStarRing.norm_of_mem_unitary (SU.fund_U ..)).trans_le s)).value
end Ledger
end YM.CF.XGarden
end
