import Anomaly.Contact
import Anomaly.Basis.Tuft
/-! Realization. Use one Root.Tag Bill.PH even including unphysical representatives. At unmasked anchors, restrict actual use alternatively to onsite inputs with street = [] so independent of all links. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered StressExchange Reed
variable {N B M:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h p' x₀ y s:ℝ}{k p q j L:ℕ}
variable {K:Scree.Loom N}{o:Site N}{A:Op (Single N)} (H: Moto.Fit o P.power 1 f A)(G:Tucked o A)(T:DockPulse P K t d a h s j q)(l:16+1+10+q≤ j*P.B)(h₁:d≤ 1)
local notation "Ω"=>Single N
local notation "Λ"=> halo (j*P.B) {node o}
local notation "uB"=> pingS P.threshold Λ
local notation "VΛ"=> ((temple j P (node o)):Aura N)
local notation "Χ" V:max=> ρlens A (profile V)
local notation "P★"=> tickA N
include l
private lemma coin_hp : halo (16*1+1+q+10) {node o}⊆ (VΛ).val :=by apply Corona.halo_mono _ le_rfl; omega -- include
include H G T l h₁
lemma logoEq (x:Orbit N)(v:pingS P.threshold Λ x.1): Χ (K x)= Χ (x.1) := profile_bind H G _ (coin_hp l) T h₁ x v
lemma same_pan (U V: Pane N) (u: Agrees Λ U V) : Χ U= Χ V:=by
 unfold ρlens; refine sum_congr rfl fun i _=> sum_congr rfl fun j w=> ?_; by_cases g:boxM A i j=0; · unfold Φp Swell.arm; rw [g,zero_mul,zero_mul]
 unfold Φp Swell.arm; obtain ⟨p,t⟩:=eyeΖ H G _ _ g; have hp:(χrod i j).card≤ 16+1:= (trace_k ..).trans (by omega)
 have hx: χrod i j⊆ Λ:=by exact (footprintGeodesic (trace_g ..) t (show _ from hp)).trans (Corona.halo_mono (by omega) le_rfl) -- tune binder j shadow
 rw [show Tulip.track _ _ _= _ from (show Tulip.track (profile U) (node i.1) (Λrod i j) = Tulip.track (profile V) (node i.1) (Λrod i j) from ?_)] -- tune
 rw [track_pr,track_pr]; exact congrArg Tulip.brand (travel_local _ _ _ _ (fun e p q=>u e (hx (List.mem_toFinset.mpr p)) (hx (List.mem_toFinset.mpr q))))
omit H G T l h₁
abbrev χmask (j:ℕ)(P:BudgetPoint)(o:Site N)(A:Op (Single N)):Pane N→Op (Single N):= Set.indicator {U|pingS P.threshold (halo (j*P.B) {node o}) U} (fun V=> ρlens A (profile V))
-- yes variables o/j Hygiene local notation conflict.Correct after check
abbrev Ωmask (j:ℕ)(P:BudgetPoint)(o:Site N)(A:Op (Single N)): Mark N:= fun v=> preJ (tickA N) (χmask j P o A v.1)
local notation "M_"=> χmask j P o A
local notation "W_"=> Ωmask j P o A
local notation "V_"=> (houseK P (grooveB j P (node o)) (firePlate K (ρlens A)))
local notation "S_"=> offsetMask (j*P.B+12) o
include G H T l h₁
lemma support_T (x:Orbit N): let L:= cutM (modesIn N Λ); L * χmask j P o A x.1 *L= χmask j P o A x.1:=by
 let S':=modesIn N Λ
 intro M; unfold χmask; by_cases t:x.1∈{V:Pane N| uB V}; swap; · rw [Set.indicator_of_notMem t]; simp
 rw [Set.indicator_of_mem t]; let F:Op Ω:= Χ (x.1); ext i j; change (cutM S' * F*cutM S') _ _=F i j; rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases v: F i j=0; · rw [v]; simp
 obtain ⟨p,q,t⟩:∃ r s:SU.Slot,A (i.1,r) (j.1,s)≠0:=by
    by_contra! k; apply v; rw [show F i j=arm A i.1 j.1 _ i.2 j.2 from stride_X A i.1 j.1 _ (fun _=>0) i.2 j.2, Swell.arm,show boxM A i.1 j.1=0 from Matrix.ext (fun p q=> k p q),zero_mul]; rfl
 have hx:= H.2.2 _ _ t; change separation o i.1.1≤1 ∧ separation o j.1.1≤1 at hx
 rw [if_pos (show i∈S' from (modes_at ..).mpr (halo_spec.mpr ⟨_,mem_singleton_self _,by rw [Hove.ζdist]; omega⟩)),if_pos (show j∈S' from (modes_at ..).mpr (halo_spec.mpr ⟨_,mem_singleton_self _,by rw [Hove.ζdist]; omega⟩)),one_mul,mul_one]
lemma kin_coat (V:Pane N)(C:Seat N→SU.E): M_ (Lattice.gauge C V)= twist (tradew N C) (M_ V):=by
 unfold χmask; let x:Orbit N:=(V,Classical.arbitrary _); by_cases g:pingS P.threshold Λ V; swap; · rw [Set.indicator_of_notMem (show V∉_ from g), Set.indicator_of_notMem (show gauge C V∉{U:Pane N| uB U} from mt (pingB V C).mp g),map_zero] -- tune `_`
 let y:Orbit N:= (gauge C V,threadG C x.2); have hy:= (pingB V C).2 g; rw [Set.indicator_of_mem (show V∈{U:Pane N|uB U} from g),Set.indicator_of_mem (show y.1∈ _ from (show y.1∈ {U:Pane N|uB U} from hy)),←logoEq H G T l h₁ x g,←logoEq H G T l h₁ y hy]
 -- general Soak via suites
 obtain ⟨F,W,h,v,u,q₁⟩:= show Soak (node o) (ρlens A) a _ d from Ωcoat H G T.pos h₁ T.hint.le; let z:= roller T.pos T.roof x
 rw [show Χ (K x)= _ from q₁ z, show Χ (K y)=_ from q₁ (roller T.pos T.roof y), map_sum]
 refine sum_congr rfl fun i _=>?_ ; rw [show roller T.pos T.roof y = _ from roll_g T.pos T.roof C x,(h i).toTicket.frame.frame]; rfl
lemma poll_Jx(x:Orbit N): V_ x=dg (M_ x.1):=by
 unfold houseK χmask; by_cases t:x∈ pingMask P Λ
 · rw [Set.indicator_of_mem t,Set.indicator_of_mem (show x.1∈{U:Pane N|uB U} from t),←logoEq H G T l h₁ x t]
 rw [Set.indicator_of_notMem t, Set.indicator_of_notMem (show x.1∉{U:Pane N|uB U} from t)]; simp [dg,dyad]
local notation "Px"=> νt a d 16*(Haro.horn*f)
open Window
attribute [local instance] Rill.boreKSpace Rill.boreXN
lemma measureχ : WindowTag W_ o (j*P.B+12) (Px+Px):=by
 let E:= Λ; let F:=M_; let A':=P★
 have ht(x:Pane N): F x = ({V:Pane N| uB V}).indicator (fun V:Pane N=>ρlens A (roller T.pos T.roof (V,Classical.arbitrary _)).val) x:=by
    by_cases l':pingS P.threshold E x; · unfold F χmask; rw [Set.indicator_of_mem (show x∈{V:Pane N|uB V} from l'),Set.indicator_of_mem (show x∈{V:Pane N|uB V} from l')]; exact (logoEq H G T l h₁ (x,Classical.arbitrary _) l').symm
    unfold F χmask; rw [Set.indicator_of_notMem (show x∉{V:Pane N|uB V} from l'),Set.indicator_of_notMem (show x∉{V:Pane N|uB V} from l')]
 let Z:=modesIn N E; have he:=Ωcoat H G T.pos h₁ T.hint.le
 have hk(x:Pane N):∑ i:Single N,∑ j:Single N,‖F x i j‖≤ Px:=by
    rw [ht]; by_cases s:uB x; · rw [Set.indicator_of_mem (show x∈{V:Pane N|uB V} from s)]; exact Soak.siteCost he T.hint.le _
    rw [Set.indicator_of_notMem (show x∉{V:Pane N|uB V} from s)]; simpa using soakCostNN he
 let Y:= Tset N; have he':A'=cutM Y:= touchP _
 have hm:Envelope F:=by
    constructor
    · have hV : Measurable (fun V:Pane N=>ρlens A (roller T.pos T.roof (V,Classical.arbitrary _)).val):=by
        obtain ⟨f,W,U,t,C,p⟩:= he; simp_rw [p]; apply Finset.measurable_fun_sum; intro i w; exact (((U i).toTicket.cont).measurable.comp (roll_m T.pos T.roof)).comp (measurable_id.prodMk measurable_const)
      rw [funext ht]; exact hV.indicator ping_o.measurableSet
    refine ⟨Px,fun v=>?_⟩
    rw [ht]; by_cases u:uB v; · rw [Set.indicator_of_mem (show v∈{x:Pane N|uB x} from u)]; exact norm_U he T.hint.le _
    rw [Set.indicator_of_notMem (show v∉{x:Pane N|uB x} from u),norm_zero]; exact soakCostNN he
 refine ⟨AtSupport.mono (AtSupport.fromEval (S:= inspected Λ) (fun x=>preJ A' (F x)) (Girt.pole_w _ (preJ A') (by unfold preJ dg dyad; fun_prop) hm) ?_ ?_) (inspect_fits ..),?_,?_, fun x y H=> congrArg (fun V:Pane N=> preJ A' (F V)) H⟩
 · intro x y Q; apply congrArg; have ht: uB x ↔ uB y:= Chaff.fenceW Λ Q _; unfold F χmask; by_cases v:uB x; · rw [Set.indicator_of_mem (show x∈{x:Pane N|uB x} from v),Set.indicator_of_mem (show y∈{x:Pane N|uB x} from ht.mp v)]; exact same_pan H G T l h₁ _ _ (agrees_mono Q (Finset.coe_subset.mpr subset_union_left))
   rw [Set.indicator_of_notMem (show x∉{x:Pane N|uB x} from v),Set.indicator_of_notMem (show y∉{x:Pane N|uB x} from mt ht.mpr v)]
 · intro x; rw [he']; refine Window.fine_enlarge (modes_monotone (show E⊆ inspected Λ from subset_union_left)) (StressExchange.inSector _ Y Z (support_T H G T l h₁ (x,Classical.arbitrary _)))
 · intro C x; let X:= F x.1; let U:= tradew N C
   change preJ A' (F (Lattice.gauge C x.1))= twist (quantU U) (preJ A' X)
   have hpA: twist U A'=A' := Cascade.tick_g _
   rw [show F (Lattice.gauge C x.1)= twist U (F x.1) from kin_coat H G T l h₁ x.1 C]; unfold preJ; rw [map_add,twist_scalar,map_one,dg_cov]; simp only [map_mul,map_sub,map_one,hpA]
   rw [show Matrix.trace (A'*twist U X)=Matrix.trace (A'*X) from ?_]
   rw [← show twist U (A'*X)=A'*twist U X from by rw [map_mul,hpA]]; exact trace_twist ..
 intro x; let W:=F x.1; let p:=hk x.1; let hA:= Cascade.plus_P N
 refine (norm_add_le (Matrix.trace (A' * W) • (1:FC Ω)) _).trans (add_le_add ?_ ((Fixed.Extensive.dgN W _ _ (hA.norm_le _) (hA.one_sub.norm_le _)).trans p))
 rw [norm_smul,norm_one,mul_one, he',Matrix.trace]; refine (norm_sum_le ..).trans ((sum_le_sum ?_).trans p)
 intro i hi; change ‖(cutM Y*W) i i‖ ≤ _
 rw [cutM,Matrix.diagonal_mul]; split_ifs; rw [one_mul]; exact single_le_sum (fun i _=> norm_nonneg _) (mem_univ _)
 rw [zero_mul,norm_zero]; exact sum_nonneg fun j _=> norm_nonneg _
lemma keepPH : Contact K S_ W_ V_:=by
 refine ⟨(measureχ H G T l h₁).ticket,fun x=> ?_,fun x=>?_⟩
 · rw [poll_Jx H G T l h₁]; exact lift_v (pair_charge (support_T H G T l h₁ x)) (modes_monotone (Corona.halo_mono (Nat.le_add_right ..) le_rfl)) -- offset equal
 rw [poll_Jx H G T l h₁]; exact (bra_eq _ (Cascade.plus_P N) (mateK N) (tickB N)).symm
end YM.CF.Swell.Porticus
