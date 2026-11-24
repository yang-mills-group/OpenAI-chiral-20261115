import YM.SU5.Exchange.Pilot.Bundle
import YM.CF.Hype.Migrate
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
-- Head of regulator as mask tile. Copies beyond positive degree 2 included!
variable {h a c:ℝ} {F : InkD n} {i:Scree.Hub n}
open Bake
variable {q:ℕ}
private lemma readings (x:X.val⊆ Y.val)(i:Orbit n)(hi:i.1∈σX P Y D) : X.val∩ D=X.val∩flags P.threshold i.1:=by
 let A:=hi.2; ext j; simp only [mem_inter]; refine ⟨fun v=>⟨v.1,A v.2⟩,fun ⟨v,w⟩=> ⟨v,?_⟩⟩; by_contra r; exact disjoint_left.mp (ping_le hi.1) (mem_sdiff.mpr ⟨x v,r⟩) w
private lemma puff_mono (t:X.val⊆Y.val)(v:Orbit n)(p:v.1∈σX P Y D): pingS P.threshold (X.val\(D∩X.val)) v.1:=by
 apply grow_b (Z:=Y.val\D) _ p.1
 intro i u; obtain ⟨x,y⟩:= mem_sdiff.mp u; exact mem_sdiff.mpr ⟨t x,fun z=> y (mem_inter.mpr ⟨z,x⟩)⟩
variable {D':Support (More n)}{C:Copy n}
abbrev realFire(x:Orbit n):= (C x).val -- implicit C issue later
lemma worth_Rack (m:Medal P X.val D' C h a)(u:1≤h)(x:X.val⊆ Y.val)(w:D'= D∩X.val): Marque P Y X D ((realFire (C:=C))) h a:=by
 -- Flour.lit read? Sector from life
 refine ⟨⟨continuous_subtype_val.measurable.comp m.keeps,fun i=>life (m.lit i),fun i j _ _ s t=> congrArg Subtype.val (m.same i j (agrees_mono s (Finset.coe_subset.mpr x)) (t.mono (Finset.coe_subset.mpr x))), fun i g _=> congrArg Subtype.val (m.gaugeX i g)⟩,?_⟩
 subst D'; let W:=(realFire (C:=C)); obtain ⟨M,hM,H,h₁⟩:= m.pays; let J(z: Finset (Dwell n))(v:Orbit n):= Pastry.crumb (W v) z • poke z
 let m'(z:Finset (Dwell n)):=M z*h^z.card
 have ha: W=∑ k:Finset _,J k:=by funext i; rw [Finset.sum_apply]; exact (fineShape (C i)).allP
 have hc(i': Finset (Dwell n)): AuraOp P Y D (J i') h (m' i') :=by
      apply AuraOp.sat h (P:=P) (fun i=> Pastry.crumb (W i) i') (poke i') (Ark.piece _ u) (hM i')
      intro V pV S U; exact (H V (puff_mono x V pV) (Subset.trans inter_subset_left U)).haveP i'
 have hz:(∑ k:Finset _,m' k)= joinV (fun i:Finset (Dwell n)=>h^i.card) M:=sum_congr rfl (fun _ _=>mul_comm ..)
 have hx: AuraOp P Y D W h a := by
    rw [ha]; exact ((AuraOp.sumR h _ _ _ (fun i _=> hc i)).bigger (zero_le_one.trans u) (hz.trans_le h₁))
 exact hx.pay
private lemma pose_side (t:Crate P Y D X W)(p:Marque P Y X D V h a)(x:∀ U:Orbit n,U.1∈σX P Y D→W U=V U): Marque P Y X D W h a:=by
 refine ⟨t,?_⟩; obtain ⟨H,f,g,m⟩:=p.vet; refine ⟨H,f,g,?_⟩; intro I i Z z j k; refine Pence.germ (m I i Z z j k) ?_; filter_upwards [whileLit (Z:=Z) i] with u v; let V' : Orbit n:=(pressQ P Z I.1 u,I.2); have hw:=x V' v; first|exact congrArg (fun x:FC (Dwell n)=> x j k) hw|exact congrArg (fun x:FC (Dwell n)=> x j k) hw.symm
lemma crate_side (p:Marque P Y X D V h a)(q: Measurable W)(v:∀ x:Orbit n,Sector (camp X.val) false (W x))(u:∀ x:Orbit n,x.1∈σX P Y D→ W x=V x):Crate P Y D X W:=by
 refine ⟨q,v,fun i j h k l m=>?_,fun i t h=>?_⟩; · rw [u i h,u j k]; exact p.same i j h k l m
 rw [u i h, ←p.gauge i t h]; exact u _ ((Salt.glowF ..).mpr h)
def frostC (P:BudgetPoint)(C:Pax n)(X:Aura n): Firing n:= capR P X.val (fun x=>(C X x).val)
lemma frostCost (p:Medal P X.val ∅ C h a)(s:∀ i:Orbit n,∀ A:Ids n,C i=C (i.1,A))(t:1≤ h) : Herb P q X h (capR P X.val ((realFire (C:=C)))) a:=by
 have hx:=p.wage (zero_le_one.trans t); refine ⟨hx,?_,?_⟩
 · intro Y u D x K; by_cases w: Disjoint X.val D
   · exact (worth_Rack p t u (disjoint_iff_inter_eq_empty.mp w.symm).symm).capMask _ u
   have he(i:Orbit n)(hp:i.1∈ σX P Y D):capR P X.val ((realFire (C:=C))) i=(0:Firing n) i:=by unfold capR; rw [Set.indicator_of_notMem (mt (pingFix u hp).mp w : i ∉ pingMask P X.val)]; rfl
   have h0:Marque P Y X D 0 h a:= Marque.noR.bigger (zero_le_one.trans t) hx; refine pose_side (crate_side h0 ((continuous_subtype_val.measurable.comp p.keeps).indicator (measurable_fst ping_o.measurableSet)) ?_ he) h0 he
   intro i; unfold capR; by_cases h: i∈ pingMask P X.val; · rw [Set.indicator_of_mem h]; exact life (p.lit i)
   rw [Set.indicator_of_notMem h]; exact Sector.zero _
 intro Y g i w m; have hg:i∈ pingMask P X.val:= (pingFix g w).mpr (by simp); unfold capR; rw [Set.indicator_of_mem (show (i.1,m)∈_ from hg),Set.indicator_of_mem hg]; unfold realFire; rw [←s i]
open Ione
variable {f:Cusp n}{r:Aura n→ℝ}
def toastC(P:BudgetPoint)(F:Cusp n)(X:Aura n):Firing n:=fun i =>if fuelH (flags P.threshold i.1) X then (F X (flags P.threshold i.1 ∩ X.val) i).val else 0
lemma toastCost (p:Larch.Anuk f r P h) (t:1 ≤ h) : Herb P q X h (toastC P f X) (r X):=by
 let Yz(i:Support (More n)):= i ∩ X.val
 let F(i:Orbit n):=flags P.threshold i.1; let W:=toastC P f X
 let Tt(k:Support (More n))(i:Orbit n):= if fuelH k X then (f X (Yz k) i).val else 0
 have ht(j) (w:fuelH j X):Medal P X.val (Yz j) (f X (Yz j)) h (r X):=p.2 X (Yz j) (nonempty_iff_ne_empty.mpr (by intro h; exact w (disjoint_iff_inter_eq_empty.mpr h).symm)) inter_subset_right -- neg def w unfolds
 have hw: Measurable W:=by
    have hx: W=fun i=> ∑ k:Support (More n), (({i:Orbit n|F i=k}:Set (Orbit n)).indicator (Tt k)) i:=funext fun i=>by
      rw [sum_eq_single_of_mem (F i) (mem_univ _),Set.indicator_of_mem (show i∈ {a| F a=F i} from rfl)]
      · rfl
      intro j z w; exact Set.indicator_of_notMem (show i∉ {a|F a=j} from Ne.symm w) _ -- alignment
    rw [hx]; apply Finset.measurable_sum; intro i _; refine Measurable.indicator ?_ (measurable_fst (flags_measurable_eq ..))
    by_cases u:fuelH i X; · rw [show Tt i=(fun x=> (f X (Yz i) x).val) from funext fun x=> if_pos u]; exact continuous_subtype_val.measurable.comp (ht _ u).keeps
    rw [show Tt i=(fun _=>0) from funext fun x=> if_neg u]; exact measurable_const
 have hs(i:Orbit n):Sector (camp X.val) false (W i):=by
    unfold W toastC; split; next h=> exact life ((ht _ h).lit i)
    exact Sector.zero _
 have hz{Y:Aura n}(D:Support (More n))(x:X.val⊆ Y.val)(v:Orbit n)(w:v.1∈ σX P Y D):W v=Tt D v:=by
    have hp:=readings x v w; unfold W toastC Tt; unfold Yz; rw [inter_comm D, hp, inter_comm (flags _ _), show fuelH D X=fuelH (flags P.threshold v.1) X from propext (by unfold fuelH; rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty,hp])]
 -- above Y too specific tied ov
 refine ⟨p.1 _,fun Y u D _ _=>?_,?_⟩
 · -- generalize hz needs polymorphic
   by_cases k: fuelH D X
   · have m(i:Orbit n)(q:i.1∈ σX P Y D): W i=(f X (Yz D) i).val:= (hz D u i q).trans (if_pos k); let M:= worth_Rack (ht D k) t u rfl; exact pose_side (crate_side M hw hs m) M m
   have m(i:Orbit n)(q:i.1∈ σX P Y D): W i=(0:Firing n) i:=(hz D u i q).trans (if_neg k); have h0:Marque P Y X D 0 h (r X):= Marque.noR.bigger (zero_le_one.trans t) (p.1 X); exact pose_side (crate_side h0 hw hs m) h0 m
 intro Y u i w m; change W _=W _; rw [hz ∅ u i w,hz ∅ u (i.1,m) w]
 simp [Tt,fuelH]
end YM.CF.Sour
