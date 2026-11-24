import Organdy.Porch
import Organdy.Spangles
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


namespace Royal
open Buffered.Afterglow Satin Lifted

section cran
variable (S: Finset Cover)(τ:ℝ)

local notation "I" => Option (↥S × Axis)
local notation "R" => PairsC
def bud (i:I) (x:R):SU.E := match i with
 | none => 1
 | some c => x.1 (c.1,c.2)

lemma bud_c(i:I): Continuous (bud S i):=by
 cases i
 · exact continuous_const
 next i=>exact (continuous_apply (A:=fun _: Edge Cover=> SU.E) ((i.1:Cover),i.2)).comp continuous_fst -- binder
variable {N:Side}
lemma crossgraft (d:Edge (Seat N)): ∃ i:I, ∀ x:R,graft S N x.1 d=bud S i x:=by
 unfold Satin.graft
 by_cases p:∃ c:↥S,pole S N c=d.1
 · exact ⟨some (p.choose,d.2),fun x=> dif_pos p⟩
 exact ⟨none,fun x=> dif_neg p⟩

abbrev paneFee(q:I × I × I × I)(x:R):=
 SU.group.chord (bud S q.1 x * (bud S q.2.1 x *
 ((bud S q.2.2.1 x)⁻¹ * ((bud S q.2.2.2 x)⁻¹ * 1))))
def hingeSet(q:I × I × I × I): Set R:= {x | paneFee S q x<τ}
lemma allFees {N:Side} (q:Face (Per (More N))): ∃ i, ∀ x:R,SU.group.chord (faceValue (graft S N x.1) q)=paneFee S i x:=by

 choose u b using crossgraft S (N:=N)
 let t:=q.1; let i:=q.2.val.1; let j:=q.2.val.2
 let v:= t+step i+step j
 refine ⟨(u (t,i),u (t+step i,j),u (v-step i,i),u (v+ -step i-step j,j)),fun x=> ?_⟩
 simp only [paneFee,faceValue,Lattice.square,travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,b]
 <;> rfl
lemma openSetFee(q:I × I × I × I):MeasurableSet (hingeSet S τ q):=by
 unfold hingeSet paneFee
 exact (isOpen_lt (SU.group.continuous_chord.comp ((bud_c S _).mul ((bud_c S _).mul (((bud_c S _).inv).mul (((bud_c S _).inv).mul continuous_const))))) continuous_const).measurableSet

def claw(V:SU.E): Bool→Twig:=fun t=> if t then brand V else star (brand V)
lemma claw_c:Continuous claw:=by
 apply continuous_pi
 intro h; cases h
 · exact Dial.spinD.star
 exact Dial.spinD

lemma prospects(δ:ℝ)(v:0<δ):
 ∃ P:Deck R,P.dark∧∀ x y,P.withZ x y →
   ∀ N, (∀ j:Face (Per (More N)), SU.group.chord (faceValue (graft S N x.1) j)<τ ↔
       SU.group.chord (faceValue (graft S N y.1) j)<τ) ∧
   (∀ d,‖profile (graft S N x.1) d-profile (graft S N y.1) d‖ ≤ δ):=by

 have u:=Deal.assembly (X:=R) (T:=fun _: Option (↥S × Axis)=> Bool → Twig)
     (fun i _ x=>claw (bud S i x)) (fun i=> deal_of_one (claw_c.comp (bud_c S i)).measurable ((isCompact_univ).image claw_c) (fun _=>Set.mem_image_of_mem _ (Set.mem_univ _))) id
 obtain ⟨P,b,w⟩:= u δ v
 let F:Deck R:= univ.image (hingeSet S τ)
 have f:F.dark:= fun k a=>by obtain ⟨q,t,rfl⟩:=mem_image.mp a; exact openSetFee ..
 refine ⟨P∪F,P.join F b f,fun x y g N=>⟨fun j=> ?_,fun d=>?_⟩⟩
 · obtain ⟨i,l⟩:=allFees S j
   rw [l,l]
   exact g (hingeSet S τ i) (mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
 · obtain ⟨i,p⟩:=crossgraft S d
   have h:=w x y (Deck.grow Finset.subset_union_left x y g) i
   rw [dist_eq_norm] at h
   change ‖claw (graft S N x.1 d)-claw (graft S N y.1 d)‖≤_; rw [p,p]; exact h.le
end cran

section press
variable {N:Side}{K:Scree.Loom N}{p:BudgetPoint}{X:SOp N}{a b d δ:ℝ}{o:Seat N}
local notation "T" => Openc (More N) d
/-- Paying only the real lipschitz fee inside each ping cell.
No complex-mask continuation used. No comparison between bare data. -/
lemma flutter_h{n:ℕ} (u:Trunk o X n a b d)(v:0≤a)(x y:Openc (More N) d)
 (t:∀ i∈ leaks (lensBox n o), ‖x.val i-y.val i‖ ≤ δ)(e:0≤δ):
    motes (X x.val-X y.val) ≤ b * (((n:ℝ)*4*δ)/|d|):=by
 obtain ⟨F,C,H,w,r,g⟩:=u.home
 let A:=((n:ℝ)*4*δ)/|d|
 have j:0≤A:=by unfold A; positivity
 have f (S:Sa N)(l:C S≠0): fare S x.val y.val / |d| ≤ A:=by
    obtain ⟨z,k⟩:=w S l; have h:= f_then (H S) l
    have v:S⊆lensBox n o:=fun i p=> halo_spec.mpr ⟨o,mem_singleton_self _, ((h.lim _ z _ p).trans k).le⟩
    have b0:leaks S ⊆ S×ˢFinset.univ:=fun i l=> mem_product.mpr ⟨(mem_filter.mp l).2.1,mem_univ _⟩
    have hs:leaks S ⊆ leaks (lensBox n o):=fun i l=> mem_filter.mpr
             ⟨mem_univ _,v (mem_filter.mp l).2.1,v (mem_filter.mp l).2.2⟩

    unfold A Tulip.fare; apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    refine (sum_le_sum fun i l=>t i (hs l)).trans ?_
    rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ e
    have i:=card_le_card b0; rw [card_product, show (univ:Finset Axis).card=4 by simp] at i
    exact_mod_cast i.trans (Nat.mul_le_mul_right 4 k.le)
 rw [g,g,← Finset.sum_sub_distrib]
 refine le_trans ((motes_sum _ _).trans (sum_le_sum (g:=fun S=>(rent a S*ledgerV (C S))*A) fun S _=>?_)) ?_
 swap
 · rw [←sum_mul]; exact mul_le_mul_of_nonneg_right r j
 rw [mul_assoc]
 have h:0≤ledgerV (C S):=sum_nonneg fun i _=>sum_nonneg fun k _=> (H S).nonn ..
 apply le_trans _ (le_mul_of_one_le_left (mul_nonneg h j) (rent_one v S))
 unfold ledgerV
 simp only [sum_mul]
 refine sum_le_sum fun i _=>sum_le_sum fun k _=>?_
 have b: ‖F S x i k-F S y i k‖ ≤ C S i k*(fare S x.val y.val / |d|):= ((H S).expo i k).variation x y
 refine b.trans ?_
 by_cases l:C S=0
 · rw [show C S i k=0 from by rw [l]; rfl,zero_mul,zero_mul]
 exact mul_le_mul_of_nonneg_left (f S l) ((H S).nonn ..)

lemma flutter
 (u:Trunk o X (p.B/10) a b d)(v:0≤a)(h:WindowDress K p d) (x y:Pane N)
 (w:x∈safeZone p o ↔ y∈safeZone p o)
 (z:∀ i,‖profile x i-profile y i‖≤δ)(e:0≤δ) (h0:0≤b):
 motes (shine K p o X x - shine K p o X y) ≤ b * ((((p.B/10:ℕ):ℝ)*4*δ)/|d|):=by
 by_cases t:x∈safeZone p o
 · have k:=trunks_canal u v
   let q:=Classical.arbitrary (Ids N)
   rw [frameLit h k t q,frameLit h k (w.mp t) q]
   apply flutter_h u v (stem_real h (x,q)) (stem_real h (y,q)) _ e
   intro i l; obtain ⟨r,s,a⟩:= mem_filter.mp l
   have hp(i0:Pane N)(v:i0 ∈ safeZone p o): profile (K (i0,q)) i= profile i0 i:=by unfold profile; rw [← h.lamp o i0 q v i s a]
   change ‖profile (K (x,q)) i- profile (K (y,q)) i‖≤ δ
   rw [hp x t,hp y (w.mp t)];exact z i -- exact
 rw [shine,Set.indicator_of_notMem t, Set.indicator_of_notMem (mt w.mpr t),sub_self,show motes (0:Op (Single N))=0 by simp[motes]]; positivity
end press

section
variable {I:Type*} {N:I→Side} {τ a b d:ℝ}{B:ℕ} {p:I→BudgetPoint}
 {K:(i:I)→ Scree.Loom (N i)} {o:(i:I)→Seat (N i)} {X:(i:I)→ SOp (N i)}
structure Ruffles(a b d τ:ℝ)(B:ℕ) (p:I→BudgetPoint)(K:(i:I)→ Scree.Loom (N i)) (o:(i:I)→Seat (N i))(X:(i:I)→SOp (N i)):Prop where
 chest:0≤a
 glow:0≤b
 depth:0<d
 measure(i:I):(p i).B=B
 hazard(i:I):(p i).threshold=τ
 paid(i:I):WindowDress (K i) (p i) d
 trunk(i:I):Trunk (o i) (X i) ((p i).B/10) a b d

variable (S:Finset Cover) (v:Ruffles a b d τ B p K o X)
local notation "L" i:max => shine (K i) (p i) (o i) (X i)
local notation "R" => PairsC
local notation "G" i:max x:max=>graft S (N i) ((x : PairsC).1)
include v
lemma wattage (i:I)(x:Pane (N i)): motes ((L i) x) ≤ b:= (slatLit (v.paid i) (trunks_canal (v.trunk i) v.chest)).quick x

lemma crease(e:ℝ)(r:0<e):
 ∃ P:Deck R,P.dark ∧ ∀ x y,P.withZ x y → ∀ i:I, motes ((L i) (G i x)-(L i) (G i y)) < e:=by
 have hb:=v.glow; have h:=v.depth
 let c:= b*((((B/10:ℕ):ℝ)*4)/|d|)
 have ck:0≤c:=by unfold c; positivity
 let δ:= e/(c+1)
 have hx:0<δ:= div_pos r (by linarith)
 obtain ⟨P,a,t⟩:=prospects S τ δ hx
 refine ⟨P,a,fun x y l i=>?_⟩
 obtain ⟨w,z⟩:=t x y l (N i)
 have h: G i x ∈ safeZone (p i) (o i)↔ G i y ∈ safeZone (p i) (o i):=by
    simp only [safeZone,Set.mem_setOf_eq,pingS]
    rw [v.hazard]
    exact ⟨fun h a g=> (w a).mp (h a g),fun h a g=> (w a).mpr (h a g)⟩
 refine (flutter (v.trunk i) v.chest (v.paid i) _ _ h z hx.le v.glow).trans_lt ?_
 have u:c*δ<e:=by have ux:δ*(c+1)=e:=div_mul_cancel₀ _ (by linarith); nlinarith
 rw [v.measure]; exact lt_of_eq_of_lt (show _=c*δ by unfold c; ring) u

lemma traceMenu:Menu (fun (i:I)(x:PairsC)=>Matrix.trace ((L i) (G i x))) :=by
 refine ⟨fun e t=>?_,b,v.glow,fun i x=> (trace_spends ..).trans (wattage v ..)⟩
 obtain ⟨P,d,q⟩:=crease S v e t
 refine ⟨P,d,fun x y a i=>?_⟩; rw [dist_eq_norm,←Matrix.trace_sub]
 exact (trace_spends _).trans_lt (q x y a i)
omit v in
lemma preJ_sub {J:Type}[LinearOrder J][Fintype J] (A X Y:Op J):preJ A (X-Y)=preJ A X-preJ A Y:=by
 unfold preJ
 rw [mul_sub,Matrix.trace_sub,sub_smul,sub_mul,sub_eq_add_neg (A*X*(1-A)),dg_add,dg_neg]
 abel

lemma harpMenu:Menu (T:=fun i=>FC (Single (N i))) (fun (i:I)(x:PairsC)=>harp (L i) (replant S (N i) x)):=by
 have u(i:I)(x:Op (Single (N i))):‖preJ (tickA _) x‖≤ 2*motes x:=by rw [touchP]; exact preJ_spends _ _
 have t:=v.glow
 refine ⟨fun e y=>?_,2*b,by linarith,fun i x=> (u ..).trans (mul_le_mul_of_nonneg_left (wattage v ..) (by norm_num))⟩
 obtain ⟨P,d,q⟩:=crease S v (e/2) (by positivity)
 refine ⟨P,d,fun x z a i=>?_⟩
 have t:=q x z a i
 change dist (preJ _ ((L i) (G i x))) (preJ _ ((L i) (G i z)))< e
 rw [dist_eq_norm,←preJ_sub]
 exact (u ..).trans_lt (by linarith)
end
