import YM.CF.Neon.Hob
import GaugeFieldConstruction.Riant

-- Third purchase. Does NOT change the Muster constants. Refine plan_B
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Hope Nor
namespace Riant
open Rate Bake Vow Neon Rive Larch Mew
variable {N:Side}{p0:BudgetPoint}{o:Seat N}{V P0 h c:ℝ}
abbrev Penned (o:Seat N)(F: Pax N)(Tp:Ids N)(X:Scree.Hub N): InkD N:= if X.val.1=o then fun v=>F (lagE X) (v,Tp) else 0
-- every Aura not containing home vanishes ignored on trunc. Reinstall later.
abbrev Stick(p:BudgetPoint)(X:Scree.Hub N)(u:ℝ):= (1+ (Hope.reel p.B X.val.2:ℝ))^7 * u
abbrev slip_C : ℝ:= Classical.choose (Chaff.polyF 7 (show 0<(1/2:ℝ) by norm_num))
def ZPay (x:ℝ) := (10*(1+(radiusB x:ℝ)))^7 * slip_C
lemma pos_C : 0≤ slip_C:= (Classical.choose_spec (Chaff.polyF 7 (show 0<(1/2:ℝ) by norm_num))).1
lemma zPay_Θ : sizeK R.L 0 ZPay:= (((sizeK.mild R.L 1).accrue (sizeK.Bcash _)|>.scale 10|>.powC 7).tint (sizeK.mild _ _ ))
lemma growth_z(x:ℝ) (p:p0.B ≤ 2*radiusB x)(X:Scree.Hub N)(u:0 ≤ c) : Stick p0 X c ≤ ZPay x*Tollup (1/2) p0 X*c:=by unfold Stick; exact mul_le_mul_of_nonneg_right ((price3 _ p _ _ _ (Classical.choose_spec (Chaff.polyF 7 (show 0<(1/2:ℝ) by norm_num))).2).trans_eq (mul_assoc ..).symm) u
abbrev ωCost (x:ℝ) := reserveT 2 6 (radiusB x) (1/2)* ZPay x
lemma ωCredit : sizeK R.L 0 ωCost:=((Nor.vale_u _ _ _).creditK _).tint zPay_Θ
lemma stick_tariff (p:p0.power=2)(hp:p0.order=6)(t:p0.B=radiusB x)(i:Scree.Hub N)(C:ℝ)(h:0≤C): Tollup 2 p0 i* Stick p0 i (fareX p0.B p0 i.val.2 * C) ≤ ωCost x*(C*Tollup 3 p0 i):=by
 let Y:= fareX p0.B p0 i.val.2; let D:=ZPay x
 have he:0≤ZPay x:=by unfold ZPay; have ht:=pos_C; positivity
 have hx:= Nor.coinPay p0 i.val.2 (k:=p0.B) (1/2) (by norm_num); change Y ≤ _ at hx; rw [p,hp,t] at hx
 let a:ℝ:=coverNumber p0.B i.val.2; have hx:Y ≤ reserveT 2 6 (radiusB x) (1/2)*Tollup (1/2) p0 i := by unfold Tollup; rw [t]; exact hx
 apply le_trans (mul_le_mul_of_nonneg_left (growth_z _ (by omega : p0.B ≤2*radiusB x) i (mul_nonneg (health_f ..) h)) (Real.exp_pos _).le);
 refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx h) (show 0 ≤ ZPay x * _ from mul_nonneg he (show 0 ≤ Tollup (1/2) p0 i from (Real.exp_pos _).le))) (Real.exp_pos _).le) (le_of_eq ?_)
 let u:= Tollup 2 p0 i; let k:=Tollup (1/2) p0 i; rw [show Tollup 3 p0 i=u*k*k from (by unfold Tollup u k Tollup; rw [←Real.exp_add,←Real.exp_add]; congr 1; ring)]; unfold ωCost u k; ring
variable {I:Type}[Fintype I][LinearOrder I] {C: Aura N→ℝ}{F:Pax N}
lemma stamp (U₁:p0.power=2)(U₂:p0.order=6)(U₃:p0.B=radiusB x)(h₁:Turf F)(A:∀ i:Aura N, Medal p0 i.val ∅ (F i) h (C i))(t:tallB C p0.B 3 o ≤ P0)(H:0≤h)(Tp:Ids N): Mew.ForgeB (Penned o F Tp) (fun i (_:Unit)=> Tollup 2 p0 i) (KeyUp p0) h (fun _=> ωCost x * P0):=by
 let Z(i:Scree.Hub N):= if i.val.1=o then Stick p0 i (fareX p0.B p0 i.val.2 * C (lagE i)) else 0; have he:0 ≤ ZPay x:=by unfold ZPay; have hh:=pos_C; positivity
 refine ⟨⟨Z,fun i=>?_,fun j=> le_trans ?_ (mul_le_mul_of_nonneg_left t (show 0 ≤ ωCost x from (by unfold ωCost; apply mul_nonneg _ he; unfold reserveT coin_n stilK; positivity)))⟩⟩
 · unfold Penned Z; split; next v=>
     have hh(i:Scree.Hub N):Medal p0 i.val.2 ∅ (oV (fun s=> F (lagE i) (s,Tp))) h (C (lagE i)):=by rw [←show F (lagE i)=oV _ from funext fun a=> h₁ _ _ Tp]; exact A (lagE i)
     have hx:=longer3 U₁ ((hh i).preservesE Tp H p0.B) H p0.B; rw [U₂] at hx; exact hx
   exact Vale.rinse ..
 unfold Z; simp_rw [mul_ite,mul_zero]; rw [←sum_filter]
 unfold tallB; rw [mul_sum]; let V:=univ.filter (fun x:Aura N=> o∈ x.val); let X:=univ.filter (fun x:Scree.Hub N=>x.val.1=o)
 rw [←sum_fiberwise_of_maps_to (s:=X) (t:=V) (g:=lagE) (fun j p=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2 ▸ j.property⟩)]
 apply sum_le_sum; intro j u; let Q:Scree.Hub N:=⟨(o,j.val),(mem_filter.mp u).2⟩; let F':=X.filter fun x:Scree.Hub N=>lagE x=j; have ht':lagE Q=j:=Subtype.ext rfl
 rw [sum_eq_single_of_mem (s:=F') Q (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,ht'⟩)]; swap; · intro v t q; have h:v=Q:=Subtype.ext (Prod.ext ((mem_filter.mp (mem_filter.mp t).1).2) (congrArg Subtype.val (mem_filter.mp t).2)); exact False.elim (q h)
 rw [ht']; exact stick_tariff U₁ U₂ U₃ Q _ ((A _).wage H)

abbrev Rooted(o: Seat N)(Y:Pax N):Prop:=∀ i,o∉i.val→ Y i=0
abbrev debit (F:Key I→Pax N)(l:I) : Pax N:= fun i j=>tipI (fun z=> F z i j) [l]
-- sharp receipts. Ascribe on Aura; use Hub equivalence for application.
structure Crafts (P:BudgetPoint)(o:Seat N)(F:Pax N)(h a w:ℝ):Prop where
 turf : Turf F
 rooted : Rooted o F
 pays :∃ C:Scree.Hub N→ℝ,(∀ (Tp:Ids N)(i:Scree.Hub N), PressB (KeyUp P) i (Penned o F Tp i) h (C i))∧(∀ i,0≤ C i) ∧(∀ i,i.val.1≠o→ C i=0) ∧ΩBook P a C≤ w
lemma prints (U₁:p0.power=2)(U₂:p0.order=6)(U₃:p0.B=radiusB x)(H:0<h)(F:Key I→ Pax N)(P:ℝ)(Q:I→Seat N)(l:I)(a:Q l=o)(t:∀ z∈hill I,Turf (F z))(u:∀ i,Hush Q i.val fun z=> F z i)(v:∀ i j,River fun z=>F z i j)(b:∀ z∈hill I,∃ C:Aura N→ℝ,(∀ i,Medal p0 i.val ∅ (F z i) h (C i))∧ tallB C p0.B 3 o≤P) : Crafts p0 o (debit F l) h 2 (ωCost x*P):=by
 let Y:=debit F l; have hx:Turf Y:=fun i U A=> lace_C _ (show Set.EqOn _ _ _ from fun z (v:z∈hill I)=> t z v i U A) roots
 refine ⟨hx,fun i k=>funext fun V=> husht_B _ _ _ (show Hush Q i.val (fun z=>F z i V) from fun z g y t h=>congrFun (u _ z g y t h) V) (v i V) [l] l (a.symm ▸ k) (by simp),?_⟩ -- bind Rooted
 let T:=Classical.arbitrary (Ids N); let G(z):=Penned o (F z) T; let W:= fun (i:Scree.Hub N) (_:Unit)=> Tollup 2 p0 i
 have hf(i y):River (fun z:Key I=>G z i y):=by unfold G Penned; split; exact v ..; exact zeroR _
 have hg(z:Key I)(p:z∈hill I):ForgeB (G z) W (KeyUp p0) h (fun _=>ωCost x*P):=by obtain ⟨C,k,φ⟩:=b z p; exact stamp U₁ U₂ U₃ (t z p) k φ H.le T
 obtain ⟨C,c,g⟩:= (onset_t G H W (fun _ _=>(Real.exp_pos _).le) (fun _=>⟨(),Real.exp_pos _⟩) (fun _=>ωCost x*P) hg hf [l]).bit
 have hK(i):0 ≤ C i:= (Taxi.eraF _ _ (c i) H.le _ (ping_f _ _)).grade
 let Z(i:Scree.Hub N):=if i.val.1=o then C i else 0
 refine ⟨Z,fun Tp i=>?_,fun i=> by unfold Z; split; exact hK i; exact le_rfl,fun i p=> if_neg p, ?_⟩ -- multi line nested tune
 · unfold Penned Z; split
   next k => refine Eq.mp ?_ (c i); congr 1; funext V; simp only [G,Penned,k,if_true]; exact hx _ _ _
   exact Vale.rinse ..
 exact le_trans (sum_le_sum (g:=fun i=>W i ()*C i) (fun i _=> mul_le_mul_of_nonneg_left (by unfold Z; split; rfl; exact hK i) (Real.exp_pos _).le)) (g ())
-- linear reset operations combine.
variable {w w' u :ℝ}{F₁ F₂:Pax N}{F': Aura N→ℝ}
lemma Crafts.shift_budget (v:Crafts p0 o F₁ h u w)(hv:w≤w') : Crafts p0 o F₁ h u w':=by obtain ⟨C,p,q,z⟩:= v.pays; exact ⟨v.turf,v.rooted,C,p,q,z.1,z.2.trans hv⟩
lemma Crafts.subE (t:Crafts p0 o F₁ h u w)(v:Crafts p0 o F₂ h u w')(p:0 ≤ h) : Crafts p0 o (F₁-F₂) h u (w+w'):=by
 obtain ⟨C,h1,h2,b,Q⟩:=t.pays; obtain ⟨C',u1,u2,d,Y⟩:=v.pays; refine ⟨fun i j p=> congrArg₂ (·-·) (t.turf ..) (v.turf ..),fun i k=> by rw [Pi.sub_apply,t.rooted i k,v.rooted i k,sub_self],C+C',fun Tp i=>?_,fun i=>add_nonneg (h2 _) (u2 _),fun i p=>by rw [Pi.add_apply,b i p,d i p,zero_add],?_⟩ -- tune comma
 · rw [show Penned o (F₁-F₂) Tp i=Penned o F₁ Tp i + -(Penned o F₂ Tp i) from (by unfold Penned; split; exact (show _=_ from by funext; simp [sub_eq_add_neg]); simp)]; exact Larch.prop_add _ _ (h1 Tp i) (Hope.ν_P (u1 Tp i) p)
 unfold ΩBook; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add Q Y
lemma Crafts.addE (t:Crafts p0 o F₁ h u w)(v:Crafts p0 o F₂ h u w')(p:0 ≤ h) : Crafts p0 o (F₁+F₂) h u (w+w'):=by
 obtain ⟨C,h1,h2,b,Q⟩:=t.pays; obtain ⟨C',u1,u2,d,Y⟩:=v.pays; refine ⟨fun i j p=> congrArg₂ (·+·) (t.turf ..) (v.turf ..),fun i k=> by rw [Pi.add_apply,t.rooted i k,v.rooted i k,zero_add],C+C',fun Tp i=>?_,fun i=>add_nonneg (h2 _) (u2 _),fun i p=>by rw [Pi.add_apply,b i p,d i p,zero_add],?_⟩ -- tune comma
 · rw [show Penned o (F₁+F₂) Tp i=Penned o F₁ Tp i + Penned o F₂ Tp i from (by unfold Penned; split; rfl; simp)]; exact Larch.prop_add _ _ (h1 Tp i) (u1 Tp i)
 unfold ΩBook; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add Q Y
end Riant
end YM.CF.Py
end
