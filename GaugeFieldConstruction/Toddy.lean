import GaugeFieldConstruction.Corbicula
import YM.CF.Ione.Rank
/- Moves Column Fraction. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 160000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive
local notation "GS"=>SU.group
abbrev MustCap(F:Seat n≃Seat n)(X:Hubber n): Hubber n:= X.map F.symm.toEmbedding
def Nearby(F:Seat n≃Seat n)(p:Bool): Wa n → Wa n → Prop
| none,none=>True
| some ⟨b,i,j⟩, some ⟨c,k,l⟩=> b.xor p=c ∧ F (aptK k)=aptK i∧F (aptK l)=aptK j
| _,_ =>False
def Shadower(F:Seat n≃Seat n)(p:Bool) (x:Wa n): Finset (Wa n):= univ.filter (Nearby F p x)
abbrev quotaL:= Fintype.card (SpinIdx× SU.Slot)
abbrev CaseL := quotaL ^2
lemma quota_Θ (s:Seat n) : (univ.filter fun i:Single n=>aptK i=s).card≤ quotaL:=by
 let f(i:Single n):= ((helix n) i).2
 apply card_le_card_of_injOn f _ _; · exact fun _ _=> mem_univ _
 rintro i h j q v; apply (helix n).injective; apply Prod.ext _ v; apply Tenant.needle; exact (mem_filter.mp h|>.2).trans (mem_filter.mp q|>.2).symm
lemma track_size(Z:Seat n≃Seat n)(p:Bool)(i:Wa n): (Shadower Z p i).card ≤ CaseL :=by
 rcases i with _|⟨u,j,k⟩
 · have hp: (Shadower Z p none)={none}:=by ext i; cases i<;>simp [Shadower,Nearby]
   rw [hp,card_singleton]; change 1≤ (quotaL:ℕ)^2; exact one_le_pow₀ (show 1 ≤ quotaL from (show 0<quotaL from Fintype.card_pos))
 let I:= Single n; let A:=univ.filter fun i':Single n=>aptK i'=Z.symm (aptK j); let B:=univ.filter fun i'=>aptK i'= Z.symm (aptK k)
 let K:= (A ×ˢ B).image fun y=> some (u.xor p,y)
 apply le_trans (card_le_card (show Shadower Z p (some (u,j,k))⊆K from ?_)) (card_image_le.trans ?_)
 · intro i hi; have hp:= (mem_filter.mp hi).2; cases i with | none=> exact hp.elim|some i=> obtain ⟨b,c,d⟩:= i; obtain ⟨rfl,e,h⟩:=hp; exact mem_image_of_mem _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,(Z.symm_apply_apply _).symm.trans (congrArg Z.symm e)⟩,mem_filter.mpr ⟨mem_univ _, (Z.symm_apply_apply _).symm.trans (congrArg Z.symm h)⟩⟩)
 rw [card_product]; exact (Nat.mul_le_mul (quota_Θ ..) (quota_Θ ..)).trans_eq (pow_two _).symm
variable (U:UNI (Single n))(q p: Bool)
def boostX : Wa n→ Wa n→ℂ
 | none,none=>1
 | some (b,j,k), some (c,i,l)=> if b.xor p=c then moko U p b i j * moko U p (!b) l k else 0
 | _,_ =>0
lemma stripeQ (A:ChartP n)(i:Wa n) : steerZ U q p A i=∑ j:Wa n,boostX U p j i * cSignX (q.xor p) (A j):=by
 rw [Fintype.sum_option]; rcases i with _|⟨b,x,y⟩
 · simp [boostX,steerZ];
 let v0:= b.xor p; obtain ⟨v,t⟩:∃ v:Bool,v.xor p=b:= ⟨v0,by unfold v0; simp [Bool.xor_assoc]⟩; subst b
 rw [swipe_u,show boostX U p none _=0 from rfl, zero_mul, zero_add, Fintype.sum_prod_type (α₁:=Bool), Finset.sum_eq_single v];
 · rw [Fintype.sum_prod_type (α₁:=Single n) (α₂:=Single n)]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro l _; simp [boostX, mul_comm]
 · intro t g p'; apply sum_eq_zero; intro i _; have hp:t.xor p≠ v.xor p:=by cases t <;> cases v <;>cases p<;>simp_all
   exact Eq.trans (congrArg (· * _) (show boostX U p (some (t,i)) (some (v.xor p,x,y))=0 from if_neg hp)) (zero_mul _)
 simp
lemma boost_D (F:Seat n≃Seat n)(h:∀ i j:Single n,U.val i j≠0→F (aptK i)=aptK j)(i j:Wa n)(v:boostX U p i j≠0):Nearby F p i j:=by
 rcases i with _|⟨b,i,j'⟩ <;> rcases j with _|⟨c,l,t⟩
 · trivial
 · exact (v rfl).elim
 · exact (v rfl).elim
 have hp(b:Bool)(i j:Single n)(u:moko U p b i j≠0): F (aptK i)=aptK j:=by
    apply h; intro v; apply u; have ht:= Urn.cream U p b j i (b.xor p); rw [if_pos rfl] at ht; rw [show moko U p b i j =_ from ht.symm]; exact Ione.spice_E _ _ _ _ v
 by_cases h:b.xor p=c; swap; · exact (v (if_neg h)).elim
 exact ⟨h,hp b l i (left_ne_zero_of_mul (show moko U p b l i*moko U p (!b) t j'≠0 from (by simpa only [boostX, if_pos h] using v))),hp (!b) t _ (right_ne_zero_of_mul (show moko U p b l i*moko U p (!b) t j'≠0 from (by simpa only [boostX,if_pos h] using v)))⟩
lemma boost_b (i j:Wa n):‖boostX U p i j‖ ≤1:=by
 cases i <;> cases j
 · exact norm_one.le
 · exact (norm_zero|>.le.trans zero_le_one)
 · exact (norm_zero|>.le.trans zero_le_one)
 rename_i i j; rcases i with ⟨b,f,g⟩; rcases j with ⟨h,u,v⟩
 simp only [boostX]; split
 · have hx(k:UNI (Single n))(a b):‖k.val a b‖ ≤1:= by
      rw [← basis_act k.val a b]; apply (PiLp.norm_apply_le ..).trans; rw [act_unit_norm]; simp [basisKet] -- names
   rw [norm_mul]; exact mul_le_one₀ (hx ..) (norm_nonneg _) (hx ..)
 simp
-- Mark processing. Canvas produces moved Paper at frame assignments; α preserves orientation composition.
variable (P:BudgetPoint)(R:Seat n≃Seat n)(a:Pane n→Pane n)
def CardCraft(L:Paper n):Paper n:=fun i V=> steerZ U q p (αLines L (a V)) i
abbrev Transport (S:Hubber n):Prop:= (∀ i j: Single n,U.val i j≠0→ R (aptK i)=aptK j)∧∀ (F:Lit n)(v:ℝ), Micro P S F v → Micro P (MustCap R S) (F ∘ a) v
-- pose(v)=sum over all allowable linear mixing matrix entries replacing absolute coefficient by ≤1.
abbrev Listing(R:Seat n≃Seat n)(p:Bool)(V:Wa n→ℝ):Wa n→ℝ:= fun i=> ∑ j:Wa n, if i∈ Shadower R p j then V j else 0
variable {v h x:ℝ}{S:Hubber n}{Q:Paper n}
lemma trade_G (t:Transport U P R a S)(V: Wa n→ℝ)(g:∀ i,Micro P S (Q i) (V i)∧(¬ DomainP S i→Q i=0))(i:Wa n): Micro P (MustCap R S) (CardCraft U q p a Q i) (Listing R p V i)∧(¬ DomainP (MustCap R S) i→ CardCraft U q p a Q i=0):=by
 let D:=MustCap R S; let L(j):Lit n:=(Q j)∘ a
 let Y (j):Lit n:= fun A=> boostX U p j i * cSignX (q.xor p) (L j A); have hv: CardCraft U q p a Q i=∑ j,Y j:=funext fun v=>by rw [Finset.sum_apply]; apply stripeQ
 have hx(j):Micro P D ((Ione.cast_B (q.xor p)) ∘ L j) (V j):= micro_e (micro_l _ (Ione.cap_X (q.xor p)) (t.2 _ _ (g j).1)) (one_mul _).le -- type
 rw [hv]; constructor
 · apply micro_sum; intro j _; split; · have hp:Micro P D (Y j) (‖boostX U p j i‖*V j):=by rw [show Y j=boostX U p j i • (Ione.cast_B (q.xor p) ∘ L j) from funext fun A=>by simp [Y,Ione.castT]]; exact micro_ms (hx j) _
                                        exact micro_e hp (mul_le_of_le_one_left (g j|>.1.1) (boost_b ..))
   next z => rw [show Y j=0 from funext fun x=>by simpa only [Y,show boostX U p j i=0 from Classical.byContradiction fun k=> z (mem_filter.mpr ⟨mem_univ _,boost_D U p R t.1 j i k⟩), zero_mul,Pi.zero_apply]]; exact micro_Z
 intro k; apply sum_eq_zero; intro j _; by_cases h: DomainP S j
 · have he: boostX U p j i=0:=Classical.byContradiction fun w=>k (show DomainP (MustCap R S) i from ?_)
   · funext x; simp [Y,he]
   have ht:=boost_D U p R t.1 j i w; cases i with
   | none=> trivial
   | some i=> cases j with
     | none=>exact ht.elim
     | some j=> rcases i with ⟨a,b,c⟩; rcases j with ⟨v,e,z⟩; exact ⟨mem_map_equiv.mpr (ht.2.1.symm ▸ h.1),mem_map_equiv.mpr (ht.2.2.symm ▸ h.2)⟩
 funext v; simp [Y,L,(g j).2 h,cSignX]
lemma wardPay(V:Wa n→ℝ)(s:∀ i,0≤V i)(h:ℝ): (∑ j:Wa n, papW n h j * Listing R p V j)≤CaseL* ∑ j:Wa n,papW n h j*V j:=by
 unfold Listing; simp_rw [mul_sum]; rw [sum_comm]; apply sum_le_sum; intro i _; let B:= Shadower R p i; rw [←sum_subset (subset_univ B) fun j _ k=> by rw [if_neg k,mul_zero]]
 have hp(j)(h': j∈B): papW n h j=papW n h i:=by have hx:= (mem_filter.mp h').2; cases i <;> cases j <;> first| exact hx.elim|rfl
 rw [show ∑ j∈B, papW n h j*(if j∈Shadower R p i then V i else 0)= _ from (show ∑ j∈B, papW n h j*(if j∈Shadower R p i then V i else 0)= ∑ j∈B,papW n h i * V i from sum_congr rfl fun j u=>by rw [if_pos u,hp j u]), sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast track_size R p i) (mul_nonneg (papW_v _) (s i))
end MastTin
end YM.CF.XGarden
end
