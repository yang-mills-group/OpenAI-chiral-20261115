import GaugeFieldConstruction.BerryM
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
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
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
variable (T: Sweep n)(P:BudgetPoint)(L:ℕ)(x:Scree.Hub n)
local notation "Ωv"=> boxA T
local notation "Y"=> Single n
abbrev Rasp (t:Signed)(x:TiltI):TiltI:= x.map fun (p,i)=>(p.xor (t.flip i),t.perm i)
lemma Aff_at(k:ℕ)(s:Signed)(v:TiltI): line_Y k (Rasp s v)= s.act (line_Y k v):=by
 funext i; obtain ⟨i,rfl⟩:= s.perm.surjective i; rw [Signed.act_at]; cases v with
 | none=> simp [Rasp,line_Y]
 | some q=> obtain ⟨p,j⟩:=q; by_cases h:i=j
            · subst j; cases p<;> cases he:s.flip i <;>simp only [Rasp,he,Option.map_some,line_Y,Option.elim_some, ↓reduceIte] <;>simp
            cases s.flip i <;> simp [line_Y,Rasp,h]
lemma view_At(v:Seat n)(t:TiltI):Ωv (Atlas_Y L v P t)= Atlas_Y L (Ωv v) P (Rasp T.s t):=by
 unfold Atlas_Y; rw [Aff_at,←wrap_signed,sitA,sitA]; unfold affine; rw [Signed.act_sub]; abel
lemma Halo_After (v:Seat n): Halo_Plus L (sh T v) P= nCap T (Halo_Plus L v P):=by
 apply Finset.Subset.antisymm
 · intro x u; obtain ⟨t,h,rfl⟩:=mem_image.mp u; change _ ∈(Halo_Plus L _ P).map _; apply Finset.mem_map.mpr -- name
   refine ⟨_,mem_image_of_mem _ (mem_univ (Rasp T.s t)),?_⟩; change (boxA T).symm _=_; apply (boxA T).injective; rw [view_At T P L,show Ωv (sh T v)=v from (boxA T).apply_symm_apply _, Equiv.apply_symm_apply]
 intro x u; obtain ⟨v,h,hv⟩:=mem_map.mp u; obtain ⟨j,s,rfl⟩:=mem_image.mp h; subst x; let T':=T⁻¹; apply mem_image.mpr ⟨Rasp T'.s j,mem_univ _,?_⟩; exact (view_At T' P L ..).symm -- tune arg order v binder
variable (σ':I→Seat n)

lemma n_afer (v:∀i∈t,σ' i=sh T (σ i))(b:Bool): padS I σ' t (nCap T S) L P b=nCap T (padS I σ t S L P b):=by
 have hp: Finset.image σ' t = (Finset.image σ t).map (boxA T).symm.toEmbedding:=by rw [map_eq_image,image_image]; apply Finset.image_congr; exact v -- tune
 unfold padS; split; exact rfl; split; swap; exact rfl
 rw [hp,show ∀x y,nCap T (x∪y)=nCap T x∪nCap T y from fun x y=>map_union ..]; apply congrArg; let A:=t.image σ; let Z:=(boxA T).symm; ext x; obtain ⟨x,rfl⟩:=Z.surjective x
 change Z x ∈((A.map Z.toEmbedding).biUnion _)↔Z x∈ ((A.biUnion _).map Z.toEmbedding)
 rw [Finset.mem_biUnion]; have he(y)(v:Finset (Seat n)): Z y ∈ v.map Z.toEmbedding↔y∈ v:= by simp
 rw [he,mem_biUnion]; constructor
 · rintro ⟨k,u,t⟩; obtain ⟨w,rfl⟩:=Z.surjective k; rw [he] at u; rw [show Z w=sh T w from rfl,Halo_After] at t; exact ⟨_,u,(he _ _).mp t⟩
 rintro ⟨k,v,y⟩; refine ⟨Z k,(he _ _).mpr v,?_⟩; rw [show Z k=sh T k from rfl,Halo_After]; exact (he _ _).mpr y
lemma Χ_It (z:Scree.Hub n):moveHub T⁻¹ (moveHub T z)=z:=by
 apply Subtype.ext
 refine Prod.ext ?_ ?_; simp [moveHub,sitU]
 ext1 i; simp [moveHub,sitU]
abbrev νIt (T:Sweep n): Scree.Hub n≃ Scree.Hub n where
 toFun:=moveHub T
 invFun:=moveHub T⁻¹
 left_inv:=Χ_It T -- P unnecessary
 right_inv:= fun x=>by simpa only [inv_inv] using Χ_It T⁻¹ x
lemma K_It (v:∀i∈t,σ' i=sh T (σ i)) (a:Bool) : MarksΥ I σ' t (nCap T S) L P a=(MarksΥ I σ t S L P a).map (νIt T).toEmbedding:=by
 let F:=νIt T
 ext1 x; obtain ⟨x,rfl⟩:= F.surjective x; have hx: Finset.image σ' t=(t.image σ).map (boxA T).symm.toEmbedding:=by rw [map_eq_image,image_image]; exact image_congr v
 change moveHub T x ∈MarksΥ _ _ _ _ _ _ _↔ F x ∈ Finset.map F.toEmbedding _
 simp_rw [MarksΥ,mem_filter,mem_univ,true_and,n_afer I σ t S T P L σ' v,hx];
 change (x.val.2.map (boxA T).symm.toEmbedding=(padS I σ t S L P a).map (boxA T).symm.toEmbedding∧(boxA T).symm x.val.1∈ (Finset.image σ t).map (boxA T).symm.toEmbedding)↔ F x ∈ (MarksΥ _ _ _ _ _ _ _).map F.toEmbedding
 simp only [Finset.map_inj]; simp [MarksΥ]
lemma Quota_k (v:∀i∈t,σ' i=sh T (σ i))(a:Bool): QuotaΥ I σ' t (nCap T S) L P a (moveHub T x)=QuotaΥ I σ t S L P a x:=by
 unfold QuotaΥ; rw [K_It I σ t S T P L σ' v]; change (if νIt _ x ∈ Finset.map _ _ then _ else _)= _; simp [exp_Plate,Χ_It]
variable (o:Seat n)(Z:Torches n)
lemma useR (F: Paper n): Barber T (useS F S V)=useS (Barber T F) (nCap T S) (nCap T V):=by
 unfold useS; have h:nCap T S ⊆nCap T V↔ S⊆V:= map_subset_map; simp_rw [h]; split; rfl; exact bornØ _
lemma Mint_R : mintP (tiro T Z) (sh T o) (nCap T V)= Barber T (mintP Z o V):=by
 unfold mintP; rw [born_Z, useR]; apply congrArg₂ (·+·) ; exact congrArg (fun x:Hubber n=>useS _ x _) (tiltY T _).symm; -- order
 let Q:= nCap T; let A:=fun i:Hubber n=> useS (Z.2 i) i V
 have he:∀ i: Finset (Hubber n),Barber T (∑ j∈i,A j)=∑ j∈i,Barber T (A j):=by
    intro i; induction i using Finset.induction_on with|empty=> rw [sum_empty,sum_empty,bornØ]|@insert i L t u=>rw [sum_insert t,sum_insert t,born_Z,u]
 rw [he]; symm; apply Fintype.sum_equiv Q; intro i; unfold A; rw [useR]; change _=useS (Barber T (Z.2 (Q.symm (Q i)))) _ _; rw [Q.symm_apply_apply]
private lemma swapRx {I D:Type}[Fintype I][AddCommMonoid D](f:I→I→I→I→D): (∑ i:I,∑ j:I,∑ k:I,∑ l:I,f i j k l)=∑ k:I,∑ l:I,∑ i:I,∑ j:I,f i j k l:=by
 conv_lhs => arg 2; intro i; rw [sum_comm (f:=fun j k:I=>∑ l:I,f i j k l)]; arg 2; intro k; rw [sum_comm (f:=fun j l:I=> f i j k l)]
 rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm (f:=fun j k:I=>∑ l:I,f j l i k)]
lemma planeB (U: UNI (Single n))(p t:Bool) {E:Type}[NormedRing E][NormedAlgebra ℂ E](F:E→+*E) (b bX:Bool→ Single n→E)(h:∀ x i, F (b x i)= ∑ j:Single n,moko U t x j i • bX (x.xor t) j)(w:∀ v:ℂ,∀ y:E,F (v • y)=cSignX (p.xor t) v • F y)(D DX:Wa n→E)(d:D none=1)(e:∀ (x:Bool)(i j: Single n),D (some (x,i,j))=b x i * b (!x) j)(dX:DX none=1)(eX:∀ (x:Bool)(i j: Single n),DX (some (x,i,j))=bX x i * bX (!x) j) (A:ChartP n):
 F (∑ j:Wa n,A j • D j)=∑ j:Wa n, steerZ U p t A j • DX j:=by
 let V:=steerZ U p t A
 let s (x:Bool):= x.xor t;
 have hh(x): F (∑ i:Single n,∑ j:Single n,A (some (x,i,j)) • D (some (x,i,j)))=∑ i:Single n,∑ j:Single n,V (some (x.xor t,i,j)) • DX (some (x.xor t,i,j)):=by
    unfold V; rw [map_sum F]; simp_rw [map_sum F]; simp_rw [e,eX,w,map_mul F,h,sum_mul,mul_sum, swipe_u, Finset.smul_sum, Finset.sum_smul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; -- maybe sum_mul loops?
    let he: (!x).xor t = !(x.xor t):=by cases x <;> cases t<;> rfl
    simp_rw [he]; exact swapRx _
 rw [Fintype.sum_option,Fintype.sum_option]; simp_rw [Fintype.sum_prod_type (α₁:=Bool) (α₂:=Single n × Single n), Fintype.sum_prod_type (α₁:=Single n) (α₂:=Single n)]; rw [map_add]; -- tune eta
 apply congrArg₂ (· + ·)
 · rw [d,dX,w,map_one]; rfl
 rw [map_sum]; -- Goal bool; get p explicit. 
 change (∑ x:Bool,F (∑ i:Single n,∑ j:Single n,A (some (x,i,j)) • D (some (x,i,j)))) = ∑ x:Bool,∑ i:Single n,∑ j:Single n,V (some (x,i,j)) • DX (some (x,i,j))
 simp_rw [hh]; let L(x:Bool):=∑ i:Single n,∑ j:Single n,V (some (x,i,j)) • DX (some (x,i,j))
 let E: Bool ≃ Bool:=⟨s,s,fun i=>by simp [s,Bool.xor_assoc],fun i=>by simp [s,Bool.xor_assoc]⟩; exact Equiv.sum_comp E L

lemma bill_delta0 (H:FinV n → FC (FinV n))(A:ChartP n): binW H (harpZ A)=∑ i:Wa n,A i • logL H (veilD i):=by
 change binW H (∑ i,A i • Pi.single (veilD i) 1)=_; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul]; apply congrArg (A i • ·); change ∑ j,(Pi.single _ _) _ • _= _; rw [sum_eq_single (veilD i)]; simp; intro j _ h; simp [h]; simp
open SeasonH
lemma beacon_T (p r:Bool)(U:UNI (Single n))(W Z X D:Op (Single n))(v:SeasonH.Altaz U p r W Z X D)(A:ChartP n): lotY p r U (binW (Icycle (alter_M W Z)) (harpZ A))= binW (Icycle (alter_M X D)) (harpZ (steerZ U p r A)):=by
 let H:= Icycle (alter_M W Z); let J:= Icycle (alter_M X D); rw [bill_delta0,bill_delta0]
 exact planeB U p r (lotY p r U) (fun x i=> H (x,i)) (fun x i=>J (x,i)) (fun x i=>archive_Z p r U W Z X D v i x) (fun i x=>G_lot ..) (fun x=>logL H (veilD x)) (fun x=>logL J (veilD x)) rfl (fun x i j=>rfl) rfl (fun x i j=>rfl) A
lemma Zen_port (h:LegTax Z): portable (mintP Z o V):=by
 have he(i j)(U:Paper n)(h:portable U):portable (useS U i j):=by unfold useS; split; exact h; exact port_Z
 let X:= fun i:Hubber n=> useS (Z.2 i) i V
 unfold mintP; refine port_add (he _ _ _ h.1) ?_; suffices u:∀ L:Finset (Hubber n),portable (∑ i∈ L,X i) from u _
 intro L; induction L using Finset.induction_on with|empty=> rw [sum_empty]; exact port_Z| @insert i L u w=> rw [sum_insert u]; exact port_add (he _ _ _ (h.2 i)) w
#print axioms beacon_T
end MintB
end MastTin
end YM.CF.XGarden
end
