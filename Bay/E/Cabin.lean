import Bay.D.Skiff
import YM.SU5.Interaction.Source.Reduction

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted D StressExchange

variable {o:Cover}{b:ℕ}{N:Side}

-- gauge to matter indices
abbrev Cot (S:Finset Cover):= {x:Cover // nodeC x∈S}
abbrev Beam (S:Finset Cover):=(Cot S×SpinIdx)×SU.Slot

lemma injectC : Injective nodeC:=by
 intro x y h
 funext i
 have u := congrFun h i
 change (2:ℤ) * x i +1=(2:ℤ)* y i+1 at u
 omega

variable {S:Finset Cover}
instance cotF:Finite (Cot S):=Finite.of_injective (β:=↥S) (fun x:Cot S=>⟨nodeC x,x.property⟩) (fun _ _ h=>Subtype.ext (injectC (congrArg Subtype.val h)))
noncomputable instance cotType:Fintype (Cot S):= Fintype.ofFinite _

lemma nodeSubC (x z:Cover)(n:ℕ) : nodeC (x+n • z)=nodeC x + (n*2) • z:=by
 unfold nodeC
 rw[smul_add,mul_comm n,mul_smul]; abel

lemma nodePre {i:Site N}{x:Cover}(h:wrap (More N) x=node i) : ∃w, nodeC w=x ∧ wrap N w=i:=by
 let y:=Lattice.lift i
 have hy:wrap (More N) (nodeC y)=node i:=by rw [←node_of,wrap_lift]
 let M:=More N
 have u:=carrying M x
 have v:=carrying M (nodeC y)
 rw [h] at u
 rw [hy] at v
 let z:=periods M x-periods M (nodeC y)
 let w:= y+N.val • z
 have ww: nodeC w=x:=by 
   rw [nodeSubC]; dsimp only [w,z];change nodeC y+M.val • _=x
   rw[smul_sub]
   linear_combination (norm := abel) u - v 

 exact ⟨w, ww,Tenant.needle (by rw [node_of,ww,h])⟩
def sta (N:Side)(i:Beam S):Single N:=Lifted.index N i.1.1.val i.1.2 i.2
lemma sta_inj (e:AtEase S N):Injective (sta (S:=S) N):=by
 intro i j h
 obtain ⟨f,g⟩:=Prod.mk.inj h
 obtain ⟨z,l⟩:=Prod.mk.inj f
 have u:=congrArg node z
 rw [node_of,node_of] at u
 exact Prod.ext (Prod.ext (Subtype.ext (injectC (e i.1.1.property j.1.1.property u))) l) g

lemma fare_sta {i:Single N}(h:i∈modesIn N (roost b (wrap _ o))):i∈Set.range (sta (S:=Band o b) N):=by
 obtain ⟨u,v,w,_⟩:=atRidge (roost_expand (Nat.le_add_left b 12) (modes_ch.mp h)) 0 
 obtain ⟨z,g,t⟩:=nodePre w
 exact ⟨((⟨z,g.symm▸v⟩,i.1.2),i.2),Prod.ext (Prod.ext t rfl) rfl⟩ 

abbrev cross (N:Side)(X:Op (Single N)):=tickA N * X * (1-tickA N)

abbrev ap(N:Side)(i:Beam S):=Lifted.winding N i.1.1.val

def unitBlade (N:Side)(i j:Beam S):FC (Single N):= if i.1.2∈plusHalf ∧ j.1.2∉plusHalf then
 create (basisC N i.1.1.val i.1.2 i.2)*Fock.remove (basisC N j.1.1.val j.1.2 j.2)
 else 0
def diagonal (N:Side)(X:Op (Single N)):=Matrix.trace (tickA N*X)
def tariff (N:Side)(X:Op (Single N))(i j:Beam S):ℂ:= ap N i*ap N j* X (sta N i) (sta N j)

open Window
lemma crossWord(i j:Single N)(X:Op (Single N)):
 cross N X i j= if i∈Tset N ∧ j∉ Tset N then X i j else 0:=by
 unfold cross
 rw [touchP,←dim_cut,cutM,cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
 by_cases h:i∈ Tset N <;> by_cases u:j∈ Tset N <;>simp[h,u]

lemma paySta(i j:Beam S)(X:Op (Single N)):tariff N X i j • unitBlade N i j=
 (cross N X (sta N i) (sta N j)) • (put (sta N i)*takeF (sta N j)):=by
 have m(k:Beam S): sta N k∈Tset N↔ k.1.2∈plusHalf:= mem_Tset ..
 rw [crossWord, unitBlade]
 simp only[m]
 split; swap; · simp
 rw[basisC,basisC,map_smul,Fock.remove,map_smul,star_smul,
    show star (Lifted.winding ..)=Lifted.winding N j.1.1.val from fee_real _,
    create_put,create_put,Matrix.smul_mul,Matrix.mul_smul,smul_smul,smul_smul]
 have h:tariff N X i j * ap N i * ap N j=X (sta N i) (sta N j):=by
   rw [tariff]
   have u (k: Beam S): ap N k^2=1 := (pow_two _).trans (fee_one _)
   linear_combination (ap N j^2 * X (sta N i) (sta N j)) * u i + X (sta N i) (sta N j)* u j
 exact congrArg (· • _) h

lemma preBlade (e:AtEase (Band o b) N) (X:Op (Single N))
    (h:sparHere X (modesIn N (roost b (wrap _ o)))) :
 diagonal N X • (1:FC (Single N))+(∑ i:Beam (Band o b),∑ j:Beam (Band o b),tariff N X i j • unitBlade N i j)
  = preJ (tickA N) X:=by
 rw [preJ]
 apply congrArg (diagonal N X • (1:FC _) + ·)
 have hx(i j) (w:i∉Set.range (sta (S:=Band o b) N) ∨ j∉Set.range (sta (S:=Band o b) N)) :
      cross N X i j • (put i*takeF j)=0:=by
   have t:X i j=0:=by
      by_contra n
      rcases w with w|w
      · exact w (fare_sta (h _ _ n).1)
      exact w (fare_sta (h _ _ n).2)
   simp [crossWord,t]
 change _= ∑ i,∑ j,cross N X i j • (put i*takeF j)

 apply Fintype.sum_of_injective _ (sta_inj e)
 · exact fun i w=>sum_eq_zero fun j _=>hx _ _ (Or.inl w)
 exact fun i=> Fintype.sum_of_injective _ (sta_inj e) _ _ (fun j w=>hx _ _ (Or.inr w)) (fun j=> paySta i j X)
end YM.CF.Bay.Silk
