import GaugeFieldConstruction.Herons
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
section grow
variable {K:Calibration}{I:Type*}{σ:Cover}{W:ℤ}{F:I→Family K}{o:I → Cover}{L J: List (Raft K I)}{m n:Side}{S:I→Finset Cover}
local notation "V"=> Vibro F o σ W n
local notation "B" j:max b:max=> Raft.foliation K W σ j b
-- abstract for spread
variable {M:List (Raft K I)→ℝ}
structure LitBank (F:I→Family K)(o:I → Cover)(σ:Cover)(W:ℤ)(m n:Side)(M:List (Raft K I)→ℝ):Prop where
 w:LatticeFare K m n W σ
 paid:∀ (L:List (Raft K I)), Vibro F o σ W n L→ 0≤M L∧ M L≤1
 cs:∀ j b s,bank σ W b j=gaugeShift K.B s→∀ L,Vibro F o σ W n L→ M L^2≤ M (Backrift σ W n j b L)* M (Forerift σ W n j b L)

-- slice diagrams
variable (n)
def Keeps (a:I)(y:Cover)(L:List (Raft K I)):Prop:=∃ e∈L,e.ink=a∧e.bow n=atDeck n y
def Splash (a:I)(l h:Cover)(L:List (Raft K I)):Prop:=∀ x,Inbox l h x→Keeps n a x L
variable {n}{a:I}{x y l h:Cover}
local notation "E"=> Keeps n a
local notation "Ι"=> Splash n a
lemma splash_seed (g:E x L): Ι x (fun i=> x i+1) L:=by
 intro y v; have he:y=x:=by
    funext i; obtain ⟨h,t⟩:= v i; beta_reduce at t; omega
 rwa[he]
-- chooses the (half cyclic) back of b, possible even if require funded at far
lemma LitBank.seam (U:LitBank F o σ W m n M)(j:Axis)(b:ℤ)(v:V L):∃ J,V J∧ M L^2 ≤ M J∧
 ∀ y:Cover,b-n.val≤y j→y j<b → E y L→E y J ∧ E (bent j (2*b) y) J:=by
 rcases U.w.auth j b with ⟨s,e⟩ |⟨s,e⟩
 · let R:=Backrift σ W n j b L
   have pR:V R:=v.back j b; have pL:= v.fore j b
   refine ⟨R,pR,(U.cs j b s e L v).trans (mul_le_of_le_one_right (U.paid _ pR).1 (U.paid _ pL).2),?_⟩
   intro y h t h'
   obtain ⟨f,k,z,u⟩:=h'
   have d:f∈downstream n j b L:= keep_down.mpr ⟨k,fun v=>halfNear h t ((creek_bank j b (show atDeck n f.posC = _ from u)).1 v)⟩ -- tune halfNear binder order
   exact ⟨⟨f,List.mem_append_left _ d,z,u⟩,⟨(B j b) f, List.mem_append_right _ (List.mem_map_of_mem d),z,bank_bent j b u⟩⟩
 let h:=b+n.val; let R:=Forerift σ W n j h L
 have pR:V R:=v.fore j h; have pL:= v.back j h
 refine ⟨R,pR,(U.cs j h s e L v).trans (mul_le_of_le_one_left (U.paid _ pR).1 (U.paid _ pL).2),?_⟩
 intro y p t h'
 obtain ⟨f,k,z,u⟩:=h'
 have d:f∈upstream n j h L:= keep_up.mpr ⟨k,(creek_bank j h (show atDeck n f.posC = _ from u)).2 (halfFar p t)⟩
 exact ⟨⟨f,List.mem_append_right _ d,z,u⟩,⟨(B j h) f, List.mem_append_left _ (List.mem_map_of_mem d),z,(bank_bent j (b+n.val) u).trans (farBent j b y)⟩⟩
lemma LitBank.pour (U:LitBank F o σ W m n M)(j:Axis){t c':ℤ}(v:V L)(g:Ι l (pet h j (l j+t)) L)(q:1≤t)(p:t≤n.val)(b:c'≤2*t):
 ∃ J, V J∧ M L^2≤ M J∧ Ι l (pet h j (l j+c')) J:=by
 let d:=l j+t; obtain ⟨J,y,e,P⟩:=U.seam (a:=a) j d v
 refine ⟨J,y,e,?_⟩
 intro x a'
 obtain ⟨a₀,t₀⟩:= a' j; rw[pet_i] at t₀
 have prices(k:Cover)(u:l j≤k j)(q':k j<d)(A:∀ i,i≠j→k i=x i): Inbox l (pet h j (l j+t)) k:=by
   intro i; by_cases w:i=j
   · subst i; rw[pet_i]; exact ⟨u,q'⟩
   rw[A i w,pet_j _ w]; specialize a' i; rwa[pet_j _ w] at a'
 have hu:d=l j+t:=rfl
 by_cases z:x j<d
 · exact (P x (by omega) z (g x (prices x a₀ z (fun _ _=>rfl)))).1
 let k:=bent j (2*d) x
 have hp : k j=2*d-x j-1:=pet_i ..
 have c:l j≤k j:=by omega
 have t':k j<d:=by omega
 have k': x=bent j (2*d) k:= (twice_bent ..).symm
 exact k' ▸ (P k (by omega) t' (g k (prices k c t' (fun _ w=> pet_j _ w _)))).2 -- rw issue direction
lemma LitBank.stretch (U:LitBank F o σ W m n M)(j:Axis){k:ℕ}(p:k+1≤n.val)(v:V L)(g:Ι l (pet h j (l j+1)) L): ∃ J,V J∧ (M L)^(2^k) ≤ M J ∧ Ι l (pet h j (l j+k+1)) J:=by
 induction k with
 | zero=> exact ⟨L,v,by simp,by simpa using g⟩
 | succ k ih=>
    obtain ⟨J,t,x,u⟩:=ih (by omega)
    rw [add_assoc] at u -- maybe changes
    have ht:(k:ℤ)+1≤ (n.val:ℤ):=by omega
    obtain ⟨H,H',ET,Q⟩:=U.pour j (c':=(k:ℤ)+2) t u (by omega) ht (by omega)
    refine ⟨H,H',?_,?_⟩
    · rw [pow_succ,pow_mul]; exact (pow_le_pow_left₀ (pow_nonneg (U.paid _ v).1 _) x _).trans ET
    rwa [show l j + ((k+1:ℕ):ℤ)+1= l j + (↑k+2) from by omega]
lemma LitBank.river (U:LitBank F o σ W m n M)(j:Axis)(v:V L)(g:Ι l (pet h j (l j+1)) L):∃ J,V J ∧ (M L)^(2^n.val)≤ M J ∧ Ι l (pet h j (l j+2*n.val)) J:=by
 have hn:=n.property; let k:ℕ:=n.val-1; have ht:k+1=n.val:=Nat.sub_add_cancel hn
 obtain ⟨J,t,x,u⟩:=U.stretch j ht.le v g
 rw[show l j + (k:ℤ)+1=l j+n.val from by omega] at u
 obtain ⟨H,H',ET,Q⟩:=U.pour j (c':=2*n.val) t u (by omega) le_rfl le_rfl
 refine ⟨H,H',?_,Q⟩
 rw [←ht,pow_succ,pow_mul]; exact (pow_le_pow_left₀ (pow_nonneg (U.paid _ v).1 _) x _).trans ET
variable (n) in
def Cabo (l:Cover)(S:Finset Axis):Cover:= fun i=> if i∈S then l i+2*n.val else l i+1
lemma cabo_zero(l:Cover)(S:Finset Axis){j:Axis}(t:j∉S) : pet (Cabo n l S) j (l j+1)=Cabo n l S:=by
 funext i; by_cases e:i=j
 · subst i; rw [pet_i]; simp[Cabo,t]
 rw [pet_j _ e]
lemma cabo_insert(l:Cover)(S:Finset Axis)(j:Axis): pet (Cabo n l S) j (l j+2*n.val)= Cabo n l (insert j S):=by
 funext i; by_cases e:i=j
 · subst i; rw[pet_i]; simp[Cabo]
 rw[pet_j _ e]; simp[Cabo,e]
lemma LitBank.splash (U:LitBank F o σ W m n M)(v:V L)(u:E x L)(P:Finset Axis):∃ J,V J ∧ (M L)^(2^(n.val*P.card))≤ M J ∧ Ι x (Cabo n x P) J:=by
 induction P using Finset.induction_on with
 | empty=>
    refine ⟨L,v,by simp,?_⟩; unfold Cabo; simp only [Finset.notMem_empty,↓reduceIte]; exact splash_seed u
 | @insert i P q ih=>
    obtain ⟨J,t,p,z⟩:=ih; rw [←cabo_zero x P q] at z
    obtain ⟨H,H',ET,x'⟩:=U.river i t z
    refine ⟨H,H',?_,cabo_insert x P i ▸ x'⟩
    rw[card_insert_of_notMem q,mul_add,mul_one,pow_add,pow_mul]
    exact (pow_le_pow_left₀ (pow_nonneg (U.paid _ v).1 _) p _).trans ET

lemma vibro_length (u:V L):L.length≤(n.val*2)^4:=by
 let T:=L.map (fun e=>e.bow n); have ht:T.toFinset.card= L.length:= (List.toFinset_card_of_nodup u.2).trans (List.length_map ..)
 have hw:=card_le_card (subset_univ T.toFinset)
 rw [ht,card_univ,site_card] at hw; exact hw
lemma Vibro.label_eq (u:V L){r e:Raft K I}(v:r∈L)(w:e∈L)(h:r.bow n=e.bow n):r=e:= by
 -- nodup implies
 induction L with
 | nil=> simp at w
 | cons a L ih=>
    have he:=List.nodup_cons.mp u.2; have ih:=ih (show V L from ⟨fun b t=>u.1 b (List.mem_cons_of_mem _ t),he.2⟩)
    rcases List.mem_cons.mp v with v|v <;> rcases List.mem_cons.mp w with w|w
    · exact v.trans w.symm
    · subst r; exact False.elim (he.1 (List.mem_map.mpr ⟨e,w,h.symm⟩))
    · subst e; exact False.elim (he.1 (List.mem_map.mpr ⟨r,v,h⟩))
    · exact ih v w
lemma Cabo.flush (u:Ι l (Cabo n l univ) L)(g:V L) : L.length=(n.val*2)^4 ∧ ∀ e∈L,e.ink=a:=by
 have y(x:Site (More n)):∃ e∈L,e.ink=a∧ e.bow n=x:=by
    obtain ⟨v,p,rfl⟩:=setBank l x
    exact u _ (fun i=>by simpa [Cabo] using p i)
 let T:=L.map (fun e=>e.bow n); have ht:T.toFinset=univ:=by ext i; obtain ⟨e,h,z,u⟩:= y i; simp [T]; exact ⟨e,h,u⟩
 constructor
 · have hv:=congrArg Finset.card ht; rw [card_univ,site_card] at hv; have hu:T.toFinset.card=L.length:= (List.toFinset_card_of_nodup g.2).trans (List.length_map ..); exact hu.symm.trans hv
 intro e h; obtain ⟨r,t,b,r'⟩:= y (e.bow n); rw [←g.label_eq t h r']; exact b
end grow
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
