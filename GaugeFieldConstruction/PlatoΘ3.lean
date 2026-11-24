import GaugeFieldConstruction.«PoultΠ3»
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
variable (P:BudgetPoint)
namespace Argos
section gen
section gas
variable {α β ι M:Type*} [Fintype ι][Fintype β] [DecidableEq β] [Fintype α]
variable (w:ι→β)(t:β→Finset α)(f:ι→M)
variable (V:Finset β)
local notation "F"=>fun j=> (univ:Finset ι).filter fun i=> w i=j
variable [CommSemiring M]
lemma repour : (∏ j∈V,PourUp w f j)=∑ s∈ ((univ:Finset (Finset ι)).filter (fun s:Finset ι=>s.image w=V∧Set.InjOn w (s:Set ι))), ∏ i∈s,f i:=by
 unfold PourUp; rw [Finset.prod_sum]; let A:= V.pi F
 let g (p:∀ (i:β), i∈V→ι):= V.attach.image fun j=>p j.val j.property
 have h {p}(u:p∈A){i:β}(t:i∈V): w (p i t)=i:=(mem_filter.mp (Finset.mem_pi.mp u i t)).2
 have he {p} (u:p∈A)(i:ι): i∈ g p ↔ ∃ t:w i∈V, p (w i) t = i:=by
    constructor
    · intro v; obtain ⟨⟨j,k⟩,z,rfl⟩:= mem_image.mp v; dsimp only
      have hx:=h u k; simp [hx,k]
    rintro ⟨k,hh⟩; exact mem_image.mpr ⟨⟨w i,k⟩,mem_attach ..,hh⟩
 let d:Finset (Finset ι):=univ.filter (fun s=> s.image w=V∧ Set.InjOn w (s:Set ι))
 have hd {s}:s∈d↔s.image w=V ∧ Set.InjOn w s:=by simp [d]
 apply sum_bij (fun a h=>g a)
 · intro i v; apply hd.mpr; constructor
   · ext j; constructor
     · intro q; obtain ⟨x,z,rfl⟩:=mem_image.mp q; exact ((he v x).mp z).choose
     intro jv; exact mem_image.mpr ⟨i j jv,mem_image.mpr ⟨⟨j,jv⟩,mem_attach ..,rfl⟩,h v jv⟩
   intro x v' y y' ht
   obtain ⟨t,x'⟩:=(he v x).mp v'; obtain ⟨z,y'⟩:=(he v y).mp y'; exact x'.symm.trans ((congrArg (fun j:↥V=>i j.val j.property) (show (⟨_,t⟩:↥V)=⟨_,z⟩ from Subtype.ext ht)).trans y')
 · intro x v y t a; funext i hi; let j:=x i hi; have hg:w j=i:=h v hi
   have hz:j∈g x:= mem_image.mpr ⟨⟨i,hi⟩,mem_attach ..,rfl⟩
   obtain ⟨l,o⟩:= (he t j).mp ((a ▸ hz) : j∈g y); exact o.symm.trans (congrArg (fun i:↥V=>y i.val i.property) (show (⟨_,l⟩:↥V)=⟨_,hi⟩ from Subtype.ext hg))
 · intro b s; obtain ⟨e,t⟩:=hd.mp s; choose x p q using fun (j:β)(u:j∈V)=> mem_image.mp ((e ▸ u): j∈ b.image w) -- rw tune
   have v:x∈A:=Finset.mem_pi.mpr fun j t=>mem_filter.mpr ⟨mem_univ _,q j t⟩
   refine ⟨x,v,?_⟩; ext i; rw[he v i]; constructor
   · rintro ⟨d,h⟩; exact h ▸ p (w i) d -- dependent anchor h may loop
   intro hi; have h:w i∈V:=e ▸ mem_image_of_mem w hi
   exact ⟨h,t (p _ h) hi (q _ h)⟩
 intro i v
 unfold g; rw [prod_image]; intro x u y t a; exact Subtype.ext ((h v x.2).symm.trans ((congrArg w a).trans (h v y.2)))

end gas
lemma sockSum {M N E:Type}[Fintype M][Fintype N][DecidableEq N][AddCommMonoid E](f:M→ E)(k:M→ N):(∑ j:M,f j)=∑ i:N,∑ j:M with k j=i,f j:=by
 simp_rw [sum_filter]; rw [sum_comm]; congr 1; funext i; simp
end gen
-- Reg fiber
variable {δ:Type}[Fintype δ](X:δ→ Support (More n))(r:α→δ)
section
variable {Y:α→Support (More n)}(y:∀ j,Y j=X (r j))
variable (Q:LeaseQ γ n)(P A:Hub n)(p d:ℕ)
local notation "Ψ"=> Heart P Y d
local notation "Φ"=> Heart P X d
include y
def θRaise(x:Heart P Y d): Heart P X d:=⟨r∘x.val,mem_filter.mpr ⟨mem_univ _,fun i=>by refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw[show X ((r∘x.val) i)=Y _ from (y _).symm]; exact (mem_filter.mp ((mem_filter.mp x.property).2 i)).2⟩⟩ -- implicit
lemma pileR (x:Heart P Y d) : Legist P Y d x=Legist P X d (θRaise X r y P d x):= by
 apply Subtype.ext; apply Prod.ext; rfl; change P.val.2 ∪ _=P.val.2 ∪ _; apply congrArg (P.val.2 ∪ ·); congr 1; exact funext fun t=>y _
variable (t:Fin p→γ)(f:Heart P X d)(D:Support (More n))(W:Orbit n)(K:α→Cipher n)(U:FC (Dwell n))
lemma κpursuit : BodyX Q p d t f.val D W U (PourUp r K) = ∑ z:(Heart P Y d) with θRaise X r y P d z=f,BodyX Q p d t z.val D W U K:=by
 change discount p d • scar U ((List.ofFn fun i=> ∑ j:α with r j=f.val i,K j)++ _) = _; rw [body_view Q p d t D W r K U f.val]
 symm; apply sum_bij (fun z _=> z.val) -- tune order
 · intro i g; exact mem_filter.mpr ⟨mem_univ _,congrArg Subtype.val (mem_filter.mp g).2⟩
 · exact fun i _ j _ u=>Subtype.ext u
 · intro b t; have ht:r ∘ b=f.val:=(mem_filter.mp t).2
   have hv:b∈ LeadQ P.val.2 Y d:=by
      refine mem_filter.mpr ⟨mem_univ _, fun i=>mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      rw [y,show r (b i)= f.val i from congrFun ht i]; exact (mem_filter.mp ((mem_filter.mp f.property).2 i)).2
   exact ⟨⟨b,hv⟩,mem_filter.mpr ⟨mem_univ _,Subtype.ext ht⟩,rfl⟩
 exact fun _ _=>rfl -- tune bodyX typeclass ins.
#print axioms κpursuit
end
-- FORCE packs.Vertex image. masks
variable (V:Hub n)(K:β→ Force n)(b:Bool)
section
variable {u:Finset β}
local notation "Z"=> (id:Force n→Force n)
local notation "Ξ"=> image K u
lemma clampW (s:Finset β):walls K s= walls (id:Force n→Force n) (s.image K):= by ext i; simp[walls,plateI]
lemma clampQ (s:Finset β):til K s= til (id:Force n→Force n) (s.image K):= by ext i; simp[til,sealI]
-- Beam_S.
lemma curveΨ :BasisI K V b u ↔ Set.InjOn K u ∧ BasisI (id:Force n→Force n) V b (image K u) :=by
 constructor
 · intro v; have ht:Set.InjOn K u:=(PriceI.inject K ⟨v.packed,rfl⟩)
   refine ⟨ht,⟨?_, ?_,image_nonempty.mpr v.inhab,?_⟩⟩
   · intro i t j w q; obtain ⟨a,p,rfl⟩:=mem_image.mp t; obtain ⟨v',y,rfl⟩:=mem_image.mp w; exact v.packed p y (fun e=>q (congrArg _ e))
   · intro i t; obtain ⟨j,u,rfl⟩:=mem_image.mp t; exact v.busy _ u
   rw [←clampQ]; exact v.meeting
 intro ⟨h,d⟩; refine ⟨?_, ?_, image_nonempty.mp d.inhab,?_⟩
 · exact fun i t j w q=> d.packed (mem_image_of_mem _ t) (mem_image_of_mem _ w) (fun e=> q (h t w e))
 · exact fun i t=> d.busy _ (mem_image_of_mem _ t)
 rw [clampQ]; exact d.meeting
def φRaise(s:Base K V b): Base (id:Force n→Force n) V b:=⟨image K s.val, ((curveΨ ..).1 s.property).2⟩
lemma riseΖ(s:Base K V b): roost K V b s=roost (id:Force n→Force n) V b (φRaise V K b s):=by
 apply Subtype.ext; apply Prod.ext
 · apply Subtype.ext; apply Prod.ext; rfl; change V.val.2∪ _ = V.val.2 ∪ _; exact congrArg (V.val.2 ∪ ·) (clampW K s.val)
 exact clampQ K s.val
lemma press_view (f:β→ Cipher n)(X:Base (id:Force n→Force n) V b): (∏ i∈ X.val,PourUp K f i)= ∑ j:(Base K V b) with φRaise V K b j=X, ∏ i∈ j.val,f i:=by
 rw [repour]; symm; apply sum_bij (fun x _=>x.val)
 · intro a t; refine mem_filter.mpr ⟨mem_univ _,congrArg Subtype.val (mem_filter.mp t).2,((curveΨ ..).1 a.property).1⟩
 · exact fun a v b t e=>Subtype.ext e
 · intro g t; obtain ⟨e,h⟩:=(mem_filter.mp t).2; let G: Base K V b:=⟨g,(curveΨ ..).2 ⟨h,e ▸ X.property⟩⟩; exact ⟨G, mem_filter.mpr ⟨mem_univ _,Subtype.ext e⟩,rfl⟩
 exact fun _ _=>rfl
#print axioms press_view
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
