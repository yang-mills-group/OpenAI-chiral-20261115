import GaugeFieldConstruction.Durango4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
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
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I:Type}[Fintype I][LinearOrder I]{n: Side}
section
-- graph transport lifted. independent 
variable (α : Equiv.Perm (Seat n))(φ: Equiv.Perm (Hub n))(Ωu:Equiv.Perm (Force n))
abbrev θSet (β:Equiv.Perm (Seat n)) (S:Support (More n)):= S.image β
structure Same4 :Prop where
   center(x): (φ x).val.1=α (x.val.1)
   tile(x):cloudP (φ x)=θSet α (cloudP x)
   pair(x:Force n):(Ωu x).val.1=φ (x.val.1)
   band(x): (Ωu x).val.2=θSet α x.val.2
variable (e:Same4 α φ Ωu)
namespace Same4
local notation "αρ"=> θSet α
private lemma inject_m :Injective (θSet α) :=by
 intro i j h; ext a; constructor
 · intro v; obtain ⟨b,t,g⟩:= mem_image.mp ((h ▸ Finset.mem_image_of_mem α v): α a∈ θSet α j); rwa [←α.injective g]
 intro v; obtain ⟨b,t,g⟩:= mem_image.mp (show α a∈θSet α i from h ▸ mem_image_of_mem α v); rwa[←α.injective g]
lemma d_p (X D:Support (More n)):Disjoint (θSet α X) (θSet α D) ↔ Disjoint X D:= by
 constructor
 · intro t; exact Finset.disjoint_left.mpr fun i k x=> Finset.disjoint_left.mp t (Finset.mem_image_of_mem α k) (Finset.mem_image_of_mem α x)
 intro t; apply Finset.disjoint_left.mpr; intro i p q; obtain ⟨j,p,h⟩:=mem_image.mp p; obtain ⟨k,q,v⟩:=mem_image.mp q; exact disjoint_left.mp t p ((α.injective (v.trans h.symm)) ▸ q)
variable (t:ℕ)(P:Hub n)
local notation "L"=> PI I n
local notation "V"=> KI I n
def ΔX (I:Type): Equiv.Perm (PI I n):= Equiv.prodCongr (Equiv.refl _) φ
def ΔF (I:Type):Equiv.Perm (KI I n):=Equiv.prodCongr (Equiv.refl _) Ωu
local notation "δ"=> ΔX φ I
local notation "Θ"=> ΔF Ωu I
abbrev Dusk (I:Type)(n:Side): PI I n→ Support (More n):=fun i=>cloudP i.2
abbrev Flak (I:Type)(n:Side):KI I n→ Force n:=Prod.snd
local notation "w"=> (Dusk I n)
local notation "f"=> (Flak I n)
include e
lemma patchP(i:PI I n): Dusk I n (ΔX φ I i)=θSet α (Dusk I n i):= e.tile _
lemma patchF(i:KI I n):plateI (Flak I n) (ΔF Ωu I i)= θSet α (plateI (Flak I n) i):=by change cloudP ((Ωu i.2).val.1)=_; rw[e.pair,e.tile]; rfl
lemma sailP (x:Fin t→ PI I n): (fun i=>ΔX φ I (x i))∈LeadQ (φ P).val.2 (Dusk I n) t ↔ x∈ LeadQ P.val.2 (Dusk I n) t:=by
 have p(i: L): δ i∈ clouds w (φ P).val.2 ↔ i∈ clouds w P.val.2:=by
    have he:(φ P).val.2= _ :=e.tile P
    unfold clouds; rw [mem_filter,mem_filter,show w (δ i)=_ from patchP α φ Ωu e i,he,d_p α]; simp[cloudP]
 simp only[LeadQ, mem_filter, mem_univ,true_and,forall_congr' (fun j=>p (x j))]
-- P stamping
abbrev αfun (φ:Equiv.Perm (Hub n))(v:Fin t→PI I n):Fin t→PI I n:= fun i=> ΔX φ I (v i)
def Drab : Heart P (Dusk I n) t ≃ Heart (φ P) (Dusk I n) t where
    toFun a:=⟨δ ∘ a.val,(sailP α φ Ωu e t P a.val).2 a.property⟩
    invFun b:=⟨(δ).symm∘ b.val, (sailP α φ Ωu e t P _).1 (show (fun i=>ΔX φ I ((ΔX φ I).symm (b.val i)))∈ LeadQ (φ P).val.2 (Dusk I n) t from (by simp[b.property]))⟩
    left_inv a:=Subtype.ext (funext fun j=>Equiv.symm_apply_apply ..)
    right_inv a:=Subtype.ext (funext fun j=>Equiv.apply_symm_apply ..)
local notation "Dk"=> Drab α φ Ωu e t P
lemma bayZ(i:Heart P (Dusk I n) t):Legist (φ P) (Dusk I n) t (Drab α φ Ωu e t P i)=φ (Legist P (Dusk I n) t i):=by
 apply Subtype.ext; apply Prod.ext; exact ((e.center P).trans ((e.center (Legist P w t i)).symm))
 change lengthQ _ _ _=cloudP _; rw [e.tile]; change (φ P).val.2 ∪ univ.biUnion (w∘ (Dk i).val)=αρ (P.val.2 ∪ univ.biUnion (w∘ i.val)); unfold θSet; rw[image_union,biUnion_image]; congr 1; exact e.tile _
 congr 1; exact funext fun j=>patchP α φ Ωu e _ -- comp reduce
-- transport Force packs atoms.Y
abbrev xBand (S:Finset (KI I n)):=S.image (ΔF Ωu I)
local notation "pF"=> plateI f
local notation "sF"=> sealI f
local notation "ωF"=> xBand Ωu
lemma patchK (i:KI I n):sealI (Flak I n) (ΔF Ωu I i) = θSet α (sealI (Flak I n) i) :=e.band _
private lemma imW {A:Type}[DecidableEq A](Xp:A→Support (More n))(B:Equiv.Perm A)(W:Finset A)(h:∀ j,Xp (B j)=θSet α (Xp j)): (W.image B).biUnion Xp=θSet α (W.biUnion Xp):=by
 unfold θSet; rw[image_biUnion]; rw[biUnion_image]; congr 1; exact funext fun i=> h i
lemma walls_Fp (A:Finset (KI I n)):walls (Flak I n) (xBand Ωu A)= θSet α (walls (Flak I n) A):=imW α φ Ωu e (plateI f) Θ A (patchF α φ Ωu e)
lemma til_Fp(A:Finset (KI I n)):til (Flak I n) (xBand Ωu A)=θSet α (til (Flak I n) A):=imW α φ Ωu e (sealI f) Θ A (patchK α φ Ωu e)
lemma eigenB (b:Bool)(A:Finset (KI I n)): BasisI (Flak I n) (φ P) b (xBand Ωu A) ↔ BasisI (Flak I n) P b A:=by
 have he(i j:KI I n):Disjoint (pF (Θ i)) (pF (Θ j)) ↔ Disjoint (pF i) (pF j):=by rw[patchF α φ Ωu e i,patchF α φ Ωu e j,d_p]
 have hb(i:V): Disjoint ((φ P).val.2) (pF (Θ i)) ↔ Disjoint P.val.2 (pF i):=by rw[show (φ P).val.2= _ from e.tile _,patchF α φ Ωu e,d_p]; rfl
 have hz: (b=true ∨ ¬Disjoint (φ P).val.2 (til f (ωF A))) ↔ b=true ∨ ¬Disjoint P.val.2 (til f A):=by rw [show (φ P).val.2=θSet α P.val.2 from e.tile _,til_Fp α φ Ωu e,d_p]
 constructor
 · intro v; exact ⟨fun i p j h q=> (he i j).1 (v.packed (mem_image_of_mem (Θ) p) (mem_image_of_mem _ h) ((Θ).injective.ne q)),fun i t=> fun g=> v.busy _ (mem_image_of_mem _ t) ((hb i).2 g),image_nonempty.mp v.inhab,hz.mp v.meeting⟩ -- tune
 intro v; refine ⟨?_, ?_,image_nonempty.mpr v.inhab,hz.mpr v.meeting⟩
 · intro i p j t q; obtain ⟨a,pz,rfl⟩:= mem_image.mp p; obtain ⟨b,tz,rfl⟩:=mem_image.mp t; exact (he a b).2 (v.packed pz tz (fun e=>q (congrArg (⇑Θ) e))) -- tune
 intro i u; obtain ⟨j,uz,rfl⟩:=mem_image.mp u; exact fun h=>v.busy _ uz ((hb _).1 h)
-- twisted Crate to Legist.V
variable (P':Hub n)(h:φ P=P')(b:Bool)
include h
lemma biasH (W:Finset (KI I n)): BasisI (Flak I n) P' b (xBand Ωu W) ↔ BasisI (Flak I n) P b W:= h ▸ eigenB α φ Ωu e P b W
lemma x_bij:Bijective (xBand (I:=I) Ωu) := by
 let V'(M:Finset (KI I n)):=M.image (ΔF Ωu I).symm; have u(a): V' (xBand Ωu a)=a:=by unfold V' xBand; rw[image_image]; simp; -- tune
 have v(A):xBand Ωu (V' A)=A:=by unfold xBand V'; rw[image_image]; simp; -- tune
 exact ⟨LeftInverse.injective u, RightInverse.surjective v⟩
def Bias : Base (Flak I n) P b ≃ Base (Flak I n) P' b:= Equiv.subtypeEquiv (Equiv.ofBijective (xBand Ωu) (x_bij α φ Ωu e P P' h)) (fun x=> (biasH α φ Ωu e P P' h b x).symm)
lemma cap_v (A:Base (Flak I n) P b): let W:=Bias α φ Ωu e P P' h b A; roost (Flak I n) P' b W=Ωu (roost (Flak I n) P b A):=by
 intro W; apply Subtype.ext; apply Prod.ext
 · change mixedHub P' f W.val= (Ωu _).val.1; rw [e.pair _]; apply Subtype.ext; apply Prod.ext; exact (show P'.val.1=(φ (mixedHub P f A.val)).val.1 from (h ▸ ((e.center P).trans (e.center (mixedHub P f A.val)|>.symm))))
   change P'.val.2∪walls f (ωF A.val)=cloudP _; rw [show P'.val.2=θSet α P.val.2 from h ▸ e.tile P,e.tile,walls_Fp α φ Ωu e A.val]; exact (image_union ..).symm
 change til f (xBand Ωu A.val)=(Ωu _).val.2; rw[til_Fp α φ Ωu e A.val,e.band]; rfl
end Same4
end
end Iona
end YM.CF.Scree.Ing
end
