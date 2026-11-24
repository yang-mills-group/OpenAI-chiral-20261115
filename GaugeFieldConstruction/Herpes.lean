import GaugeFieldConstruction.Shoot
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
-- master movement kit.Instantiated Gauge and Sweep
structure Courier where
 actor : (Pane n)→(Pane n)
 Φ: Seat n≃ Seat n
 Θ: Scree.Hub n ≃ Scree.Hub n
 vol: UNI Y
 k: Bool
 lot : Bool
 tide : Torches n → Torches n
 ambit :Torches n→Prop
 bite (X:Scree.Hub n): (Θ X).val.1= Φ X.val.1 ∧ (Θ X).val.2=X.val.2.map Φ.toEmbedding
 pad(i:Seat n)(L:ℕ)(P:BudgetPoint): Halo_Plus L (Φ i) P=(Halo_Plus L i P).map Φ.toEmbedding
 steers(g:Torches n)(h:ambit g)(o:Seat n)(x:Hubber n)(A:Pane n): Benck (Φ o) (tide g) (actor A) (x.map Φ.toEmbedding)= steerZ vol k lot (Benck o g A x)
 core(g:Torches n)(h:ambit g)(A: Pane n): AlphaY (tide g).1 (actor A)= paintR k lot vol (AlphaY g.1 A)
 limb(o:Seat n):Pach (Φ o)=(Pach o).map Φ.toEmbedding
#print Courier
def bright(T:Sweep n):Courier (n:=n) where
 actor:=flashA T
 Φ:=(boxA T).symm
 Θ:= νIt T
 vol:=launchZ T
 k:= T.charge
 lot:= Typer T
 tide:= tiro T
 ambit:=fun _=> True
 bite _:=⟨rfl,rfl⟩
 pad i L P:=Halo_After T P L i
 steers g h o x A:=by unfold Benck; change αLines (mintP (tiro T g) (sh T o) (nCap T x)) _=_; rw [Mint_R]; exact boothK ..
 core g h A:=(axis_V g.1 T).turns A
 limb o:= (tiltY T o).symm

def dayG(g: Agora n):Courier (n:=n) where
 actor:= GA g
 Φ:=Equiv.refl _
 Θ:=Equiv.refl _
 vol:=tradew n g
 k:= false
 lot:=false
 tide:=id
 ambit:=LegTax
 bite x:=⟨rfl,(map_refl ..).symm⟩
 pad _ _ _:= (map_refl ..).symm
 steers F h i x A:=by simp only [Equiv.refl_apply, map_refl,Equiv.refl_toEmbedding]; first| exact (Zen_port x i F h) A g|rw [map_refl]; exact (Zen_port x i F h) A g
 core F h A:= warp_B h.1 A g
 limb _:= (map_refl ..).symm

variable (C:Courier (n:=n))(σ':I→Seat n)
lemma cost_actor (v:∀i∈t,σ' i=C.Φ (σ i))(b:Bool): padS I σ' t (S.map C.Φ.toEmbedding) L P b= (padS I σ t S L P b).map C.Φ.toEmbedding:=by
 let X:= C.Φ; have hp: Finset.image σ' t = (Finset.image σ t).map X.toEmbedding:=by rw [map_eq_image,image_image]; exact Finset.image_congr v
 unfold padS; split; exact rfl; split; swap; exact rfl
 rw [hp, Finset.map_union]; apply congrArg; let A:= t.image σ; ext x; obtain ⟨x,rfl⟩:=X.surjective x
 rw [Finset.mem_biUnion]; have he(y)(v:Finset (Seat n)): X y ∈ v.map X.toEmbedding↔y∈ v:= by simp
 change _↔ X x∈ Finset.map X.toEmbedding _
 rw [he x,mem_biUnion]; constructor
 · rintro ⟨k,u,t⟩; obtain ⟨w,rfl⟩:=X.surjective k; rw [he] at u; change X x∈ Halo_Plus L (C.Φ w) P at t; rw [C.pad] at t; exact ⟨_,u,(he _ _).mp t⟩
 rintro ⟨k,v,y⟩; refine ⟨X k,(he _ _).mpr v,?_⟩; change _∈Halo_Plus L (C.Φ k) P; rw [C.pad]; exact (he _ _).mpr y
lemma ΨActor (v:∀i∈t,σ' i=C.Φ (σ i)) (a:Bool): QuotaΥ I σ' t (S.map C.Φ.toEmbedding) L P a (C.Θ x)=QuotaΥ I σ t S L P a x:=by
 let F:= C.Θ
 have p: MarksΥ I σ' t (S.map C.Φ.toEmbedding) L P a=(MarksΥ I σ t S L P a).map F.toEmbedding:=by
    ext1 x; obtain ⟨x,rfl⟩:= F.surjective x; have hx: Finset.image σ' t=(t.image σ).map C.Φ.toEmbedding:=by rw [map_eq_image,image_image]; exact image_congr v
    have he:=C.bite x
    change C.Θ x ∈MarksΥ _ _ _ _ _ _ _↔ C.Θ x ∈ Finset.map _ _
    simp_rw [MarksΥ,mem_filter,mem_univ,true_and,cost_actor I σ t S P L C σ' v,hx,he.1,he.2, F]; simp
 unfold QuotaΥ; rw [p]; simp [exp_Plate,F]

variable {d c a b f k u e :ℝ}{R: Loom n}{m:ℕ}
variable (J: Elm n Unit d a c)(T':Ids n)(b0:ℝ)
-- needs Bark.OR for all scales. Proof in Context $cost_Hart.
open SeasonH
structure AngularC (C:Courier (n:=n))(F F': Fork n I): Prop where
 size0: stabH F
 size1: stabH F'
 nox0: darkH F
 nox1: darkH F'
 turn:∀ (x: Pane n)(V:Support (More n)),let A:=cryH F V (0:Key I) x; let B:=cryH F' (V.map C.Φ.toEmbedding) (0:Key I) (C.actor x); ∃ u v K T:Op (Single n),A=alter_M u v∧B=alter_M K T ∧Altaz C.vol C.k C.lot u v K T
variable (Q':Roof n u k m R)(g:k<d)(hp:0<d)(A₁:b0≥0)(tK:coinH f b0)(z:hud_T 7 f)(f0:1≤f)(vS:P.threshold≤u)(U:P.order≤6)(S':groupShape J)(W:pure_Rim J)
local notation "FQ"=>street I J R u m b0 T'
local notation "Zq" A:max V:max=>blade0 J R u m T' V A
local notation "Wq" A:max V:max=>blade1 J R u m T' V A
include g Q' hp A₁ tK z f0 vS U S' W
lemma Rotor : AngularC I (bright T) FQ FQ:=by
 let S:=Ker_Ω I J R k u P m b0 T' Q' g hp A₁ tK z f0 vS U; refine ⟨S.size,S.size, S.mist,S.mist,fun x V=>?_⟩; dsimp only; let A:= flashA T x; let V':= nCap T V; exact ⟨Zq x V,Wq x V,Zq A V',Wq A V', dimL I J R k u m b0 T' Q' g hp A₁ tK f0 V x _,dimL I J R k u m b0 T' Q' g hp A₁ tK f0 V' A _, Beef_R J R k u m b0 T' Q' g hp A₁ tK f0 V x S' W T⟩
lemma Gauge_e (p:Agora n): AngularC I (dayG p) FQ FQ:=by
 let S:= Ker_Ω I J R k u P m b0 T' Q' g hp A₁ tK z f0 vS U; refine ⟨S.size,S.size,S.mist,S.mist,fun x V=>?_⟩; dsimp only; let A:= GA p x; exact ⟨Zq x V,Wq x V,Zq A V,Wq A V,dimL I J R k u m b0 T' Q' g hp A₁ tK f0 V x _,(by rw [show V.map (dayG p).Φ.toEmbedding=V from map_refl ..]; exact dimL I J R k u m b0 T' Q' g hp A₁ tK f0 V A _), Beef_P J R k u m b0 T' Q' g hp A₁ tK f0 V x W p⟩
#print axioms Gauge_e
end MintB
end MastTin
end YM.CF.XGarden
end
