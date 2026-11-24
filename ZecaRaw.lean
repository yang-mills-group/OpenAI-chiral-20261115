import ZecaGourd
import YM.SU5.Selected.Recolor
import YM.SU5.Aria.Crew
import ZecaSlide
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric

open scoped TensorProduct
open Six
local notation "κ"=> P.calibration
local notation "R"=> ruler P.par.block
local notation "H"=> P.large
local notation "Y"=> P.run
local notation "Φ"=> P.stateSpace j x
local notation "X"=> P.PortionHil j x
local notation "σ"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "R₀"=> P.history
local notation "J"=> P.Slabs j
local notation "T"=> P.Test


variable (s w:ℕ)

/-- Entries as raw tests. -/
def Cellar:Submodule ℂ P.Test where
 carrier:={f|∃ p:P.Card j s w,P.entryTest j s p=f}
 zero_mem':=by
   exact ⟨jamScale P.run P.large s j false w (SlabMark.identity ..) 0,
      show (0:ℂ) • (1:P.Test)=0 from zero_smul ℂ _⟩
 add_mem':=by
   rintro f g ⟨f,rfl⟩ ⟨g,rfl⟩; exact ⟨jamAdd P.run P.large s j false w f g,rfl⟩
 smul_mem':=by
   rintro a f ⟨f,rfl⟩; exact ⟨jamScale P.run P.large s j false w f a,rfl⟩

abbrev straight (f:P.Test):Prop:= f∈ P.Cellar j s w

/-- Geometric qualification -/
lemma straight_ok (f:P.Test):P.straight j s w f ↔
  ∃ S:Finset Cover, Between κ j 0 (ruler P.par.block*w) S ∧ f∈ bay κ S true:=by
 constructor

 · rintro ⟨p,rfl⟩; obtain ⟨U,v,h⟩:=p.property; exact ⟨_,h,v⟩
 rintro ⟨U,h,v⟩
 exact ⟨⟨P.positiveVox j s U f v (fun x u=> (h x u).1),U,v,h⟩,rfl⟩

def straightC (f:P.Cellar j s w) : P.Card j s w:=
  (show ∃ p:P.Card j s w, P.entryTest j s p=f.val from f.property).choose
private lemma cext{a b:P.Card j s w}(h:P.entryTest j s a=P.entryTest j s b):a=b:=
 Subtype.ext (Subtype.ext (congrArg (fun t:P.Test=> t.val) h))
lemma straightTest(f: P.Cellar j s w):P.entryTest j s (P.straightC j s w f)=f.val:=
  (show ∃ p:P.Card j s w, P.entryTest j s p=f.val from f.property).choose_spec

variable (hw:0<w)
lemma chairsJ : ∃ T': T→ₗ[ℂ] J, ∀ p:P.Card j s w,T' (P.entryTest j s p)=P.atSide j s w hw p:=by
 let Z := P.Cellar j s w
 let f (a:Z) := P.straightC j s w a
 let g: Z→ₗ[ℂ] J:=
  { toFun:=fun a=>P.atSide j s w hw (f a)
    map_add':=by
      intro a b
      have e:f (a+b)=jamAdd Y H s j false w (f a) (f b):=by
        apply cext P j s w
        change P.entryTest j s (f (a+b))=P.entryTest j s (f a)+P.entryTest j s (f b)

        simp only [f,straightTest]; rfl
      rw [e]; exact Subtype.ext (jam_add Y H P.law s R₀ σ j false C₀ w (f a) hw (f b))
    map_smul':=by
      intro c a; change P.atSide j s w hw (f (c•a))=c•P.atSide j s w hw (f a)
      have e:f (c•a)=jamScale Y H s j false w (f a) c:=by
        apply cext P j s w
        change P.entryTest j s (f (c•a))=c•P.entryTest j s (f a)
        simp only [f,straightTest]; rfl
      rw [e]; exact Subtype.ext (jam_scale Y H P.law s R₀ σ j false C₀ w _ hw c) }
 obtain ⟨L,h⟩:=Gourd.liftLin Z.subtype Z.ker_subtype
 refine ⟨g.comp L, fun p=>?_⟩
 let a:Z:=⟨_, show P.straight j s w _ from ⟨p,rfl⟩⟩
 have ha:f a=p:=cext P j s w (P.straightTest j s w a)
 change P.atSide j s w hw (f ((L.comp Z.subtype) a))= _
 rw [h,LinearMap.id_apply,ha]

def chairs: T→ₗ[ℂ] (X).Op :=(Φ).toLinearMap.comp (P.chairsJ j s w hw).choose
lemma chairs_card (p:P.Card j s w):P.chairs j x s w hw (P.entryTest j s p)=Φ (P.atSide j s w hw p):=
  congrArg (Φ ·) ((P.chairsJ j s w hw).choose_spec p)


lemma chairs_pearl (f:P.Test)(q:P.straight j s w f):
 inner ℂ (P.emptyV j x) (P.chairs j x s w hw f (P.emptyV j x)) = P.singleState j s x f:=by
 obtain ⟨a,rfl⟩:=q
 rw [P.chairs_card]; exact (gns_state (P.portion j x) _).trans (P.room_single j x s w hw a)
lemma chairs_paint (S:Finset Cover)(v:Between κ j 0 (ruler P.par.block*w) S)
 (f g:T)(a:f∈bay κ S true)(b:g∈bay κ S true)
 (u:Cover→SU.E)(t:Circular S u f.val g.val):
 P.chairs j x s w hw f=P.chairs j x s w hw g:=by
 obtain ⟨p,rfl⟩:P.straight j s w f:= (P.straight_ok ..).mpr ⟨S,v,a⟩
 obtain ⟨q,rfl⟩:P.straight j s w g:= (P.straight_ok ..).mpr ⟨S,v,b⟩
 rw [chairs_card,chairs_card]
 apply congrArg (Φ ·)
 apply Subtype.ext
 have e:= Selected.color_slab Y H P.law s R₀ σ j false C₀ hw p q
   ((Tapestry.locates ..).1 a : InTest κ true S false p.val.val) ((Tapestry.locates ..).1 b : InTest κ true S false q.val.val) v u t
 have ee:=congrArg Subtype.val e
 exact ee  -- might be deeper subtype.


abbrev TwinPort :Type:= (P.PortionHil j x).space ⊗[ℂ] (P.PortionHil j x).space
def Pome:P.TwinPort j x:= P.emptyV j x ⊗ₜ[ℂ] P.emptyV j x
-- hw type arg omitted? abbreviation TwinPort
abbrev PomeOp:Type:=P.TwinPort j x→L[ℂ]P.TwinPort j x
def pith: T→ₗ[ℂ] P.PomeOp j x:= (Gourd.request κ (P.chairs j x s w hw)).choose
lemma pithFactors (f g:T)(p:PureGauge κ f)(q:PureMatter κ g):
    P.pith j x s w hw (f*g) = TensorProduct.mapL (P.chairs j x s w hw f) (P.chairs j x s w hw g):=
  (Gourd.request κ (P.chairs j x s w hw)).choose_spec f g p q

/-- Test any linear claim on eligible f,g products: span. -/
lemma straight_join {f g:P.Test}(a:P.straight j s w f)(b:P.straight j s w g):P.straight j s w (f*g):=by
 obtain ⟨D,p,h⟩:=(P.straight_ok ..).1 a
 obtain ⟨U,t,q⟩:=(P.straight_ok ..).1 b
 exact (P.straight_ok ..).mpr ⟨D∪U,fun y i=> (Finset.mem_union.mp i).elim (p y) (t y),
   (bay κ (D∪U) true).mul_mem (tallerBay κ _ _ subset_union_left h) (tallerBay κ _ _ subset_union_right q)⟩

open Sound
lemma straight_exhaust (f:T)(p:P.straight j s w f):
 ∃ (I:Type)(d:Finset I)(a b:I→P.Test), f=∑ i∈d,a i*b i ∧ 
    ∀i,P.straight j s w (a i)∧ P.straight j s w (b i)∧
         PureGauge κ (a i) ∧ PureMatter κ (b i):=by
  obtain ⟨S,v,p⟩:= (P.straight_ok ..).1 p
  obtain ⟨g,h⟩:=circulation S κ ((Tapestry.locates ..).1 p)
  let f₁(i:Evens S):=tagWord S i.val
  have ht(i:Evens S): InTest κ true S false (Sound.sing κ (f₁ i)):=i.property ▸ sung κ (f₁ i) (Satin.brand S _)
  let b(i:Evens S): T:= ⟨Sound.sing κ (f₁ i), broadCompile κ S (ht i)⟩
  let a(i:Evens S):T:= ⟨scalar κ (g i).val,broadCompile κ S (.seed (g i).property)⟩
  let vs:=∑ i:Evens S,a i*b i
  have hv:f=vs:= by
    apply Subtype.ext
    exact h.trans (map_sum (screenHall κ).val (fun i:Evens S=>a i*b i) univ).symm -- argument inference?
  refine ⟨_,_,_,_,hv,fun i=>⟨(P.straight_ok ..).mpr ⟨S,v,?_⟩,
                                  (P.straight_ok ..).mpr ⟨S,v,ht i⟩,
                                  ⟨S,(g i).val,(g i).property,rfl⟩,
                                  wordIndependent κ _⟩⟩
  exact InTest.seed (g i).property
