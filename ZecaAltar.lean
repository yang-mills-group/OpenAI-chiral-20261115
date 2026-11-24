import ZecaPetra
import ZecaHarvest
import YM.SU5.FiniteGaugeData.Cirrus.Nappe
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Monument
open Poin Boundary Probe
variable {ι:Type}{H:Hilbert}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)
   (Ω:Bench S)(hΩ:∀x:E4,M S x Ω.val=Ω.val)
local notation "J"=>Grotto S G Ω.val
local notation "T"=>springs S G Ω.val
local notation "φ"=>saint S G Ω hΩ
local notation "N"=>chapel S G Ω.val
local notation "C"=>Cove S G Ω.val
local notation "L"=> (C).subtypeL
local notation "h'"=> crystalline S G Ω.val


open Poin.Cirrus.PavilionM
variable (D:Moment H)
local notation "U"=>G.Model S Ω

lemma act_field {D:Moment H} (p:Paid S G D) (f:Test4):
  ∃ t:G.Token, tsupport t.2⊆tsupport f ∧
    D.field S f=(letter G t.1).field S t.2 :=by
 obtain ⟨a,j⟩:= p;obtain ⟨k,v,r⟩:=j f;exact ⟨(a,k),v,r⟩
def base {D:Moment H} (p:Paid S G D)(f:Test4):Effort S Ω G:=G.conduct S Ω (act_field S G p f).choose
lemma base_money {D:Moment H}(p:Paid S G D)(f:Test4)(x:U):
    (base S G Ω p f x).val=D.field S f x.val:= by rw [(act_field S G p f).choose_spec.2];rfl
lemma gen {D:Moment H}(p:Paid S G D)(f:Test4)(hp:HasCompactSupport (⇑f)):
    base S G Ω p f ∈ Hull S Ω G univ (tsupport f):=by
 let t:= (act_field S G p f).choose; let q:= (act_field S G p f).choose_spec
 exact seeds _ _ _ _ _ t ⟨mem_univ _, hp.of_isClosed_subset (isClosed_tsupport _) q.1, q.1⟩

variable {D:Moment H}(p:Paid S G D)

/-- Unbounded tempered field, actually restriction, albeit on smaller dense domain -/
def organ:Test4→ₗ[ℂ] Effort S Ω G where
  toFun:=base S G Ω p
  map_add' f g:=by
    ext1 x; apply Subtype.ext
    rw [base_money,map_add]; exact congrArg₂ (·+·) (base_money _ _ _ p f x).symm (base_money _ _ _ p g x).symm
  map_smul' c f:=by
    ext1 x;apply Subtype.ext
    rw [base_money,map_smul];exact congrArg (c • ·) (base_money _ _ _ p f x).symm
local notation "γ"=> (organ S G Ω p)
local notation "Λ"=>G.lens S Ω
lemma closed_field (x:U):Continuous fun f=>Λ (organ S G Ω p f x):=by
  have k : (fun f=>Λ (γ f x))=fun f=>(D.field S f x.val).val:=funext fun f=> congrArg Subtype.val (base_money S G Ω p f x) -- tune
  rw [k]; exact (realStamp S).dist _ x.val

variable (V:Boundary.Action H)(e:G.Arrival S Ω V)
include e
lemma chamber {D':Moment H}(q:Paid S G D')(f g:Test4)(c:Fields.causal f g):
 Commute (γ f) (organ S G Ω q g):=by
 let t:= (act_field S G p f).choose; let z:= (act_field S G q g).choose
 have a:= (act_field S G p f).choose_spec.1;have b:=(act_field S G q g).choose_spec.1
 exact e.localC t.1 z.1 t.2 z.2 (fun x v y w=> c x (a v) y (b w))

omit e
include hΩ
lemma determine (k:G.Climb S Ω=⊤)(A:H.Op): D.op=A↔∀(f:Test4)(x:U),
   Λ (γ f x)=(ℑ S A f D.n x.val).val:=by
 constructor
 · intro a f x;rw [←a]; exact congrArg Subtype.val (base_money S G Ω p f x)
 intro t
 refine G.encase S Ω hΩ D.n D.op A k (fun f x y=>?_ )
 exact congrArg (inner ℂ (Λ x)) ((congrArg (Subtype.val) (base_money S G Ω p f y).symm).trans (t _ _))
#print axioms chamber
#print axioms determine
