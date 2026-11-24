import ZecaGerm
import ZecaQuilt
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

abbrev letter (u:G.Chip) : Moment H:= ⟨G.grade u,G.dep u⟩
abbrev Paid (D:Moment H) :=∃ t:G.Chip,D.Copy S (letter G t)
lemma originals(t:G.Chip):Paid S G (letter G t):=⟨t,Moment.selfCopy S _⟩
variable (D:Moment H)
lemma starred {D:Moment H} (p:Paid S G D): Paid S G D.dagger:=by
 obtain ⟨t,v⟩:=p
 refine ⟨G.mirrorK t,?_⟩
 rw [show letter G (G.mirrorK t)=(letter G t).dagger from (by unfold letter Moment.dagger;rw [G.spar t];rfl)]
 exact Moment.twinCopy S D _ v
-- Stone is preserved by even unsmeared paid symbols of the large H.
variable (x:Bench (springs S G Ω.val))
lemma marked (t:G.Chip)(g:Test4): (((letter G t).field S g) ((h').site x)).val ∈ (C):=by
  let u:=(letter (N) t).field T g

  rw [show ((letter G t).field S g) ((h').site x) = (h').site (u x)
           from ((h').showtime (A:=(N).dep t) (B:=G.dep t) (fun v=>rfl) _ _ x).symm]
  exact (u x).val.property
variable (p:Paid S G D)
include p
lemma marks (g:Test4): (D.field S g ((h').site x)).val∈ (C):=by
 obtain ⟨t,k⟩:=p
 obtain ⟨f,_,v⟩:=k g
 rw [v];exact marked S G Ω x t f

lemma valut (g:Test4) : valise S D.op g (L (hall T D.n x))∈ (C):=by
 rw [(h').desk,show _ = Cache _ _ _ from (native S D.op g ((h').site x) D.n).symm]
 obtain ⟨y,e⟩:∃y:J,L y=(D.field S g ((h').site x)).val:=⟨⟨_, marks S G Ω D x p g⟩,rfl⟩
 rw [←show L y=(ℑ S D.op g D.n ((h').site x)).val from e,← (h').cache]
 exact (Cache T D.n y).property
lemma staple:D.op (L (hall T D.n x))∈ (C):=by
 have w:(C)ᗮᗮ≤(C):=by
   rw [Submodule.orthogonal_orthogonal_eq_closure]; exact
     (closure_minimal _root_.subset_rfl (secret S G Ω.val).closed)
 apply w
 refine (Submodule.mem_orthogonal _ _).mpr ?_
 intro y t

 let v:=L (hall T D.n x)
 let f:=lucent S y v D.op
 have hf:f=fun _=>0:=Canopy.oracle _ (continuous_const.inner (village ..))
    (fun g=>by
      unfold f; rw [sell_in]
      rw [←inner_conj_symm]; rw [(Submodule.mem_orthogonal _ _).mp t _ (valut S G Ω D x p g),map_zero])
 unfold f lucent at hf
 exact (congrArg (inner ℂ y ·) (DFunLike.congr_fun (vroot S D.op) v)).symm.trans (congrFun hf 0)
omit p in
lemma hallFull {a:Axis}{V:Hilbert}(U:OS.Semigroup V a)(n:ℕ) :DenseRange (hall U n):=by
     refine Dense.mono ?_ (bench_warm U)
     intro x q; let y:Bench U:=⟨x,q⟩
     exact ⟨park U (Cache U n) (autumn U _ ((Commute.refl (saucer U)).pow_left _)) y,
      congrArg Subtype.val (cache_park U y n)⟩
lemma keeps: Keeps (C) D.op:=by
  have h(y:J):D.op y.val∈(C):=by
     induction y using (hallFull T D.n).induction_on with
     | hp=>exact (secret S G Ω.val).closed.preimage (D.op.continuous.comp continuous_subtype_val)
     | ih x=>exact staple S G Ω D x p
  exact fun y v=> h ⟨y,v⟩
#print axioms keeps
