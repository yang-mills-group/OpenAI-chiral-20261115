import ZecaAltar
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


variable {D:Moment H}(p:Paid S G D)
abbrev post: Moment (J):=⟨D.n,restr (C) D.op (keeps _ _ Ω _ p)⟩
lemma posted_test (f:Test4)(x:Bench T):
 ((h').site) ((post S G Ω p).field T f x)=D.field S f ((h').site x):=
   (h').showtime (A:=(post S G Ω p).op) (B:=D.op) (fun _=>rfl) _ _ _
private lemma inj(a b:Bench T): ((h').site a) = ((h').site b)→a=b:=
 fun t=>Subtype.ext (Subtype.ext (congrArg (fun a:Bench S=>a.val) t))

lemma posting: Paid T N (post S G Ω p):=by
  obtain ⟨t,z⟩:=p
  refine ⟨t,fun f=>?_⟩
  obtain ⟨g,a,q⟩:=z f; refine ⟨g,a,?_⟩
  ext1 x
  apply inj;rw [posted_test,q]
  exact ((h').showtime (A:=(N).dep t) (B:=G.dep t) (fun _=>rfl) _ _ x).symm

abbrev Sachet := { D:Moment H// Paid S G D}
abbrev side (t:Sachet S G):=post S G Ω t.property
abbrev twin (t:Sachet S G): Sachet S G:=⟨_,starred _ _ t.property⟩
abbrev sky (t:G.Chip): Sachet S G:=⟨_, originals _ _ t⟩

local notation "Γ"=>Sachet S G
local notation "⬝"=>side S G Ω

local notation "vv"=>pilgrimV S G Ω.val
lemma value2 {α:Type}(F:α→Γ)(sp:α→Cross timeAxis)(t:α→ℝ)
    (u:List α)(e:u.Pairwise fun i j=>t i<t j) :
 quoteL T (vv) (fun x=>⬝ (F x)) sp t u=quoteL S Ω.val (fun x=>(F x).val) sp t u:=by
 let A:=lodgedOp T (fun x=>⬝ (F x)) sp
 let B:=lodgedOp S (fun x=>(F x).val) sp
 let Q:=leap0 T (fun x=>⬝ (F x)) t
 let W:=leap0 S (fun x=>(F x).val) t
 suffices L (Film A Q u vv)= Film B W u Ω.val from congrArg (inner ℂ Ω.val) this
 induction u with
 | nil=>rfl
 | cons i u ih=>
    have v(y:J): L (A i y)=B i (L y):=by
      change L (M (T) _ ((⬝ (F i)).op (M (T) _ _)))=M S _ _
      rw [(h').trans];change M S _ ((F i).val.op (L (M (T) _ _)))=_
      rw [(h').trans];rfl
    rw [Film_step, Film_step]
    change L (A i (clip Q i u (Film A Q u vv)))= B i (clip W i u (Film B W u Ω.val))
    rw [v];congr 1
    obtain ⟨r,s⟩:=List.pairwise_cons.mp e
    rw [← ih s]
    cases u with
    | nil=>rfl
    | cons j u=>
       have d: (↑(t j-t i):ℂ)∈inside:= by rw [inside,Set.mem_setOf, ofReal_re];exact sub_pos.mpr (r j List.mem_cons_self)
       exact (h').par d _ _
