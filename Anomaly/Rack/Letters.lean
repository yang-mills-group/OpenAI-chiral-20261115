import Anomaly.Rack.Facets
-- membership & physical money on arbitrary ordered layout
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open Buffered StressExchange
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side} {I:Type*}
local notation "Ω" => Single N

namespace Contact

variable {K:Scree.Loom N}{S:I→Support (More N)}{F:I→ Mark N}{V:I→phy N}{l:List I}

def fan (S:I→Support (More N))(l:List I):Support (More N):=l.toFinset.biUnion S

lemma spacing (t:ℕ)(k m:ℕ)(x:Site N)(y:Site N)(b:separation (node x) (node y)>k+m):
   Disjoint (offsetMask k x) (offsetMask m y) := by
  refine Finset.disjoint_left.mpr (fun i u v=>?_)
  obtain ⟨j,h,z⟩:= halo_spec.mp u
  obtain ⟨j',h',z'⟩:=halo_spec.mp v
  rw [mem_singleton.mp h] at z; rw [mem_singleton.mp h',separation_comm] at z'
  exact (not_lt_of_ge ((separation_triangle _ _ _).trans (Nat.add_le_add z z'))) b

lemma assemblePitch (L:List I)(p:∀ i∈L,Contact K (S i) (F i) (V i)): AtSupport false (fan S L) (L.map F).prod:=by
  induction L with
  | nil=> exact AtSupport.oneM _
  | cons i L h=>
    have hx:fan S (i::L)=S i∪fan S L:=by unfold fan; ext j; simp
    simp only [List.map_cons,List.prod_cons,hx]
    exact AtSupport.mulM ((p i (List.mem_cons_self)).pitch.mono subset_union_left) ((h (fun j u=>p j (List.mem_cons_of_mem _ u))).mono subset_union_right)

lemma commAux {A B:Support (More N)} {F G:FC (Single N)}(p:Sector (modesIn _ A) false F)(q:Sector (modesIn _ B) false G)(u:Disjoint A B) : Commute F G := (p.apart q (Finset.disjoint_left.mpr (fun _ w v=> disjoint_left.mp u (modes_at A _|>.mp w) (modes_at B _|>.mp v)))).trans (one_smul _ _)

variable (p:∀ i,Contact K (S i) (F i) (V i))(d:l.Pairwise fun i j=>Disjoint (S i) (S j))
include p d

lemma commuteStack(x:Orbit N): l.Pairwise fun i j=> Commute (V i x) (V j x) := d.imp fun i=>(commAux ((p _).oscillator x) ((p _).oscillator x) i)

lemma prod_mark (x:Orbit N) (U: Fields N): ((l.map F).prod) U=(l.map fun i=> F i U).prod:=by induction l with| nil=> rfl| cons i L h=> simp only [List.map_cons,List.prod_cons,Pi.mul_apply,h (List.pairwise_cons.mp d).2]
lemma letters (x:Orbit N) :
    acts (star ((l.map fun i=> F i (x.1,K x)).prod)) (mateK N)=
      acts (star ((l.map fun i=>V i x).prod)) (mateK N) := by
  let X:=(x.1,K x); let m:=mateK N; let Z(i): FC (Single N):= F i X; let T (i): FC (Single N):= V i x
  have p'(j): acts (star (Z j)) m= acts (star (T j)) m:= (p j).bra x
  have va(j): Sector (modesIn _ (S j)) false (Z j) := ((p j).pitch.allV X).sector
  have vb(j): Sector (modesIn _ (S j)) false (T j) := (p j).oscillator x
  have he(L:List I)(j:I)(A: FC (Single N))(Y:I→FC (Single N))(u:Sector (modesIn _ (S j)) false A)(v:∀ i∈L,Disjoint (S i) (S j))(t:∀ i∈L,Sector (modesIn _ (S i)) false (Y i)):
      Commute (star ((L.map Y).prod)) (star A) := by
    induction L with
    | nil=>rw [List.map_nil,List.prod_nil,star_one]; exact Commute.one_left _
    | cons i L h=>
      rw [List.map_cons,List.prod_cons,star_mul]
      have H : Commute (star ((L.map Y).prod)) (star A):= h (fun i u=> v _ (List.mem_cons_of_mem _ u)) (fun i u=> t _ (List.mem_cons_of_mem _ u))
      exact Commute.mul_left H (commAux (t _ (List.mem_cons_self)).contr u.contr (v _ (List.mem_cons_self)))
  induction l with
  | nil => rfl
  | cons i l IH =>
    obtain ⟨w,v⟩:=List.pairwise_cons.mp d
    specialize IH v
    change acts (star ((Z i)*(l.map Z).prod)) m= acts (star ((T i)*(l.map T).prod)) m
    rw [star_mul,star_mul,act_mul,p',←act_mul,(he l i (T i) Z (vb i) (fun j y=>(w _ y).symm) (fun j _=>va j)).eq,(he l i (T i) T (vb i) (fun j y=> (w _ y).symm) (fun j _=>vb j)).eq,act_mul,act_mul (star (T i))]
    exact congrArg _ IH

lemma stencil (x:Orbit N)(y:Phys N) : letterRead ((l.map F).prod (x.1,K x)) y= beamZ N (acts ((l.map fun i=>V i x).prod) y):=by
  change inner ℂ (mateK N) (acts ((l.map F).prod (x.1,K x)) y)= _
  unfold beamZ; rw [prod_mark p d x, ←act_inner, ←act_inner, letters p d x]

end Contact
end YM.CF.Swell
