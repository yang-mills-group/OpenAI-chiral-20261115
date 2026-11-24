import YM.CF.Reflect.Park
import YM.CF.Pastry.Pie
import YM.CF.Petal.Event

/-! All marked axillary values paid in the same local envelope. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Finset
attribute [local instance] opCStarAlgebra
abbrev EdgeN (m B : Side) := CSide m B
abbrev Elf (m B : Side) := Xmind m B
abbrev Hearth (m B : Side) := LeanV (Elf m B)
abbrev Ewe (m B : Side) := ↥(ribbon (Elf m B))
abbrev Briar (m B : Side) (e : ℝ) := {U:Skin m B // Guard U e}
abbrev Train (m B : Side) (e : ℝ) := Mood (Index m) (Briar m B e) Ballot
abbrev Acres (m : Side) := Seal (Index m)
abbrev Court (m B : Side) := Geometry (EdgeN m B)
variable {m B : Side} {e H : ℝ}
instance : CompactSpace (Briar m B e) := isCompact_iff_compactSpace.mp (cover_closed (Domain m B) e).isCompact
def release (p : Train m B e) : Pack m B := (p.1.val,p.2)
lemma releaseCt : Continuous (release (m:=m) (B:=B) (e:=e)) := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
def mount (m B : Side) (X : Acres m) := X.biUnion (room m B)
def brigade (m B : Side) (X : Acres m) := Finset.univ.filter (α:=Hearth m B) fun i=> carrier (EdgeN m B) i.2∈ mount m B X -- tune
lemma mount_up : Monotone (mount m B) := by intro x y h i g; obtain ⟨a,p,k⟩:=mem_biUnion.mp g; exact mem_biUnion.mpr ⟨a,h p,k⟩
lemma brigade_up : Monotone (brigade m B) := by
  intro X Y g i h; exact mem_filter.mpr ⟨mem_univ _,mount_up g (mem_filter.mp h).2⟩
-- express walls for Common Bank
lemma mount_p (S : Stamp m B) : mount m B (pavilion m B S)= walls m B S := by
  unfold walls; symm; apply union_eq_right.mpr; intro x g; obtain ⟨a,k,H⟩:= full_r m B x; exact mem_biUnion.mpr ⟨a,(pad_iff ..).mpr ⟨x,g,a,k,by simp⟩,k⟩
lemma sign_up (S : Stamp m B) {i : Elf m B} (e : carrier (EdgeN m B) i∈ S) (j) : (j,i)∈ brigade m B (pavilion m B S) := mem_filter.mpr ⟨mem_univ _,by rw [mount_p]; exact mem_union_left _ e⟩ -- tune
def routeS (g : Court m B) (U : Briar m B e) : Briar m B e := ⟨Lattice.gauge g U.val,Guard.cov U.property g⟩
abbrev balls (m B : Side) (g : Court m B) := conjG matter (g ∘ node (N:=EdgeN m B))
def routeM (m B : Side) (g : Court m B) := Pastry.fold (closeV (n:=Elf m B) (balls m B g))
def routeT (p : Train m B e) (g : Court m B) : Train m B e := (routeS (m:=m) (B:=B) g p.1,partner m B g p.2)
def welter (m B : Side) (e H : ℝ) (p : 1≤H) : Lodge (Index m) (Ewe m B) (Briar m B e) (Court m B) where
  toBell:= shelf H p (brigade m B) brigade_up
  zone S U V:= Agrees (mount m B S) U.val V.val
  grows g h:= fun _ u k=> h _ (mount_up g u) (mount_up g k)
  pick:= routeS (m:=m) (B:=B)
  rule := routeM m B
  ct g:= (routeM m B g).toLinearMap.continuous_of_finiteDimensional

def travel (m B : Side) (e H : ℝ) (p : 1≤H) : Petal.Cabin cloud (welter m B e H p) where
  seat U:= rock m B U.val
  unionV := partner m B
  board g:= (pass m B g).measurableEmbedding
  plenty g := rain_g m B g
  mass g U x:= by change law m B (Lattice.gauge g U.val) _=law m B U.val x; exact law_g m B U.val x g
  ct:= by
    let J := fun t:Pack m B=>law m B t.1 t.2
    change Continuous (J ∘ release (m:=m) (B:=B) (e:=e)); exact (show Continuous J from law_cont m B).comp (releaseCt (m:=m) (B:=B) (e:=e))
  reflL _ _ := fun _ _ _=>rfl

def Breath (m B : Side) (e : ℝ) := {x:Train m B e|law m B x.1.val x.2≠0}
lemma breathed (p : 1 ≤ H) (e : ℝ) : booth (travel m B e H p)=Breath m B e:= rfl
lemma openB (m B : Side) (e : ℝ) : IsOpen (Breath m B e) := isOpen_ne_fun ((travel m B e 1 le_rfl).ct) continuous_const
lemma pays {v : Train m B e} (p : v∈ Breath m B e) : release v∈payer m B e := ⟨v.1.property,law_rich m B v.1.val v.2 p⟩ -- tune
lemma scents (p : 1≤H) {U V : Briar m B e} {S : Stamp m B} (k : (welter m B e H p).zone (pavilion m B S) U V) (i) (h:i∈chairs m B S) : ((travel m B e H p).seat U).run i=((travel m B e H p).seat V).run i := by
  funext x; apply water_limit _ _ i x x (fun i _=>rfl)
  change Agrees (mount m B _) U.val V.val at k; rw [mount_p] at k; exact fun j g p=> k j (in_wall (chair_pad h) g) (in_wall (chair_pad h) p)
abbrev Dedicated (p:1≤H) (S : Stamp m B) (f : Train m B e→ Ewe m B) (w : ℝ) := Petal.Manifest (travel m B e H p) f w (pavilion m B S) (chairs m B S)
lemma subscribing {S : Stamp m B} (p:1≤H) {v : Train m B e→ Ewe m B} {w : ℝ} (hw:0≤w) (e : ∀ x∈Breath m B e,tier H (v x).val≤w) -- shadows e rename
    (k : ContinuousOn v (Breath m B _)) (K : ∀ x∈Breath m B _,(v x)∈ stretch (brigade m B (pavilion m B S))) (m' : ∀ x∈Breath m B _,∀ y∈Breath m B _,Agrees (walls m B S) x.1.val y.1.val→AgreeF (chairs m B S) x.2 y.2→ v x=v y) (q : ∀ x∈Breath m B _,∀ g,routeM m B g (v x)=v (routeT x g)) : Dedicated p S v w := by
  refine ⟨hw,chair_pad,e,K,k,fun U=> base_down U.val (nested_ch S), ?_,fun k i l=>scents p k i l, fun g x p=> q x p g⟩ -- implicit trouble
  intro x y hx hy P H; change Agrees (mount m B _) x.1.val y.1.val at P; rw [mount_p] at P; exact m' x hx y hy P H
lemma scalarC : Continuous (hollow (n:=Hearth m B)) := Continuous.subtype_mk (by change Continuous fun x:ℂ=>x • (1:FC (Hearth m B)); fun_prop) _
lemma route_s (g : Court m B) (x : ℂ) : routeM m B g (hollow x)=hollow x := by
  exact fold_hollow (n:=Elf m B) x _
lemma curried {S : Stamp m B} {v : Pack m B → ℂ} {w : ℝ} (p : 1≤H) (he : supportsCup m B S v w e) : Dedicated (e:=e) p S (fun x:Train m B _=> hollow (v (release x))) w := by
  refine subscribing (v:=fun x:Train m B e=> hollow (n:=Hearth m B) (v (release x))) (S:=S) p he.2.2.1 (fun x g=>?_) ?_ (fun x g=>?_) (fun x hx y hy g l=>?_) (fun x g k=>?_)
  · rw [hollow_cost]; exact he.2.1 _ (pays g)
  · exact (scalarC (m:=m) (B:=B)).comp_continuousOn (he.1.comp releaseCt.continuousOn (fun _=>pays))
  · apply (stretch_ok ..).mpr; exact Flour.grainE (s:=brigade m B (pavilion m B S)) |>.smul (v (release x))
  · exact congrArg _ ( he.2.2.2.2.2 _ (pays hx) _ (pays hy) l g)
  · rw [show v (release (routeT x k))=v (release x) from he.2.2.2.1 k (release x) (pays g)]; exact route_s (m:=m) (B:=B) k _
end YM.CF.Ave
