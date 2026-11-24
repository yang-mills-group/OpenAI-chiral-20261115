import Mathlib.Logic.Equiv.Bool
import YM.CF.BProof.Stave.Bire
import YM.CF.BProof.Borel
/-! Tolerance d fixed ⇒ actual gallery. color bit for charge to restore
conjugate snap also on self-conjugate frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Metric MeasureTheory Filter Topology Finset Set
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators ENNReal NNReal Classical
variable {I C : Type*}[Fintype I][Fintype C]
-- matrix measurable inst check
variable [MeasurableSpace (plate I)] [BorelSpace (plate I)] -- tune library
structure Tray (I:Type*) [Fintype I] [MeasurableSpace (plate I)] (d:ℝ) where
  q : ℕ
  pos : 0<q
  port : Fin q→plate I
  king (i) : port i ∈ King I
  snap : plate I → Fin q
  meas : Measurable snap
  cost (A:plate I) : A∈ King I→ dist (port (snap A)) A<d
namespace Tray
private lemma selector {d:ℝ}{k:ℕ}[Nonempty (Fin k)](A:Fin k→plate I) (H:∀ x∈ King I,∃ i,dist (A i) x<d):∃ T:plate I→Fin k, Measurable T ∧ ∀ x∈ King I,dist (A (T x)) x<d:=by
 have he:IsClosed {p: plate I × Fin k|∀ i,dist (A p.2) p.1≤ dist (A i) p.1}:=by
    have ht:Continuous A:= continuous_of_discreteTopology; rw [Set.setOf_forall]; exact isClosed_iInter fun i=> isClosed_le ((ht.comp continuous_snd).dist continuous_fst) (continuous_const.dist continuous_fst)
 obtain ⟨f,g,h⟩:= closed_choice _ he (fun x=>by obtain ⟨i,_,hi⟩:= isCompact_univ.exists_isMinOn Set.univ_nonempty (f:=fun i=>dist (A i) x) continuous_of_discreteTopology.continuousOn; exact ⟨i,fun j=> hi (Set.mem_univ j)⟩)
 refine ⟨f,g,fun x hx=>?_⟩; obtain ⟨i,hi⟩:= H x hx; exact ((show ∀ i,dist (A (f x)) x ≤ dist (A i) x from h x) i).trans_lt hi
lemma tender {d:ℝ}(h:0<d)(p:(King I).Nonempty):Nonempty (Tray I d):=by
 obtain ⟨S,hS,g,W⟩:=finite_cover_balls_of_compact (compact_F I) h; letI:=g.fintype; let q:=Fintype.card S; let a:= Fintype.equivFin S; let A(i:Fin q) : plate I:= (a.symm i).val
 have H(x)(hx:x∈ King I):∃ i,dist (A i) x < d:=by
    obtain ⟨j,e,he⟩:= Set.mem_iUnion₂.mp (W hx); refine ⟨a ⟨j,e⟩,?_⟩; rw [dist_comm]; simpa only [A,Equiv.symm_apply_apply] using (Metric.mem_ball.mp he)
 obtain ⟨x,p⟩:=p; haveI : Nonempty (Fin q):= ⟨(H x p).choose⟩; refine ⟨⟨q,(Fin.pos_iff_nonempty).2 this,A,fun i=>hS (a.symm i).property,(selector A H).choose,(selector A H).choose_spec.1,(selector A H).choose_spec.2⟩⟩ -- tune
variable {d:ℝ} (T:Tray I d)
abbrev Mint (q:ℕ)(C:Type*):=C×(Fin q × Bool)
local notation "M" => Mint T.q C
def pose (v:M): plate I:= if v.2.2=true then blink (T.port v.2.1) else T.port v.2.1
def tag (c:C)(b:Bool)(A:plate I):M:= (c,T.snap (if b=true then blink A else A),b)
def flip (k:ℕ)(C:Type*): Equiv.Perm (Mint k C) := Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (Equiv.boolNot))
omit [Fintype C] [BorelSpace (plate I)] in
lemma marks(c:C)(b:Bool)(A:plate I):T.tag c (!b) (blink A)= flip T.q C (T.tag c b A):=by cases b <;> simp [tag,flip]
omit [Fintype C] [BorelSpace (plate I)] in
lemma budget(c:C)(b:Bool){A:plate I}(h:A∈ King I): dist (T.pose (T.tag c b A)) A<d:=by
 cases b; exact T.cost A h; unfold tag pose; simp only [↓reduceIte]; rw [← blink_dist,blink_blink]; exact T.cost _ (king_blink h)
omit [Fintype C] in
lemma stamps [MeasurableSpace C](c:C)(b:Bool) : Measurable (T.tag c b):=by cases b; exact measurable_const.prodMk (T.meas.prodMk measurable_const); exact measurable_const.prodMk ((T.meas.comp (show Continuous (blink : plate I→plate I) from isometry_blink.continuous).measurable).prodMk measurable_const)
variable (C)
def house: Gallery (Mint T.q C) I where
 adm S:= Set.InjOn Prod.fst (S:Set M)
 less h g:= g.mono h
 μ:= flip T.q C
 flip_μ:=by ext x <;> rfl
 μ_adm S:= by
    let e:=flip T.q C; apply propext; constructor
    · rintro h a (ha:a∈S) b (hb:b∈S) hab; exact e.injective (h (Finset.mem_map_of_mem _ ha) (Finset.mem_map_of_mem _ hb) hab)
    intro h a ha b hb hab; obtain ⟨a,(p:a∈S),rfl⟩:=Finset.mem_map.mp (Finset.mem_coe.mp ha); obtain ⟨b,p',rfl⟩:=Finset.mem_map.mp (Finset.mem_coe.mp hb); rw [h (Finset.mem_coe.mpr p) (Finset.mem_coe.mpr p') (show Prod.fst a=Prod.fst b from hab)]
 car:=T.pose
 portrait i:=by unfold pose; split; exact king_blink (T.king _); exact T.king _
 μ_car:= by rintro ⟨i,j,p|p⟩ <;> simp [pose,flip] -- Bool syntax
 cross S h p z:= by
    obtain ⟨i,hi⟩:= p; have he:(flip T.q C) i=i:=h (z ▸ (show (flip T.q C) i∈ S.map _ from Finset.mem_map_of_mem _ hi)) hi rfl; obtain ⟨i,j,u⟩:=i; cases u <;> simp [flip] at he
end Tray
end YM.CF.BProof.Mesh.Stave
