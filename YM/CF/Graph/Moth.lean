import YM.CF.Graph.Easel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open scoped NNReal ENNReal Classical
variable {m B J:Side}{o:Odd J.val}{j n:ℕ}{e a l r t K b v c:ℝ}{Y: Pricing j J o (Vault.Thread j)}{P:Grasp Y B e}{H:Pearl P}(D: Pic.Span H K b v c l r n) (A:GramM (mid m B))(X:Loom (mid m B))(W:Ward A)(hX:SkinT A X e)
def start(A:GramM (mid m B))(P:Grasp Y B e)(X:Loom (mid m B)):ℂ:=integralF m B (dim A) (cab A P X) (city _)
abbrev drip(A: GramM (mid m B))(P:Grasp Y B e):ℝ:= angle A *Kea.angel m P A.J.M
lemma dim_p(n:Side)(R:GramM n)(t:Orbit n) :0 ≤ dim R t:=Set.indicator_nonneg (fun _ _=> (Real.exp_pos _).le) _
lemma snake(n:Side)(R:GramM n)(t:Orbit n):t∈ Lace R ↔ 0<dim R t:=by
 constructor
 · intro h; rw [dim,Set.indicator_of_mem h]; exact Real.exp_pos _
 intro h; by_contra t'; rw [dim,Set.indicator_of_notMem t'] at h; exact (lt_irrefl _ h)
omit D W hX
include D W hX
lemma handout (Q:CoolR D m t A.p.threshold): Tab H Prod.fst (city _) (dim A) (cab A P X) A.J.M (K*(mid m B).val) t 0 1:=by
 let N:=mid m B; let f(i:Hat):Orbit N ≃ᵐ Orbit N:= (wEquiv (More N) i).prodCongr (MeasurableEquiv.refl _); have hk:= D.plan _ Q.frame; refine ⟨⟨f,fun i=>⟨(welt_p i).prod ((MeasurePreserving.id _)),fun p=>⟨rfl,?_⟩⟩⟩,one_pos,fun i=>dim_p _ _ _,(worth W).integrable _,?_,fun i h=> Q.roll i.1 ((snake _ A i).mpr h),fun i h=>⟨0,Pic.Pays.nil,?_⟩⟩
 · simp only [one_mul]; apply le_of_eq; unfold dim; by_cases p': p∈ Lace A
   · rw [Set.indicator_of_mem p',Set.indicator_of_mem (show (f i) p∈ Lace A from ?_)]; unfold past; rw [show ((f i) p).1=welt p.1 i from rfl,choc]
     change flags _ (welt p.1 i)=∅; rw [zen]; exact p'
   rw [Set.indicator_of_notMem p',Set.indicator_of_notMem]; intro h; apply p'; change flags _ (welt p.1 i)=∅ at h; rw [zen] at h; exact h
 · let R(f: Pic.wit m B):= inner ℂ (mateK (mid m B)) f; have ht: Envelope fun i=> Pic.beamM m B (cab A P X i):= pole_w _ R (Continuous.inner continuous_const continuous_id) (moon H D.stmt D.eP D.p hk.1 A X hX); exact ((worth W).integrable (city _)).smul_bdd _ ht.meas.aestronglyMeasurable (Eventually.of_forall ht.cost.choose_spec)
 rw [act_zero,add_zero]; unfold cab; rw [hX.high _ ((snake _ A i).2 h)]
lemma stoutC (Q:CoolR D m t A.p.threshold)(h:0≤ angle A): let U:= drip A P; let Z:=gleam m P A.J.M*start A P X; U*(b/(2* poseX))≤Z.re ∧ |Z.im| ≤ duty (mid m B).val t c 0*U ∧ U*(b/(2* poseX))≤ ‖start A P X‖∧ qpay (dim A) (cab A P X) (city _) ≤ 2*c*U :=by
 intro U Z; let M:=A.J.M; let a:=gleam m P M; obtain ⟨t',F⟩:= D.plan m Q.frame; have hp:0≤U:=mul_nonneg h (Kea.angel_p H D.stmt t' D.p D.eP A.J.M F).le
 obtain ⟨he,v,V⟩:= poised D Q.frame (handout D A X W hX Q) Q.pose Q.data Q.cap; have hx:= Q.coat; have hk:= pose_p
 have ht:U*(b/(2*poseX)) ≤ Z.re:=by apply le_trans ?_ he; apply mul_le_mul_of_nonneg_left _ hp; refine le_trans ?_ (sub_le_sub_left hx _); rw [one_mul]; field_simp; linarith -- tune
 have hq:= (gleams D Q.frame M).1; change ‖a‖=1 at hq
 refine ⟨ht,v,(ht.trans (Complex.re_le_norm Z)).trans_eq ?_,?_⟩; rw [norm_mul, (show ‖gleam _ _ _‖=1 from hq),one_mul]; apply V.trans; unfold U drip angle; apply le_of_eq; ring -- tune
end YM.CF.Graph
