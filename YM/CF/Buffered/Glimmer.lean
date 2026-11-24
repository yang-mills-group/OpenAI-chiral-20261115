import YM.CF.Buffered.Marquee
/-!
# PaintLoom: corresponding *marginal laws* on adequate subboxes (not repeats)

Using the component implementation property of the Loomloc choice from earlier, including its family of finite displacement coloring laws! This is not a dependence-only fact, nor a result of Roof conditions. Prove using the Basic description, iid inputs etc. Don't need to construct any Basic approximations nor prove the Color sampling availability.
-/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory ProbabilityTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye Py Mail.Unison Mail Scree
open Further.PhysicalPeriodLimitF933 Macrame Wilson
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal NNReal
attribute [local instance] opCStarAlgebra
namespace Pont
-- tape starts at degree zero vertex indeg =0. max continuation Fintype.card
-- Literal form of 'margin on proper runs, no cycles included' from lemma loomloc.
abbrev Ink := Fin 4
def fill {I:Type*} (G:I→ I→Prop) (x:I): Option I:= by classical exact if p:∃ y,G x y then some p.choose else none
def road {I:Type*}(G:I→I→Prop)(f:I→Ink)(x:I):ℕ→List Ink
 | 0=>[]
 | n+1=> f x::(match fill G x with|none=>[]|some y => road G f y n)
noncomputable def combo {I:Type*}[Fintype I] (μ:List Ink→ℝ≥0∞)(G:I→I→ Prop)(f:I→Ink): ℝ≥0∞:= by classical exact ∏ i∈univ.filter (fun j=> ¬∃ i,G i j),μ (road G f i (Fintype.card I))
def Rising {I:Type*} (G:I→I→Prop): Prop:=∃ φ:I→ℤ,∀ i j, G i j → φ i<φ j
variable {m n p v k B B':Side} {T:Type}[MeasurableSpace T]
-- `ν` describes iid draws (Haar, orientations and numbers; we don't
-- need to know actual distribution details provided issued) and S is the set
-- of nonzero coloring displacements. μ density on linear coloring run (length dependent normalizers included).
abbrev Mood (I:Type*) := I→ Ink
abbrev MoodS (S:Finset Cover) (I:Type*) := {x: Cover // x∈S} → Mood I
abbrev Dye (S: Finset Cover) (T I:Type*) := (I→T)× MoodS S I
structure InkPlan (N:Side)(S:Finset Cover)(μ:List Ink→ℝ≥0∞) where
 dyer : S → Measure (Mood (Site N))
 dyer_p (x:S) : IsProbabilityMeasure (dyer x)
 mark (x:S) (I:Type)[Fintype I](v:I↪ Site N) (h: Rising (fun i j=> v i+wrap N x.val = v j)) (f:I→Ink) :
   (Measure.map (fun y:Site N→ Ink=> y∘ v) (dyer x)) {f}= combo μ (fun i j=> v i+wrap N x.val=v j) f
attribute [instance] InkPlan.dyer_p
variable {S:Finset Cover}
variable {μ:List Ink→ℝ≥0∞} {ν:Measure T}[IsProbabilityMeasure ν]
noncomputable def law (ν:Measure T) (H:InkPlan m S μ) : Measure (Dye S T (Site m)):= (Measure.pi (fun _=> ν)).prod (Measure.pi (H.dyer))
instance ink_prob(H:InkPlan m S μ) : IsProbabilityMeasure (law ν H):=by unfold law; infer_instance
def project (S:Finset Cover)(T: Type*) {I J:Type*}(i:I→J) (x: Dye S T J) : Dye S T I:= ((x.1 ∘ i),fun z=> x.2 z ∘ i)
private lemma projection_m {I J:Type*}(i:I→J) : Measurable (project S T i):= by apply Measurable.prodMk (measurable_pi_lambda _ fun j=>(measurable_pi_apply _).comp measurable_fst); apply measurable_pi_lambda; intro z; exact measurable_pi_lambda _ fun j=> (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
private lemma prP {I J:Type}[Fintype I][Fintype J](A:S→ Measure (Mood J)) [∀ z,IsFiniteMeasure (A z)] (e:I↪J) : (Measure.pi (fun _:J=>ν)|>.prod (Measure.pi A)).map (project S T e) = (Measure.pi (fun _:I=>ν)).prod (Measure.pi (fun z=> (A z).map (fun y:Mood J=>y ∘ e))) :=by
 classical
 let f(x:J→T):= x ∘ e; let g(x:MoodS S J):= fun z:S=> x z ∘ e; rw [show project S T e=Prod.map f g from rfl, ← Measure.map_prod_map]; swap; · exact measurable_pi_lambda _ fun i=> measurable_pi_apply _
 swap; · apply measurable_pi_lambda; intro x; exact measurable_pi_lambda _ fun i=> (measurable_pi_apply _).comp (measurable_pi_apply _)
 refine congrArg₂ Measure.prod ?_ (Measure.pi_map_pi (f:=fun z y=> y ∘ e) (fun z=>((show Measurable (fun y:Mood J=> y ∘ e) from measurable_pi_lambda _ fun i=> measurable_pi_apply _)).aemeasurable))
 -- projection to I is independent
 let k:=Radiant.keysZ e; let l := (MeasurableEquiv.sumPiEquivProdPi (fun _: I⊕ Radiant.other e=> T)).symm.trans (MeasurableEquiv.piCongrLeft (fun _:J=>T) k); let s'(I:Type):=fun (_:I)=> ν
 have h: MeasurePreserving l ((Measure.pi (s' I)).prod (Measure.pi (s' (Radiant.other e)))) (Measure.pi (s' J)) := (measurePreserving_piCongrLeft (fun _:J=>ν) k).comp (measurePreserving_sumPiEquivProdPi_symm (X:=fun _=> T) (fun _=> ν))
 apply MeasurePreserving.map_eq; rw [show f=Prod.fst ∘ l.symm from ?_]; · exact measurePreserving_fst.comp (MeasurePreserving.symm l h)
 funext x i; change x (e i)= _; nth_rw 1 [←Radiant.key_in]; rfl
-- patch

-- incomplete cycles at every embedded box tile. Relation for these stencils gets same cover displacement costs, never periodic within such a run.
lemma dv_up (K:Ordered m v p)(j:Side): 2*(Domain v j).val ≤ (Domain m j).val:=by rw [(K.sugar j).ratio]; have ht:2≤ p.val:=landing_ge K.onGrid 0; rw [mul_comm 2]; exact Nat.mul_le_mul_left _ ht
section geometry
variable (K:Planck m v p)(H:2*v.val ≤ m.val) {x:Cover} (b:x≠0) (a:∀ i:Axis, 2*(x i).natAbs < m.val)
include K
abbrev dimC (K:Planck m v p) := Installed.point K.slots (0:Rail (Uniform p))
lemma atC (z:Post v): dimC K z=wrap m z.val:=by change K.zone _ z.val = _; unfold Planck.zone; rw [show K.sail (0:Rail (Uniform p))=0 from funext fun _=>by simp [Planck.sail],zero_add]
include a H
lemma alongP (j k:Post v): dimC K j+wrap m x=dimC K k ↔ j.val+x=k.val:=by
 have h': lift (dimC K k-dimC K j)=k.val-j.val:=by
    rw [atC,atC,←map_sub]; apply lift_eq_iff.2; refine ⟨rfl,fun i=>?_⟩; rw [Pi.sub_apply]; have hp:= (j.property i).1; have hv:= j.below i (mem_univ _); have hs:=k.nonneg i; have hu:= k.below i (mem_univ _); omega
 have hx: lift (wrap m x)=x:= lift_eq_iff.2 ⟨rfl,fun i=>by specialize a i; omega⟩
 constructor; · intro h; have hv:= h'; rw [←h,add_sub_cancel_left,hx] at hv; rw [hv,add_sub_cancel]
 intro h; rw [atC,atC,← map_add,h]
include b
lemma steep: Rising (fun i j=> dimC K i+wrap m x=dimC K j):=by
 obtain ⟨i,t⟩:=Function.ne_iff.mp b; change x i≠0 at t; rcases lt_or_gt_of_ne t with v'|v'; · refine ⟨fun x=> -x.val i,fun j k h=>?_⟩; have he:= congr_fun ((alongP K H a j k).1 h) i; rw [Pi.add_apply] at he; change -j.val i < -k.val i; omega
 refine ⟨fun x=> x.val i,fun j k h=>?_⟩; have he:= congr_fun ((alongP K H a j k).1 h) i; rw [Pi.add_apply] at he; change j.val i < k.val i; omega
end geometry
include S
lemma costs (K:Planck m v p)(L:Planck n v k)(b:2*v.val ≤ m.val)(a:2*v.val ≤ n.val) (h:∀ i∈S, i≠0∧∀ j, 2*(i j).natAbs < m.val ∧ 2*(i j).natAbs<n.val) (Z:InkPlan m S μ)(Q:InkPlan n S μ): (law ν Z).map (project S T (dimC K))=(law ν Q).map (project S T (dimC L)):=by
 unfold law; rw [prP,prP]; apply congrArg; apply congrArg; funext i; classical
 obtain ⟨v,p⟩:= h i.val i.property; have w':∀ j,2*(i.val j).natAbs < m.val:=fun j=>(p j).1; let l':=fun j=>(p j).2
 apply Measure.ext_of_singleton; intro j
 have hc:(fun j k=> dimC K j+wrap m i.val=dimC K k)=(fun j k=> dimC L j+wrap n i.val=dimC L k):=funext fun j=> funext fun k=>propext ((alongP K b w' j k).trans (alongP L a l' j k).symm)
 rw [Z.mark i _ _ (steep K b v w'),Q.mark i _ _ (steep L a v l'), hc]
-- standalone for a partner Cube. Input: a selection which implements and repeats even on LEGAL decor Paint, including those values not drawn in actual law, and is locally expressible in all its variables there. Lifts of legal Paint still legal at larger sizes. Don't assert independence of Loom w/ arbitrary Id reads. Need not know any choice of values off sector of dependences here, except construction post(a.e.).
structure Colors (S:Finset Cover)(T:Type)[MeasurableSpace T](μ: List Ink→ℝ≥0∞)(ν: Measure T)[IsProbabilityMeasure ν](N: Side)(w:ℕ)(Y:Loom N) where
 ink : InkPlan (More N) S μ
 mix : Pane N → Dye S T (Site (More N)) → Pane N
 measurable x : Measurable (mix x)
 valid : Set (Dye S T (Site (More N)))
 legality : ∀ᵐ x ∂law ν ink,x∈valid
 Y_m : Measurable Y
 genuine (x:Pane N) : Measure.map (mix x) (law ν ink) = Measure.map (fun i:Ids N=>Y (x,i)) (depot N)
 essence (x:Pane N)(I:Support (More N)):∃ g:Dye S T {i: Site (More N)// i∈(halo w I : Finset _)}→ LEData I, Measurable g ∧ ∀ p∈valid, g (project S T Subtype.val p)=extract I (mix x p)
variable (Y:Loom m)(y:Loom n) -- remove implicit
variable {w:ℕ} (G': Planck m n B) (H:Colors S T μ ν m w Y) (F:Colors S T μ ν n w y)
local notation "r" => (slump (Mail.gauge_plan G'))
def Intent (N:Planck m n B)(S:Finset Cover)(T:Type)(U:Dye S T (Site (More n))) := project S T (Macrame.Window.cut (slump (Mail.gauge_plan N))) U
structure Replicable (G:Planck m n B)(H:Colors S T μ ν m w Y)(F:Colors S T μ ν n w y): Prop where
 tall : ∀ x∈S,x≠0 ∧ ∀ i:Axis, 2*(x i).natAbs < (More n).val
 goes (x)(p:x∈F.valid): Intent G S T x∈ H.valid
 hits (x)(p:x∈F.valid)(U:Pane n): H.mix (weave (gauge_plan G) U) (Intent G S T x)=weave (gauge_plan G) (F.mix U x)

variable (W:Planck (More m) v p)(J:Planck (More n) v k)
-- first box & bounds on both
include J in
lemma under_one (I: Support (More m))(b:2*v.val ≤ (More m).val)(a:2*v.val ≤ (More n).val)(Z:halo w I⊆ wallZ W 0 1) (L: Replicable Y y G' H F): Grok.LoomLaw2 G' Y y I:= by
 intro X; let Q:=weave (gauge_plan G') (show Wilson.Config SU.group _ from X); obtain ⟨g,hg,d⟩:=H.essence Q I
 let A:={x: Seat m// x∈(halo w I : Finset _)}
 have ht(x:A): ∃ j, dimC W j=x.val:= by
    obtain ⟨z,l,p⟩:=(Solid.seam ..).1 (Z x.property); refine ⟨⟨z,fun i=>?_⟩,p.symm⟩; specialize l i; rw [wall_mem i (mem_univ _)]; norm_num at l; omega
 choose k T' using ht
 let V':Dye S T (Post v)→ LEData I:= g ∘ project S T k
 have hp:Pont.project S T (Subtype.val:A→ Seat m) = project S T k ∘ project S T (dimC W):= by
    rw [←show (dimC W) ∘ k=(Subtype.val:A→ Seat m) from funext T']; rfl
 let Fv:=law ν F.ink; let Y₀(x:Dye S T (Site (More m))):=H.mix Q x
 have he:(∃ t:ℕ,0 ≤ t):=⟨0,le_rfl⟩
 have hv(x:Dye S T (Site (More n))): project S T (dimC W) (Intent G' S T x)= project S T (dimC J) x :=by
    have he(z:Post v):(slump (gauge_plan G')).cut (dimC W z)=dimC J z:=by rw [atC,atC]; exact (Macrame.branch ..)
    apply Prod.ext; · exact funext fun z=> congrArg x.1 (he z)
    exact funext fun i=>funext fun z=>congrArg (x.2 i) (he z)
 let f(x):= extract I (weave (gauge_plan G') (show Wilson.Config SU.group _ from F.mix X x))
 let l: Pane n → Pane m:=fun x=>weave (gauge_plan G') x
 have hm:Measurable l:=(weave_cont ..).measurable -- tune
 have hf:Measurable V':=hg.comp (projection_m ..)
 have he: extract I ∘ H.mix Q =ᵐ[law ν H.ink] V' ∘ project S T (dimC W):= H.legality.mono fun x p=> (by unfold V'; rw [Function.comp_assoc,←hp]; exact (d x p).symm)
 have hu: f =ᵐ[law ν F.ink] V' ∘ project S T (dimC J):= F.legality.mono fun x t=>by unfold f V'; dsimp only [Function.comp_apply]; rw [← L.hits x t X, ← d (Intent G' S T x) (L.goes x t), hp]; rw [Function.comp_apply,hv]
 change Measure.map (extract I ∘ fun i=> Y (Q,i)) _=Measure.map ((extract I ∘ l) ∘ fun i=> y (X,i)) _
 rw [←Measure.map_map (extract_mp _) (show Measurable (fun i:Ids m=>Y (Q,i)) from H.Y_m.comp (measurable_const.prodMk measurable_id)),←Measure.map_map ((extract_mp _).comp hm) (show Measurable (fun i:Ids n=> y (X,i)) from F.Y_m.comp (measurable_const.prodMk measurable_id)),← H.genuine,← F.genuine, Measure.map_map (extract_mp _) (H.measurable _), Measure.map_map ((extract_mp _).comp hm) (F.measurable _), Measure.map_congr he,Measure.map_congr (show (extract I ∘ l) ∘ F.mix X =ᵐ[_] _ from hu),← Measure.map_map hf (projection_m _),← Measure.map_map hf (projection_m _), costs W J b a ?_ H.ink F.ink]; intro i h; refine ⟨(L.tall i h).1,fun j=>?_⟩; have ht:=(L.tall i h).2 j; exact ⟨ht.trans_le (Mail.width (gauge_plan G')),ht⟩
end Pont
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.Pont.costs
