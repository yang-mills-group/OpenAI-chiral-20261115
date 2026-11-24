import YM.CF.BProof.Mapping.Lens
import YM.CF.BProof.Release.Gain

/- measurability as projections of product, Borel source of physical variables.
 Definition non-trims supports/pay (guard fall back via extensions later).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.Pawn
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox House Gauss Release Charge Release.hot
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(S:Hall s)

abbrev Coord (Y:Yard s):= (Finset Y.Col × Y.Glyph) × (Roll.Plan Y × Locale.House Y) × Config G s
def pack : Pawn Y≃ Coord Y where
 toFun x:= ((x.sev,x.mood),(x.gauss,x.gap),x.dust)
 invFun x:=⟨x.1.1,x.2.1.1,x.2.1.2,x.2.2,x.1.2⟩
 left_inv x:=rfl
 right_inv x:=rfl
instance : MeasurableSpace (Pawn Y):=MeasurableSpace.comap (pack Y) inferInstance
def volume : Pawn Y≃ᵐ Coord Y:= ⟨pack Y,comap_measurable _,by apply measurable_comap_iff.mpr; rw [Equiv.self_comp_symm]; exact measurable_id⟩ -- tune
@[fun_prop] lemma sev_m : Measurable (Pawn.sev (Y:=Y)):= ((measurable_fst.comp measurable_fst).comp (volume Y).measurable) -- tune
@[fun_prop] lemma mood_m : Measurable (Pawn.mood (Y:=Y)):= ((measurable_snd.comp measurable_fst).comp (volume Y).measurable)
@[fun_prop] lemma gauss_m : Measurable (Pawn.gauss (Y:=Y)):= (measurable_fst.comp (measurable_fst.comp measurable_snd) |>.comp (volume Y).measurable)
@[fun_prop] lemma gap_m : Measurable (Pawn.gap (Y:=Y)):= (measurable_snd.comp (measurable_fst.comp measurable_snd) |>.comp (volume Y).measurable)
@[fun_prop] lemma dust_m : Measurable (Pawn.dust (Y:=Y)):= (measurable_snd.comp measurable_snd |>.comp (volume Y).measurable)
variable {Y}
variable (x: Pawn Y)(y:ℝ)(T:PathData G){R:ℝ}{c:Clip}{M:ℕ}(θ:ℝ)(U: Beam c R Y.short M y)
/-- Measurable evaluator of an arbitrary function selected by a finite charge (`Pawn.sev`). -/
lemma onSev {F:Type*}[MeasurableSpace F](f:Finset Y.Col→ Pawn Y→ F)(p:∀ i,Measurable (f i)) : Measurable (fun x:Pawn Y=> f x.sev x):= (measurable_from_prod_countable_left (f:=fun x: Pawn Y×Finset Y.Col=> f x.2 x.1) p).comp (measurable_id.prodMk (sev_m Y)) -- universe
lemma onSign {F:Type*}[MeasurableSpace F](f:Y.Glyph→ Pawn Y→ F)(p:∀ i,Measurable (f i)) : Measurable (fun x:Pawn Y=> f x.mood x):= (measurable_from_prod_countable_left (f:=fun x: Pawn Y×Y.Glyph=> f x.2 x.1) p).comp (measurable_id.prodMk (mood_m Y))
lemma sev_sets (f:Finset Y.Col→ Prop) : MeasurableSet {x:Pawn Y| f x.sev}:= (show Measurable (Pawn.sev (Y:=Y)) from sev_m Y) (Set.Countable.measurableSet (Set.to_countable _)) -- tune
lemma sev_eq_m (Z:Finset Y.Col):MeasurableSet {x:Pawn Y|x.sev=Z}:= sev_sets (fun i=>i=Z)
variable (Y)
@[fun_prop] lemma level_m : Measurable (fun a:Pawn Y=> level (Y:=Y) a y T θ U):= by unfold Pawn.level; refine onSev (F:=Locale.House Y) (fun Z (x:Pawn Y)=> Release.γ Y T θ y U Z x.gauss x.gap) ?_; intro b; change Measurable (Function.uncurry (Sky.reach Y T θ y U b) ∘ (fun x:Pawn Y=> (x.gap,x.gauss))); exact (Sky.reach_m Y T θ y U (Z:=b)).comp ((gap_m Y).prodMk (gauss_m Y))
@[fun_prop] lemma issue_m : Measurable (fun a:Pawn Y=> issue (Y:=Y) a y T θ U):= (Locale.issue_c ..).comp (level_m ..)
@[fun_prop] lemma rent_m : Measurable (fun a:Pawn Y=> rent S a y T θ U):= onSign (fun m a=> Y.sweepLabel y S (issue a y T θ U) m) (fun i=> (Y.sweepLabel_m y S i).comp (issue_m ..))
@[fun_prop] lemma put_m : Measurable (fun a:Pawn Y=> Pawn.put S a y T θ U):= (Y.play_m y S).comp (f:=fun x:Pawn Y=> ((issue x y T θ U,rent S x y T θ U),x.dust)) (((issue_m Y y T θ U).prodMk (rent_m Y S y T θ U)).prodMk (dust_m Y))
@[fun_prop] lemma weight_m : Measurable (fun a:Pawn Y=> Pawn.weight a y T θ U):=onSev (fun Z x=> tape Y T θ U Z x.gauss) (fun Z=> (hot.tape_m ..).comp (gauss_m Y))
@[fun_prop] lemma roof_m : Measurable (fun a:Pawn Y=> Pawn.roof a y T θ U):=by
 let f(a:Pawn Y):= Pawn.weight a y T θ U; have he:Measurable f:= weight_m Y y T θ U; apply onSev (fun Z x=> Y.roof Z (f x)); intro Z; apply measurable_pi_lambda; intro i; unfold Yard.roof; split; exact measurable_const; exact (measurable_pi_apply (X:=fun _ : Y.Door => Mag.Lie) i).comp he

-- draw argument domain (for readability estimates, not core extension yet)
def Proceeds (κ:ℝ) (x:Pawn Y):= Fares Y y x.gauss ∧ Locale.bed Y κ y (level x y T θ U)=x.sev ∧ Certified S x y T θ U ∧ Y.Climate y S (Pawn.put S x y T θ U) (rent S x y T θ U)
def Rich (κ:ℝ)(x:Pawn Y) := Fares Y y x.gauss ∧ Locale.bed Y κ y (level x y T θ U)=x.sev ∧ Y.accepted y S (issue x y T θ U) x.mood ∧ ∀ i, group.chord (x.dust i)≤xi y
lemma Rich.lucky {κ:ℝ} (p:Rich Y S y T θ U κ x)(v: ∀ i, ¬Y.D i→ ∀ b:Bool,Y.Firmly S (issue x y T θ U) (rent S x y T θ U) i b) : Proceeds Y S y T θ U κ x:= ⟨p.1,p.2.1,v, Y.created y S _ _ x.dust v p.2.2.2⟩
-- avoid proof Measurable Climate includes existential. All activity applications on assembly rich, never arbitrary. prove Rich measurable
lemma rich_m (κ:ℝ): MeasurableSet {x:Pawn Y|Rich Y S y T θ U κ x}:=by
 let a:= {x:Pawn Y|Fares Y y x.gauss}; let b:= {x:Pawn Y|Locale.bed Y κ y (level x y T θ U)=x.sev}; let t:Pawn Y→ Config G s:= (fun x=>issue x y T θ U)
 have he : MeasurableSet a:=by
    unfold a Fares; simp_rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro k; exact (show Measurable (fun x:Pawn Y=> hot.entry Y x.gauss k) by unfold hot.entry Function.curry; fun_prop) (Day.pit_c _) -- tune
 have hp: MeasurableSet b:=by
    unfold b; rw [show {x:Pawn Y| _}=⋃ z:Finset Y.Col, {x: Pawn Y|Locale.bed Y κ y (level x y T θ U)=z}∩{x|x.sev=z} from ?_]; exact MeasurableSet.iUnion fun z=> ((level_m Y y T θ U) (Locale.berth Y κ y z)).inter (sev_eq_m z); ext; simp; exact eq_comm -- tune
 have hv : MeasurableSet {x:Pawn Y| Y.accepted y S (t x) x.mood}:=by
    rw [show {x:Pawn Y| _}=⋃ i:Y.Glyph, {x:Pawn Y|Y.accepted y S (t x) i}∩{x|x.mood=i} from ?_]; exact MeasurableSet.iUnion fun i=> ((issue_m ..) (Y.accepted_m y S i)).inter ((mood_m Y) (measurableSet_singleton i)); ext; simp
 apply he.inter; apply hp.inter; apply hv.inter; change MeasurableSet {x:Pawn Y|∀ i, group.chord (x.dust i)≤xi y}; rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro i; exact measurableSet_le (by fun_prop) measurable_const
end YM.CF.BProof.Mapping.Pawn
