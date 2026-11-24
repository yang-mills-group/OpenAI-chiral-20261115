import YM.CF.Buffered.Piling
/-! # Exact tilings into the physical cubes -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase RP MeasureTheory Roost Mil
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {m p v B:Side}{δ:Axis→Side}{w:Side}

lemma gauge_vs (v B : Side) : (Domain v B).val=(GridN v).val* B.val:= (scaleR v B).exact_size -- tune
lemma forG (m n:Side)(K:Planck m n p) : Planck (GridN m) (GridN n) p:=⟨by rw [natM,natM,natM,natM,K.ratio]; ring⟩
structure Ordered (m v p:Side):Prop extends Planck m v p where
 onGrid : Landing (Uniform p)
namespace Ordered
variable (K:Ordered m v p)

theorem pebbles (K:Ordered m v p) : Planck (GridN m) (GridN v) p:=forG m v K.toPlanck
theorem sugar (K:Ordered m v p)(B:Side): Planck (Domain m B) (Domain v B) p:=⟨by rw [gauge_vs,gauge_vs,K.pebbles.ratio]; ring⟩
theorem spirit (K:Ordered m v p)(B:Side): Planck (CSide m B) (CSide v B) p:=⟨by change m.val*2*B.val=v.val*2*B.val*p.val; rw [K.ratio]; ring⟩
end Ordered

abbrev Locale (v:Side) (B:Side):= ((i:Axis) → Roost (Domain v B) {i} → E) × (Roost (GridN v) ∅ →Ballot)
abbrev Rails (δ:Axis→Side)(v B:Side) := (((Rail δ × Post (Domain v B)) × Axis) → E) × (Rail δ × Post (GridN v) → Ballot)
namespace Rails

def law (δ:Axis→Side)(v B:Side): Measure (Rails δ v B) := (Measure.pi (fun _=> SU.group.probHaar)).prod (Measure.pi (fun _=>cloud))
instance (δ:Axis→Side)(v B:Side) : IsProbabilityMeasure (law δ v B):= by unfold law; infer_instance

def reel (r:Rail δ)(x:Rails δ v B) : Locale v B := (fun i j=> x.1 (Roost.slide r j,i),fun j=>x.2 (Roost.slide r j))
@[fun_prop] lemma reel_cont (r:Rail δ) : Continuous (reel (v:=v) (B:=B) r):= ((continuous_pi fun _=>continuous_pi fun _=> continuous_apply _).comp continuous_fst).prodMk ((continuous_pi fun _=> continuous_apply _).comp continuous_snd)

def past (T:Finset Axis)(x:Locale v B): Locale v B:=
 (fun i j=> if i∈T then (x.1 i (shades T j))⁻¹ else x.1 i (shades T j),fun j=> x.2 (shades T j))
lemma past_one {i:Axis} {T:Finset Axis}(p:i∉T)(x:Locale v B) : past (insert i T) x=past {i} (past T x):=by
 have he{w A} (x:Roost w A) : shades (insert i T) x= shades T (shades {i} x):=by
    rw [shades_push x p]; apply Subtype.ext; funext k; simp only [shadeOne,shades,mem_singleton]; by_cases h:k=i
    · subst k; simp [p]
    simp [h]
 apply Prod.ext
 · funext j k; dsimp only [past]; rw [he]; by_cases h:j=i <;> simp_all
 funext j; dsimp only [past]; rw [he]
lemma past_empty (x:Locale v B): past ∅ x=x:=by
 have he{w A}(x:Roost w A): shades ∅ x=x:=Subtype.ext (funext fun i=> by simp [shades])
 apply Prod.ext; · funext i x; simp [past,he];
 funext i; simp [past,he]
@[fun_prop] lemma past_cont (T) : Continuous (past (v:=v) (B:=B) T):= by unfold past; apply Continuous.prodMk _ (continuous_pi fun _=> (continuous_apply _).comp continuous_snd); refine continuous_pi fun _=> continuous_pi fun _=>?_ ; split <;> fun_prop
private lemma shade_advance (h: Landing δ) {A:Finset Axis}(x:Roost w A)(r: Rail δ) (i:Axis) :
 i∈shade (Roost.slide r x).1 ↔ if x.val i=w.val then i∉shade r else i∈shade r:=by
 unfold shade; simp only [mem_filter,mem_univ,true_and, Roost.slide, Pi.add_apply, corner, plusWall]; split_ifs with e; swap; · rw [add_zero]
 rw [←next_rail r i]; simpa only [if_true, shade,mem_filter,mem_univ,true_and] using shade_next r i h i
private lemma shade_across (h:Landing δ)(r:Rail δ){A:Finset Axis}(x:Roost w A):
    shades (shade (Roost.slide r x).1) (ofpost A x.wallet)=shades (shade r) x:=by
 apply Subtype.ext; funext i; by_cases p:x.val i=w.val
 · have ht:= (shade_advance h x r i); rw [if_pos p] at ht; have hx:(ofpost A x.wallet).val i=0:=if_pos p; have hz: i∉A:= fun u=> (x.below i u).ne p
   unfold shades; dsimp only; by_cases e:i∈shade r <;> simp [ht,topwall,hx,hz,e,p] -- tune replacements
 have ht:= (shade_advance h x r i); rw [if_neg p] at ht; unfold shades; dsimp only; simp only [ht,show (ofpost A x.wallet).val i=x.val i from if_neg p]

/-- Reflected repetition of one closed tile. Legal continuations use this. -/
def replica (δ:Axis→Side)(x:Locale v B): Rails δ v B:= (fun y=> (past (shade y.1.1) x).1 y.2 (ofpost {y.2} y.1.2),fun y=> (past (shade y.1) x).2 (ofpost ∅ y.2))
lemma reeling (h: Landing δ) (x: Locale v B)(z:Rail δ) : reel z (replica δ x) = past (shade z) x:=by
 apply Prod.ext
 · funext i y; dsimp only [reel,past,replica]; change (if i∈shade (Roost.slide z y).1 then _ else _)= _
   have ht:=shade_advance h y z i; rw [if_neg (y.below i (mem_singleton_self i)).ne] at ht; simp only [show (Roost.slide z y).2=y.wallet from rfl, ht,shade_across h z y] -- tune
 funext y; dsimp only [reel,past,replica]; exact congrArg x.2 (shade_across h z y)
lemma reel_zero (h: Landing δ)(x: Locale v B): reel 0 (replica δ x) = x:=by
 rw [reeling h, show shade (0:Rail δ)=∅ from ?_,past_empty]; ext i; unfold shade; simp
@[fun_prop] lemma replica_cont (δ): Continuous (replica (v:=v) (B:=B) δ):= by unfold replica; exact (continuous_pi fun _=> (continuous_apply _).comp ((continuous_apply _).comp (continuous_fst.comp (past_cont _)))).prodMk (continuous_pi fun _=> (continuous_apply _).comp (continuous_snd.comp (past_cont _)))
end Rails
namespace Ordered
open Rails
variable (K:Ordered m v p)
local notation "δ" => Uniform p
local notation "G" => sugar K B
local notation "D" => K.pebbles

def coast (K:Ordered m v p)(x:Rails (Uniform p) v B): Pack m B:=
 (x.1 ∘ ((sugar K B).slots.prodCongr (Equiv.refl Axis)).symm, x.2 ∘ K.pebbles.slots.symm)
def fromCube (K:Ordered m v p)(x:Pack m B): Rails (Uniform p) v B:=
 (x.1 ∘ ((sugar K B).slots.prodCongr (Equiv.refl Axis)), x.2 ∘ K.pebbles.slots)
lemma atCube (x:Rails δ v B): fromCube K (coast K x)=x:=by
 unfold fromCube coast; simp only [comp_assoc, Equiv.symm_comp_self,comp_id,Prod.eta]
lemma onto (x:Pack m B): coast K (fromCube K x)=x:=by unfold coast fromCube; simp only [comp_assoc, Equiv.self_comp_symm, comp_id,Prod.eta]
lemma butter (x:Pack m B)(r:Rail δ)(i:Axis)(y:Roost (Domain v B) {i}): (reel r (fromCube K x)).1 i y=x.1 ((sugar K B).zone r y.val,i):=by unfold reel fromCube; dsimp only; simp only [comp_apply]; change x.1 (((sugar K B).zone (Roost.slide _ y).1 _),_)=_; rw [Planck.zone_slide]; rfl
lemma cand (x:Pack m B)(r:Rail δ)(y: Roost (GridN v) ∅): (reel r (fromCube K x)).2 y=x.2 (K.pebbles.zone r y.val):=by unfold reel fromCube; dsimp only; simp only [comp_apply]; change x.2 _=_; exact congrArg x.2 (Planck.zone_slide ..)

omit B
section
variable {T I J:Type*}[MeasurableSpace T][Fintype I][Fintype J] (F:I≃J)
lemma reEnd (μ:Measure T)[SigmaFinite μ]: MeasurePreserving (fun x:I→T=> x∘F.symm) (Measure.pi (fun _=>μ)) (Measure.pi (fun _=>μ)):=by
 have he := measurePreserving_piCongrLeft (α:=fun _:J=>T) (fun _=>μ) F
 rw [show (fun x:I→T=> x∘F.symm)=(MeasurableEquiv.piCongrLeft (fun _:J=>T) F) from ?_]; · exact he
 funext x y; obtain ⟨y,rfl⟩:= F.surjective y; simp [MeasurableEquiv.piCongrLeft_apply_apply]
end
include B
lemma coast_mp : MeasurePreserving (coast (B:=B) K) (Rails.law δ v B) (wheel m B) := (reEnd ((sugar K B).slots.prodCongr (Equiv.refl Axis)) SU.group.probHaar).prod (reEnd K.pebbles.slots cloud)
lemma coast_cont : Continuous (coast (B:=B) K):= by unfold coast; fun_prop
lemma cube_cont : Continuous (fromCube (B:=B) K):= by unfold fromCube; fun_prop

def toRails (K:Ordered m v p)(B:Side) : Rails (Uniform p) v B ≃ᵐ Pack m B:= ⟨⟨coast K, fromCube K, atCube K, onto K⟩,(coast_cont K).measurable,(cube_cont K).measurable⟩
lemma into_coast {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F](f: Pack m B→ F): ∫ z, f z∂wheel m B= ∫ z,f (coast K z)∂ Rails.law δ v B:= ((show MeasurePreserving (toRails K B) _ _ from coast_mp K).integral_comp' f).symm
end Ordered
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ordered.into_coast
#print axioms YM.CF.Buffered.Region.Rails.reeling
