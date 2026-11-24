import YM.CF.Buffered.Imprints
/-! # Scalar plaquette facades on the closed tiles -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {m p v w B n:Side}

def energyF (q: Clip)(u:E): ℝ := SU.group.price u - Design.bulk q*surplus (G:=SU.group) u
def coinF (q: Clip)(u:E): ℝ:= (energyF q u+ energyF q (Reef.qG u))/2
def tideF (u:E): ℝ:= max ‖(firstF u).val-1‖ ‖(matter u).val-1‖
structure Sanctum {Y:Type*}(F:E→Y) : Prop where
 inv(x): F x⁻¹=F x
 conj(x y): F (x*y*x⁻¹)=F y
variable (q:Clip)(V:Bkg n)
lemma energy_s : Sanctum (energyF q):= by
 refine ⟨fun x=> ?_,fun x y=>?_⟩; · unfold energyF; rw [Gauge.price_inv, surplus_inv]
 unfold energyF; rw [Gauge.price_conj,surplus_conjugate]
lemma coin_s : Sanctum (coinF q):=by
 refine ⟨fun x=>?_,fun x y=>?_⟩; · rw [coinF,map_inv,(energy_s q).inv,(energy_s q).inv]; rfl
 rw [coinF,map_mul,map_mul, map_inv,(energy_s q).conj,(energy_s q).conj]; rfl
lemma chord_s : Sanctum SU.group.chord:= ⟨SU.group.chord_inv, SU.group.chord_conj⟩
private lemma fare_s {I:Type*}[Fintype I][DecidableEq I](R:E→*UNI I): Sanctum fun u:E=> ‖(R u).val-1‖:=by
 constructor
 · intro u; rw [map_inv]; change ‖star _-_‖=_; rw [← star_one (R:=Op I), ←star_sub, norm_star, star_one]
 intro g v; rw [map_mul,map_mul,map_inv]; change ‖(R g).val*_*star (R g).val-1‖=_; rw [←twist_formula, show twist (R g) _-1=twist (R g) ((R v).val-1) by rw [map_sub,map_one],twist_norm]
lemma tide_s : Sanctum tideF:= ⟨fun _=>congrArg₂ max ((fare_s firstF).inv _) ((fare_s matter).inv _),fun _ _=>congrArg₂ max ((fare_s firstF).conj ..) ((fare_s matter).conj ..)⟩
-- no one-plaquette smoothness claims. 
lemma plain_s : Vale.basicP q V=∑ i:Face (Per n), coinF q (faceValue V i):=by
 unfold Vale.basicP coinF; rw [←sum_div, sum_add_distrib, Spark.renFace q id V V (fun _=>rfl), Spark.renFace q Reef.qG V _ (fun _=>Reef.echo_t ..)]; rfl
lemma flags_s (x:ℝ) : V∈Calm group n x↔ ∀ i:Face (Per n), SU.group.chord (faceValue V i) ≤ x:=by
 change flags x V=∅ ↔_; rw [eq_empty_iff_forall_notMem]; constructor
 · intro h i; by_contra! p; exact h i.1 ((flags_spec ..).mpr ⟨i,WilsonStartup.anchor_visit i,p⟩)
 rintro h i t; obtain ⟨j,_,e⟩:= (flags_spec ..).mp t; exact (not_lt_of_ge (h j)) e
lemma guard_s (x:ℝ): Guard V x ↔ ∀ i:Face (Per n), tideF (faceValue V i) ≤ x:=by
 unfold tideF; simp_rw [max_le_iff]; rw [forall_and]; apply and_congr <;> apply (show ∀ {I:Type} [Fintype I][DecidableEq I](R:E→*UNI I), PlaqBound R V x ↔ ∀ i:Face (Per n), ‖(R (faceValue V i)).val-1‖ ≤ x from ?_)
 all_goals
  intro I _ _ R; constructor
  · rintro t ⟨p,⟨⟨i,j⟩,h⟩⟩; exact t p i j (ne_of_lt h)
  intro t p i j h; cases lt_or_gt_of_ne h
  next h=> exact t (p,⟨(i,j),h⟩)
  next h=> rw [show travel V p (square i j)= _ from oriented_swap (posDir j) (posDir i) p V,(fare_s R).inv]; exact t (p,⟨(j,i),h⟩)

namespace Facade
def frame (i:PlaqAxes):Finset Axis:= {i.val.1,i.val.2}
def leftE (w:Side)(i:PlaqAxes)(j:Axis)(p:j∈frame i)(x:Roost w (frame i)): Roost w {j}:=⟨x.val,fun k=> ⟨x.nonneg k,by
 unfold topwall; split; next h=> rw [mem_singleton] at h; exact le_trans ((x.property k).2) (le_of_eq (if_pos (h ▸ p)))
 exact x.maxval k⟩⟩ -- tune
lemma west (i:PlaqAxes): i.val.1∈frame i:= mem_insert_self ..
lemma east (i:PlaqAxes): i.val.2∈frame i:=mem_insert_of_mem (mem_singleton_self ..)
def nextE (w:Side)(i:PlaqAxes)(j k:Axis)(p:j∈frame i)(g:k∈frame i)(e:j≠k)(x:Roost w (frame i)):Roost w {j}:=⟨x.val+step k,fun l=> by
 by_cases h:l=k; swap; · simp [Pi.add_apply,step_apply,h]; exact (leftE w i j p x).property l
 subst l; rw [Pi.add_apply,step_apply, if_pos rfl,topwall, if_neg (by simp [Ne.symm e])]; have a:= x.below k g; have u:= x.nonneg k; omega⟩
-- tile plaquette oriented +i,+j,-i,-j.
def detail (i:PlaqAxes)(x:Roost (Domain v B) (frame i))(U:Locale v B): E:=
 U.1 i.val.1 (leftE _ _ _ (west i) x)*(U.1 i.val.2 (nextE _ _ _ _ (east i) (west i) (Ne.symm i.property.ne) x) * ((U.1 i.val.1 (nextE _ _ _ _ (west i) (east i) i.property.ne x))⁻¹ * (U.1 i.val.2 (leftE _ _ _ (east i) x))⁻¹))
lemma intrinsic (K:Ordered m v p)(r:Rail (Uniform p))(i:PlaqAxes)(x:Roost (Domain v B) (frame i))(U:Pack m B):
 detail i x (reel r (K.fromCube U)) = faceValue U.1 ((K.sugar B).zone r x.val,i):=by
 unfold detail; simp_rw [Ordered.butter]; dsimp only [leftE,nextE]; rw [Ordered.placePlus B K, Ordered.placePlus B K]; unfold faceValue square; simp only [travel,mul_one,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg]; simp [sub_eq_add_neg, add_left_comm, add_comm, add_assoc]
 congr 4 <;> abel

lemma shift_price (K:Ordered m v p)(r t:Rail (Uniform p))(T:Finset Axis)(i:PlaqAxes)(x:Roost (Domain v B) (frame i))(U:Pack m B){Y:Type*}{F:E→Y}(h:Sanctum F):
 F (faceValue (onPack B (K.ferry r t T) U).1 ((K.sugar B).zone r x.val,i))= F (faceValue U.1 ((K.sugar B).zone t (shades T x).val,i)):=by
 let Q:= K.ferry r t T; let K':= torShift B Q; let P:= glazed (maskC T); let z: Site (Domain m B) :=(K.sugar B).zone r x.val
 have he : i.rotate P=i:=Subtype.ext (show (min i.val.1 i.val.2,max i.val.1 i.val.2)=_ from Prod.ext (min_eq_left i.property.le) (max_eq_right i.property.le))
 change F (faceValue (pull P K' U.1) (z,i))=_; rw [Face.send_price _ _ _ _ _ h.inv (fun x y=>h.conj y x)]
 congr 2 -- tune
 unfold Face.send Face.lower atFace; simp only [he]; congr 1; rw [show affine P K' z= run B Q z from rfl,Ordered.ferry_read B K r t T x.val]
 let a(i:Axis):Step:=if i∈T then negDir i else posDir i
 have ha(i:Axis): Step.rotate (posDir i) P=a i:=by unfold a P posDir; simp [maskC,glazed,Step.rotate]; split_ifs <;> simp_all [negDir]
 funext j
 have h':= i.property.ne
 simp_rw [ha, Pi.add_apply]; rw [Planck.zone_one,Planck.zone_one,flip_iff]; unfold a; split_ifs with e; all_goals by_cases l:j=i.val.1 <;> by_cases z:j=i.val.2 <;> simp_all [shades,topwall,frame,Step.vec,posDir,negDir,step_apply] <;> ring

lemma detail_cont (i:PlaqAxes)(x:Roost (Domain v B) (frame i)): Continuous (detail i x):= by unfold detail; fun_prop
end Facade
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Facade.shift_price
