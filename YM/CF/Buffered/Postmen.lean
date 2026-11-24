import YM.CF.Buffered.Buttons
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.RoofTile
/-!
# Actual tesselation mark across two m with tickets on same d' & data

Pull repeated links, corner push into first period box and then support integration. Don't
re-invoke a volume gluing lemma for the response, prove affinity of link kernel adjoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Mail
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase Reflect Window MeasureTheory RG
open Region Roost Rails Mil Fock Graph Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale
open Further.PhysicalPeriodLimitF933 Macrame
open Crust Grid Wilson
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K V C k v N P L D M B B' l c: Side} {G:Gauge}

lemma gauge_plan (A:Planck N P D) : Planck (More N) (More P) D:=⟨by rw [natM,natM,A.ratio]; ring⟩
variable (A:Planck N P D)
-- map on sites no tag order. always the unlabeled repeating copies
abbrev slump (A:Planck N P D) := Macrame.normal (show P.val∣N.val from Dvd.intro _ A.ratio.symm) A.ratio
abbrev weave (U: Config G P) := (slump A).links U
lemma too (x:Site N): (slump A).cut x= lesser₀ A x:= rfl
abbrev recurM {n p:Side}(A:Planck n p D) (U: Fields p) : Fields n:= (weave (gauge_plan A) (show Config SU.group _ from U.1),weave (gauge_plan A) U.2)
lemma weave_cont : Continuous (weave (G:=G) A):=continuous_pi fun _=> continuous_apply _

def pointO (A:Planck N P D) (r : Tower D): Site P ↪ Site N := Installed.point (send A) r
variable (r: Tower D)
def modeO (r: Tower D): Single P ↪ Single N:= Embedding.prodMap ((pointO A r).prodMap (Embedding.refl SpinIdx)) (Embedding.refl SU.Slot)
abbrev Vc (x:Site N) := ledge A x
def blockF : Support N:= univ.filter fun x=> ledge A x=r
lemma atF {x:Site N}: x∈ blockF A r ↔ ledge A x=r :=by unfold blockF; simp
lemma takeL (x:Site P): pointO A r x=A.zone r (natural x):=rfl
lemma dime (x:Site P) : pointO A 0 x=Lattice.wrap N (natural x):=by rw [takeL]; unfold Planck.zone; rw [show A.sail 0=0 from funext fun j=>by simp [Planck.sail],zero_add]
lemma stepR (x:Site P): (slump A).cut (pointO A r x)=x:= by rw [too,lesser_pay]; exact (lesser_here A r x).2
lemma ledge_of (x:Site P): ledge A (pointO A r x)=r:=(lesser_here A r x).1
lemma restep {x:Site N}(h:x∈blockF A r): pointO A r ((slump A).cut x)=x:= by rw [too,lesser_pay,←(atF A r).1 h,takeL]; exact tile ..
lemma oh (A:Planck N P D){x:Cover}(h:∀ i,0≤x i∧x i<P.val): natural (wrap P x)=x:=by funext i; unfold natural; rw [wrap_here,int_val _ (h i).1 (h i).2,Int.toNat_of_nonneg (h i).1]
lemma modes_step (x:Site P): node (pointO A 0 x)=pointO (gauge_plan A) 0 (node x) := by
 rw [dime,node_of,dime]; apply congrArg; nth_rw 2 [←Rush.nat_true x]; rw [node_of]; apply Eq.symm; apply oh (gauge_plan A); intro i; unfold nodeC natural; have he:= (x i).val_lt; simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply,natM,two_smul]; omega
-- codomain hugs
abbrev EvenBox (A:Planck N P D){u:Support N}: Prop := u ⊆ blockF A 0
include A in
lemma width : P.val ≤ N.val:=by rw [A.ratio]; exact Nat.le_mul_of_pos_right _ D.property
lemma nested (H:Planck P B M)(F:Planck N B l){e:ℕ}(u:0<e) {b:Site N}(p:b∈wallZ F 0 e) : b∈blockF A 0 :=by
 obtain ⟨z,t,rfl⟩:=(Solid.seam ..).1 p; apply (atF ..).2; let x:=wrap P z; rw [show F.zone 0 z=pointO A 0 x from ?_]; · exact ledge_of ..
 unfold Planck.zone; rw [dime,show F.sail 0=0 from funext fun j=>by simp [Planck.sail],zero_add,oh A ?_]; intro i; specialize t i; have he:=width H; omega
lemma inside_to (H:Planck P B M)(F:Planck N B l){e:ℕ}(u:0<e){x:Site P}(h:x∈ wallZ H 0 e): pointO A 0 x∈wallZ F 0 e:=by
 obtain ⟨z,t,rfl⟩:=(Solid.seam ..).1 h; apply (Solid.seam ..).2; refine ⟨z,t,?_⟩; unfold Planck.zone; rw [dime,show F.sail 0=0 from funext fun j=>by simp [Planck.sail],show H.sail 0=0 from funext fun j=>by simp [Planck.sail],zero_add,oh A ?_]; intro i; specialize t i; have he:=width H; omega
variable {p' m:Side}
abbrev SugarGrid (A:Planck m v p')(B:Side) : Planck (CSide m B) (CSide v B) p' :=⟨by change m.val*2*B.val=v.val*2*B.val*p'.val; rw [A.ratio]; ring⟩
abbrev gaugedG (K:Planck m v p')(B:Side):= gauge_plan (SugarGrid K B) -- `More`
abbrev CoherentV (f: Mark P) (g : Mark N) : Prop:= ∀ W:Fields P,g (recurM A W) =into (modeO A 0) (f W)
-- leverage support in first tile infers winding alignment (provided kTiles/p tiles≥2): any edge in the Locale tails of the small & big first tile uses bottom through closed. so can compare on first Locale directly when BIG is whole despite repeating from small (perhaps change tag tail synth using ax-independent whole). Don't require coherentV on other pairs than physical here.
lemma erect_outer (A:Ordered K L C)(F:Ordered V L M)(h:Planck K V v)(B:Side) (p:GridM L B): modeO (SugarGrid h B) 0 (Installed.point (Region.Wings.regionX F B) 0 p)=Installed.point (Region.Wings.regionX A B) 0 p:=by
 obtain ⟨⟨x,u,s⟩,rfl⟩:= (Bays.wall (Post (CSide L B)) Spin).surjective p
 let J:= SugarGrid h B; let z(K:Side)(r:Planck K (CSide L B) M):= r.zone 0 x.val
 have ht: pointO J 0 ((F.spirit B).zone 0 x.val)=(A.spirit B).zone 0 x.val := by rw [dime, Region.Wings.natural_true, Wings.liftZ,show (F.spirit B).sail 0=(A.spirit B).sail 0 from funext fun j=> by simp [Planck.sail]]; rfl
 exact congrArg (fun z:Site (CSide K B)=>((z,u),s)) ht
lemma smaller_tile (A:Ordered K L C)(F:Ordered V L M)(h:Planck K V v)(r:Pack V B)(x:Pack K B)(t:x.1=weave (gauge_plan (SugarGrid h B)) (show Config SU.group _ from r.1)): (reel 0 (A.fromCube x)).1=(reel 0 (F.fromCube r)).1:=by
 funext j u; rw [A.butter,F.butter,t]; change r.1 ((slump _).cut _, j)=_; apply congrArg (fun z=> r.1 (z,j)); unfold Planck.zone; rw [show (slump _).cut _=wrap (Domain V B) _ from (Macrame.branch .. : _), show (F.sugar B).sail 0=(A.sugar B).sail 0 from funext fun j=>by simp [Planck.sail]] -- tune
lemma child_reach (A:Ordered K L C)(F:Ordered V L M)(h: Planck K V v){b:Mark (CSide V B)}{t:Mark (CSide K B)}{e:ℕ} (p:AtSupport false (wallZ (A.sugar B) 0 e) t)(hp:0<e)(u:CoherentV (SugarGrid h B) b t){Z:Badge L B}(g:Wings.stamps F 0 b Z)(j:∀ x y:Locale L B,x.1=y.1→ Z.label x=Z.label y): Wings.stamps A 0 t Z:=by
 intro x; let r:= reel 0 (A.fromCube x); let a:=whole F r; let y: Pack K B := (weave (gauge_plan (SugarGrid h B)) (show Config SU.group _ from a.1),x.2)
 have he:(reel 0 (A.fromCube y)).1=(reel 0 (F.fromCube a)).1:=smaller_tile A F h a y rfl
 have ha : reel 0 (F.fromCube a)=reel 0 (A.fromCube x):=whole_zero ..
 have ht:=Wings.interior A 0 hp (he.trans (congrArg Prod.fst ha))
 have hx:= g a
 have hu: both t y.1=into (modeO (SugarGrid h B) 0) (both b a.1):=u (a.1,a.1)
 rw [← show both t y.1=both t x.1 from p.dep _ _ ht ht,hu,hx,ha,into_trans _ (Installed.point (Region.Wings.regionX A B) 0) _ (erect_outer A F h B) (Z.state _)]
-- not using j if ha exact
end YM.CF.Buffered.Mail
#print axioms YM.CF.Buffered.Mail.child_reach
