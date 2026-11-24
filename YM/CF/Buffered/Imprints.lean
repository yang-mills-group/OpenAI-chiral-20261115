import YM.CF.Buffered.Cloakage
/-! # Same tile, mirrored or carried to new slot, cubical cover laws -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {m p v w B:Side}

def maskC (T:Finset Axis): Axis→Bool:= fun i=> decide (i∈T)
def lengthV (w:Side)(T:Finset Axis):Cover:=fun i=> if i∈T then w.val else 0
def flipC (w:Side)(T:Finset Axis)(x:Cover):Cover:=(glazed (maskC T)).act x + lengthV w T
lemma flip_iff (T:Finset Axis)(x:Cover)(i:Axis) : flipC w T x i= if i∈T then w.val-x i else x i:=by
 simp [flipC,lengthV,maskC]; split_ifs <;> omega
lemma flip_empty (T:Finset Axis)(x:Roost w ∅) : flipC w T x.val=(shades T x).val:= funext fun i=>by rw [flip_iff]; simp [shades,topwall]
lemma flip_edge (T:Finset Axis)(i:Axis)(x:Roost w {i}) : flipC w T x.val=(shades T x).val+if i∈T then step i else 0:=by
 funext j; rw [flip_iff]; unfold shades topwall; by_cases h:i∈T <;> by_cases e:j=i <;> simp_all [step_apply] <;> omega
lemma wrap_one (w:Side): Lattice.wrap w 1=(1:Site w):=funext fun i=> by change ((1:ℤ):Per w)=_; norm_cast
lemma mirror_mask (i:Axis) : glazed (maskC {i})=Signed.mirror i:=by
 rw [show (maskC {i})=(fun j=>decide (i=j)) from funext fun j => by by_cases h:i=j <;> simp [maskC,h,eq_comm]]
 ext; rfl; simp [Signed.mirror,glazed] -- tune

namespace Ordered
variable (K:Ordered m v p)(B) (r t:Rail (Uniform p)) (T:Finset Axis)
local notation "G" => sugar K B
local notation "q" => K.pebbles
local notation "d" => spirit K B
local notation "a" => Signed.act (glazed (maskC T))

def cruise (_K:Ordered m v p)(r t:Rail (Uniform p))(T:Finset Axis) : Cover :=
 let s (r:Rail (Uniform p)) : Cover:= fun i=> (More v).val*(r i).val; a' T (s r) (s t)
 where a' (T:Finset Axis)(s w:Cover):Cover:= w - (glazed (maskC T)).act s + lengthV (More v) T
-- Trip chosen in actuality. sends r→t and uses mask T for tile center mirrors.
def ferry (K:Ordered m v p)(r t: Rail (Uniform p))(T:Finset Axis): Trip m:= ⟨maskC T, Lattice.wrap _ (cruise K r t T)⟩
lemma ferry_grid : paneShift (ferry K r t T)= Lattice.wrap _ (Planck.sail q t - a (Planck.sail q r)+lengthV (GridN v) T):=by
 unfold paneShift; rw [Ratio.root_embed]; change Ratio.embed _ (Lattice.wrap _ _)=_; rw [Ratio.embed_wrap]; apply congrArg; funext i; unfold Planck.sail; change (2:ℕ) • (cruise K r t T) i = _; unfold cruise cruise.a'; dsimp only; simp [maskC,lengthV, show (GridN v).val=(More v).val*2 from rfl]; split_ifs <;> ring
lemma ferry_gauge : torShift B (ferry K r t T)=Lattice.wrap _ (Planck.sail G t-a (Planck.sail G r)+lengthV (Domain v B) T) :=by
 unfold torShift; rw [ferry_grid,Ratio.root_embed, Ratio.embed_wrap]; apply congrArg; funext j; unfold Planck.sail; rw [show (scaleR _ _).count=B from rfl]; simp [lengthV,maskC]; split_ifs <;> ring
lemma ferry_label (x:Cover): Trip.adv (ferry K r t T) (Planck.zone q r x)=(Planck.zone q t (flipC (GridN v) T x)):=by
 unfold Trip.adv affine Planck.zone flipC; rw [Lattice.wrap_signed,ferry_grid,← map_add]; apply congrArg; simp only [ferry,Signed.act_add]; abel
lemma ferry_read (x: Cover): run B (ferry K r t T) (Planck.zone G r x)=Planck.zone G t (flipC (Domain v B) T x) := by unfold run affine Planck.zone flipC; rw [wrap_signed,ferry_gauge,←map_add]; apply congrArg; simp only [ferry,Signed.act_add]; abel
lemma ferry_link (i:Axis) (x : Roost (Domain v B) {i})(F: Skin m B) : through B (ferry K r t T) F (Planck.zone G r x.val,i)= (if i∈T then (F (Planck.zone G t (shades T x).val,i))⁻¹ else F (Planck.zone G t (shades T x).val,i)):=by
 let z:=ferry K r t T; let U:=Planck.zone G r x.val
 have he : through B z F (U,i)=if z.glare i then (F (run B z U-step i,i))⁻¹ else F (run B z U,i):=by
    unfold through; change Step.read _ _ _=_; cases g:z.glare i <;> simp [Step.read,Step.used,g,glazed,posDir,Step.rotate]; rfl; rfl
 rw [he,show run B z U=_ from ferry_read B K r t T x.val, flip_edge]; unfold z; simp only [ferry,maskC,decide_eq_true_eq]; split_ifs <;> simp [Planck.zone,← add_assoc] -- tune
lemma ferry_extract (x:Pack m B) : reel r (fromCube K (onPack B (ferry K r t T) x)) = Rails.past T (reel t (fromCube K x)):=by
 apply Prod.ext
 · funext i y; unfold Rails.past; dsimp only; simp_rw [butter]; exact ferry_link ..
 funext i; unfold Rails.past; dsimp only; rw [cand,cand]; change x.2 (Trip.adv _ _)=_; rw [ferry_label,flip_empty]

lemma placeAddress (x:Cover) : address m B (Planck.zone q r x)=Planck.zone G r (B.val • x):=by
 unfold address Planck.zone; rw [Ratio.root_embed,Ratio.embed_wrap]; apply congrArg; funext i; rw [show (scaleR _ _).count=B from rfl]; unfold Planck.sail; simp only [Pi.add_apply, Pi.smul_apply]; rw [gauge_vs]; simp only [nsmul_eq_mul]; push_cast; ring
lemma placeNode (x:Cover) : node (Planck.zone d r x)= Planck.zone G r ((2:ℕ) • x+1):=by
 unfold node Planck.zone; rw [Ratio.root_embed,Ratio.embed_wrap,←wrap_one,←map_add]; apply congrArg; funext i; rw [show (assembly _).count.val=2 from rfl]; unfold Planck.sail; simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply]; rw [show (Domain v B).val=(CSide v B).val*2 from rfl]; simp only [nsmul_eq_mul]; push_cast; ring
lemma placePlus (x:Cover) (i:Axis) : Planck.zone G r (x+step i)=Planck.zone G r x+step i:=by unfold Planck.zone; rw [←add_assoc,map_add,wrap_step]
lemma placeMinus (x:Cover) (i:Axis) : Planck.zone G r (x-step i)=Planck.zone G r x-step i:=by rw [eq_sub_iff_add_eq, ←placePlus (K:=K),sub_add_cancel] -- tune
end Ordered
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ordered.ferry_extract
