import YM.CF.Buffered.Tracks
/-!
# Seam coordinates at the *many-slab horizon*. We can permit sharing of
cue variables also on the transverse subfaces. Film's seam alphabet holds full
arrays, coordinates unused filled by probability variables. Mirror across slab
midplane sees high-to-low seam swap.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B n w:Side}{δ:Axis→Side}{i:Axis}{ζ:TStem i}
variable (V:Traversed ζ δ n)
local notation "C" => Car ζ
local notation "T" => Fin n.val

-- shared addresses from neighbouring Transverse Car slots
variable {A:Finset Axis}(u:Car ζ)
def hotLoc (k:Side) (i:Axis)(x:Roost k A): Prop:= x.val i=k.val
def Lith (i:Axis)(A:Finset Axis)(x:Post w):Prop:= i∉A∧ x.val i=0 -- seam owned at low rail
instance (i A)(x:Post w): Decidable (Lith i A x):= by unfold Lith; infer_instance
instance (x:Roost w A) : Decidable (hotLoc w i x) := by unfold hotLoc; infer_instance

def cornea (u:Car ζ)(A:Finset Axis): Car ζ:=fun j=> if j.val∈A then u j+1 else u j
lemma scatters (u:Car ζ)(t:T)(x:Roost w A): Roost.slide (loc V t u) x=(loc V (if hotLoc w i x then t+1 else t) (cornea u x.plusWall), x.wallet):=by
 apply Prod.ext; swap; · rfl
 simp only [Roost.slide]; funext j; rw [Pi.add_apply]; unfold hotLoc; by_cases h:j=i
 · subst j; split_ifs with z
   · rw [← V.verge t (cornea u x.plusWall),next_rail,loc_v,loc_v, show corner δ _ i=1 from (show corner _ x.plusWall i=1 from by simp [corner,plusWall,z])]
   rw [loc_v,loc_v]; rw [show corner δ x.plusWall i=0 from by simp [corner,plusWall,z],add_zero]
 let t':Off i:=⟨j,h⟩; change loc _ _ _ t'.val+_ = loc _ _ _ t'.val; rw [loc_h,loc_h]; unfold corner cornea; by_cases e:t'.val∈x.plusWall
 · rw [if_pos (show j∈x.plusWall from e), if_pos e]; -- need franco
   exact (franco' (u t') (V.others t')).symm
 rw [if_neg (show j∉x.plusWall from e),if_neg e,add_zero]
where franco' {k l:Side}(x:Fin k.val)(e:k=l): Fin.cast (show k.val=l.val from congrArg Subtype.val e) (x+1)=(Fin.cast (show k.val=l.val from congrArg Subtype.val e) x)+1:=by subst k; rfl -- private prior copy
lemma cornea_v (x:Roost w A): cornea u (shades {i} x).plusWall=cornea u x.plusWall:=by
 funext j; unfold cornea; simp only [plusWall,mem_filter,mem_univ,true_and,shades_other x (mem_singleton.not.mpr j.property)]
lemma tipHigh (x:Roost w A)(h:hotLoc w i x): Lith i A x.wallet:= (mem_filter.mp (plus_allowed x (mem_filter.mpr ⟨mem_univ _,h⟩))).2.symm
lemma lith_mirror (x:Roost w A): Lith i A (wallet (shades {i} x)) ↔ Lith i A (wallet x):=by
 have ht(y:Roost w A) : Lith i A (wallet y)↔ i∈ball A (wallet y):=by simp only [Lith, Roost.ball,mem_filter,mem_univ,true_and,and_comm]
 rw [ht,ball_mirror, ht]
lemma twin_high (x:Roost w A)(h:Lith i A (wallet x)): hotLoc w i x ↔ ¬ hotLoc w i (shades {i} x):=by
 have he := (ball_iff i x).1 (mem_filter.mpr ⟨mem_univ _,h.2,h.1⟩); unfold hotLoc; rw [shades_eq _ (mem_singleton_self i)]; have hu:0< w.val:=floorL; unfold topwall; rw [if_neg h.1]; omega
-- mirror permutation on post coords. inactive, map only modulo its base (0 ≃w read); not between-volume.
def rear (A:Finset Axis)(i:Axis)(x:Post w):= (shades {i} (ofpost A x)).wallet
lemma commute_rear (x:Roost w A): rear A i x.wallet=(shades {i} x).wallet:=by
 apply Subtype.ext; funext j; by_cases e:j=i
 · subst j; by_cases p: x.val i=w.val
   · have he:i∉A:=fun h=> (x.below i h).ne p; simp [rear,wallet,ofpost,shades,topwall,he,p]
   simp [rear,wallet,ofpost,shades,p]
 have h:0<w.val:=floorL; simp [rear,wallet,ofpost,shades, e]; split_ifs <;> omega
lemma rear_mirror (A:Finset Axis)(i:Axis)(x:Post w): rear A i (rear A i x)=x:=by
 change rear A i ((shades {i} (ofpost A x)).wallet)=_; rw [commute_rear,shades_square,wallet_a]
lemma rear_lith (x:Post w) : Lith i A (rear A i x) ↔ Lith i A x:=by rw [rear,lith_mirror,wallet_a]

def LUT (ζ:TStem i)(w:Side) := (Car ζ × Post w) × Axis -- abbrev
abbrev Atlas (ζ:TStem i)(w:Side):= ((Car ζ × Post w) × Axis) → E
abbrev Ledger (ζ:TStem i)(w:Side):= Car ζ × Post w → Ballot
abbrev Wet (ζ:TStem i)(v B:Side) := Atlas ζ (Domain v B) × Ledger ζ (GridN v)
local notation "S" => Domain v B
local notation "b" => GridN v
local notation "L" => Locale v B

variable (s₀:Wet ζ v B)
def invertP {A:Type*}[Inv A](p:Prop)[Decidable p](x:A): A:=if p then x⁻¹ else x

def shell (f:Wet ζ v B): Wet ζ v B := (fun j=> invertP (i=j.2) (f.1 ((j.1.1, rear {j.2} i j.1.2),j.2)),fun j=> f.2 (j.1,rear ∅ i j.2))

@[fun_prop] lemma shell_cont : Continuous (shell (ζ:=ζ) (v:=v) (B:=B)):=by
 unfold shell; apply Continuous.prodMk; swap; · fun_prop
 apply continuous_pi; intro t; unfold invertP; split <;> fun_prop
lemma shell_one : shell (shell s₀)=s₀:=by
 apply Prod.ext; · funext j; simp only [shell,rear_mirror]; unfold invertP; split_ifs <;> simp
 funext j; simp only [shell,rear_mirror]

-- pack two seam + one interior. local tile exposures
local notation "Σq" => Stack.Cell (Wet ζ v B) (Wet ζ v B)
def selected {K:Type*}(v w x:K)(i:Axis)(z:Roost n A):= if Lith i A z.wallet then if hotLoc n i z then w else v else x
def host (x: Stack.Cell (Wet ζ v B) (Wet ζ v B))(u:Car ζ): L:= (fun j y=>
 let c:= cornea u y.plusWall; let z:= ((c,y.wallet),j)
 selected (x.1.1.1 z) (x.1.2.1 z) (x.2.1 z) i y,
 fun y=> let z := (cornea u y.plusWall,y.wallet); selected (x.1.1.2 z) (x.1.2.2 z) (x.2.2 z) i y)

lemma host_cont : Continuous fun x:Σq=> host x u:=by
 refine Continuous.prodMk (continuous_pi (fun _=> continuous_pi (fun _=>?_))) (continuous_pi (fun _=>?_)); all_goals unfold selected; dsimp only; split_ifs <;> fun_prop
-- orientation from shell, boundary coordinates don't rotate. prove formula either case inactive data invertP is id. 
lemma same_rear (x:Roost w A)(h:Lith i A x.wallet): x.wallet= (shades {i} x).wallet:=by apply Subtype.ext; funext j; by_cases e:j=i; subst j; exact h.2.trans ((lith_mirror x).2 h).2.symm; simp only [wallet, shades_other x (mem_singleton.not.mpr e)]
lemma host_mirror (x:Σq) : host (x.1,shell x.2) u=Rails.past {i} (host (mirrorCell _ _ x) u):=by
 apply Prod.ext
 · funext j y; dsimp only [mirrorCell,host,Rails.past,selected]; rw [cornea_v]; unfold shell invertP; dsimp only; by_cases l:Lith i {j} y.wallet
   · rw [if_pos l, same_rear y l]; have he:= (lith_mirror y).2 l; have hT:= twin_high y l; rw [if_pos he,if_neg (mem_singleton.not.mpr (fun e=> l.1 (mem_singleton.mpr e.symm)))]; split_ifs <;> first|rfl|tauto
   rw [if_neg l,if_neg (fun k=> l ((lith_mirror y).1 k)), commute_rear]; by_cases h:j=i <;> simp_all [eq_comm]
 funext y; dsimp only [mirrorCell,host,Rails.past,selected]; rw [cornea_v]; unfold shell; dsimp only; by_cases l:Lith i ∅ y.wallet
 · rw [if_pos l,same_rear y l]; have he:= (lith_mirror y).2 l; have hT:= twin_high y l; rw [if_pos he]; split_ifs <;> first|rfl|tauto
 rw [if_neg l,if_neg (fun k=> l ((lith_mirror y).1 k)),commute_rear]
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.host_mirror
